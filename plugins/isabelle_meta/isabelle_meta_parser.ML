(* EOC proof reader template, adapted from iogos Cpc/Runtime/Parser.ML.
   Syntax and signature definitions come from isabelle-meta's generated tables.
   This reader is unverified; rule execution uses Isabelle's checker export. *)
structure CpcParser = struct
open CPC CpcSexp CpcSyntax;
exception Fuel;

fun find key entries = Option.map #2 (List.find (fn (name, _) => name = key) entries);
fun apply f x = Term_Apply (f, x);
fun applyAll head args = List.foldl (fn (x, f) => apply f x) head args;
fun argList terms = List.foldr (fn (t, rest) => CArgList_cons (t, rest)) CArgList_nil terms;
fun indexList indices = List.foldr
  (fn (i, rest) => CIndexList_cons (runtime_int (IntInf.fromInt i), rest)) CIndexList_nil indices;
fun cmdList cmds = List.foldr (fn (c, rest) => CCmdList_cons (c, rest)) CCmdList_nil cmds;

fun digits s = String.size s > 0 andalso List.all Char.isDigit (String.explode s);
fun integer s =
  let val body = if String.isPrefix "-" s then String.extract (s, 1, NONE) else s
  in if digits body then IntInf.fromString s else NONE end;
fun requireInteger s = case integer s of SOME n => n
  | NONE => raise Error ("expected integer, got " ^ s);
fun numeral n = Term_Numeral (runtime_int n);

fun literal text =
  let
    fun baseValue base chars = List.foldl (fn (c, n) =>
      let val digit = if Char.isDigit c then Char.ord c - 48
            else Char.ord (Char.toLower c) - Char.ord #"a" + 10
      in if digit < 0 orelse digit >= base then raise Error "invalid bit-vector literal"
         else n * IntInf.fromInt base + IntInf.fromInt digit end) 0 chars;
    fun rational a b = if b = 0 then raise Error "zero rational denominator"
      else SOME (runtime_rational a b);
  in
    if String.isPrefix "#b" text orelse String.isPrefix "#x" text then
      let val binary = String.sub (text, 1) = #"b";
          val chars = String.explode (String.extract (text, 2, NONE));
          val width = length chars * (if binary then 1 else 4)
      in if null chars then raise Error "empty bit-vector literal"
         else SOME (Term_Binary (runtime_int (IntInf.fromInt width),
                    runtime_int (baseValue (if binary then 2 else 16) chars))) end
    else case integer text of SOME n => SOME (numeral n) | NONE =>
      (case String.fields (fn c => c = #"/") text of
         [a, b] => (case (integer a, integer b) of
             (SOME x, SOME y) => rational x y | _ => NONE)
       | _ => (case String.fields (fn c => c = #".") text of
           [a, b] => if digits b then (case integer a of
               SOME x => let val d = IntInf.pow (10, String.size b);
                             val fraction = requireInteger b;
                             val n = x * d + (if String.isPrefix "-" a then ~fraction else fraction)
                         in rational n d end
             | NONE => NONE) else NONE
         | _ => NONE))
  end;

fun parse fuel text =
  let
    val bindings = ref [];
    val shadowed = ref [];
    val macros = ref [];
    val expanding = ref [];
    val symbols = ref 0;
    val sorts = ref 0;
    val stack = ref [];
    val scopes = ref [];
    val assumptions = ref [];
    val commands = ref [];
    fun result NONE = raise Fuel | result (SOME t) = t;
    fun bind key value = bindings := (key, value) :: !bindings;
    fun typeOf t = result ($TYPEOF$ fuel t);
    fun wellTyped t = typeOf t <> Term_Stuck;
    fun withBindings temporary body =
      let val saved = !bindings;
          val savedShadowed = !shadowed;
          val names = map #1 temporary;
          fun restore () = (bindings := saved; shadowed := savedShadowed)
      in
        bindings := temporary @ List.filter
          (fn (name, _) => not (List.exists (fn n => n = name) names)) saved;
        shadowed := names @ savedShadowed;
        (body () before restore ())
          handle exn => (restore (); raise exn)
      end;
    fun operator name = case List.find (fn (n, k, _, _) => n = name andalso k = 0) operators of
        SOME (_, _, _, build) => build []
      | NONE => raise Error ("unknown operator " ^ name);
    fun nilTerm head terms =
      if head = operator "@list" then operator "@list.nil"
      else result ($NIL$ fuel head (case terms of [] => Term_Type
        | t :: _ => typeOf t));
    fun right head [x] = x
      | right head (x :: xs) = apply (apply head x) (right head xs)
      | right _ [] = raise Error "operator needs at least two arguments";
    fun rightNil head args = List.foldr (fn (x, rest) => apply (apply head x) rest)
      (nilTerm head args) args;
    fun leftNil head args = List.foldl (fn (x, rest) => apply (apply head rest) x)
      (nilTerm head args) args;
    fun buildApp (Exact _) head args = applyAll head args
      | buildApp Left head (x :: xs) = List.foldl (fn (y, acc) => apply (apply head acc) y) x xs
      | buildApp Left _ [] = raise Error "operator needs arguments"
      | buildApp Right head args = right head args
      | buildApp RightNil head args = rightNil head args
      | buildApp LeftNil head args = leftNil head args
      | buildApp LeftNonSingletonNil _ [x] = x
      | buildApp LeftNonSingletonNil head args = leftNil head args
      | buildApp RightNonSingletonNil _ [x] = x
      | buildApp RightNonSingletonNil head args = rightNil head args
      | buildApp (Chain _) head [x, y] = apply (apply head x) y
      | buildApp (Chain connector) head args =
          let fun pairs (x :: y :: rest) = apply (apply head x) y :: pairs (y :: rest)
                | pairs _ = []
          in rightNil (operator connector) (pairs args) end
      | buildApp (Pairwise _) head [x, y] = apply (apply head x) y
      | buildApp (Pairwise connector) head args =
          let fun pairs [] = []
                | pairs (x :: xs) = map (fn y => apply (apply head x) y) xs @ pairs xs
          in rightNil (operator connector) (pairs args) end
      | buildApp (ArgList connector) head args = apply head (rightNil (operator connector) args);
    fun admits (Exact n) k = k <= n
      | admits RightNil _ = true
      | admits LeftNil _ = true
      | admits LeftNonSingletonNil _ = true
      | admits RightNonSingletonNil _ = true
      | admits (ArgList _) k = k > 0
      | admits _ k = k >= 2;
    fun resolve terms = case terms of
        [] => raise Error "no reading of overloaded symbol has the required type"
      | [t] => t
      | ts => (case List.find wellTyped ts of SOME t => t
          | NONE => raise Error "no reading of overloaded symbol has the required type");
    fun bound name = map #2 (List.filter (fn (n, _) => n = name) (!bindings));
    fun term depth sexp =
      if depth > 4096 then raise Error "term nesting exceeds 4096"
      else case sexp of
        Str s => Term_String (map (runtime_nat o IntInf.fromInt) (stringLiteral s))
      | Quoted name => if null (bound name) then operator name else resolve (bound name)
      | Atom "Type" => if null (bound "Type") then Term_Type else resolve (bound "Type")
      | Atom name => (case literal name of SOME t => t | NONE =>
          if not (null (bound name)) then resolve (bound name)
          else operator name)
      | Expr [Atom "let", Expr lets, body] =>
          let fun binding (Expr [name, value]) = (CpcSexp.name name, term (depth + 1) value)
                | binding _ = raise Error "malformed let binding"
          in withBindings (map binding lets) (fn () => term (depth + 1) body) end
      | Expr (Atom "_" :: Atom name :: indices) => indexed (depth + 1) name indices []
      | Expr (Expr (Atom "_" :: Atom name :: indices) :: args) => indexed (depth + 1) name indices args
      | Expr (Atom "_" :: head :: args) => applyAll (term (depth + 1) head) (map (term (depth + 1)) args)
      | Expr (Atom name :: args) => app (depth + 1) name [] args false
      | Expr (head :: args) => applyAll (term (depth + 1) head) (map (term (depth + 1)) args)
      | Expr [] => raise Error "empty term"
    and indexed depth name indices args =
      if String.isPrefix "bv" name andalso digits (String.extract (name, 2, NONE)) then
        (case (indices, args) of ([Atom width], []) =>
          let val w = requireInteger width;
              val value = requireInteger (String.extract (name, 2, NONE))
          in if w < 0 then raise Error "negative bit-vector width"
             else Term_Binary (runtime_int w, runtime_int value) end
         | _ => raise Error "malformed indexed bit-vector literal")
      else app depth name indices args true
    and app depth name indices args indexedForm =
      if not indexedForm andalso Option.isSome (find name (!macros)) then
        expand depth name args
      else let
        val appliedBindings = map (fn head => applyAll head
          (map (term depth) (indices @ args))) (bound name);
        val boundReading = List.find wellTyped appliedBindings;
        fun builtin () = case (indexedForm, List.find (fn (n, _, _) => n = name) definitions) of
          (false, SOME (_, count, build)) =>
            if length args = count then build (map (term depth) args)
            else raise Error ("wrong argument count for definition " ^ name)
        | _ => let
        val choices = List.filter (fn (n, _, _, _) => n = name) operators;
        fun suitable (_, k, arity, _) =
          if indexedForm then k = length indices andalso admits arity (length args)
          else k <= length args andalso admits arity (length args - k);
        val selected = List.find suitable choices;
      in case selected of
          NONE => raise Error ("unknown operator or unsupported arity: " ^ name)
        | SOME (_, k, arity, head) =>
          let val (ix, values) = if indexedForm then (indices, args)
                else (List.take (args, k), List.drop (args, k));
              val h = head (map (term depth) ix)
          in buildApp arity h (map (term depth) values) end
        end
      in case boundReading of SOME t => t | NONE =>
        if List.exists (fn n => n = name) (!shadowed)
        then raise Error ("local binding has the wrong type: " ^ name)
        else builtin ()
      end
    and expand depth name args =
      if List.exists (fn n => n = name) (!expanding) then raise Error ("recursive macro " ^ name)
      else case find name (!macros) of NONE => raise Error ("unknown macro " ^ name)
        | SOME (params, body) =>
          if length params <> length args then raise Error ("wrong argument count for macro " ^ name)
          else let val values = map (term depth) args;
                   val saved = !expanding
               in expanding := name :: saved;
                  (withBindings (ListPair.zip (params, values)) (fn () => term depth body)
                    before expanding := saved)
                  handle exn => (expanding := saved; raise exn)
               end;
    fun declare name ty =
      if ty = Term_Type then
        (sorts := !sorts + 1; bind name (Term_USort (runtime_nat (IntInf.fromInt (!sorts)))))
      else (symbols := !symbols + 1;
        bind name (Term_UConst (runtime_nat (IntInf.fromInt (!symbols)), ty)));
    fun push id = if List.exists (fn n => n = id) (!stack)
      then raise Error ("duplicate active proof name " ^ id) else stack := id :: !stack;
    fun premise sexp =
      let val id = CpcSexp.name sexp;
          fun index _ [] = raise Error ("unknown or out-of-scope premise " ^ id)
            | index n (x :: xs) = if x = id then n else index (n + 1) xs
      in index 0 (!stack) end;
    fun annots rest =
      let
        val rest = case rest of Atom s :: _ => if String.isPrefix ":" s then rest else tl rest
          | [] => [] | _ => tl rest;
        fun read [] rule args prems = (case rule of NONE => raise Error "step has no :rule"
          | SOME r => (r, args, prems))
          | read (Atom ":rule" :: value :: more) NONE args prems =
              let val name = CpcSexp.name value in
                case find name rules of NONE => raise Error ("unknown CPC rule " ^ name)
                  | SOME r => read more (SOME r) args prems end
          | read (Atom ":args" :: Expr values :: more) rule NONE prems =
              read more rule (SOME (map (term 0) values)) prems
          | read (Atom ":premises" :: Expr values :: more) rule args NONE =
              read more rule args (SOME (map premise values))
          | read _ _ _ _ = raise Error "malformed or duplicate step annotation";
        val (rule, args, prems) = read rest NONE NONE NONE
      in (rule, argList (Option.getOpt (args, [])), indexList (Option.getOpt (prems, []))) end;
    fun datatypes names bodies =
      let
        fun sort (Expr [name, Atom "0"]) = CpcSexp.name name
          | sort _ = raise Error "only non-parametric datatype declarations are supported";
        val names = map sort names;
        val _ = if length names = length bodies then () else raise Error "datatype declaration count mismatch";
        val _ = if length (List.foldl (fn (n, acc) =>
              if List.exists (fn x => x = n) acc then acc else n :: acc) [] names) = length names
            then () else raise Error "duplicate datatype name";
        fun characters name = map (runtime_nat o IntInf.fromInt) (utf8 name);
        fun references (Atom n) = if List.exists (fn x => x = n) names then [n] else []
          | references (Quoted n) = if List.exists (fn x => x = n) names then [n] else []
          | references (Expr xs) = List.concat (map references xs)
          | references _ = [];
        fun selector (Expr [name, ty]) = (CpcSexp.name name, term 0 ty, references ty)
          | selector _ = raise Error "malformed datatype selector";
        fun constructor (Expr (name :: selectors)) = (CpcSexp.name name, map selector selectors)
          | constructor _ = raise Error "malformed datatype constructor";
        fun body (Expr constructors) =
              if null constructors then raise Error "datatype has no constructors"
              else map constructor constructors
          | body _ = raise Error "malformed datatype body";
        val parsed = withBindings
          (map (fn n => (n, Term_DatatypeTypeRef (characters n))) names)
          (fn () => ListPair.zip (names, map body bodies));
        fun ready placed (_, constructors) = List.exists (fn (_, selectors) =>
          List.all (fn (_, _, refs) => List.all
            (fn n => List.exists (fn x => x = n) placed) refs) selectors) constructors;
        fun order placed [] = []
          | order placed pending = (case List.find (ready placed) pending of
              NONE => raise Error "datatype block has no finite constructor"
            | SOME (entry as (name, _)) => entry :: order (name :: placed)
                (List.filter (fn (n, _) => n <> name) pending));
        val ordered = order [] parsed;
        fun consType (_, selectors) = List.foldr
          (fn ((_, ty, _), rest) => DatatypeCons_cons (ty, rest)) DatatypeCons_unit selectors;
        fun datatypeType constructors = List.foldr
          (fn (c, rest) => Datatype_sum (consType c, rest)) Datatype_null constructors;
        val declaration = List.foldr (fn ((name, constructors), rest) =>
          DatatypeDecl_cons (characters name, datatypeType constructors, rest)) DatatypeDecl_nil ordered;
        fun indexed f xs = List.app f (ListPair.zip (xs, List.tabulate (length xs, fn i => i)));
        fun register (name, constructors) =
          let val key = characters name in
            bind name (Term_DatatypeType (key, declaration));
            indexed (fn ((constructor, selectors), i) =>
              (bind constructor (Term_DtCons (key, declaration, runtime_nat (IntInf.fromInt i)));
               indexed (fn ((selector, _, _), j) => bind selector
                 (Term_DtSel (key, declaration, runtime_nat (IntInf.fromInt i),
                   runtime_nat (IntInf.fromInt j)))) selectors)) constructors
          end;
      in List.app register ordered end;
    fun command sexp = case sexp of
        Expr [Atom "declare-const", name, ty] => declare (CpcSexp.name name) (term 0 ty)
      | Expr [Atom "declare-fun", name, Expr args, ty] =>
          declare (CpcSexp.name name) (if null args then term 0 ty
            else term 0 (Expr (Atom "->" :: args @ [ty])))
      | Expr [Atom "declare-sort", name, Atom arity] =>
          let val n = requireInteger arity
          in if n < 0 orelse n > 4096 then raise Error "unsupported sort arity"
             else declare (CpcSexp.name name) (if n = 0 then Term_Type
               else right Term_FunType (List.tabulate (IntInf.toInt n + 1, fn _ => Term_Type))) end
      | Expr [Atom "declare-datatypes", Expr names, Expr bodies] => datatypes names bodies
      | Expr [Atom "define", name, Expr [], body] => bind (CpcSexp.name name) (term 0 body)
      | Expr [Atom "define", name, Expr params, body] =>
          let fun param (Expr [name, _]) = CpcSexp.name name
                | param _ = raise Error "malformed macro parameter"
          in macros := (CpcSexp.name name, (map param params, body)) :: !macros end
      | Expr [Atom "assume", name, value] =>
          if not (null (!commands)) then raise Error "assumption after first proof command"
          else (assumptions := term 0 value :: !assumptions; push (CpcSexp.name name))
      | Expr [Atom "assume-push", name, value] =>
          (scopes := !stack :: !scopes; push (CpcSexp.name name);
           commands := CCmd_assume_push (term 0 value) :: !commands)
      | Expr (Atom "step" :: name :: rest) =>
          let val (rule, args, prems) = annots rest
          in commands := CCmd_step (rule, args, prems) :: !commands; push (CpcSexp.name name) end
      | Expr (Atom "step-pop" :: name :: rest) =>
          let val (rule, args, prems) = annots rest
          in case !scopes of [] => raise Error "step-pop without assume-push"
            | saved :: more => (stack := saved; scopes := more; push (CpcSexp.name name);
                commands := CCmd_step_pop (rule, args, prems) :: !commands) end
      | Expr (Atom "include" :: _) => ()
      | Expr (Atom "reference" :: _) => ()
      | Expr (Atom name :: _) => raise Error ("unsupported proof command " ^ name)
      | _ => raise Error "expected a proof command";
    val sexps = CpcSexp.read text;
    val sexps = case sexps of [Expr xs] =>
          if not (null xs) andalso List.all (fn Expr _ => true | _ => false) xs then xs else sexps
        | _ => sexps;
    val _ = List.app command sexps;
    (* invoke_assume_list pushes its tail first, so retain the reversed input
       assumptions to match the named proof stack (most recent on top). *)
  in (argList (!assumptions), cmdList (rev (!commands))) end;
end;

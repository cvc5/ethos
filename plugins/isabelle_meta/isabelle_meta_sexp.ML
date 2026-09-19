(* CPC's s-expression surface syntax. No proof files are evaluated as ML. *)
structure CpcSexp = struct
exception Error of string;
datatype sexp = Atom of string | Quoted of string | Str of string | Expr of sexp list;

fun read input =
  let
    val size = String.size input;
    val pos = ref 0;
    val line = ref 1;
    fun fail message = raise Error ("line " ^ Int.toString (!line) ^ ": " ^ message);
    fun peek () = if !pos < size then SOME (String.sub (input, !pos)) else NONE;
    fun take () =
      case peek () of
        NONE => fail "unexpected end of file"
      | SOME c => (pos := !pos + 1; if c = #"\n" then line := !line + 1 else (); c);
    fun comment () = case peek () of NONE => () | SOME #"\n" => ()
      | _ => (ignore (take ()); comment ());
    fun space () = case peek () of
        SOME #";" => (comment (); space ())
      | SOME c => if Char.isSpace c then (ignore (take ()); space ()) else ()
      | NONE => ();
    fun quoted delimiter acc =
      let val c = take () in
        if c = delimiter then
          if delimiter = #"\"" andalso peek () = SOME #"\""
          then (ignore (take ()); quoted delimiter (c :: acc))
          else String.implode (rev acc)
        else quoted delimiter (c :: acc)
      end;
    fun atom acc = case peek () of
        NONE => String.implode (rev acc)
      | SOME c => if Char.isSpace c orelse c = #"(" orelse c = #")" orelse c = #";"
          then String.implode (rev acc)
          else if c = #"\"" orelse c = #"|" then fail "quote inside an unquoted symbol"
          else atom (take () :: acc);
    fun expression depth =
      if depth > 4096 then fail "s-expression nesting exceeds 4096"
      else (space (); case take () of
          #"(" => Expr (items depth [])
        | #")" => fail "unexpected closing parenthesis"
        | #"\"" => Str (quoted #"\"" [])
        | #"|" => Quoted (quoted #"|" [])
        | c => Atom (atom [c]))
    and items depth acc = (space (); case peek () of
        NONE => fail "unclosed parenthesis"
      | SOME #")" => (ignore (take ()); rev acc)
      | _ => items depth (expression (depth + 1) :: acc));
    fun all acc = (space (); case peek () of NONE => rev acc
      | _ => all (expression 0 :: acc));
  in all [] end;

fun name (Atom s) = s
  | name (Quoted s) = s
  | name _ = raise Error "expected a symbol";

fun utf8 text =
  let
    val bytes = map Char.ord (String.explode text);
    fun fail () = raise Error "invalid UTF-8 string";
    fun continuation b = b >= 128 andalso b < 192;
    fun gather 0 acc rest = (acc, rest)
      | gather n acc (b :: bs) =
          if continuation b then gather (n - 1) (acc * 64 + b - 128) bs else fail ()
      | gather _ _ [] = fail ();
    fun loop [] = []
      | loop (b :: bs) =
        if b < 128 then b :: loop bs
        else let
          val (n, seed, minimum) =
            if b >= 194 andalso b < 224 then (1, b - 192, 128)
            else if b < 240 andalso b >= 224 then (2, b - 224, 2048)
            else if b < 245 andalso b >= 240 then (3, b - 240, 65536)
            else fail ();
          val (c, rest) = gather n seed bs;
        in if c < minimum orelse c > 1114111 orelse (c >= 55296 andalso c <= 57343)
           then fail () else c :: loop rest end;
  in loop bytes end;

fun stringLiteral text =
  let
    fun hex c = if c >= 48 andalso c <= 57 then SOME (c - 48)
      else if c >= 65 andalso c <= 70 then SOME (c - 55)
      else if c >= 97 andalso c <= 102 then SOME (c - 87) else NONE;
    fun valid n = n < 196608 andalso not (n >= 55296 andalso n <= 57343);
    fun fixed 0 n rest = SOME (n, rest)
      | fixed k n (c :: cs) = (case hex c of NONE => NONE | SOME d => fixed (k - 1) (n * 16 + d) cs)
      | fixed _ _ [] = NONE;
    fun braced k n (125 :: cs) = if k > 0 then SOME (n, cs) else NONE
      | braced k n (c :: cs) = if k >= 5 then NONE
          else (case hex c of NONE => NONE | SOME d => braced (k + 1) (n * 16 + d) cs)
      | braced _ _ [] = NONE;
    fun loop [] = []
      | loop (92 :: 117 :: cs) =
          let val escape = case cs of 123 :: rest => braced 0 0 rest | _ => fixed 4 0 cs
          in case escape of
              SOME (n, rest) => if valid n then n :: loop rest
                else raise Error "Unicode escape outside CPC's character range"
            | NONE => raise Error "invalid Unicode escape"
          end
      | loop (c :: cs) = if valid c then c :: loop cs
          else raise Error "string character outside CPC's character range";
  in loop (utf8 text) end;
end;

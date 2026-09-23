fun assert message true = ()
  | assert message false = raise Fail message;
val fuel = CPC.runtime_nat 1000;
fun check text = let val (assumptions, commands) = CpcParser.parse fuel text
  in CPC.check_refutation fuel assumptions commands end;
val finish = " (step c :rule contra :premises (a b))";
val _ = assert "generated rule and macro"
  (check ("(assume a true) (assume b (negate true))" ^ finish));
val _ = assert "wrong premises must reject"
  (not (check "(assume a true) (step c :rule contra :premises (a a))"));
val _ = assert "exhaustion must not accept"
  ((CpcParser.parse (CPC.runtime_nat 0)
     "(declare-const p Bool) (assume a (p true))"; false)
   handle CpcParser.Fuel => true);
fun sameTerm left right =
  let fun read value = #1 (CpcParser.parse fuel ("(assume a " ^ value ^ ")"))
  in assert (left ^ " differs from " ^ right) (read left = read right) end;
val _ = sameTerm "(conjunction true false true)" "(and true false true)";
val _ = sameTerm "(negate true)" "(not true)";
val _ = sameTerm "(gather true false)" "(let ((f gather)) (f (or true false)))";
val _ = sameTerm "(chained true false true)"
  "(let ((c chained)) (or (c true false) (c false true)))";
val _ = sameTerm "negative_constant" "-3";
val _ = sameTerm "string_constant" "\"abc\"";
val _ = sameTerm "(_ indexed 0)" "(indexed 0)";
val _ = sameTerm "|a b|" "(let ((x |a b|)) x)";
val _ = assert "quoted names remain distinct"
  (#1 (CpcParser.parse fuel "(assume a |a b|)") <>
   #1 (CpcParser.parse fuel "(assume a a_x20b)"));
val _ = assert "unknown rules fail"
  ((CpcParser.parse fuel "(step a :rule missing)"; false)
   handle CpcSexp.Error _ => true);
val _ = print "Generated Isabelle parser tests passed.\n";

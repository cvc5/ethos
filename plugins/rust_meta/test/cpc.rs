use pathos_compiled_checker::*;

fn n(s: &mut Store, name: &str, args: &[Term]) -> Term {
    s.named(name, args).unwrap()
}
fn index(s: &mut Store, i: u32) -> Term {
    s.raw(Lit::Numeral(Integer::from(i))).unwrap()
}
fn list(s: &mut Store, nil: &str, cons: &str, ts: &[Term]) -> Term {
    let mut tail = n(s, nil, &[]);
    for &t in ts.iter().rev() {
        tail = n(s, cons, &[t, tail]);
    }
    tail
}

#[test]
fn arithmetic_normalization_of_a_real_constant_proves_a_refutation() {
    // (declare-const x Real)
    // (assume @p0 (not (= x x)))
    // (step @p1 (= x x) :rule arith_poly_norm :args ((= x x)))
    // (step @p2 false :rule contra :premises (@p1 @p0))
    let mut s = Store::default();
    let real = n(&mut s, "Real", &[]);
    let id = index(&mut s, 0);
    let x = n(&mut s, "$emb_UConst", &[id, real]);
    let eq = n(&mut s, "=", &[]);
    let eq_x = s.apply(eq, x).unwrap();
    let eq_xx = s.apply(eq_x, x).unwrap();
    let not = n(&mut s, "not", &[]);
    let denial = s.apply(not, eq_xx).unwrap();
    let assumptions = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[denial]);
    let args = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[eq_xx]);
    let empty_premises = n(&mut s, "$emb_indl.nil", &[]);
    let norm = n(&mut s, "$emb_r.arith_poly_norm", &[]);
    let step = n(&mut s, "$emb_cmd.step", &[norm, args, empty_premises]);
    let empty_args = n(&mut s, "$emb_al.nil", &[]);
    let zero = index(&mut s, 0);
    let one = index(&mut s, 1);
    let premises = list(&mut s, "$emb_indl.nil", "$emb_indl.cons", &[zero, one]);
    let contra = n(&mut s, "$emb_r.contra", &[]);
    let contradiction = n(&mut s, "$emb_cmd.step", &[contra, empty_args, premises]);
    let commands = list(
        &mut s,
        "$emb_cmdl.nil",
        "$emb_cmdl.cons",
        &[step, contradiction],
    );
    for caching in [true, false] {
        s.set_caching(caching);
        assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
        assert_eq!(s.check_proof(assumptions, commands), Ok(Verdict::Correct));
    }
}

// The translation side conditions are compiled from Eunoia, see
// plugins/model_smt/translation_checks.eo; what a rule asks of its arguments
// is what the CPC semantics says with `define-rule ... :args`.
fn translatable(s: &mut Store, rule: &str, args: &[Term]) -> bool {
    let r = n(s, rule, &[]);
    let args = list(s, "$emb_al.nil", "$emb_al.cons", args);
    let b = generated::eo__24eo_5ftranslatable_5frule_5fargs(s, r, args).unwrap();
    s.boolean_value(b, true).unwrap() == Some(true)
}

#[test]
fn rule_arguments_are_asked_what_the_semantics_says() {
    let mut s = Store::default();
    let real = n(&mut s, "Real", &[]);
    let reglan = n(&mut s, "RegLan", &[]);
    let zero = index(&mut s, 0);
    let one = index(&mut s, 1);
    let x = n(&mut s, "$emb_UConst", &[zero, real]);
    let r = n(&mut s, "$emb_UConst", &[one, reglan]);
    // A rule that says nothing asks that each argument have a translation,
    // whatever their number.
    assert!(translatable(&mut s, "$emb_r.contra", &[]));
    assert!(translatable(&mut s, "$emb_r.contra", &[x, r]));
    let bad = n(&mut s, "$emb_al.nil", &[]);
    assert!(!translatable(&mut s, "$emb_r.contra", &[x, bad]));
    // wf_elem: an element of a container, which a regular language cannot be.
    assert!(translatable(&mut s, "$emb_r.sets_choose_singleton", &[x]));
    assert!(!translatable(&mut s, "$emb_r.sets_choose_singleton", &[r]));
    // A rule that says :args takes exactly as many arguments as it gives kinds.
    assert!(!translatable(&mut s, "$emb_r.sets_choose_singleton", &[]));
    assert!(!translatable(&mut s, "$emb_r.sets_choose_singleton", &[x, x]));
    // list: an EO list of terms that each translate, and nothing else.
    let nil = n(&mut s, "$eo_List_nil", &[]);
    let cons = n(&mut s, "$eo_List_cons", &[]);
    let cx = s.apply(cons, x).unwrap();
    let xs = s.apply(cx, nil).unwrap();
    assert!(translatable(&mut s, "$emb_r.instantiate", &[nil]));
    assert!(translatable(&mut s, "$emb_r.instantiate", &[xs]));
    assert!(!translatable(&mut s, "$emb_r.instantiate", &[x]));
    let cb = s.apply(cons, bad).unwrap();
    let bads = s.apply(cb, nil).unwrap();
    assert!(!translatable(&mut s, "$emb_r.instantiate", &[bads]));
    // type: a type, translating to a well-formed one; a term is not one.
    assert!(translatable(&mut s, "$emb_r.exists_string_length", &[real, x, x]));
    assert!(!translatable(&mut s, "$emb_r.exists_string_length", &[x, x, x]));
    // wf_term: a term of a well-formed type, which RegLan is at top level.
    assert!(translatable(&mut s, "$emb_r.distinct_binary_elim", &[x, x]));
    assert!(translatable(&mut s, "$emb_r.distinct_binary_elim", &[r, x]));
    assert!(!translatable(&mut s, "$emb_r.distinct_binary_elim", &[bad, x]));
}

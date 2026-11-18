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

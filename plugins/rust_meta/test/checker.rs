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
fn checks_a_complete_refutation_and_rejects_wrong_premises() {
    let mut s = Store::default();
    let ty = n(&mut s, "$emb_Bool", &[]);
    let id = index(&mut s, 0);
    let p = n(&mut s, "$emb_UConst", &[id, ty]);
    let not = n(&mut s, "not", &[]);
    let np = s.apply(not, p).unwrap();
    let assumptions = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[p, np]);
    let args = n(&mut s, "$emb_al.nil", &[]);
    let i0 = index(&mut s, 0);
    let i1 = index(&mut s, 1);
    let premises = list(&mut s, "$emb_indl.nil", "$emb_indl.cons", &[i0, i1]);
    let contra = n(&mut s, "$emb_r.contra", &[]);
    let step = n(&mut s, "$emb_cmd.step", &[contra, args, premises]);
    let commands = list(&mut s, "$emb_cmdl.nil", "$emb_cmdl.cons", &[step]);
    assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
    let expected = if Constructor::from_name("$emb_tsm.None").is_some() {
        Verdict::Correct
    } else {
        Verdict::Incomplete
    };
    assert_eq!(s.check_proof(assumptions, commands), Ok(expected));
    let wrong = list(&mut s, "$emb_indl.nil", "$emb_indl.cons", &[i1, i0]);
    let bad_step = n(&mut s, "$emb_cmd.step", &[contra, args, wrong]);
    let bad = list(&mut s, "$emb_cmdl.nil", "$emb_cmdl.cons", &[bad_step]);
    assert_eq!(s.check_refutation(assumptions, bad), Ok(false));
    let empty = n(&mut s, "$emb_cmdl.nil", &[]);
    assert_eq!(s.check_refutation(assumptions, empty), Ok(false));
    // The optional optimization must preserve both accepted and rejected
    // proofs, even after the arena has grown and across separate checks.
    s.set_caching(false);
    assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
    assert_eq!(s.check_proof(assumptions, commands), Ok(expected));
    assert_eq!(s.check_refutation(assumptions, bad), Ok(false));
    s.set_caching(true);
    assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
}

#[test]
fn step_pop_discharges_its_assumption() {
    let mut s = Store::default();
    let yes = s.boolean(true).unwrap();
    let imp = n(&mut s, "=>", &[]);
    let a = s.apply(imp, yes).unwrap();
    let tautology = s.apply(a, yes).unwrap();
    let not = n(&mut s, "not", &[]);
    let denial = s.apply(not, tautology).unwrap();
    let assumptions = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[denial]);
    let args = n(&mut s, "$emb_al.nil", &[]);
    let zero = index(&mut s, 0);
    let one = index(&mut s, 1);
    let scope = n(&mut s, "$emb_r.scope", &[]);
    let premises = list(&mut s, "$emb_indl.nil", "$emb_indl.cons", &[zero]);
    let pop = n(&mut s, "$emb_cmd.step_pop", &[scope, args, premises]);
    let push = n(&mut s, "$emb_cmd.assume_push", &[yes]);
    let contra = n(&mut s, "$emb_r.contra", &[]);
    let premises = list(&mut s, "$emb_indl.nil", "$emb_indl.cons", &[zero, one]);
    let contradiction = n(&mut s, "$emb_cmd.step", &[contra, args, premises]);
    let commands = list(
        &mut s,
        "$emb_cmdl.nil",
        "$emb_cmdl.cons",
        &[push, pop, contradiction],
    );
    assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
}

#[test]
fn open_scope_and_ill_typed_assumptions_are_rejected() {
    let mut s = Store::default();
    let f = s.boolean(false).unwrap();
    let args = n(&mut s, "$emb_al.nil", &[]);
    let push = n(&mut s, "$emb_cmd.assume_push", &[f]);
    let cmds = list(&mut s, "$emb_cmdl.nil", "$emb_cmdl.cons", &[push]);
    assert_eq!(s.check_refutation(args, cmds), Ok(false));
    let numeral = s.numeral(Integer::one()).unwrap();
    let bad = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[numeral]);
    let empty = n(&mut s, "$emb_cmdl.nil", &[]);
    assert_eq!(s.check_refutation(bad, empty), Ok(false));
}

#[test]
fn primitive_edge_cases_and_interning() {
    let mut s = Store::default();
    let x = s.numeral(Integer::parse("-7", 10).unwrap()).unwrap();
    let y = s.numeral(Integer::from(2u32)).unwrap();
    let q = s.builtin(EvalOp::IntDiv, &[x, y]).unwrap();
    assert_eq!(
        s.view(q),
        Ok(&TermData::Literal(Lit::Numeral(
            Integer::parse("-4", 10).unwrap()
        )))
    );
    let zero = s.numeral(Integer::zero()).unwrap();
    assert_eq!(s.builtin(EvalOp::IntDiv, &[x, zero]), Ok(s.stuck()));
    let stuck = s.stuck();
    let no = s.boolean(false).unwrap();
    assert_eq!(s.builtin(EvalOp::IsEq, &[stuck, stuck]), Ok(no));
    assert_eq!(s.literal(Lit::Numeral(Integer::from(2u32))), Ok(y));
    assert_eq!(
        s.named("$emb_cmd.step", &[]),
        Err(CheckError::InvalidConstructor)
    );
    // Term order follows Logos constructor/field order, independently of
    // allocation order. Rational fields compare numerator, then denominator.
    let real = n(&mut s, "Real", &[]);
    let int = n(&mut s, "Int", &[]);
    assert!(s.compare(int, real).unwrap().is_lt());
    let half = s
        .literal(Lit::Rational(Rational::parse("1/2").unwrap()))
        .unwrap();
    let third = s
        .literal(Lit::Rational(Rational::parse("1/3").unwrap()))
        .unwrap();
    assert!(s.compare(half, third).unwrap().is_lt());
}

#[test]
fn recognizers_return_booleans_including_on_stuck() {
    let mut s = Store::default();
    let ty = n(&mut s, "Real", &[]);
    let name = s.literal(Lit::Str(EoString::parse("x", false))).unwrap();
    let variable = n(&mut s, "$emb_Var", &[name, ty]);
    let numeral = s.numeral(Integer::one()).unwrap();
    let rational = s
        .literal(Lit::Rational(Rational::from_integer(&Integer::one())))
        .unwrap();
    let binary = s
        .literal(Lit::Binary(BitVec::new(1, &Integer::one())))
        .unwrap();
    let boolean = s.boolean(true).unwrap();
    let no = s.boolean(false).unwrap();
    let stuck = s.stuck();
    // This failed conversion is the input to is_q in arithmetic normalization.
    assert_eq!(s.builtin(EvalOp::ToRat, &[variable]), Ok(stuck));
    for (op, matching) in [
        (EvalOp::IsZ, numeral),
        (EvalOp::IsQ, rational),
        (EvalOp::IsBin, binary),
        (EvalOp::IsStr, name),
        (EvalOp::IsBool, boolean),
        (EvalOp::IsVar, variable),
    ] {
        assert_eq!(s.builtin(op, &[stuck]), Ok(no), "{op:?} on Stuck");
        for arg in [numeral, rational, binary, name, boolean, variable] {
            let expected = s.boolean(arg == matching).unwrap();
            assert_eq!(s.builtin(op, &[arg]), Ok(expected), "{op:?} on {arg:?}");
        }
    }
    assert_eq!(s.builtin(EvalOp::Not, &[stuck]), Ok(stuck));
}

#[test]
fn primitive_lists_preserve_order_and_multiplicity() {
    let mut s = Store::default();
    let t = s.boolean(true).unwrap();
    let f = s.boolean(false).unwrap();
    let mut names = vec!["or"];
    if Constructor::from_name("test-left").is_some() {
        names.push("test-left");
    }
    for name in names {
        let op = n(&mut s, name, &[]);
        let tail = s.builtin(EvalOp::Cons, &[op, t, f]).unwrap();
        let xs = s.builtin(EvalOp::Cons, &[op, t, tail]).unwrap();
        let length = s.builtin(EvalOp::ListLength, &[op, xs]).unwrap();
        let two = s.numeral(Integer::from(2u32)).unwrap();
        assert_eq!(length, two);
        assert_eq!(s.builtin(EvalOp::ListMinclude, &[op, xs, tail]), Ok(t));
        assert_eq!(s.builtin(EvalOp::ListMinclude, &[op, tail, xs]), Ok(f));
        assert_eq!(s.builtin(EvalOp::ListDiff, &[op, xs, tail]), Ok(tail));
        assert_eq!(s.builtin(EvalOp::ListSetof, &[op, xs]), Ok(tail));
    }
}

#[test]
fn resource_exhaustion_is_an_error() {
    let mut s = Store::new(Limits {
        calls: 0,
        ..Limits::default()
    });
    let assumptions = n(&mut s, "$emb_al.nil", &[]);
    let commands = n(&mut s, "$emb_cmdl.nil", &[]);
    assert_eq!(
        s.check_refutation(assumptions, commands),
        Err(CheckError::Limit)
    );
}

#[test]
fn long_command_lists_use_a_loop() {
    let mut s = Store::default();
    let f = s.boolean(false).unwrap();
    let not = n(&mut s, "not", &[]);
    let nf = s.apply(not, f).unwrap();
    let nnf = s.apply(not, nf).unwrap();
    let assumptions = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[nnf]);
    let args = n(&mut s, "$emb_al.nil", &[]);
    let zero = index(&mut s, 0);
    let premises = list(&mut s, "$emb_indl.nil", "$emb_indl.cons", &[zero]);
    let rule = n(&mut s, "$emb_r.not_not_elim", &[]);
    let step = n(&mut s, "$emb_cmd.step", &[rule, args, premises]);
    let check = n(&mut s, "$emb_cmd.check_proven", &[f]);
    let mut steps = vec![step];
    steps.extend(vec![check; 2000]);
    let cmds = list(&mut s, "$emb_cmdl.nil", "$emb_cmdl.cons", &steps);
    assert_eq!(s.check_refutation(assumptions, cmds), Ok(true));
}

fn contradiction_commands(s: &mut Store) -> Term {
    let args = n(s, "$emb_al.nil", &[]);
    let zero = index(s, 0);
    let one = index(s, 1);
    let premises = list(s, "$emb_indl.nil", "$emb_indl.cons", &[zero, one]);
    let contra = n(s, "$emb_r.contra", &[]);
    let step = n(s, "$emb_cmd.step", &[contra, args, premises]);
    list(s, "$emb_cmdl.nil", "$emb_cmdl.cons", &[step])
}

#[test]
fn default_limits_check_deep_terms() {
    let mut s = Store::default();
    let yes = s.boolean(true).unwrap();
    let mut formula = s.boolean(false).unwrap();
    let or = n(&mut s, "or", &[]);
    for _ in 0..200_000 {
        let head = s.apply(or, yes).unwrap();
        formula = s.apply(head, formula).unwrap();
    }
    let not = n(&mut s, "not", &[]);
    let denial = s.apply(not, formula).unwrap();
    let assumptions = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[formula, denial]);
    let commands = contradiction_commands(&mut s);
    assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
    let expected = if Constructor::from_name("$emb_tsm.None").is_some() {
        Verdict::Correct
    } else {
        Verdict::Incomplete
    };
    assert_eq!(s.check_proof(assumptions, commands), Ok(expected));
    // Going beyond the default still returns a recoverable resource error.
    // Start with uncached outer nodes so the earlier check cannot hide depth.
    let mut too_deep = formula;
    for _ in 0..400_000 {
        let head = s.apply(or, yes).unwrap();
        too_deep = s.apply(head, too_deep).unwrap();
    }
    let deep_assumptions = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[too_deep]);
    assert_eq!(
        s.check_refutation(deep_assumptions, commands),
        Err(CheckError::Limit)
    );
    assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
}

#[test]
fn assumption_count_does_not_consume_recursive_depth() {
    let mut s = Store::new(Limits {
        depth: 128,
        ..Limits::default()
    });
    let yes = s.boolean(true).unwrap();
    let not = n(&mut s, "not", &[]);
    let denial = s.apply(not, yes).unwrap();
    let mut assumptions = list(&mut s, "$emb_al.nil", "$emb_al.cons", &vec![yes; 120_000]);
    assumptions = n(&mut s, "$emb_al.cons", &[denial, assumptions]);
    assumptions = n(&mut s, "$emb_al.cons", &[yes, assumptions]);
    // Preserving the order matters: contra needs true at 0 and not true at 1.
    let commands = contradiction_commands(&mut s);
    assert_eq!(s.check_refutation(assumptions, commands), Ok(true));
}

#[test]
fn assumption_fold_preserves_guards_and_malformed_tails() {
    let mut s = Store::default();
    let yes = s.boolean(true).unwrap();
    let empty = n(&mut s, "$emb_al.nil", &[]);
    let initial = n(&mut s, "$emb_s.nil", &[]);
    let invoke = generated::eo__24eo_5finvoke_5fassume_5flist;
    assert_eq!(invoke(&mut s, initial, empty), Ok(initial));
    let numeral = s.numeral(Integer::one()).unwrap();
    let name = s.literal(Lit::Str(EoString::parse("x", false))).unwrap();
    let ty = n(&mut s, "$emb_Bool", &[]);
    let variable = n(&mut s, "$emb_Var", &[name, ty]);
    let bad_state = n(&mut s, "$emb_s.Stuck", &[]);
    // An ill-typed assumption, an open assumption and Stuck all fail the guard.
    for bad in [numeral, variable, s.stuck()] {
        let args = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[bad]);
        assert_eq!(invoke(&mut s, initial, args), Ok(bad_state));
    }
    // A malformed tail evaluates to term Stuck; the outer guarded pushes
    // still happen, exactly as in the recursive EO definition.
    let malformed = n(&mut s, "$emb_al.cons", &[yes, numeral]);
    let entry = n(&mut s, "$emb_so.assume", &[yes]);
    let stuck = s.stuck();
    let expected = n(&mut s, "$emb_s.cons", &[entry, stuck]);
    assert_eq!(invoke(&mut s, initial, malformed), Ok(expected));
    let again = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[yes]);
    assert_eq!(invoke(&mut s, expected, empty), Ok(expected));
    let expected_again = n(&mut s, "$emb_s.cons", &[entry, expected]);
    assert_eq!(invoke(&mut s, expected, again), Ok(expected_again));
    let args = list(&mut s, "$emb_al.nil", "$emb_al.cons", &[yes, numeral]);
    let expected = n(&mut s, "$emb_s.cons", &[entry, bad_state]);
    assert_eq!(invoke(&mut s, initial, args), Ok(expected));
}

#[test]
fn indexed_operators_have_the_logos_wrapper_view() {
    let mut s = Store::default();
    let name = if Constructor::from_name("test-index").is_some() {
        "test-index"
    } else {
        "extract"
    };
    let ty = n(&mut s, "Int", &[]);
    let name_term = s.literal(Lit::Str(EoString::parse("x", false))).unwrap();
    let variable = n(&mut s, "$emb_Var", &[name_term, ty]);
    let zero = s.numeral(Integer::zero()).unwrap();
    let indexed = n(&mut s, name, &[variable, zero]);
    let wrapper = Constructor::from_name("$emb_UOp2").unwrap();
    let fields = s.destruct(wrapper, indexed).unwrap().unwrap();
    assert_eq!(fields.len(), 3);
    assert_eq!(s.construct(wrapper, &fields), Ok(indexed));
    let no = s.boolean(false).unwrap();
    assert_eq!(generated::eo__24eo_5fis_5fclosed(&mut s, indexed), Ok(no));
}

#[test]
fn program_keys_include_the_environment() {
    let mut s = Store::default();
    let ty = n(&mut s, "$emb_Bool", &[]);
    let name = s.literal(Lit::Str(EoString::parse("x", false))).unwrap();
    let variable = n(&mut s, "$emb_Var", &[name, ty]);
    let empty = n(&mut s, "$eo_List_nil", &[]);
    let cons = n(&mut s, "$eo_List_cons", &[]);
    let head = s.apply(cons, variable).unwrap();
    let bound = s.apply(head, empty).unwrap();
    let yes = s.boolean(true).unwrap();
    let no = s.boolean(false).unwrap();
    assert_eq!(
        generated::eo__24eo_5fis_5fclosed_5frec(&mut s, variable, empty),
        Ok(no)
    );
    assert_eq!(
        generated::eo__24eo_5fis_5fclosed_5frec(&mut s, variable, bound),
        Ok(yes)
    );
    let hits = s.cache_stats().program_hits;
    assert_eq!(
        generated::eo__24eo_5fis_5fclosed_5frec(&mut s, variable, empty),
        Ok(no)
    );
    assert_eq!(s.cache_stats().program_hits, hits + 1);
}

#[test]
fn an_operator_with_a_stuck_index_is_stuck() {
    let mut s = Store::default();
    let yes = s.boolean(true).unwrap();
    let no = s.boolean(false).unwrap();
    let stuck = s.stuck();
    let zero = s.numeral(Integer::zero()).unwrap();
    let one = s.numeral(Integer::one()).unwrap();
    // built strictly, as logos's __eo_mk_uop2 builds it
    assert_eq!(n(&mut s, "test-index", &[stuck, zero]), stuck);
    assert_eq!(n(&mut s, "test-index", &[zero, stuck]), stuck);
    assert_eq!(n(&mut s, "test-index", &[stuck, stuck]), stuck);
    let same = n(&mut s, "test-index", &[zero, zero]);
    let differ = n(&mut s, "test-index", &[zero, one]);
    assert_ne!(same, stuck);
    // a repeated index is compared by handle equality
    assert_eq!(generated::eo__24eo_5fprog_5findex_5fsame(&mut s, same), Ok(yes));
    assert_eq!(generated::eo__24eo_5fprog_5findex_5fsame(&mut s, differ), Ok(no));
}

#[test]
fn nonlinear_patterns_requirements_and_lazy_branches() {
    let mut s = Store::new(Limits {
        calls: 1000,
        ..Limits::default()
    });
    let yes = s.boolean(true).unwrap();
    let no = s.boolean(false).unwrap();
    assert_eq!(
        generated::eo__24eo_5fprog_5fnonlin(&mut s, yes, yes),
        Ok(yes)
    );
    assert_eq!(generated::eo__24eo_5fprog_5fnonlin(&mut s, yes, no), Ok(no));
    let stuck = s.stuck();
    assert_eq!(
        generated::eo__24eo_5fprog_5frequire_5ffirst(&mut s, no),
        Ok(stuck)
    );
    assert_eq!(generated::eo__24eo_5fprog_5flazy(&mut s, yes), Ok(yes));
    assert_eq!(
        generated::eo__24eo_5fprog_5flazy(&mut s, no),
        Err(CheckError::Limit)
    );
    assert_eq!(s.cache_stats().program_entries, 0);
    // A failed call must restore the depth counter (and the call budget
    // remains exhausted until a new proof starts).
    let assumptions = n(&mut s, "$emb_al.nil", &[]);
    let commands = n(&mut s, "$emb_cmdl.nil", &[]);
    assert_eq!(s.check_refutation(assumptions, commands), Ok(false));
    assert_eq!(generated::eo__24eo_5fprog_5flazy(&mut s, yes), Ok(yes));
    let one = s.numeral(Integer::one()).unwrap();
    assert_eq!(
        generated::eo__24eo_5fprog_5fswap(&mut s, one, yes, no),
        Ok(no)
    );
    let hits = s.cache_stats().program_hits;
    assert_eq!(
        generated::eo__24eo_5fprog_5fswap(&mut s, one, yes, no),
        Ok(no)
    );
    assert_eq!(s.cache_stats().program_hits, hits + 1);
}

fn shared_dag(s: &mut Store, depth: usize) -> Term {
    let and = n(s, "and", &[]);
    let mut t = s.boolean(true).unwrap();
    for _ in 0..depth {
        let head = s.apply(and, t).unwrap();
        t = s.apply(head, t).unwrap();
    }
    t
}

#[test]
fn type_memoization_traverses_shared_terms_once() {
    let mut s = Store::new(Limits {
        calls: 1000,
        ..Limits::default()
    });
    let dag = shared_dag(&mut s, 40);
    let ty = n(&mut s, "$emb_Bool", &[]);
    assert_eq!(generated::eo__24eo_5ftypeof(&mut s, dag), Ok(ty));
    let stats = s.cache_stats();
    assert!(stats.type_hits >= 40);
    assert!(stats.type_misses < 100);
    // New arena nodes do not invalidate old results or overwrite their slots.
    let new_node = s.numeral(Integer::from(99u32)).unwrap();
    let _ = generated::eo__24eo_5ftypeof(&mut s, new_node).unwrap();
    assert_eq!(generated::eo__24eo_5ftypeof(&mut s, dag), Ok(ty));
    assert!(s.cache_stats().type_hits > stats.type_hits);
    s.clear_caches();
    assert_eq!(s.cache_stats(), CacheStats::default());
    s.set_caching(false);
    // Same DAG, same budget: unfolding its 2^40 occurrences cannot finish.
    assert_eq!(
        generated::eo__24eo_5ftypeof(&mut s, dag),
        Err(CheckError::Limit)
    );
}

#[test]
fn program_memoization_uses_exact_keys_and_only_successful_results() {
    let mut s = Store::new(Limits {
        calls: 1000,
        ..Limits::default()
    });
    let dag = shared_dag(&mut s, 40);
    let yes = s.boolean(true).unwrap();
    let no = s.boolean(false).unwrap();
    assert_eq!(generated::eo__24eo_5fprog_5fdag(&mut s, dag), Ok(yes));
    let stats = s.cache_stats();
    assert!(stats.program_hits >= 40);
    assert!(stats.program_misses < 100);
    // Same arguments, different program ID: results must not alias.
    assert_eq!(
        generated::eo__24eo_5fprog_5fdag_5ffalse(&mut s, dag),
        Ok(no)
    );
    let small = shared_dag(&mut s, 6);
    s.set_caching(false);
    assert_eq!(generated::eo__24eo_5fprog_5fdag(&mut s, small), Ok(yes));
    s.clear_caches();
    assert_eq!(
        generated::eo__24eo_5fprog_5fdag(&mut s, dag),
        Err(CheckError::Limit)
    );
    assert_eq!(s.cache_stats().program_entries, 0);
}

#[test]
fn mutual_recursion_is_memoized() {
    let mut s = Store::default();
    let dag = shared_dag(&mut s, 2);
    let yes = s.boolean(true).unwrap();
    let no = s.boolean(false).unwrap();
    assert_eq!(
        generated::eo__24eo_5fprog_5fmutual_5fa(&mut s, dag),
        Ok(yes)
    );
    assert_eq!(generated::eo__24eo_5fprog_5fmutual_5fb(&mut s, dag), Ok(no));
    let hits = s.cache_stats().program_hits;
    assert_eq!(
        generated::eo__24eo_5fprog_5fmutual_5fa(&mut s, dag),
        Ok(yes)
    );
    assert_eq!(s.cache_stats().program_hits, hits + 1);
}

#[test]
fn max_code_point_is_the_generated_one() {
    let mut s = Store::new(Limits::default());
    let zero = s.numeral(Integer::zero()).unwrap();
    let max = s.numeral(Integer::from(MAX_CODE_POINT)).unwrap();
    let above = s.numeral(Integer::from(MAX_CODE_POINT + 1)).unwrap();
    let yes = s.boolean(true).unwrap();
    let no = s.boolean(false).unwrap();
    assert_eq!(MAX_CODE_POINT, 0x2FFFF);
    assert_eq!(
        generated::eo__24eo_5fprog_5fmax_5fcode(&mut s, zero),
        Ok(max)
    );
    assert_eq!(generated::eo__24eo_5fprog_5fcode_5fstr(&mut s, max), Ok(yes));
    assert_eq!(
        generated::eo__24eo_5fprog_5fcode_5fstr(&mut s, above),
        Ok(no)
    );
}

use vstd::prelude::*;
// use vstd::prelude::int;

verus! {
    mod problem_1 {
        use vstd::prelude::*;       
        pub open spec fn count_spec(s: Seq<int>, x: int) -> int
            decreases s.len(),
        {
            // let mut i: int = s.len() as int;
            // let mut count: int = 0;

            // while i > 0 
            //     invariant
            //         i <= s.len() as int,
            //         i >= 0,
            //     decreases i
            // {
            //     if s[i] == x {
            //         count = count + 1;
            //     }
            //     i = i - 1;
            // }
            // count
            if s.len() == 0 {
                0
            } else {
                (if s[0] == x { 1 as int } else { 0 as int }) + count_spec(s.skip(1), x)
            }
        }

        // pub exec fn count_vec(v: Vec<isize>, x: isize) -> (count: usize) 
        //     ensures
        //         count as int == count_spec(v@.map(|idx: int, val: isize| val as int), x as int),
        // {
        //     let mut i: usize = 0;
        //     let mut count: usize = 0;

        //     while i < v.len() 
        //         invariant 
        //             0 <= i <= v.len(),
        //             count <= i,
        //             count as int == count_spec(
        //                 v@.take(i as int).map(|idx: int, val: isize| val as int),
        //                 x as int,
        //             ),
        //         decreases 
        //             v.len() - i,
        //     {
        //         if v[i] == x {
        //             count = count + 1;
        //         }
        //         i = i + 1;
        //     }
        //     count
        // }

        // pub proof fn lemma_count(v: Vec<isize>, x: isize)
        //     ensures 
        //         count_vec(v, x) as int == count_spec(v@.map(|idx: int, val: isize| val as int), x as int),
        // {
        //     // assert(count_vec(v, x) == count_spec(v@, x));
        // }

    }

    mod problem_2 {
        use vstd::prelude::*;

        pub open spec fn sum_spec(s: Seq<usize>) -> int
            decreases s.len(),
        {
            if s.len() == 0 {
                0
            } else {
                // recurses from the back 
                sum_spec(s.drop_last()) + s.last() as int
            }
        }

        pub proof fn lemma_sum_spec_appending_x_adds_to_the_sum(s: Seq<usize>, x: usize)
            ensures
                sum_spec(s.push(x)) == sum_spec(s) + x as int,
        {
            let t = s.push(x);
            assert(t.len() == s.len() + 1);
            assert(t.drop_last() =~= s);
            assert(t.last() == x);
        }

        pub proof fn lemma_sum_spec_take_succ(s: Seq<usize>, i: int)
            requires
                0 <= i < s.len(),
            ensures
                // prefix of length i+1 = prefix of length i plus s[i]
                sum_spec(s.take(i + 1)) == sum_spec(s.take(i)) + s[i] as int,
        {
            assert(s.take(i + 1).drop_last() =~= s.take(i));
            assert(s.take(i + 1).last() == s[i]);
        }

        pub exec fn sum(s: Vec<usize>) -> (total: usize)
            requires
                forall|k: int| 0 <= k <= s@.len() ==>
                    #[trigger] sum_spec(s@.take(k)) <= usize::MAX,
            ensures
                total as int == sum_spec(s@),
        {
            let mut total: usize = 0;
            let mut i: usize = 0;

            proof {
                assert(s@.take(0) =~= Seq::<usize>::empty());
            }

            while i < s.len()
                invariant
                    i <= s.len(),
                    total as int == sum_spec(s@.take(i as int)),
                    forall|k: int| 0 <= k <= s@.len() ==>
                        #[trigger] sum_spec(s@.take(k)) <= usize::MAX,
                decreases s.len() - i,
            {
                proof {
                    lemma_sum_spec_take_succ(s@, i as int);
                    assert(sum_spec(s@.take(i as int + 1)) <= usize::MAX);
                }
                total = total + s[i];
                i += 1;
            }

            proof {
                assert(s@.take(s@.len() as int) =~= s@);
            }
            total
        }
    }

    mod problem_3 {
        use vstd::prelude::*;       
        // Remove consecutive duplicates (run squashing)

        // 3.1: Write a spec for dedup_runs_spec(s: Seq<int>) -> Seq<int> that removes 
        // adjacent duplicates (keeps the first of each run).
        pub open spec fn dedup_runs_spec(s: Seq<int>) -> Seq<int>
            decreases s.len(),
        {
            if s.len() == 0 {
                Seq::empty()
            } else {
                let rest = dedup_runs_spec(s.drop_last());
                if rest.len() > 0 && rest.last() == s.last() {
                    // same value as previous run so skip
                    rest
                } else {
                    // not same value so add it back to the Seq
                    rest.push(s.last())
                }
            }
        }

        // 3.2: Prove that the spec guarantees no consecutive duplicates preserves 
        // all other elements in the source array. So for r = dedup_runs_spec(s)
        // forall i (0 <= i < r.len() - 1 ==> r[i] != r[i+1])
        // and
        // forall i (0 <= i < r.len() ==> )
        pub proof fn lemma_dedup_runs_spec(s: Seq<int>)
            ensures
                forall|i: int| 0 <= i < dedup_runs_spec(s).len() ==>
                    s.contains(#[trigger] dedup_runs_spec(s)[i]),
                forall|i: int| 0 <= i < s.len() ==>
                    dedup_runs_spec(s).contains(#[trigger] s[i]),
            decreases s.len(),
        {
            if s.len() > 0 {
                let p = s.drop_last();
                assert(p.len() == s.len() - 1);
                lemma_dedup_runs_spec(p);

                let rest = dedup_runs_spec(p);
                let r = dedup_runs_spec(s);
                let same = rest.len() > 0 && rest.last() == s.last();

                // unfold the definition once, in a form that stays in scope
                assert(same ==> r == rest);
                assert(!same ==> r == rest.push(s.last()));

                // Part 1: every element of the result is in s
                assert forall|i: int| 0 <= i < r.len() implies s.contains(#[trigger] r[i]) by {
                    if i < rest.len() {
                        assert(r[i] == rest[i]);
                        assert(p.contains(rest[i]));
                        let j = choose|j: int| 0 <= j < p.len() && p[j] == rest[i];
                        assert(s[j] == p[j]);
                        assert(0 <= j < s.len() && s[j] == r[i]);
                    } else {
                        // if `same`, r == rest and i >= rest.len() contradicts i < r.len()
                        assert(!same);
                        assert(i == rest.len());
                        assert(r[i] == s.last());
                        assert(0 <= s.len() - 1 < s.len() && s[s.len() - 1] == r[i]);
                    }
                }

                // Part 2: every element of s is in the result
                assert forall|i: int| 0 <= i < s.len() implies r.contains(#[trigger] s[i]) by {
                    if i < p.len() {
                        assert(s[i] == p[i]);
                        assert(rest.contains(p[i]));
                        let j = choose|j: int| 0 <= j < rest.len() && rest[j] == p[i];
                        assert(r[j] == rest[j]);
                        assert(0 <= j < r.len() && r[j] == s[i]);
                    } else {
                        assert(i == s.len() - 1);
                        assert(s[i] == s.last());
                        if same {
                            assert(r[rest.len() - 1] == s.last());
                            assert(0 <= rest.len() - 1 < r.len());
                        } else {
                            assert(r[rest.len() as int] == s.last());
                            assert(0 <= rest.len() < r.len());
                        }
                    }
                }
            }
        }

        pub proof fn lemma_dedup_runs_no_adjacent_dups(s: Seq<int>)
            ensures
                forall|i: int| 0 <= i < dedup_runs_spec(s).len() - 1 ==>
                    #[trigger] dedup_runs_spec(s)[i] != dedup_runs_spec(s)[i + 1],
            decreases s.len(),
        {
            if s.len() > 0 {
                let p = s.drop_last();
                assert(p.len() == s.len() - 1);
                lemma_dedup_runs_no_adjacent_dups(p);

                let rest = dedup_runs_spec(p);
                let r = dedup_runs_spec(s);
                let same = rest.len() > 0 && rest.last() == s.last();
                assert(same ==> r == rest);
                assert(!same ==> r == rest.push(s.last()));

                assert forall|i: int| 0 <= i < r.len() - 1 implies #[trigger] r[i] != r[i + 1] by {
                    if same {
                        assert(rest[i] != rest[i + 1]);          // induction hypothesis
                    } else if i + 1 < rest.len() {
                        assert(r[i] == rest[i]);
                        assert(r[i + 1] == rest[i + 1]);
                        assert(rest[i] != rest[i + 1]);          // induction hypothesis
                    } else {
                        // i + 1 == rest.len(): the pair straddles rest.last() and the pushed s.last()
                        assert(i + 1 == rest.len());
                        assert(r[i] == rest[i]);
                        assert(rest[i] == rest.last());
                        assert(r[i + 1] == s.last());
                        // !same && rest.len() > 0  ==>  rest.last() != s.last()
                    }
                }
            } else {
                assert(dedup_runs_spec(s) == Seq::<int>::empty());
            }
        }

        // 3.3: Implement dedup_runs(v: &Vec<isize>) -> Vec<isize> iteratively and prove 
        // refinement relative to the spec.
        pub open spec fn to_ints(s: Seq<isize>) -> Seq<int> {
            Seq::new(s.len(), |i: int| s[i] as int)
        }

        pub open spec fn dedup_step(rest: Seq<int>, x: int) -> Seq<int> {
            if rest.len() > 0 && rest.last() == x { rest } else { rest.push(x) }
        }

        pub proof fn lemma_to_ints_push(s: Seq<isize>, x: isize)
            ensures
                to_ints(s.push(x)) == to_ints(s).push(x as int),
        {
            assert(to_ints(s.push(x)) =~= to_ints(s).push(x as int));
        }

        pub proof fn lemma_to_ints_take_succ(s: Seq<isize>, i: int)
            requires
                0 <= i < s.len(),
            ensures
                to_ints(s.take(i + 1)).len() == i + 1,
                to_ints(s.take(i + 1)).drop_last() == to_ints(s.take(i)),
                to_ints(s.take(i + 1)).last() == s[i] as int,
        {
            let t = s.take(i + 1);
            assert(t.len() == i + 1);
            assert(s.take(i).len() == i);
            assert(to_ints(t).drop_last() =~= to_ints(s.take(i)));
            assert(t[i] == s[i]);
        }

        // one loop step of the exec code, expressed on the spec side
        pub proof fn lemma_dedup_take_succ(v: Seq<isize>, i: int)
            requires
                0 <= i < v.len(),
            ensures
                dedup_runs_spec(to_ints(v.take(i + 1)))
                    == dedup_step(dedup_runs_spec(to_ints(v.take(i))), v[i] as int),
        {
            lemma_to_ints_take_succ(v, i);
            let ns = to_ints(v.take(i + 1));
            assert(ns.len() > 0);
            assert(dedup_runs_spec(ns) == dedup_step(dedup_runs_spec(ns.drop_last()), ns.last()));
        }

        pub exec fn dedup_runs(v: &Vec<isize>) -> (out: Vec<isize>)
            ensures
                to_ints(out@) == dedup_runs_spec(to_ints(v@)),
        {
            let mut out: Vec<isize> = Vec::new();
            let mut i: usize = 0;

            proof {
                let e = to_ints(v@.take(0));
                assert(e.len() == 0);
                assert(dedup_runs_spec(e) == Seq::<int>::empty());
                assert(to_ints(out@) =~= Seq::<int>::empty());
            }

            while i < v.len()
                invariant
                    i <= v.len(),
                    to_ints(out@) == dedup_runs_spec(to_ints(v@.take(i as int))),
                decreases v.len() - i,
            {
                let x = v[i];
                let ghost rest = to_ints(out@);

                proof {
                    lemma_dedup_take_succ(v@, i as int);
                    assert(rest.len() == out@.len());
                    if out@.len() > 0 {
                        assert(rest.last() == out@[out@.len() - 1] as int);
                    }
                }

                if out.len() > 0 && out[out.len() - 1] == x {
                    // x continues the current run: drop it
                } else {
                    proof { lemma_to_ints_push(out@, x); }
                    out.push(x);
                }

                proof {
                    assert(to_ints(out@) == dedup_step(rest, x as int));
                }
                i += 1;
            }

            proof {
                assert(v@.take(v@.len() as int) =~= v@);
            }
            out
        }
    }

    mod problem_4 {
        use vstd::prelude::*;       
        
    }

    fn main() {}
} // verus!
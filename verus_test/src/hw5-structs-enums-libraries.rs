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

        pub proof fn lemma_dedup_runs_spec(s: Seq<int>)
            ensures
                forall|i: int| 0 <= i < dedup_runs_spec(s).len() ==> #[trigger] (exists|j: int| 0 <= j < s.len() && dedup_runs_spec(s)[i] == s[j]),
                forall|i: int| 0 <= i < s.len() ==> #[trigger] (exists|j: int| 0 <= j < dedup_runs_spec(s).len() && s[i] == dedup_runs_spec(s)[j]),
        {
        }
    }

    mod problem_4 {
        use vstd::prelude::*;       
        
    }

    fn main() {}
} // verus!
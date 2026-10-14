use vstd::prelude::*;

verus! {
    mod problem_1 {
        use vstd::prelude::*;
        use vstd::arithmetic::mul::lemma_mul_is_distributive_add;
        use vstd::arithmetic::mul::lemma_mul_basics;
        use vstd::arithmetic::mul::lemma_mul_left_inequality;

        pub exec fn q3(n0: usize, m0: usize) -> (res: usize)
            requires
                m0 != 0,
                n0 * m0 <= usize::MAX
            ensures
                n0 * m0 == res,
        {
            let mut res: usize = 0;
            let mut n = n0;

            while 0 < n
                invariant
                    m0 != 0,
                    n0 * m0 <= usize::MAX,
                    n0 * m0 == res + n * m0,
                decreases n,
            {
                assert(res + m0 <= n0 * m0) by {
                    lemma_mul_left_inequality(m0 as int, 1, n as int);
                }
                res = res + m0;
                n = n - 1;
                assert(n0 * m0 == res + n * m0) by {
                    lemma_mul_is_distributive_add(m0 as int, n as int, 1);
                    lemma_mul_basics(m0 as int);
                };
            }
            res
        }

        pub proof fn lemma_q3(n0: usize, m0: usize, res: usize, n: usize) 
        {
            // I (invariant)
            // assert requires implies invariant
            assert((m0 != 0 && n0 * m0 <= usize::MAX) ==> (m0 != 0 && n0 * m0 <= usize::MAX && n0 * m0 == res + n * m0));

            // while loop body preserves I
            assert((0 < n) ==> (m0 != 0 && n0 * m0 <= usize::MAX && n0 * m0 == res + n * m0 && res + m0 <= n0 * m0));
            assert((0 < n) ==> (n0 * m0 == (res + m0) + (n-1) * m0) && ((res+m0) + m0 <= n0 * m0));
            // not looping implies Q
            assert((0 < n) ==> (res == 0));
            // termination
            assert((n > 0));
        }

    }

    mod problem_2 {
        use vstd::prelude::*;

    }

    mod problem_3 {
        use vstd::prelude::*;
    }

    fn main() {}
} // verus!
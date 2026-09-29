use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_inequality;

verus! {

    mod problem_1 {
        use vstd::prelude::*;
        use vstd::arithmetic::mul::lemma_mul_inequality;

        // 1.1
        pub open spec fn factorial_spec(n: nat) -> nat 
            decreases 
                n
        {
            if n == 0 {
                1
            } else {
                n * factorial_spec((n-1) as nat)
            }
        }

        // 1.2
        pub proof fn test_factorial_n_gte_1() {
            assert(factorial_spec(0) == 1);
            assert(factorial_spec(1) == 1);
            assert(factorial_spec(2) == 2);
        }

        // 1.3 
        pub proof fn lemma_factorial_is_monotonic(i: nat, j:nat) by (nonlinear_arith) // tell remember how to do math
            ensures 
                i <= j ==> factorial_spec(i) <= factorial_spec(j),
            decreases
                j,
        {
            if j == 0 {
            } else {
                lemma_factorial_is_monotonic(i, (j - 1) as nat);
            }
            
        }

        pub proof fn test_i_lt_j_then_factorial_i_will_be_gte_factorial_i() 
        {
            assert_by_compute(factorial_spec(3) >= factorial_spec(2));
        }

        // 1.4
        pub fn factorial_exec(n: usize) -> (result: usize)
            requires
                factorial_spec(n as nat) <= usize::MAX as nat,
            ensures
                factorial_spec(n as nat) == result,
            decreases 
                n
        {
            if n == 0 {
                1
            } else {
                proof {
                lemma_factorial_is_monotonic((n - 1) as nat, n as nat);
                }
                n * factorial_exec((n-1))
            }
        }

        // 1.5
        pub fn factorial_iter(n: usize) -> (result: usize)
            requires
                factorial_spec(n as nat) <= usize::MAX as nat,
            ensures
                factorial_spec(n as nat) == result,
        {
            let mut result: usize = 1;
            let mut i: usize = 0;
            
            while i < n  
                invariant
                    0 <= i <= n, // i bounds 
                    factorial_spec(n as nat) <= usize::MAX as nat,
                    result == factorial_spec(i as nat),
                decreases
                    n - i 
            {
                i += 1;
                proof {
                    lemma_factorial_is_monotonic(i as nat, n as nat);
                }
                result = result * i;
            }
            result
        }

        pub fn test_factorial_spec_and_factorial_iter_are_equal() {
            // let result = factorial_iter(2);
            // assert(result == factorial_spec(2));
            proof {
            assert_by_compute(factorial_spec(2) == 2);
            }

            let result = factorial_iter(2);
            assert(result == 2);
        }
    }

    mod problem_2 {
        use vstd::prelude::*;
    }

    mod problem_3 {
        use vstd::prelude::*;
    }

    fn main()
    {

    }
} //verus!
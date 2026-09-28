use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_inequality;

verus! {

    mod problem_1 {
        use vstd::prelude::*;
        use vstd::arithmetic::mul::lemma_mul_inequality;

        // 1.1
        pub open spec fn factorial(n: nat) -> nat 
            decreases 
                n
        {
            if n == 0 {
                1
            } else {
                n * factorial((n-1) as nat)
            }
        }

        // 1.2
        pub proof fn test_factorial_n_gte_1() {
            assert(factorial(0) == 1);
            assert(factorial(1) == 1);
            assert(factorial(2) == 2);
        }

        // 1.3 
        pub proof fn lemma_factorial_is_monotonic(i: nat, j:nat) by (nonlinear_arith) // tell remember how to do math
            ensures 
                i <= j ==> factorial(i) <= factorial(j),
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
            assert_by_compute(factorial(3) >= factorial(2));
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
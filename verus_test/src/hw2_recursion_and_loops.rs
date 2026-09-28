use vstd::prelude::*;

verus! {

    mod problem_1 {
        use vstd::prelude::*;
        pub open spec fn factorial(n: nat) -> nat 
            decreases n,
        {
            if n == 0 {
                1
            } else {
                n * factorial((n-1) as nat)
            }
        }

        pub proof fn lemma_factorial_is_monotonic(i: nat, j:nat)
            requires
                i <= j,
        {
            
        }

        pub proof fn test_i_less_than_j_then_factorial_i_will_be_greater_than_factorial_i() 
        {
            // Given
            let i: nat = 5;
            let j: nat = 10;
            
            // When
            let answer_i: nat = factorial(i);
            let answer_j: nat = factorial(j);

            assert(answer_j >= answer_i);
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
use vstd::prelude::*;

verus! {

    spec fn mult_spec(n: nat, m: nat) -> nat
        decreases
            n
    {
        if n == 0 {
            0
        } else {
            let n0: nat = (n - 1) as nat; 
            m + mult_spec(n0, m)
        }
    }

    proof fn test_given_four_and_five_when_mult_spec_then_twenty()
    {
        // given
        let n: nat = 4;
        let m: nat = 5;
        let expected: nat = 20;

        // when
        // let answer: nat = mult_spec(n, m);

        // then 
        // assert(expected == answer) by (compute_only); 
        assert_by_compute(expected == mult_spec(n, m)); // call mult_spec directly
        assert_by_compute(42 == mult_spec(6, 7)); 
    }

    proof fn lemma_mult_spec(n: nat, m: nat) by (nonlinear_arith) // tell remember how to do math
        ensures 
            n * m == mult_spec(n, m)
        decreases
            n 
    {
        if n == 0 {

        } else {
            // assume(false); will make true but instead use recursion call
            let n0: nat = (n - 1) as nat;
            lemma_mult_spec(n0, m);
        }

    }
} // verus!
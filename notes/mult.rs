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
        let answer: nat = mult_spec(n, m);

        // then 
        // assert(expected == answer) by (compute_only); 
        // assert_by_compute(expected == mult_spec(n, m)); // call mult_spec directly
        // how to use variables 
        assert(expected == answer) by {
            reveal_with_fuel(mult_spec, 6);
        }
        // how to use without variables 
        assert_by_compute(42 == mult_spec(6, 7)); 
    }

    proof fn lemma_mult_spec(n: nat, m: nat) by (nonlinear_arith) // tell remember how to do math
        ensures 
            n * m == mult_spec(n, m)
        decreases
            n 
    {
        if n == 0 { // base case P(0)

        } else { // inductive step 
            // assume(false); will make true but instead use recursion call
            let n0: nat = (n - 1) as nat;
            lemma_mult_spec(n0, m); // key part of inductive step where assume P(n-1) and show P(n)
        }
    }

    exec fn mult(n: usize, m: usize) -> (result: usize)
        requires
            usize::MIN <= mult_spec(n as nat, m as nat) <= usize::MAX as nat,
        ensures
            mult_spec(n as nat, m as nat) == result,
    {
        let mut i: usize = n;
        let mut result: usize = 0;

        while i > 0 
            invariant 
                usize::MIN <= mult_spec(n as nat, m as nat) <= usize::MAX as nat,
                mult_spec(n as nat, m as nat) == result + mult_spec(i as nat, m as nat), 
            decreases
                i 
        {
            result += m;
            i -= 1;
        }
        result 
    }
} // verus!
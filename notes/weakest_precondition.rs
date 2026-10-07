use vstd::prelude::*;

verus! {

    exec fn g(x: isize) -> (r: isize) 
        requires
            x > isize::MIN + 1,
            x < isize::MAX - 1,
            x <= -9 || x >= 9,
        ensures
            r > 9,
            r > x,
    {
        let mut r: isize = x;
        if r < 0 {
            r = -r;
        }
        r = r + 1;

        r
    }

    proof fn g_wp(x: isize)
    {
        // let ghost q_0: bool = r > 9 && r > x;
        // let ghost q_1: bool = r + 1 > 9 && r + 1 > x;
        // let ghost q_2: bool = -r + 1 > 9 && -r + 1 > x; // use substitution rule, sub q_1  r with line 16 r 
        // let ghost q_3: bool = (r < 0 && q_2) || (r >= 0 && q_1);
        // now substitute r with x 
        // let ghost q_0: bool = r > 9 && r > x; // comment out q_0 because basically became q_1 
        let ghost q_1: bool = x + 1 > 9 && x + 1 > x;
        let ghost q_2: bool = -x + 1 > 9 && -x + 1 > x; 
        let ghost q_3: bool = (x < 0 && q_2) || (x >= 0 && q_1);
        let req: bool = {
            &&& x > isize::MIN + 1
            &&& x < isize::MAX - 1
            &&& x <= -9 || x >= 9
        };
        assert(req ==> q_3);
        // req needs to be strong enough to guarantee q_3 (the weakest precondition)
    }

    // While Loop

    exec fn h(n: usize) -> (m: usize)
        requires 
            n >= 0,
        ensures 
            n == m,
    {
        let mut m: usize = 0;
        assert(n >= 0 && m <= n); // assert the invariant at the head of the loop
        // havoc m
        assume(n >= 0 && m <= n);
        if m < n // change while to if
        {
            m = m + 1;
            assert(n >= 0 && m <= n); // end of loop assert the invariant 
            assume(false); // false -> 0 
        } 
        
        m
    }

} // verus!
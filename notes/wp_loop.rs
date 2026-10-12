use vstd::prelude::*;

verus! {
    fn f(x: usize, y: usize) -> (result: (usize, usize)) 
        by (nonlinear_arith)
        requires
            x >= 0,
            y > 0,
        ensures
            result.0 * y + result.1 == x,
            result.1 > 0,
            result.1 <y,
    {
        let mut q: usize = 0;
        let mut r: usize = x;
        while (r >= y)
            invariant 
                x >= 0,
                y > 0,
                q * y + r == x,
                r >= 0,
            decreases r
        {
            broadcast use vstd::arithmetic::mul::group_mul_properties;

            r = r - y;
            q = q + 1;
        }
        (q, r)
    }

    proof fn lemma_f(x: usize, y: usize, q: usize, r: usize)
    {
        assert((x >= 0 && y > 0) ==> (x >= 0 && y > 0 && x == x && x >= 0)); // I (invariant)
        assert((r >= y && x >= 0 && y > 0 && q * y + r = x && r >= 0) ==> (x >= 0 && y > 0 && (q + 1) * y + (r - y) == x && r >= 0)) by { // loop body preserves I 
            broadcast use vstd::arithmetic::mul::group_mul_properties;
        };
        assert(!(r >= y && x >= 0 && y > 0 && q * y + r = x && r >= 0) ==> (q * y + r == x && r >= 0 && r < y)); // not going through loop, not looping implies Q 
        assert((r >= y && x >= 0 && y > 0 && q * y + r = x && r >= 0) ==> r - y >= 0); // termination, r bounded by 0 when looping
        assert((r >= y && x >= 0 && y > 0 && q * y + r = x && r >= 0) ==> r > r - y); // termination, r decreases on every loop iteration 
    }
} //verus!

// 0: q * y + r = x and r >= 0 and r < y
// 1: x >= 0 and y > 0 and q * y + r = x and r >= 0 
// 2: x >= 0 and y > 0 and (q+1) * y + r = x and r >= 0 
// 3: x >= 0 and y > 0 and (q+1) * y + (r-y) = x and r >= 0 
// for all q, r (r >= y and (1)) ==> (3)
// for all q, r (not r >= y and (1)) ==> (0) (not going through loop)
// 4: r - y >= 0
// for all q, r (r >= y and (1)) ==> (4)
// [t = r; 26;27], t > r
// 5: t > r - y
// 6: r > r - y
// for all q, r (r >= y and (1)) ==> (6)
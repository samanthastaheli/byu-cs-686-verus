use vstd::prelude::*;

verus! {
    mod problem_1 {
        use vstd::prelude::*;

        fn m(x: isize, y: isize) -> (result: (isize, isize))
            requires
                x != y,
            ensures
                result.0 > result.1
        {
            if x > y {
                (x, y)
            } else {
                (y, x)
            }
        }

        proof fn m_gp(x: isize, y: isize)
        {
            // Use conditional (if) rule
            let ghost branch_then: bool = (x > y);
            let ghost branch_else: bool = (y > x);
            let ghost condition_rule: bool = ((x > y) ==> branch_then) && (!(x > y) ==> branch_else);
            let ghost req: bool = x != y;
            assert(req ==> condition_rule);
        }
    }

    mod problem_2 {
        use vstd::prelude::*;

        exec fn m(x0: isize) -> (x: isize)
            requires
                usize::MIN <= x0 - 3 <= usize::MAX
            ensures
                (x0 < 3 ==> x == 1),
                (x0 >= 3 ==> x < x0),
        {
            let mut x = x0 - 3;
            if x < 0 {
                x = 1;
            } else {
                if true {
                    x = x + 1;
                } else {
                    x = 10;
                }
            }
            x
        }

        proof fn m_wp(x0: isize)
        {
            let ghost q_0: bool = (x0 < 3) || (x0 >= 3);
            let ghost q_1: bool = x0 < 3;
            let ghost q_2: bool = q_1 < 0; // then
            let ghost q_3: bool = q_1 == 1;
            let ghost q_4: bool =  (true && q_1 + 1 > 1) || q_1 == 10; // else
            let ghost condition_rule: bool = q_3 || q_4;
            let ghost req: bool = usize::MIN <= x0 - 3 <= usize::MAX;
            assert(req ==> condition_rule);
        }
    }

    mod problem_3 {
        use vstd::prelude::*;
    }

    fn main() {}
} // verus!
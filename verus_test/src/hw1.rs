use vstd::prelude::*;

verus! {

    mod problem_1 {
        use vstd::prelude::*;
        pub open spec fn spec_is_in_range_by_step(value: int, min: int, max: int, step: nat) -> (result: bool) {
            if min <= value <= max {
                let diff = value - min;
                diff % (step as int) == 0
            } else {
                false
            }
        }

        pub exec fn is_in_range_by_step(value: i32, min: i32, max: i32, step: u16) -> (result: bool)
            requires
                step > 0,
                max - min <= i32::MAX as int, // proves won't overflow
            ensures
                result == spec_is_in_range_by_step(value as int, min as int, max as int, step as nat),
        {
            if min > value || value > max {
                return false;
            }
            let diff = value - min;
            let remainder = diff.checked_rem_euclid(step as i32);
            if remainder == Some(0) {
                true
            } else {
                false
            }
        }
    }
    
    mod problem_2 {
        use vstd::prelude::*;
        pub open spec fn spec_absolute_difference(x:int, y:int) -> (result: nat) {
            let diff = x - y;
            if diff < 0 {
                (-diff) as nat
            } else {
                diff as nat
            }
        }

        pub exec fn absolute_difference(x:i32, y:i32) -> (result: u32) 
            requires
                // set explicit bounds (prevent underflow/overflow)
                x - y >= i32::MIN as int,
                y - x >= i32::MIN as int,
                x - y <= i32::MAX as int,
                y - x <= i32::MAX as int,
            ensures
                result as int == spec_absolute_difference(x as int, y as int)
        {
        if x >= y {
                (x - y) as u32
            } else {
                (y - x) as u32
            }
        }
    }

    mod problem_3 {
        use vstd::prelude::*;
        pub open spec fn spec_median_three(a:int, b:int, c:int) -> int {
            if b <= a <= c {
                a 
            } else if a <= b <= c {
                b
            } else {
                c
            }
        }

        pub open spec fn spec_median_five(a:int, b:int, c:int, d:int, e:int) -> int {
            let median_1 = spec_median_three(a, b, c);
            let median_2 = spec_median_three(b, c, d);
            let median_3 = spec_median_three(c, d, e);
            spec_median_three(median_1, median_2, median_3)
        }

        pub proof fn median_of_medians_filter(a:i32, b:i32, c:i32, d:i32, e:i32) -> (median: int) 
            requires
                a <= b <= c <= d <= e,
            ensures
                median == spec_median_five(a as int, b as int, c as int, d as int, e as int)
        {
            let median = spec_median_five(a as int, b as int, c as int, d as int, e as int);
            assert(median == c);
            assert(spec_median_five(1, 2, 3, 4, 5) == 3);
            median 
        }
    }


    fn main() {

        // Problem 1
        let result1 = problem_1::is_in_range_by_step(10, 0, 20, 5);
        assert(result1 == true);
        let result2 = problem_1::is_in_range_by_step(11, 0, 20, 5);
        assert(result2 == false);

        // Problem 2
        let diff1 = problem_2::absolute_difference(10, 5);
        let diff2 = problem_2::absolute_difference(5, 10);
        assert(diff1 == diff2)
    }

} // verus!
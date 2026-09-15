use vstd::prelude::*;

verus! {

spec fn spec_is_in_range_by_step(value: int, min: int, max: int, step: nat) -> (result: bool) {
    if min <= value <= max {
        let diff = value - min;
        diff % (step as int) == 0
    } else {
        false
    }
}

exec fn is_in_range_by_step(value: i32, min: i32, max: i32, step: u16) -> (result: bool)
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

fn main() {

    // Problem 1
    let result1 = is_in_range_by_step(10, 0, 20, 5);
    assert(result1 == true);
    let result2 = is_in_range_by_step(11, 0, 20, 5);
    assert(result2 == false);
}

} // verus!
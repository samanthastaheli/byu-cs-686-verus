use vstd::prelude::*;

verus! {

spec fn spec_is_in_range_by_step(value: int, min: int, max: int, step: nat) -> (result: bool) {
    if min <= value <= max {
        let diff = value - min;
        diff % step == 0
    } else {
        false
    }
}

exec fn is_in_range_by_step(value: i32, min: i32, max: i32, step: u16) -> (result: bool)
    requires
        step > 0,
    ensures
        result == spec_is_in_range_by_step(value as int, min as int, max as int, step as nat),
{
    if min > value || value > max {
        return false;
    }
    let diff = value - min;
    let remainder = diff.checked_rem_euclid(step);
    if remainder == 0 {
        true
    } else {
        false
    }
}

fn main() {
    assert(is_in_range_by_step(10, 0, 20, 5) == true);
    assert(is_in_range_by_step(11, 0, 20, 5) == false);
}

} // verus!
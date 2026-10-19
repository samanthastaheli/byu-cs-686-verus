use vstd::prelude::*;

verus! {
    spec fn max_spec(i: isize, j: isize) -> isize
    {
        if i > j {
            i
        } else {
            j
        }
    }

    spec fn max_from_spec(s: Seq<isize>, initial: isize) -> isize
    {
        s.fold_left(initial, |i: isize, j: isize | max_spec(i, j))
    } 
    
    spec fn is_max_from_value(s: Seq<isize>, initial: isize, max_from_value: isize) -> bool
    {
        /// &&& = low precedent conjunction 
        &&& forall|i: int| 0 <= i < s.len() ==> s[i] <= max_from_value
        &&& max_from_value == initial || (exists|i: int| 0 <= i < s.len() && max_from_value == s[i])
    }

    proof fn lemma_max_from_spec_take_successor(s: Seq<isize>, initial: isize, i: int)
        requires
            0 <= i < s.len()
        ensures
            max_from_spec(s.take(i + 1), initial) == max_spec(max_from_spec(s.take(i), initial), s[i])
    {
        assert(s.take(i + 1).drop_last() == s.take(i));
    }

    // prove a proper max
    proof fn lemma_max_from_spec_returns_max_from_value(s: Seq<isize>, initial: isize)
        ensures
            is_max_from_value(s, initial, max_from_spec(s, initial))
    {
        if s.len() > 0 {
            lemma_max_from_spec_returns_max_from_value(s.drop_last(), initial);
            lemma_max_from_spec_take_successor(s, initial, s.len() as int - 1); // take with one smaller
            assert(s.take(s.len() as int) == s); // structural, keep track of what the take does
        }
    }

    exec fn max(i: isize, j: isize) -> (answer: isize)
        ensures
            answer == max_spec(i, j)
    {
        if i > j {
            i
        } else {
            j
        }
    }

    exec fn max_from(v: Vec<isize>, initial: isize) -> (answer: isize)
        ensures 
            answer == max_from_spec(v@, initial)
    {
        let mut answer: isize = initial;
        let mut i: usize = 0;

        while i < v.len()
            invariant 
                0 <= i as int <= v@.len(),
                answer == max_from_spec(v@.take(i as int), initial),
            decreases 
                v@.len() - i
        {
            proof { // satisfy the invariant 
                lemma_max_from_spec_take_successor(v@, initial, i as int);
            }
            answer = max(answer, v[i]);
            i += 1;
        }
        answer
    }
} // verus!
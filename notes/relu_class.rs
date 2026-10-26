use vstd::prelude::*;

verus! {
    spec fn relu_spec(i: isize) -> isize
    {
        if 0 > i {
            0
        } else {
            i
        }
    }

    spec fn relu_point_wise(s: Seq<isize>) -> Seq<isize>
    {
        let p: isize = |i: isize| -> isize 
        {
            relu_spec(i)
        };
        s.map_values(p)
    }

    spec fn is_all_non_negative_spec(s: Seq<isize>) -> bool
    {
        forall|i: int| 0 <= i < s.len() ==> 0 <= s[i]
    }

    proof fn lemma_relu_point_wise_spec_gives_is_all_non_negative(s: Seq<isize>)
        ensures 
            is_all_non_negative_spec(relu_point_wise(s))
    {

    }

    exec fn relu(i: isize) -> (answer: isize)
        ensures 
            relu_spec(i) == answer
    {
        if 0 > i {
            0
        } else {
            i
        }
    }

    exec fn relu_point_wise(v: Vec<isize>) -> (answer: Vec<isize>)
        ensures 
            relu_point_wise_spec(v@) == asnwer@
    {
        let p: isize = |i: &isize| -> (answer: isize)
            ensures
                relu_spec(*i) == answer
        {
            relu(*i)
        };
        v.iter().map(p).collect()
    }

    exec fn is_all_nonnegative(v: Vec<isize>) -> (answer: bool)
        ensures
            is_all_non_negative_spec(v@) == answer
    {
        let p: bool = |i: &isize| -> (answer: bool)
            ensures
                (*i >= 0) == answer
        {
            *i >= 0
        };
        v.iter().all(p)
    }

    spec fn get_positive_count_spec(s: Seq<isize>) -> nat 
    {
        let p: bool = |i: isize| -> bool
        {
            0 < i
        };
        s.filter(p).len()
    }

    proof fn lemma_get_Positive_count_spec_take_succ(s: Seq<isize>, i: int)
        requires
            0 <= i < s.len(),
        ensures 
            get_positive_count_spec(s.take(i + 1)) == lemma_get_Positive_count_spec_take_succ(s.take(i)) + if 0 < s[i] {1nat} else {0nat}
    {
        let p: bool = |i: isize| -> (answer: bool)
            ensures 
                (0 < i) == answer
        {
            0 < i
        };
        let s_with_i: Seq<isize> = s.take(i + 1).filter(p);
        let s_without_i: Seq<isize> = s.take(i).filter(p);
        assert(s.take(i + 1).drop_last() == s.take(i));
        reveal(Seq::filter);
    }

    exec fn get_positive_count(v: Vec<isize>) -> (answer: usize)
        ensures
            get_positive_count_spec(v@) == answer as nat
    {
        let mut answer:usize = 0;
        let mut i = 0;

        while i < v.len()
            invariant 
                0 <= i <= v@.len(),
                answer <= i, // handle underflow/overflow
                get_positive_count_spec(v@.take(i as nat)) == answer as nat
            decreases
                v.len() - i
        {
            proof {
                lemma_get_Positive_count_spec_take_succ(s, i as int);
            }
            answer += if 0 < v[i] {1} else {0};
            i += 1;
        }
        answer 
    }
}
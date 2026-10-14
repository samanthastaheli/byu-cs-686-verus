use vstd::prelude::*;

verus! {
    // iff = if and only if 
    proof fn lemma_all_iff_forall<A>(s: Seq<A>, p: spec_fn(A) -> bool) // spec_fn is type notation for function
        ensures 
            s.all(p) <==> forall|i: int| 0 <= i < s.len() ==> p(s[i])
    {
    }

    spec fn is_all_nonneg_spec(s: Seq<isize>) -> bool {
        s.all(|i: isize| i >= 0)
    }

    proof fn lemma_all_nonneg_iff_forall_nonneg(s: Seq<isize>)
        ensures
            s.all(|i: int| i >= 0) <==> forall|i: int| (0 <= i < s.len() ==> s[i] >= 0)
    {
        let p: () = |i: isize| i >= 0;
        lemma_all_iff_forall(s, p);
    }

    proof fn lemma_all_nonneg_take_succ(s: Seq<isize>, i: int)
        requires 
            0 <= i < s.len(),
        ensures 
            is_all_nonneg_spec(s.take(i + 1)) <==> (is_all_nonneg_spec(s.take(i)) && s[i] >= 0), // way for verus to understand take relationship
    {
        lemma_all_nonneg_iff_forall_nonneg(s.take(i + 1));
        lemma_all_nonneg_iff_forall_nonneg(s.take(i));
        assert(s.take(i + 1)[i] == s[i]);
    }

    exec fn is_all_nonneg(v: Vec<isize>) -> (out: bool)
        ensures 
            out == is_all_nonneg_spec(v@)
    {
        let mut i: i32 = 0;
        while i < v.len()
            invariant
                0 <= i <= v@.len(),
                is_all_nonneg_spec(v@.take(i as int)),
            decreases v.len() - i
        {
            proof {
                lemma_all_nonneg_take_succ(v@, i as int);
            }
            if v[i] < 0 {
                return false
            } 

            i += 1;
        }
        true 
    }

    

    // proof fn lemma_is_all_nonneg_spec_iff_forall_nonneg(s: Seq<int>) 
    //     ensures 
    //         is_all_nonneg_spec(s) <==> forall|i: int| (0 <= i < s.len() ==> s[i] >= 0)
    //     {

    //     }
} //verus!
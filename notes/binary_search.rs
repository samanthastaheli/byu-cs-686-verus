use vstd::prelude::*;

verus! {
    spec fn is_sorted(s: Seq<int>) {
        forall|i:int, j:int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    spec(checked) fn binary_search_spec(x: int, s:Seq<int>) -> Option<int> 
        // Option is some i or None (monad)
        // can use some(i).bind(f) same as f(i)
        // unwrap using ! 
        recommends 
            is_sorted(s),
    {
        if s.len() == 0 || s.first() > x || s.last() < x {
            None::<int>
        } else {
            binary_search_core_spec(x, s, 0, (s.len() - 1) as int)
        }
    }

    spec fn is_all_lt(s: Seq<int>, x: int) -> Option<int>
    {
        forall|i: int| 0 <= i <= s.len() ==> s[i] < x
    }

    spec fn is_all_gte(s: Seq<int>, x: int) -> Option<int>
    {
        forall|i: int| 0 <= i < s.len() ==> s[i] >= x
    }

    // checked is call site, so at call site check recommends 
    spec(checked) fn binary_search_core_spec(x: int, s: Seq<int>, low: int, high:int) -> Option<int> 
        recommends
            is_sorted(s),
            0 < s.len(),
            0 <= low <= high < s.len(),
            is_all_lt(s.subrange(0, low), x),
            is_all_gte(s.subrange(high, s.len()), x),
        decreases
            high - low when high >= low
            // add when because need to know high and lows relationship 
    {
        if low == high {
            if s[low] == x {
                Some::<int>(low)
            } else {
                None::<int>
            }
        } else {
            let mid: int = low + (high - low) / 2;
            if s[mid] < x {
                binary_search_core_spec(x, s, mid+1, high)
            } else {
                binary_search_core_spec(x, s, low, mid)
            }
        }
    }

    proof fn test_spec()
    {
        assert_by_compute(None::<int> == binary_search_spec(0, seq!()));
        // assert_by_compute(Seq::<int>(0) == binary_search_spec(0, seq!())); // should fail
        assert_by_compute(None::<int>, binary_search_spec(0, seq!(1, 2, 3, 3, 4, 5))); // check lower bound
        assert_by_compute(None::<int>, binary_search_spec(7, seq!(1, 2, 3, 3, 5, 6))); // check higher bound
        assert_by_compute(None::<int>, binary_search_spec(4, seq!(1, 2, 3, 3, 5, 6))); // check not in list
        assert_by_compute(Some::<int>(2), binary_search_spec(3, seq!(1, 2, 3, 3, 5, 6))); // check in list
    }

    proof fn lemma_binary_search_core_spec(x: int, s: Seq<int>, low: int, high:int)
        requires
                is_sorted(s),
                0 < s.len(),
                0 <= low <= high < s.len(),
                is_all_lt(s.subrange(0, low), x),
                is_all_gte(s.subrange(high, s.len()), x),
        ensures
            match binary_search_core_spec(x, s, low, high) {
                Some::<int>(i) => {
                    &&& s.contains(x)
                    &&& 0 <= i < s.len() // i within length of array
                    &&& s[i] == x
                    &&& is_all_gte(s.subrange(i, s.len()), x)
                },
                None::<int> => !s.contains(x),
            }
        decreases
            high - low,
    {
        if low == high {
            assert(s == s.subrange(0, low) + s.subrange(high, s.len() as int));
            if s[low] == x {
            } else {
            }
        } else {
            let mid: int = low + (high - low) / 2;
            if s[mid] < x {
                lemma_binary_search_core_spec(x, s, mid+1, high)
            } else {
                lemma_binary_search_core_spec(x, s, low, mid)
            }
        }
    }

    proof fn lemma_binary_search_spec(x:int, s:Seq<int>)
        requires
            is_sorted(s),
        ensures
            match binary_search_spec(x, s) {
                Some::<int>(i) => {
                    &&& s.contains(x)
                    &&& 0 <= i < s.len() // i within length of array
                    &&& s[i] == x
                    &&& is_all_gte(s.subrange(i, s.len()), x)
                },
                None::<int> => !s.contains(x),
            }
        {
            if s.len() == 0 || s.first() > x || s.last() < x {
            } else {
                binary_search_core_spec(x, s, 0, (s.len() - 1) as int)
            }
        }
} //verus!
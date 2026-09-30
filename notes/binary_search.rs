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
        let s: Seq<int> = seq!(1, 2, 3, 3, 5, 6);
        assert_by_compute(Some::<int>(2), binary_search_spec(3, s)); // check in list
        // assert(Some::<int>(2), binary_search_spec(3, s));
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
                    // tell verus how put together 
                    &&& s == s.subrange(0, i) + s.subrange(i, s.len() as int)
                    &&& is_all_lt((0, i), x)
                    &&& s[i] == x
                    // &&& is_all_gte(s.subrange(i, s.len()), x)
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


    spec fn seq_isize_to_seq_int(s: Seq<isize>) -> Seq<int> 
    {
        s.map_values(|x: isize | x as int)
    }

    spec fn option_isize_to_option_int(o: Option<usize>) -> Option<int> 
    {
        match o {
            Some(i) => Some::<int>(i as int),
            None => None<int>
        }
        o.map(|x: usize | x as int)
    }

    // to make not need invariant in while loop (if requires and invariant are going to be the same)
    #[verifier::loop_isolation(false)]
    exec fn binary_search_core(x: isize, s: &[isize], low: isize, high: isize) -> (result: Option<usize>) // s is a slice/borrow
        requires
            is_sorted(seq_isize_to_seq_int(s@)),
            0 < s.len(),
            0 <= low <= high < s.len(),
            // ({let x: bool = true; x}),
            is_all_lt(seq_isize_to_seq_int((s@).subrange(0, low as int)), x as int),
            is_all_gte(seq_isize_to_seq_int((s@).subrange(high as int, s.len() as int)), x as int),
        ensures 
            binary_search_core_spec(x as int, seq_isize_to_seq_int(s@), low as int, high as int) == option_isize_to_option_int(result)
    {
        let mut ll: usize = low;
        let mut hh: usize = high;

        while ll != hh 
        // verus treats while loop as a func so need to do requires again by doing invariant 
            invariant
                // is_sorted(seq_isize_to_seq_int(s@)), // don't need because of verifier::loop_isolation(false)
                // 0 < s.len(), // don't need because of verifier::loop_isolation(false)
                0 <= low <= ll <= hh <= high < s.len(),
                is_all_lt(seq_isize_to_seq_int((s@).subrange(0, ll as int)), x as int),
                is_all_gte(seq_isize_to_seq_int((s@).subrange(hh as int, s.len() as int)), x as int),
            decreases
                hh - ll
        {
            let mid: usize = ll + (hh - ll) / 2;
            if s[mid] < x {
                ll = mid + 1;
                let ghost s_low: Seq<int> = seq_isize_to_seq_int(s@).subrange(hh as int, s@.len() as int); // ghost pulls out and does't go to the rust compiler
                assert(s_low.last() < x as int);
            } else {
                hh = mid;
                let ghost s_high: Seq<int> = seq_isize_to_seq_int(s@).subrange(hh as int, s@.len() as int); // ghost pulls out and does't go to the rust compiler
                assert(s_high.first() >= x as int);
            }
        }

        // connect what did in while loop to ensures statement
        let ghost s_all: Seq<int> = seq_usize_to_seq_int(s@);
        assert(binary_search_core_spec(x as int, s_all, low as int, high as int) == binary_search_core_spec(x as int, s_all, ll as int, hh as int)) by {
            lemma_binary_search_core_spec(x as int, s_all, low as int, high as int);
            lemma_binary_search_core_spec(x as int, s_all, ll as int, hh as int);
        }

        if s[ll] == x {
            Some::<usize>(ll)
        } else {
            None::<usize>
        }
    }
} //verus!
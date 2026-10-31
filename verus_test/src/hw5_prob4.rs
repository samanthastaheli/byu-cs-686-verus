// Verified merge sort in Verus.
//
// Proves two things about `merge_sort`:
//   1. the output is sorted
//   2. the output is a permutation of the input (same multiset of elements)
//
// Run with:  verus merge_sort.rs            (verify only)
//            verus merge_sort.rs --compile  (verify, then build and run main)

use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

broadcast use {
    vstd::multiset::group_multiset_axioms,
    vstd::multiset::group_multiset_properties,
    vstd::seq_lib::group_seq_lib_default,
};

// ------------------------------------------------------------------
// Specification
// ------------------------------------------------------------------

pub open spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Appending an element that is >= everything so far keeps a sequence sorted.
proof fn lemma_sorted_push(s: Seq<i32>, x: i32)
    requires
        sorted(s),
        forall|k: int| 0 <= k < s.len() ==> s[k] <= x,
    ensures
        sorted(s.push(x)),
{
    let t = s.push(x);
    assert forall|p: int, q: int| 0 <= p < q < t.len() implies t[p] <= t[q] by {
        assert(t[p] == s[p]);
        if q < s.len() {
            assert(t[q] == s[q]);
        } else {
            assert(q == s.len());
            assert(t[q] == x);
        }
    }
}

// ------------------------------------------------------------------
// copy_range: out = v[lo..hi]
// ------------------------------------------------------------------

fn copy_range(v: &Vec<i32>, lo: usize, hi: usize) -> (out: Vec<i32>)
    requires
        lo <= hi <= v.len(),
    ensures
        out@ == v@.subrange(lo as int, hi as int),
        out.len() == hi - lo,
{
    let mut out: Vec<i32> = Vec::new();
    let mut k: usize = lo;
    proof {
        assert(out@ =~= v@.subrange(lo as int, lo as int));
    }
    while k < hi
        invariant
            lo <= k <= hi,
            hi <= v.len(),
            out@ == v@.subrange(lo as int, k as int),
        decreases hi - k,
    {
        proof {
            assert(out@.push(v@[k as int]) =~= v@.subrange(lo as int, k as int + 1));
        }
        out.push(v[k]);
        k += 1;
    }
    out
}

// ------------------------------------------------------------------
// merge: combine two sorted vectors into one sorted vector
// ------------------------------------------------------------------

fn merge(a: &Vec<i32>, b: &Vec<i32>) -> (out: Vec<i32>)
    requires
        sorted(a@),
        sorted(b@),
    ensures
        sorted(out@),
        out@.to_multiset() == a@.to_multiset().add(b@.to_multiset()),
        out.len() == a.len() + b.len(),
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(out@.to_multiset() =~= a@.subrange(0, 0).to_multiset().add(
            b@.subrange(0, 0).to_multiset(),
        ));
    }
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            out.len() == i + j,
            sorted(out@),
            // everything already output is <= the next unread element of each input
            forall|k: int| 0 <= k < out@.len() && i < a.len() ==> out@[k] <= a@[i as int],
            forall|k: int| 0 <= k < out@.len() && j < b.len() ==> out@[k] <= b@[j as int],
            // the output so far is exactly the multiset of what has been consumed
            out@.to_multiset() == a@.subrange(0, i as int).to_multiset().add(
                b@.subrange(0, j as int).to_multiset(),
            ),
        decreases (a.len() - i) + (b.len() - j),
    {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            // ---- take from a ----
            let x = a[i];
            proof {
                let sa = a@.subrange(0, i as int);
                let sb = b@.subrange(0, j as int);

                // multiset bookkeeping
                assert(a@.subrange(0, i as int + 1) =~= sa.push(x));
                to_multiset_build(sa, x);
                to_multiset_build(out@, x);
                assert(sa.to_multiset().insert(x).add(sb.to_multiset())
                    =~= sa.to_multiset().add(sb.to_multiset()).insert(x));
                assert(out@.push(x).to_multiset()
                    =~= a@.subrange(0, i as int + 1).to_multiset().add(sb.to_multiset()));

                // sortedness bookkeeping
                assert forall|k: int| 0 <= k < out@.len() implies out@[k] <= x by {}
                lemma_sorted_push(out@, x);
                assert forall|k: int|
                    0 <= k < out@.push(x).len() && i as int + 1 < a.len()
                    implies out@.push(x)[k] <= a@[i as int + 1] by {
                    assert(a@[i as int] <= a@[i as int + 1]);
                    if k < out@.len() {
                        assert(out@.push(x)[k] == out@[k]);
                    } else {
                        assert(out@.push(x)[k] == x);
                    }
                }
                assert forall|k: int|
                    0 <= k < out@.push(x).len() && j < b.len()
                    implies out@.push(x)[k] <= b@[j as int] by {
                    if k < out@.len() {
                        assert(out@.push(x)[k] == out@[k]);
                    } else {
                        assert(out@.push(x)[k] == x);
                    }
                }
            }
            out.push(x);
            i += 1;
        } else {
            // ---- take from b ----
            let y = b[j];
            proof {
                let sa = a@.subrange(0, i as int);
                let sb = b@.subrange(0, j as int);

                // multiset bookkeeping
                assert(b@.subrange(0, j as int + 1) =~= sb.push(y));
                to_multiset_build(sb, y);
                to_multiset_build(out@, y);
                assert(sa.to_multiset().add(sb.to_multiset().insert(y))
                    =~= sa.to_multiset().add(sb.to_multiset()).insert(y));
                assert(out@.push(y).to_multiset()
                    =~= sa.to_multiset().add(b@.subrange(0, j as int + 1).to_multiset()));

                // sortedness bookkeeping
                assert forall|k: int| 0 <= k < out@.len() implies out@[k] <= y by {}
                lemma_sorted_push(out@, y);
                assert forall|k: int|
                    0 <= k < out@.push(y).len() && i < a.len()
                    implies out@.push(y)[k] <= a@[i as int] by {
                    if k < out@.len() {
                        assert(out@.push(y)[k] == out@[k]);
                    } else {
                        assert(out@.push(y)[k] == y);
                    }
                }
                assert forall|k: int|
                    0 <= k < out@.push(y).len() && j as int + 1 < b.len()
                    implies out@.push(y)[k] <= b@[j as int + 1] by {
                    assert(b@[j as int] <= b@[j as int + 1]);
                    if k < out@.len() {
                        assert(out@.push(y)[k] == out@[k]);
                    } else {
                        assert(out@.push(y)[k] == y);
                    }
                }
            }
            out.push(y);
            j += 1;
        }
    }
    proof {
        // loop exit: both inputs fully consumed, so the subranges are the whole vectors
        assert(i == a.len() && j == b.len());
        assert(a@.subrange(0, i as int) =~= a@);
        assert(b@.subrange(0, j as int) =~= b@);
    }
    out
}

// ------------------------------------------------------------------
// merge_sort
// ------------------------------------------------------------------

fn merge_sort(v: &Vec<i32>) -> (out: Vec<i32>)
    ensures
        sorted(out@),
        out@.to_multiset() == v@.to_multiset(),
        out.len() == v.len(),
    decreases v.len(),
{
    if v.len() <= 1 {
        // 0 or 1 elements: already sorted, just copy
        let out = copy_range(v, 0, v.len());
        proof {
            assert(v@.subrange(0, v.len() as int) =~= v@);
            assert(sorted(out@));
        }
        return out;
    }

    let mid = v.len() / 2;
    let left = copy_range(v, 0, mid);
    let right = copy_range(v, mid, v.len());

    let sl = merge_sort(&left);
    let sr = merge_sort(&right);
    let out = merge(&sl, &sr);

    proof {
        // v is the concatenation of its two halves, so multisets add up
        assert(left@ + right@ =~= v@);
        lemma_multiset_commutative(left@, right@);
        assert(out@.to_multiset() =~= v@.to_multiset());
    }
    out
}

} // verus!

fn main() {
    let v: Vec<i32> = vec![5, 2, 9, 1, 5, 6, 3];
    let sorted_v = merge_sort(&v);
    println!("{:?}", sorted_v);
}
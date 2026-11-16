// Homework 6 starting point: specification of Dijkstra's shortest path.
// Everything marked TODO(student) is yours to complete:
//   - `uninterp` spec functions: write their definitions (remove `uninterp`).
//   - `admit()` bodies: replace with proofs. The statements are given.
//   - Not given: the invariant, any further helper specs, and the lemmas that
//     preserve the invariant. Add the ones your proof needs in `DijkstrasSpec`.
// Not wired into main.rs yet.

// * this is marked as my notes 
use vstd::prelude::*;

verus! {

/// Mathematical graph: what the specification talks about.
pub ghost struct GraphSpec {
    pub n: nat,
    pub e: spec_fn(nat, nat) -> Option<nat>,
}

impl GraphSpec {
    pub open spec fn edge(self, u: nat, v: nat) -> Option<nat> {
        (self.e)(u, v)
    }

    pub open spec fn well_formed(self) -> bool {
        forall|u: nat, v: nat|
            (#[trigger] (self.e)(u, v)).is_some() ==> u < self.n && v < self.n
    }

    /// `p` is a walk: non-empty, in range, and every consecutive pair is an edge.
    pub open spec fn is_path(self, p: Seq<nat>) -> bool {
        &&& 0 < p.len()
        &&& forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] < self.n
        &&& forall|i: int| 0 <= i < p.len() - 1 ==> (#[trigger] self.edge(p[i], p[i + 1])).is_some()
    }

    pub open spec fn is_path_from_to(self, p: Seq<nat>, s: nat, t: nat) -> bool {
        self.is_path(p) && p.first() == s && p.last() == t
    }

    // * Cost is not declarative it is functional, it unfolds the path
    /// Cost is defined by recursion on the *last* step so that
    /// `cost(p.push(v)) == cost(p) + w(p.last(), v)` holds by unfolding.
    /// Only meaningful when `is_path(p)`.
    pub open spec fn cost(self, p: Seq<nat>) -> nat
        decreases p.len(),
    {
        if p.len() <= 1 {
            0
        } else {
            let u: nat = p[p.len() - 2];
            let v: nat = p.last();
            self.cost(p.drop_last()) + self.edge(u, v).unwrap_or(0)
        }
    }

    /// `p` is a shortest path from `s` to `t`.
    pub open spec fn is_shortest(self, p: Seq<nat>, s: nat, t: nat) -> bool {
        &&& self.is_path_from_to(p, s, t)
        &&& forall|q: Seq<nat>|
            self.is_path_from_to(q, s, t) ==> self.cost(p) <= #[trigger] self.cost(q)
    }

    pub open spec fn reachable(self, s: nat, t: nat) -> bool {
        // * let p = choose reachable(s, t)
        // * might use choose concept in some of proofs 
        // * let p be a path between s,t (choose)
        // * have to prove path exists before choose  
        exists|p: Seq<nat>| self.is_path_from_to(p, s, t) // * existential are tricky 
    }

    // ---- Lectures 1-2: the classical-proof lemmas (graph facts, no algorithm) ----

    /// Extending a path by one edge adds exactly that edge's weight.
    pub proof fn lemma_cost_push(self, p: Seq<nat>, v: nat)
        requires
            self.is_path(p),
            self.edge(p.last(), v).is_some(),
            v < self.n,
        ensures
            self.is_path(p.push(v)),
            self.cost(p.push(v)) == self.cost(p) + self.edge(p.last(), v).unwrap(),
            // * cost + weight = cost of that node 
    {
        let q = p.push(v);

        // TODO(student): replace with a proof
        // * need assertions for push
        assert(q.len() == p.len() + 1); // assert same length 
        assert(q.last() == v); // assert last element is v
        assert(q.drop_last() =~= p); // assert equal 
        assert forall|i: int| 0 <= i < p.len() implies q[i] == p[i] by {}  // push_index_different
    }

    /// Prefixes of paths are paths and cost no more (weights are naturals).
    pub proof fn lemma_prefix(self, p: Seq<nat>, k: int)
        requires
            self.is_path(p),
            1 <= k <= p.len(),
        ensures
            self.is_path(p.take(k)),
            self.cost(p.take(k)) <= self.cost(p),
        decreases p.len() - k,
    {
        // TODO(student): replace with a proof
        // * need assertions for take 
        let q = p.take(k);

        assert(q.len() == k);
        // assert(q.len() == p.len() - k);
        assert(q.last() == p[k - 1]);
        assert forall|i: int| 0 <= i < k implies q[i] == p[i] by {}   // take_index

        // assert cost (self.cost(p.take(k)) <= self.cost(p)) (need to use induction)
        if k == p.len() {
            assert(p.take(k) =~= p);
        } else {
            let r = p.drop_last();
            assert(r.len() == p.len() - 1);
            assert(r.take(k) =~= p.take(k));
            assert(p =~= r.push(p.last()));

            self.lemma_prefix(r, k);
        }
    }
}
/// Dijkstra's state: the settled set `S`, and for every node the best path found
/// so far from `src` (`None` = not yet reached). The tentative distance of a node
/// is the cost of its best path.
pub ghost struct DijkstraState { // * shows up as st
    pub settled: Set<nat>,
    pub best: spec_fn(nat) -> Option<Seq<nat>>,
    // * how to initialize best
}

/// Dijkstra's algorithm as a specification, kept apart from the graph so that
/// all of its machinery (helper specs, invariant, lemmas) lives here.
pub ghost struct DijkstrasSpec<'a> {
    pub graph: &'a GraphSpec,
}

/// HELPER (induction). A finite set of naturals that are all `< n` has at most
/// `n` elements. This is what makes `fuel = graph.n` enough.
pub proof fn lemma_nat_set_len_le(s: Set<nat>, n: nat)
    requires
        forall|x: nat| #[trigger] s.contains(x) ==> x < n,
    ensures
        s.len() <= n,
    decreases n,
{
    if n == 0 {
        assert(s =~= Set::<nat>::empty());
    } else {
        let m = (n - 1) as nat;
        let t = s.remove(m);
        assert forall|x: nat| #[trigger] t.contains(x) implies x < m by {}
        lemma_nat_set_len_le(t, m);
        // s.len() <= t.len() + 1 <= m + 1 == n
    }
}

impl DijkstrasSpec<'_> {
    // TODO(student): add the invariant, helper specs, and supporting lemmas here.
    // * spec invariant
    // * three separate specs (pick, settle, run)

    // pub open spec fn inv(self, st: DijkstraState, src: nat) -> bool {
    //     &&& src < self.graph.n
    //     &&& (st.best)(src) == Some(seq![src])
    //     &&& (st.settled.contains(src) || forall|v: nat| v != src ==> (#[trigger] (st.best)(v)).is_none()) // init src is not in S at first
    //     // everything settled has a shortest best path
    //     &&& forall|v: nat| #[trigger] st.settled.contains(v) ==> v < self.graph.n
    //     &&& forall|v: nat| #[trigger] st.settled.contains(v) ==> {
    //         &&& (st.best)(v).is_some()
    //         &&& self.graph.is_shortest((st.best)(v).unwrap(), src, v)
    //     }
    //     // any best path is a path from src to that node
    //     &&& forall|v: nat| 0 <= v < self.graph.n && (#[trigger] (st.best)(v)).is_some() ==>
    //         self.graph.is_path_from_to((st.best)(v).unwrap(), src, v)
    //     // edges leaving the settled set have been relaxed
    //     &&& forall|i: nat, j: nat|
    //         st.settled.contains(i) && !st.settled.contains(j)
    //             && (#[trigger] self.graph.edge(i, j)).is_some() ==> {
    //         &&& (st.best)(j).is_some()
    //         &&& self.cost_of(st, j) <= self.cost_of(st, i) + self.graph.edge(i, j).unwrap() // show select always choose least cost candidate
    //     }
    // }

    pub open spec fn inv(self, st: DijkstraState, src: nat) -> bool {
        &&& src < self.graph.n
        &&& (st.best)(src) == Some(seq![src])
        // NEW: settled nodes are inside the graph (needed for the fuel argument)
        &&& forall|v: nat| #[trigger] st.settled.contains(v) ==> v < self.graph.n
        // NEW: `init` settles nothing, so src is not in S at first. Until it is,
        // src is the only node with a path. Without this, `pick` could choose some
        // other node with a bogus best path in the very first round.
        &&& (st.settled.contains(src)
            || forall|v: nat| v != src ==> (#[trigger] (st.best)(v)).is_none())
        // everything settled has a shortest best path
        &&& forall|v: nat| #[trigger] st.settled.contains(v) ==> {
            &&& (st.best)(v).is_some()
            &&& self.graph.is_shortest((st.best)(v).unwrap(), src, v)
        }
        // any best path is a path from src to that node
        &&& forall|v: nat| 0 <= v < self.graph.n && (#[trigger] (st.best)(v)).is_some() ==>
            self.graph.is_path_from_to((st.best)(v).unwrap(), src, v)
        // edges leaving the settled set have been relaxed
        &&& forall|i: nat, j: nat|
            st.settled.contains(i) && !st.settled.contains(j)
                && (#[trigger] self.graph.edge(i, j)).is_some() ==> {
            &&& (st.best)(j).is_some()
            &&& self.cost_of(st, j) <= self.cost_of(st, i) + self.graph.edge(i, j).unwrap()
        }
    }

    /// The crossing-edge lemma: a path from inside `S` to outside `S` has a
    /// first vertex `y` outside `S`; its prefix to `y` only has `S` before the end.
    pub proof fn lemma_first_exit(self, p: Seq<nat>, inside: spec_fn(nat) -> bool)
        requires
            self.graph.is_path(p),
            inside(p.first()), // * at a minimum the first node is inside 
            !inside(p.last()), // * last node outside 
        ensures
            exists|k: int|
                1 <= k < p.len() && !inside(p[k]) && forall|j: int| 0 <= j < k ==> inside(p[j]),
        decreases p.len(),
    {
        // TODO(student): replace with a proof
        
        // p.len() >= 2, since first is inside and last is not
        if exists|j: int| 1 <= j < p.len() - 1 && !inside(p[j]) {
            let j = choose|j: int| 1 <= j < p.len() - 1 && !inside(p[j]);
            let q = p.take(j + 1);
            self.graph.lemma_prefix(p, j + 1);
            assert(q.first() == p.first());
            assert(q.last() == p[j]);
            self.lemma_first_exit(q, inside);
            let k = choose|k: int| 1 <= k < q.len() && !inside(q[k])
                && forall|i: int| 0 <= i < k ==> inside(q[i]);
            assert(q[k] == p[k]);
            assert forall|i: int| 0 <= i < k implies inside(p[i]) by { assert(q[i] == p[i]); }
            assert(1 <= k < p.len() && !inside(p[k])
                && forall|i: int| 0 <= i < k ==> inside(p[i]));  // witness
        } else {
            let k = p.len() - 1;
            assert(!inside(p[k]));
            assert(forall|i: int| 0 <= i < k ==> inside(p[i]));  // i == 0 is p.first()
        }
    }

    /// Tentative distance of `v` in `st`: the cost of its best path.
    /// TODO(student) Meaningful only when `v` has a best path. 
    pub open spec fn cost_of(self, st: DijkstraState, v: nat) -> nat
    {
        self.graph.cost((st.best)(v).unwrap())
    }

    /// TODO(student) `v` is in range, unsettled, and has a best path. 
    pub open spec fn is_candidate(self, st: DijkstraState, v: nat) -> bool
    {
        &&& v < self.graph.n // in range
        &&& !st.settled.contains(v) // unsettled
        &&& (st.best)(v).is_some() // best path
    }

    /// Helper: a candidate whose distance is <= every other candidate's.
    pub open spec fn is_min_candidate(self, st: DijkstraState, u: nat) -> bool {
        &&& self.is_candidate(st, u)
        &&& forall|v: nat| #[trigger] self.is_candidate(st, v)
                ==> self.cost_of(st, u) <= self.cost_of(st, v)
    }

    /// The next node to settle: `Some(u)` where `u` is a candidate whose
    /// tentative distance is at most that of every other candidate, or `None`
    /// TODO(student) when there is no candidate. 
    pub open spec fn pick(self, st: DijkstraState) -> Option<nat> {
        if exists|u: nat| self.is_min_candidate(st, u) {
            Some(choose|u: nat| self.is_min_candidate(st, u))
        } else {
            None
        }
    }

    /// Initial state: nothing settled; only `src` has a path, `[src]`.
    /// TODO(student)
    pub open spec fn init(self, src: nat) -> DijkstraState {
        DijkstraState {
            settled: Set::empty(),
            best: |v: nat| if v == src { Some(seq![src]) } else { None },
        }
    }

    /// Helper: relaxing edge (u, v) gives a strictly better path to `v`.
    /// `v != u` is needed because `st.settled` doesn't contain `u` yet.
    pub open spec fn improves(self, st: DijkstraState, u: nat, v: nat) -> bool {
        &&& self.graph.edge(u, v).is_some()
        &&& v != u
        &&& !st.settled.contains(v)
        &&& match (st.best)(v) {
            None => true,
            Some(old) => self.graph.cost((st.best)(u).unwrap().push(v))
                < self.graph.cost(old),
        }
    }

    /// One round: settle `u` (the node chosen by `pick`) and relax its
    /// out-edges.
    /// TODO(student)
    pub open spec fn settle(self, st: DijkstraState, u: nat) -> DijkstraState
    // * figure out how to define best 
    {
        DijkstraState {
            settled: st.settled.insert(u),
            best: |v: nat|
                if self.improves(st, u, v) {
                    Some((st.best)(u).unwrap().push(v))
                } else {
                    (st.best)(v)
                },
        }
    }
    
    /// Repeat `settle(st, pick(st))` until `dst` is settled or `pick` returns `None`.
    /// TODO(student): define it, including its `decreases` measure.
    pub open spec fn run(self, dst: nat, st: DijkstraState, fuel: nat) -> DijkstraState
        decreases fuel,
    {
        if fuel == 0 || st.settled.contains(dst) {
            st
        } else {
            match self.pick(st) {
                None => st,
                Some(u) => self.run(dst, self.settle(st, u), (fuel - 1) as nat),
            }
        }
    }

    pub proof fn lemma_candidate_gives_pick(self, st: DijkstraState, v: nat)
        requires
            self.is_candidate(st, v),
        ensures
            self.pick(st).is_some(),
        decreases self.cost_of(st, v),
    {
        if self.is_min_candidate(st, v) {
            // v is a witness for the `exists` inside `pick`
            assert(exists|u: nat| self.is_min_candidate(st, u));
        } else {
            // some candidate is strictly cheaper than v
            assert(exists|w: nat|
                self.is_candidate(st, w) && self.cost_of(st, w) < self.cost_of(st, v));
            let w = choose|w: nat|
                self.is_candidate(st, w) && self.cost_of(st, w) < self.cost_of(st, v);
            self.lemma_candidate_gives_pick(st, w);
        }
    }

    pub proof fn lemma_pick(self, st: DijkstraState, src: nat)
        requires
            self.graph.well_formed(),
            self.inv(st, src),
        ensures
            match self.pick(st) {
                Some(u) => {
                    &&& self.is_min_candidate(st, u)
                    &&& self.graph.is_shortest((st.best)(u).unwrap(), src, u)
                    &&& (st.settled.contains(src) || u == src)
                },
                None => forall|dst: nat|
                    !st.settled.contains(dst) ==> !(#[trigger] self.graph.reachable(src, dst)),
            },
    {
        match self.pick(st) {
            Some(u) => {
                // `pick` is only `Some(choose ..)` when the `exists` held
                assert(self.is_min_candidate(st, u));
                let p = (st.best)(u).unwrap();
                assert(self.graph.is_path_from_to(p, src, u));  // inv clause 4 (u < n)

                // until src is settled, src is the only node with a path
                assert(st.settled.contains(src) || u == src) by {
                    if !st.settled.contains(src) && u != src {
                        assert((st.best)(u).is_none());   // NEW clause of inv
                    }
                }

                assert forall|q: Seq<nat>| self.graph.is_path_from_to(q, src, u)
                    implies self.graph.cost(p) <= #[trigger] self.graph.cost(q) by {
                    if st.settled.contains(src) {
                        // q starts inside S and ends outside S (u is unsettled): it must leave S
                        let inside = |x: nat| st.settled.contains(x);
                        self.lemma_first_exit(q, inside);
                        let k = choose|k: int|
                            1 <= k < q.len() && !inside(q[k])
                                && forall|j: int| 0 <= j < k ==> inside(q[j]);
                        let x = q[k - 1];
                        let y = q[k];
                        // x is inside S (j = k - 1) and y is outside S
                        assert(inside(q[k - 1]));
                        assert(st.settled.contains(x));
                        assert(!st.settled.contains(y));
                        // (x, y) is an edge of q: is_path at index i = k - 1. Verus only
                        // matches the trigger edge(p[i], p[i + 1]) if the index is written
                        // as `k - 1 + 1`, so spell it out and then rewrite it to `k`.
                        assert(self.graph.edge(q[k - 1], q[k - 1 + 1]).is_some());
                        assert(q[k - 1 + 1] == q[k]);
                        assert(self.graph.edge(x, y).is_some());
                        assert(y < self.graph.n);
                        let qx = q.take(k);                    // src ~> x, all inside S
                        self.graph.lemma_prefix(q, k);         // qx is a path, cost(qx) <= cost(q)
                        assert(qx.len() == k);
                        assert(qx[0] == q[0]);
                        assert(qx[k - 1] == q[k - 1]);
                        assert(qx.first() == src);
                        assert(qx.last() == x);
                        // x is settled, so best(x) is shortest: cost(best x) <= cost(qx)
                        let bx = (st.best)(x).unwrap();
                        assert(self.graph.is_path_from_to(qx, src, x));
                        assert(self.graph.cost(bx) <= self.graph.cost(qx));
                        // the crossing edge (x, y) was relaxed: cost(best y) <= cost(best x) + w
                        assert(self.cost_of(st, y) <= self.cost_of(st, x)
                            + self.graph.edge(x, y).unwrap());
                        // the prefix of q through y costs cost(qx) + w, and is <= cost(q)
                        self.graph.lemma_cost_push(qx, y);
                        assert(qx.push(y) =~= q.take(k + 1));
                        assert(self.graph.cost(qx.push(y)) == self.graph.cost(q.take(k + 1)));
                        self.graph.lemma_prefix(q, k + 1);
                        // y is a candidate, and u is a minimum candidate
                        assert(self.is_candidate(st, y));
                        assert(self.cost_of(st, u) <= self.cost_of(st, y));
                        // cost(p) <= cost(best y) <= cost(best x) + w <= cost(qx) + w
                        //         == cost(q.take(k + 1)) <= cost(q)
                        assert(self.graph.cost(p) <= self.graph.cost(q));
                    } else {
                        // src is not settled yet, so u == src and its cost is 0
                        assert(u == src);
                        assert(p == seq![src]);
                        assert(self.graph.cost(seq![src]) == 0);
                    }
                }
            },
            None => {
                // `pick` is None. By lemma_candidate_gives_pick, a single candidate
                // would make `pick` return Some, so "z is a candidate" below is a
                // contradiction with `None`.
                assert forall|dst: nat| !st.settled.contains(dst)
                    implies !(#[trigger] self.graph.reachable(src, dst)) by {
                    if self.graph.reachable(src, dst) {
                        let q = choose|q: Seq<nat>| self.graph.is_path_from_to(q, src, dst);
                        // src must be settled, otherwise src itself would be a candidate
                        assert(st.settled.contains(src)) by {
                            if !st.settled.contains(src) {
                                assert(self.is_candidate(st, src));
                                self.lemma_candidate_gives_pick(st, src);   // contradicts `None`
                            }
                        }
                        let inside = |x: nat| st.settled.contains(x);
                        self.lemma_first_exit(q, inside);
                        let k = choose|k: int|
                            1 <= k < q.len() && !inside(q[k])
                                && forall|j: int| 0 <= j < k ==> inside(q[j]);
                        let x = q[k - 1];
                        let y = q[k];
                        assert(inside(q[k - 1]));
                        assert(st.settled.contains(x));
                        assert(!st.settled.contains(y));
                        // (x, y) is an edge of q (same `k - 1 + 1` trick as above)
                        assert(self.graph.edge(q[k - 1], q[k - 1 + 1]).is_some());
                        assert(q[k - 1 + 1] == q[k]);
                        assert(self.graph.edge(x, y).is_some());
                        assert(y < self.graph.n);
                        // the relaxed crossing edge gives y a best path, so y is a candidate
                        assert(self.is_candidate(st, y));
                        self.lemma_candidate_gives_pick(st, y);     // contradicts `None`
                    }
                }
            },
        }
    }

    pub proof fn lemma_settle(self, st: DijkstraState, src: nat, u: nat)
        requires
            self.graph.well_formed(),
            self.inv(st, src),
            self.pick(st) == Some(u),
        ensures
            self.inv(self.settle(st, u), src),
            self.settle(st, u).settled.len() == st.settled.len() + 1,
    {
        // what `pick` guarantees about u
        self.lemma_pick(st, src);
        assert(self.is_min_candidate(st, u));
        assert(self.graph.is_shortest((st.best)(u).unwrap(), src, u));
        assert(st.settled.contains(src) || u == src);

        let st2 = self.settle(st, u);
        let pu = (st.best)(u).unwrap();
        assert(self.graph.is_path_from_to(pu, src, u));
        assert(pu.last() == u);
        assert(st2.settled =~= st.settled.insert(u));

        // what `best` looks like after settling
        assert forall|v: nat| #[trigger] (st2.best)(v) == (if self.improves(st, u, v) {
            Some(pu.push(v))
        } else {
            (st.best)(v)
        }) by {}

        // (a) nodes in the new settled set never get a new best path
        assert forall|v: nat| #[trigger] st2.settled.contains(v)
            implies (st2.best)(v) == (st.best)(v) by {
            assert(!self.improves(st, u, v));   // v == u, or v already settled
        }

        // (b) a node that does improve gets a genuine path of the right cost
        assert forall|v: nat| #[trigger] self.improves(st, u, v) implies
            self.graph.is_path_from_to(pu.push(v), src, v)
            && self.graph.cost(pu.push(v)) == self.graph.cost(pu) + self.graph.edge(u, v).unwrap()
        by {
            assert(self.graph.edge(u, v).is_some());
            assert(v < self.graph.n);               // well_formed
            self.graph.lemma_cost_push(pu, v);
            assert(pu.push(v).first() == src);
            assert(pu.push(v).last() == v);
        }

        // ---- the clauses of inv(st2) ----
        assert(st2.settled.len() == st.settled.len() + 1);
        assert forall|v: nat| #[trigger] st2.settled.contains(v) implies v < self.graph.n by {}

        // src is settled afterwards (it is the first thing settled)
        assert(st2.settled.contains(src));

        // best(src) is still [src]: nothing is strictly cheaper than cost 0
        assert(self.graph.cost(seq![src]) == 0);
        assert(!self.improves(st, u, src));
        assert((st2.best)(src) == Some(seq![src]));

        // settled nodes have shortest best paths
        assert forall|v: nat| #[trigger] st2.settled.contains(v) implies {
            &&& (st2.best)(v).is_some()
            &&& self.graph.is_shortest((st2.best)(v).unwrap(), src, v)
        } by {
            assert((st2.best)(v) == (st.best)(v));
            if v == u {
                // from lemma_pick
            } else {
                assert(st.settled.contains(v));
            }
        }

        // every best path is a path from src
        assert forall|v: nat| 0 <= v < self.graph.n && (#[trigger] (st2.best)(v)).is_some()
            implies self.graph.is_path_from_to((st2.best)(v).unwrap(), src, v) by {
            if self.improves(st, u, v) {
                // (b)
            } else {
                assert((st2.best)(v) == (st.best)(v));
            }
        }

        // edges leaving the new settled set are relaxed
        assert forall|i: nat, j: nat|
            st2.settled.contains(i) && !st2.settled.contains(j)
                && (#[trigger] self.graph.edge(i, j)).is_some()
            implies (st2.best)(j).is_some()
                && self.cost_of(st2, j) <= self.cost_of(st2, i) + self.graph.edge(i, j).unwrap()
        by {
            assert(!st.settled.contains(j) && j != u);
            assert((st2.best)(i) == (st.best)(i));
            assert(self.cost_of(st2, i) == self.cost_of(st, i));
            if i == u {
                assert(j < self.graph.n);           // well_formed
                self.graph.lemma_cost_push(pu, j);
                if self.improves(st, u, j) {
                    assert((st2.best)(j) == Some(pu.push(j)));
                } else {
                    // improves failed only because best(j) exists and is already no worse
                    assert((st.best)(j).is_some());
                    assert((st2.best)(j) == (st.best)(j));
                }
            } else {
                assert(st.settled.contains(i));     // old inv clause 5 applies
                if self.improves(st, u, j) {
                    assert((st.best)(j).is_some());
                    assert((st2.best)(j) == Some(pu.push(j)));
                } else {
                    assert((st2.best)(j) == (st.best)(j));
                }
            }
        }
    }

    pub proof fn lemma_run(self, src: nat, dst: nat, st: DijkstraState, fuel: nat)
        requires
            self.graph.well_formed(),
            self.inv(st, src),
        ensures
            self.inv(self.run(dst, st, fuel), src),
            self.run(dst, st, fuel).settled.contains(dst)
                || self.pick(self.run(dst, st, fuel)).is_none()
                || self.run(dst, st, fuel).settled.len() >= st.settled.len() + fuel,
        decreases fuel,
    {
        if fuel == 0 || st.settled.contains(dst) {
        } else {
            match self.pick(st) {
                None => {},
                Some(u) => {
                    self.lemma_settle(st, src, u);
                    self.lemma_run(src, dst, self.settle(st, u), (fuel - 1) as nat);
                },
            }
        }
    }

    /// Cost and path found by Dijkstra's algorithm; `None` when a node is out of
    /// range or `dst` is unreachable.
    pub open spec fn shortest_path(self, src: nat, dst: nat) -> Option<(nat, Seq<nat>)> {
        if src < self.graph.n && dst < self.graph.n {
            let f = self.run(dst, self.init(src), self.graph.n); // * run needs a terminations arg, via func arg
            if f.settled.contains(dst) {
                let p = (f.best)(dst).unwrap();
                Some((self.graph.cost(p), p))
            } else {
                None
            }
        } else {
            None
            // * if asking for 2 nodes that aren't part of graph 
        }
    }

    /// The algorithm's result satisfies the shortest-path contract.
    pub proof fn lemma_shortest_path_correct(self, src: nat, dst: nat)
        requires
            self.graph.well_formed(),
        ensures
            match self.shortest_path(src, dst) {
                Some((c, p)) => {
                    &&& self.graph.is_shortest(p, src, dst)
                    &&& c == self.graph.cost(p)
                },
                None => !(src < self.graph.n && dst < self.graph.n && self.graph.reachable(
                    src,
                    dst,
                )),
            },
    {
        // admit();  // TODO(student): replace with a proof
        // * show select preserves invariant
        // self.inv(self.init(src), src);
        // * show relax preserves invariant
        // * show run preserves invariant
        if src < self.graph.n && dst < self.graph.n {
            let n = self.graph.n;
            let st0 = self.init(src);

            // ---- init satisfies inv ----
            let p0 = seq![src];
            assert(p0.len() == 1);
            assert(p0[0] == src);
            assert(self.graph.is_path(p0));
            assert((st0.best)(src) == Some(p0));
            assert(st0.settled =~= Set::<nat>::empty());
            assert forall|v: nat| v != src implies (#[trigger] (st0.best)(v)).is_none() by {}
            assert forall|v: nat| 0 <= v < n && (#[trigger] (st0.best)(v)).is_some()
                implies self.graph.is_path_from_to((st0.best)(v).unwrap(), src, v) by {
                assert(v == src);
            }
            assert(self.inv(st0, src));
            assert(st0.settled.len() == 0);

            // ---- run keeps inv, and says why it stopped ----
            self.lemma_run(src, dst, st0, n);
            let f = self.run(dst, st0, n);

            // Some case: dst settled => inv clause 3 gives is_shortest(best(dst))
            if !f.settled.contains(dst) {
                // None case. First rule out "ran out of fuel":
                if !self.pick(f).is_none() {
                    // then f.settled.len() >= n, but adding dst would give n + 1 nodes < n
                    let g = f.settled.insert(dst);
                    assert forall|x: nat| #[trigger] g.contains(x) implies x < n by {}
                    lemma_nat_set_len_le(g, n);
                    assert(g.len() == f.settled.len() + 1);
                    assert(false);
                }
                // so no candidates remain, hence dst is unreachable (lemma_pick, None case)
                self.lemma_pick(f, src);
            }
        }
    }
}

fn main() {}

} // verus!
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
        exists|p: Seq<nat>| self.is_path_from_to(p, s, t) // * existentials are tricky 
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

impl DijkstrasSpec<'_> {
    // TODO(student): add the invariant, helper specs, and supporting lemmas here.
    // * spec invariant
    // * three seprate specs (pick, settle, run)

    pub open spec fn inv(self, st: DijkstraState, src: nat) -> bool {
        &&& src < self.graph.n
        &&& (st.best)(src) == Some(seq![src])
        // everything settled has a shortest best path
        &&& forall|v: nat| #[trigger] st.settled.contains(v) ==> {
            &&& (st.best)(v).is_some()
            &&& self.graph.is_shortest((st.best)(v).unwrap(), src, v)
        }
        // any best path is a path from src to that node
        &&& forall|v: nat| v < self.graph.n && (#[trigger] (st.best)(v)).is_some() ==>
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
        &&& v < self.graph.n
        &&& !st.settled.contains(v)
        &&& (st.best)(v).is_some()
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
        self.inv(self.init(src), src);
        // * show relax preserves invariant
        // * show run preserves invariant
    }
}

fn main() {}

} // verus!
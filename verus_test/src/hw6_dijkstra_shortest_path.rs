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
        admit();  // TODO(student): replace with a proof
        // * need assertions for push
    }

    /// Prefixes of paths are paths and cost no more (weights are naturals).
    pub proof fn lemma_prefix(self, p: Seq<nat>, k: int)
        requires
            self.is_path(p),
            1 <= k <= p.len(),
        ensures
            self.is_path(p.take(k)),
            self.cost(p.take(k)) <= self.cost(p),
    {
        admit();  // TODO(student): replace with a proof
        // * need assertions for take 
    }
}

/// Dijkstra's state: the settled set `S`, and for every node the best path found
/// so far from `src` (`None` = not yet reached). The tentative distance of a node
/// is the cost of its best path.
pub ghost struct DijkstraState {
    pub settled: Set<nat>,
    pub best: spec_fn(nat) -> Option<Seq<nat>>,
}

/// Dijkstra's algorithm as a specification, kept apart from the graph so that
/// all of its machinery (helper specs, invariant, lemmas) lives here.
pub ghost struct DijkstrasSpec<'a> {
    pub graph: &'a GraphSpec,
}

impl DijkstrasSpec<'_> {
    // TODO(student): add the invariant, helper specs, and supporting lemmas here.

    /// The crossing-edge lemma: a path from inside `S` to outside `S` has a
    /// first vertex `y` outside `S`; its prefix to `y` only has `S` before the end.
    pub proof fn lemma_first_exit(self, p: Seq<nat>, inside: spec_fn(nat) -> bool)
        requires
            self.graph.is_path(p),
            inside(p.first()),
            !inside(p.last()),
        ensures
            exists|k: int|
                1 <= k < p.len() && !inside(p[k]) && forall|j: int| 0 <= j < k ==> inside(p[j]),
    {
        admit();  // TODO(student): replace with a proof
    }

    /// Tentative distance of `v` in `st`: the cost of its best path.
    /// TODO(student) Meaningful only when `v` has a best path. 
    pub uninterp spec fn cost_of(self, st: DijkstraState, v: nat) -> nat;

    /// TODO(student) `v` is in range, unsettled, and has a best path. 
    pub uninterp spec fn is_candidate(self, st: DijkstraState, v: nat) -> bool;

    /// The next node to settle: `Some(u)` where `u` is a candidate whose
    /// tentative distance is at most that of every other candidate, or `None`
    /// TODO(student) when there is no candidate. 
    pub uninterp spec fn pick(self, st: DijkstraState) -> Option<nat>;

    /// Initial state: nothing settled; only `src` has a path, `[src]`.
    /// TODO(student)
    pub uninterp spec fn init(self, src: nat) -> DijkstraState;

    /// One round: settle `u` (the node chosen by `pick`) and relax its
    /// out-edges.
    /// TODO(student)
    pub uninterp spec fn settle(self, st: DijkstraState, u: nat) -> DijkstraState;

    /// Repeat `settle(st, pick(st))` until `dst` is settled or `pick` returns `None`.
    /// TODO(student): define it, including its `decreases` measure.
    pub uninterp spec fn run(self, dst: nat, st: DijkstraState) -> DijkstraState;

    /// Cost and path found by Dijkstra's algorithm; `None` when a node is out of
    /// range or `dst` is unreachable.
    pub open spec fn shortest_path(self, src: nat, dst: nat) -> Option<(nat, Seq<nat>)> {
        if src < self.graph.n && dst < self.graph.n {
            let f = self.run(dst, self.init(src)); // * run needs a terminations arg, via func arg
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
        // * talking about on Monday (Nov 2)
        admit();  // TODO(student): replace with a proof
    }
}

} // verus!
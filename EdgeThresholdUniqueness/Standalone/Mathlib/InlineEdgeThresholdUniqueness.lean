/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card

/-!
# Uniqueness of `K_{d+2}` at `C(d+2, 2)` edges

For every natural number `d ≥ 6`, a finite simple graph with exactly `C(d+2, 2)` edges, with no
isolated vertex, and with no unit-distance representation in Euclidean `d`-space is isomorphic to
the complete graph `K_{d+2}`.

A unit-distance representation is an injective placement of the vertices into
`EuclideanSpace ℝ (Fin d)` under which every edge has length `1`. A non-edge may also have
length `1`. This is the Erdős–Harary–Tutte notion of realizability in `ℝᵈ`: the edge set
is a
subset of the unit-distance pairs, not necessarily the whole set of them.

`Challenge.lean` is generated from this file, up to the proof-link note, with
`scripts/palomar-challenge-footer.txt`.
-/

@[expose] public section

namespace EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness

open SimpleGraph

/-- `G` has a unit-distance representation in Euclidean `d`-space.

`d` is universally available as any natural number, including the degenerate value `0`.
`EuclideanSpace ℝ (Fin 0)` is a single point, so the only distance there is `0`. Thus no graph
with an edge is representable in dimension `0`, and a graph with no edges is representable in
dimension `0` exactly when its vertex set has at most one element: the empty vertex set and the
one-vertex graph are representable, and two or more isolated vertices are not, because the map
has to be injective.

In every dimension, the empty graph is representable: the empty map is injective and there is no
edge to constrain. A graph with no edge does not separate this definition from one that also
accepts every edgeless graph.

The implication runs only from adjacency to distance `1`. The converse is not required, and two
nonadjacent vertices may land at distance `1`. Injectivity is separate from the distance
condition: without it, nonadjacent vertices could be sent to the same point. -/
def UnitDistanceRepresentable {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin d),
    Function.Injective f ∧ ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

/-- Separating example for `UnitDistanceRepresentable`.

The nearest stricter reading demands that non-edges have length different from `1`. The first
witness is a graph with an edge, placed in `ℝ¹` by sending that edge to `0` and `1` and a third
vertex to `2`. The third vertex is not adjacent to the vertex at `1`, and those two points are at
distance `1`, so this placement satisfies the definition and fails the stricter reading. The same
graph may admit another placement whose non-edges all have length different from `1`; the
definition does not forbid that.

The nearest looser reading drops injectivity. The second witness is the star `K_{1,3}`: the
center at `0` and the three leaves at `1` send every edge to a segment of length `1`, and the map
is not injective. No injective placement in `ℝ¹` exists, because the three leaves would have to
occupy the two points at distance `1` from the center. Both graphs have an edge, so neither
witness is the empty graph. -/
def UnitDistanceRepresentable.separating : Prop :=
  (∃ G : SimpleGraph (Fin 3),
    (∀ u v : Fin 3, G.Adj u v ↔ (u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 0)) ∧
    G.Adj 0 1 ∧
    ∃ f : Fin 3 → EuclideanSpace ℝ (Fin 1),
      f = ![!₂[(0 : ℝ)], !₂[(1 : ℝ)], !₂[(2 : ℝ)]] ∧
      Function.Injective f ∧
      (∀ u v : Fin 3, G.Adj u v → dist (f u) (f v) = 1) ∧
      (1 : Fin 3) ≠ 2 ∧ ¬ G.Adj 1 2 ∧ dist (f 1) (f 2) = 1 ∧
      UnitDistanceRepresentable G 1) ∧
  (∃ G : SimpleGraph (Fin 4),
    (∀ u v : Fin 4, G.Adj u v ↔ ((u = 0 ∨ v = 0) ∧ u ≠ v)) ∧
    G.Adj 0 1 ∧
    ∃ f : Fin 4 → EuclideanSpace ℝ (Fin 1),
      f 0 = !₂[(0 : ℝ)] ∧ f 1 = !₂[(1 : ℝ)] ∧
      f 2 = !₂[(1 : ℝ)] ∧ f 3 = !₂[(1 : ℝ)] ∧
      ¬ Function.Injective f ∧
      (∀ u v : Fin 4, G.Adj u v → dist (f u) (f v) = 1) ∧
      ¬ UnitDistanceRepresentable G 1)

/-- Uniqueness of `K_{d+2}` among graphs with `C(d+2, 2)` edges and no unit-distance
representation in `ℝᵈ`, for every `d ≥ 6`.

Quantifiers, in order. `d`, `n`, and `G` are universal. There is no existential quantifier in
the conclusion. `_hdeg` contains one existential quantifier, the neighbor of a vertex. `_hrep` is
the negation of an existential quantifier, the unit-distance representation.

* `d : ℕ` ranges over dimensions. The source states every integer `d ≥ 6`. Typing `d` as an
  integer `≥ 6` or as a natural number `≥ 6` gives the same range: every such integer is the
  cast of one natural number, and the dimension enters as the index of
  `EuclideanSpace ℝ (Fin d)`. The statement uses `ℕ`.
* `_hd : 6 ≤ d` is a closed lower bound. It holds at `d = 6` and fails for every `d < 6`. For
  `d < 6` the implication does not claim uniqueness.
* `n : ℕ` and `G : SimpleGraph (Fin n)` range over finite simple graphs, including `n = 0`.
  An arbitrary finite vertex type yields an equivalent statement: edge count, absence of
  isolated vertices, unit-distance representability, and isomorphism with `K_{d+2}` are
  invariant under relabeling, and every finite type is in bijection with `Fin` of its
  cardinality. `SimpleGraph` supplies an irreflexive symmetric relation, so there are no loops
  and no multiple edges, and `G.edgeSet.ncard` counts each undirected edge once. The count does
  not assume decidability of adjacency.
* `_hcard` is equality with `(d + 2).choose 2`, not `≤` and not `≥`. One edge more, or one edge
  fewer, lies outside the hypothesis.
* `_hdeg` says that no vertex is isolated: every vertex has a neighbor. Adjacency is
  irreflexive, so the neighbor is distinct from the vertex. On `n = 0` the vertex set is empty,
  so `_hdeg` is vacuously true and the edge set is empty. For `d ≥ 6` one has
  `(d + 2).choose 2 ≥ (8).choose 2 = 28 > 0`, so `_hcard` fails and the implication does not
  identify the empty graph with `K_{d+2}`. On `n = 1` the only vertex is isolated, so `_hdeg`
  fails. On `n ≥ 1` with an empty edge set, `_hdeg` likewise fails.
* `_hrep` says there is no unit-distance representation in `ℝᵈ`. It does not say that the
  dimension is exactly `d + 1`, and it does not require a representation in `ℝᵈ⁺¹`.
* The conclusion is graph isomorphism with `completeGraph (Fin (d + 2))`, that is `K_{d+2}`.

At the boundary `d = 6` the edge count is `28`, the space is Euclidean `6`-space, and the
conclusion is isomorphism with `K₈`. -/
def UniqueKComplete : Prop :=
  ∀ (d : ℕ) (_hd : 6 ≤ d) (n : ℕ) (G : SimpleGraph (Fin n))
    (_hcard : G.edgeSet.ncard = (d + 2).choose 2)
    (_hdeg : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w)
    (_hrep : ¬ UnitDistanceRepresentable G d),
    Nonempty (G ≃g completeGraph (Fin (d + 2)))

/-- Satisfiability witness for `UniqueKComplete`.

At the boundary `d = 6`, the complete graph `K₈` has `(6 + 2).choose 2 = 28` edges, every vertex
has a neighbor, and `K₈` has no unit-distance representation in Euclidean `6`-space. The four
hypotheses of `UniqueKComplete` therefore hold together of a graph with edges. The empty graph
has `0` edges, so it does not satisfy the edge-count hypothesis. -/
def UniqueKComplete.witness : Prop :=
  UniqueKComplete ∧
    (6 : ℕ) ≤ 6 ∧
    (completeGraph (Fin (6 + 2))).edgeSet.ncard = (6 + 2).choose 2 ∧
    (∀ v : Fin (6 + 2), ∃ w : Fin (6 + 2), (completeGraph (Fin (6 + 2))).Adj v w) ∧
    ¬ UnitDistanceRepresentable (completeGraph (Fin (6 + 2))) 6

/-- Dropping `d ≥ 6` is false. At `d = 1`, the star `K_{1,3}` has `3 = (1 + 2).choose 2` edges
and no isolated vertex. It has no injective unit-distance representation in `ℝ¹`: the three
leaves would have to occupy the two points at distance `1` from the center. It is not
isomorphic to `K₃`. -/
def UniqueKComplete.dropHd : Prop :=
  ¬ ∀ (d : ℕ) (n : ℕ) (G : SimpleGraph (Fin n))
      (_hcard : G.edgeSet.ncard = (d + 2).choose 2)
      (_hdeg : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w)
      (_hrep : ¬ UnitDistanceRepresentable G d),
      Nonempty (G ≃g completeGraph (Fin (d + 2)))

/-- Dropping the exact edge count is false. At `d = 6`, `K₉` contains `K₈`, so it has no
unit-distance representation in `ℝ⁶`. It has no isolated vertex, it is not isomorphic to `K₈`,
and it has `36` edges rather than `28`. -/
def UniqueKComplete.dropHcard : Prop :=
  ¬ ∀ (d : ℕ) (_hd : 6 ≤ d) (n : ℕ) (G : SimpleGraph (Fin n))
      (_hdeg : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w)
      (_hrep : ¬ UnitDistanceRepresentable G d),
      Nonempty (G ≃g completeGraph (Fin (d + 2)))

/-- Dropping the ban on isolated vertices is false. At `d = 6`, the disjoint union of `K₈` with
one isolated vertex still has `28` edges and still has no unit-distance representation in `ℝ⁶`,
because its `K₈` subgraph has none, but the union is not isomorphic to `K₈`. -/
def UniqueKComplete.dropHdeg : Prop :=
  ¬ ∀ (d : ℕ) (_hd : 6 ≤ d) (n : ℕ) (G : SimpleGraph (Fin n))
      (_hcard : G.edgeSet.ncard = (d + 2).choose 2)
      (_hrep : ¬ UnitDistanceRepresentable G d),
      Nonempty (G ≃g completeGraph (Fin (d + 2)))

/-- Dropping non-representability in `ℝᵈ` is false. At `d = 6`, the path of `28` edges has
`29` vertices, hence exactly `(6 + 2).choose 2` edges and no isolated vertex, and it is not
isomorphic to `K₈`. -/
def UniqueKComplete.dropHrep : Prop :=
  ¬ ∀ (d : ℕ) (_hd : 6 ≤ d) (n : ℕ) (G : SimpleGraph (Fin n))
      (_hcard : G.edgeSet.ncard = (d + 2).choose 2)
      (_hdeg : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w),
      Nonempty (G ≃g completeGraph (Fin (d + 2)))

end EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness

/-!
## Formal proof

Proved in `InlineEdgeThresholdUniquenessProof`.

* `separating` → `separating.proof`
* `UniqueKComplete` → `UniqueKComplete.proof`
* `witness` → `witness.proof`
* `dropHd` → `dropHd.proof`
* `dropHcard` → `dropHcard.proof`
* `dropHdeg` → `dropHdeg.proof`
* `dropHrep` → `dropHrep.proof`
-/

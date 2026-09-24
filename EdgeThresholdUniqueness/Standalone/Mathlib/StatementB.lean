module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card

/-!
# Uniqueness at the Euclidean unit-distance edge threshold

Rung 4 of ADR 0004, with the owner's quantifiers of 2026-09-23: for every `d ≥ 6`,
the only finite simple graph without isolated vertices having exactly `C(d + 2, 2)`
edges and no unit-distance representation in `ℝᵈ` is `K_{d+2}`, up to isomorphism.

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, JCTA 171
(2020), 105146, Theorem 3, establishes the edge threshold for `d > 3`.
The uniqueness assertion here is the additional rung-4 claim, not that theorem.
-/

@[expose] public section

namespace EdgeThresholdUniqueness.StatementB

/-- A unit-distance representation is an injective map `p : V → EuclideanSpace ℝ (Fin d)`
such that `G.Adj u v → dist (p u) (p v) = 1` for every pair of vertices.
Non-edges are unconstrained and may also have distance one. Mathlib's `UnitDistEmbedding`
bundles exactly this map, its injectivity, and the edge-length condition.
In dimension zero the Euclidean space is a singleton, so only graphs with at most one
vertex admit a representation. The empty graph on the empty vertex type admits one in
every dimension; an edgeless graph with several vertices still requires an injection. -/
def HasUnitDistanceRepresentation {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (G.UnitDistEmbedding (EuclideanSpace ℝ (Fin d)))

/-- The two-edge path `K_{1,2}` has an injective representation on the line. It also has
a plane representation as three vertices of an equilateral triangle, so its two nonadjacent
leaves may be a unit distance apart. In contrast, the three-edge star `K_{1,3}` has no
injective representation on the line, although collapsing its leaves gives a map preserving
every edge length. These nonempty examples separate both conventions from the stated one. -/
def HasUnitDistanceRepresentation.separating : Prop :=
  HasUnitDistanceRepresentation (completeBipartiteGraph (Fin 1) (Fin 2)) 1 ∧
    (∃ p : (Fin 1 ⊕ Fin 2) → EuclideanSpace ℝ (Fin 2),
      Function.Injective p ∧
      (∀ u v, (completeBipartiteGraph (Fin 1) (Fin 2)).Adj u v → dist (p u) (p v) = 1) ∧
      ∃ u v, u ≠ v ∧ ¬ (completeBipartiteGraph (Fin 1) (Fin 2)).Adj u v ∧
        dist (p u) (p v) = 1) ∧
    ¬ HasUnitDistanceRepresentation (completeBipartiteGraph (Fin 1) (Fin 3)) 1 ∧
    (∃ p : (Fin 1 ⊕ Fin 3) → EuclideanSpace ℝ (Fin 1),
      ¬ Function.Injective p ∧
      ∀ u v, (completeBipartiteGraph (Fin 1) (Fin 3)).Adj u v → dist (p u) (p v) = 1)

/-- For every natural dimension `d`, every vertex count `n`, and every simple graph `G`
on `Fin n`, if `6 ≤ d`, the number of unordered edges is exactly `(d + 2).choose 2`,
every vertex has a neighbor, and no injective unit-distance representation in `ℝᵈ` exists,
then there exists a graph isomorphism from `G` to the complete graph on `Fin (d + 2)`.
These are universal quantifiers in the displayed order; `Nonempty` existentially asserts
the isomorphism. Quantifying over `Fin n` covers every finite graph up to relabelling.

The lower bound includes `d = 6`, where the edge count is 28 and the conclusion is `K₈`.
For `d < 6`, including `d = 0`, the implication has a false dimension hypothesis.
For `n = 0` the no-isolated-vertex condition is vacuous, but the edge count is zero and
the empty placement exists, so the hypotheses cannot all hold. For `n = 1` the vertex
is isolated and there are no edges. At any allowed dimension an edgeless graph fails
the positive edge-count hypothesis. The count is equality, not an upper or lower bound.
No connectedness or assertion that the graph's dimension equals `d + 1` is assumed. -/
def edgeThresholdUniqueness : Prop :=
  ∀ (d n : ℕ) (G : SimpleGraph (Fin n))
    (_hdim : 6 ≤ d)
    (_hedges : G.edgeSet.ncard = (d + 2).choose 2)
    (_hneighbors : ∀ v, ∃ w, G.Adj v w)
    (_hnonrealizable : ¬ HasUnitDistanceRepresentation G d),
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin (d + 2)))

/-- The instance `d = 6`, `n = 8`, `G = K₈` satisfies every hypothesis of
`edgeThresholdUniqueness`: 28 edges, no isolated vertex, and no placement in `ℝ⁶`. -/
def edgeThresholdUniqueness.witness : Prop :=
  let G : SimpleGraph (Fin 8) := SimpleGraph.completeGraph (Fin 8)
  6 ≤ (6 : ℕ) ∧
    G.edgeSet.ncard = (6 + 2).choose 2 ∧
    (∀ v, ∃ w, G.Adj v w) ∧
    ¬ HasUnitDistanceRepresentation G 6

/-- The star `K_{1,28}`, labelled on 29 vertices with center zero, has 28 edges and
no isolated vertices, and admits a representation in `ℝ⁶`, but is not `K₈`.
It separates the stated claim from the assertion that the edge count alone forces
the complete graph, even when isolated vertices are excluded. -/
def edgeThresholdUniqueness.separating : Prop :=
  ∃ G : SimpleGraph (Fin 29),
    (∀ u v, G.Adj u v ↔ u ≠ v ∧ (u = 0 ∨ v = 0)) ∧
    G.edgeSet.ncard = (6 + 2).choose 2 ∧
    (∀ v, ∃ w, G.Adj v w) ∧
    HasUnitDistanceRepresentation G 6 ∧
    ¬ Nonempty (G ≃g SimpleGraph.completeGraph (Fin 8))

/-- Without the dimension restriction, the three-edge star `K_{1,3}` at `d = 1`
has no representation on the line and is not `K₃`. -/
def edgeThresholdUniqueness.dropHdim : Prop :=
  ¬ (∀ (d n : ℕ) (G : SimpleGraph (Fin n))
    (_hedges : G.edgeSet.ncard = (d + 2).choose 2)
    (_hneighbors : ∀ v, ∃ w, G.Adj v w)
    (_hnonrealizable : ¬ HasUnitDistanceRepresentation G d),
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin (d + 2))))

/-- Without the edge-count restriction, `K₉` at `d = 6` has no representation in
`ℝ⁶` and no isolated vertices, but is not `K₈`. -/
def edgeThresholdUniqueness.dropHedges : Prop :=
  ¬ (∀ (d n : ℕ) (G : SimpleGraph (Fin n))
    (_hdim : 6 ≤ d)
    (_hneighbors : ∀ v, ∃ w, G.Adj v w)
    (_hnonrealizable : ¬ HasUnitDistanceRepresentation G d),
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin (d + 2))))

/-- Without the neighbor condition, `K₈` together with one isolated vertex at
`d = 6` has 28 edges and no representation in `ℝ⁶`, but is not `K₈`. -/
def edgeThresholdUniqueness.dropHneighbors : Prop :=
  ¬ (∀ (d n : ℕ) (G : SimpleGraph (Fin n))
    (_hdim : 6 ≤ d)
    (_hedges : G.edgeSet.ncard = (d + 2).choose 2)
    (_hnonrealizable : ¬ HasUnitDistanceRepresentation G d),
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin (d + 2))))

/-- Without the absence of a representation, the star `K_{1,28}` at `d = 6`
has 28 edges and no isolated vertices, but is not `K₈`. -/
def edgeThresholdUniqueness.dropHnonrealizable : Prop :=
  ¬ (∀ (d n : ℕ) (G : SimpleGraph (Fin n))
    (_hdim : 6 ≤ d)
    (_hedges : G.edgeSet.ncard = (d + 2).choose 2)
    (_hneighbors : ∀ v, ∃ w, G.Adj v w),
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin (d + 2))))

end EdgeThresholdUniqueness.StatementB

/-!
## Formal proof

Proved in `StatementBProof`.

* `separating` → `separating.proof`
* `edgeThresholdUniqueness` → `edgeThresholdUniqueness.proof`
* `witness` → `witness.proof`
* `dropHdim` → `dropHdim.proof`
* `dropHedges` → `dropHedges.proof`
* `dropHneighbors` → `dropHneighbors.proof`
* `dropHnonrealizable` → `dropHnonrealizable.proof`
-/

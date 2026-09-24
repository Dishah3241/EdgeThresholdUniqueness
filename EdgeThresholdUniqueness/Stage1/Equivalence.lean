/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness
public import EdgeThresholdUniqueness.Standalone.Mathlib.StatementA
public import EdgeThresholdUniqueness.Standalone.Mathlib.StatementB
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card

/-!
# Equivalence of the two rung-4 statements

Statement A (`StatementA.UniqueKComplete`) and Statement B
(`StatementB.edgeThresholdUniqueness`) are the two independent encodings of rung 4. The bridge
has two steps: unbundle Mathlib's `UnitDistEmbedding` to identify the two readings of
*unit-distance representation*, then reorder the hypothesis `6 ≤ d`. Both steps are equalities
of reading, so the two statements are interchangeable.
-/

@[expose] public section

namespace EdgeThresholdUniqueness

open SimpleGraph

/-- The two readings of *unit-distance representation* agree on the Mathlib side: an injective
placement of `V` in `EuclideanSpace ℝ (Fin d)` under which every edge has length `1` exists
exactly when Mathlib's bundled `UnitDistEmbedding` of `G` is inhabited. The placement function,
its injectivity, and the edge-distance condition are the same data, only packed differently. -/
theorem unitDistanceRepresentable_iff_nonempty_unitDistEmbedding {V : Type*}
    (G : SimpleGraph V) (d : ℕ) :
    StatementA.UnitDistanceRepresentable G d ↔
      Nonempty (G.UnitDistEmbedding (EuclideanSpace ℝ (Fin d))) := by
  constructor
  · rintro ⟨f, hfInj, hfDist⟩
    exact ⟨⟨⟨f, hfInj⟩, fun {u v} huv => hfDist u v huv⟩⟩
  · rintro ⟨U⟩
    exact ⟨U.p, U.p.injective, fun _ _ huv => U.unit_dist huv⟩

/-- Statement A's predicate implies Statement B's: the unbundled placement is the bundled one. -/
theorem hasUnitDistanceRepresentation_of_unitDistanceRepresentable {V : Type*}
    (G : SimpleGraph V) (d : ℕ) (h : StatementA.UnitDistanceRepresentable G d) :
    StatementB.HasUnitDistanceRepresentation G d :=
  (unitDistanceRepresentable_iff_nonempty_unitDistEmbedding G d).mp h

/-- Statement B's predicate implies Statement A's: the bundled placement unbundles. -/
theorem unitDistanceRepresentable_of_hasUnitDistanceRepresentation {V : Type*}
    (G : SimpleGraph V) (d : ℕ) (h : StatementB.HasUnitDistanceRepresentation G d) :
    StatementA.UnitDistanceRepresentable G d :=
  (unitDistanceRepresentable_iff_nonempty_unitDistEmbedding G d).mpr h

/-- Statement B implies Statement A. The only differences are the position of `6 ≤ d` among the
hypotheses and which of the two intertranslatable predicates the non-representability hypothesis
negates. -/
theorem uniqueKComplete_of_edgeThresholdUniqueness
    (h : StatementB.edgeThresholdUniqueness) : StatementA.UniqueKComplete := by
  intro d _hd n G _hcard _hdeg _hrep
  exact h d n G _hd _hcard _hdeg fun hb =>
    _hrep (unitDistanceRepresentable_of_hasUnitDistanceRepresentation G d hb)

/-- Statement A implies Statement B. The only differences are the position of `6 ≤ d` among the
hypotheses and which of the two intertranslatable predicates the non-representability hypothesis
negates. -/
theorem edgeThresholdUniqueness_of_uniqueKComplete
    (h : StatementA.UniqueKComplete) : StatementB.edgeThresholdUniqueness := by
  intro d n G _hdim _hedges _hneighbors _hnonrealizable
  exact h d _hdim n G _hedges _hneighbors fun ha =>
    _hnonrealizable (hasUnitDistanceRepresentation_of_unitDistanceRepresentable G d ha)

/-- The target equivalence: the two rung-4 statements are the same claim. -/
theorem uniqueKComplete_iff_edgeThresholdUniqueness :
    StatementA.UniqueKComplete ↔ StatementB.edgeThresholdUniqueness :=
  ⟨edgeThresholdUniqueness_of_uniqueKComplete, uniqueKComplete_of_edgeThresholdUniqueness⟩

/-- The inline statement has the same body as `StatementA.UniqueKComplete`. -/
theorem inlineIffStatementA :
    Standalone.Mathlib.InlineEdgeThresholdUniqueness.UniqueKComplete ↔
      StatementA.UniqueKComplete :=
  Iff.rfl

end EdgeThresholdUniqueness

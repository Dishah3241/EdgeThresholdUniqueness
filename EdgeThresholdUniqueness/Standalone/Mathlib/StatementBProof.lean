/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import EdgeThresholdUniqueness.Standalone.Mathlib.StatementB

import EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniquenessProof

/-!
# Proofs of statement B

Statement B packages a unit-distance representation as Mathlib's `UnitDistEmbedding`. The inline
statement uses the unbundled predicate, and the two agree.
-/

public section

namespace EdgeThresholdUniqueness.StatementB

open SimpleGraph
open EdgeThresholdUniqueness.Bridge
open EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness

private lemma hasRep_iff {V : Type*} (G : SimpleGraph V) (d : ℕ) :
    HasUnitDistanceRepresentation G d ↔ UnitDistanceRepresentable G d := by
  rw [unitDistanceRepresentable_iff]
  constructor
  · rintro ⟨U⟩
    exact ⟨U.p, U.p.injective, fun u v huv => U.unit_dist huv⟩
  · rintro ⟨f, hf, hdist⟩
    exact ⟨⟨⟨f, hf⟩, fun {_u _v} huv => hdist _ _ huv⟩⟩

theorem HasUnitDistanceRepresentation.separating.proof :
    HasUnitDistanceRepresentation.separating := by
  refine ⟨?_, bipartite12_equilateral, ?_, bipartite13_collapsed⟩
  · exact (hasRep_iff _ _).mpr bipartite12_unitDist
  · intro h
    exact not_bipartite13_unitDist ((hasRep_iff _ _).mp h)

theorem edgeThresholdUniqueness.proof : edgeThresholdUniqueness := by
  intro d n G hd hcard hdeg hnon
  exact UniqueKComplete.proof d hd n G hcard hdeg (by
    intro hrep
    exact hnon ((hasRep_iff G d).mpr hrep))

theorem edgeThresholdUniqueness.witness.proof : edgeThresholdUniqueness.witness := by
  unfold edgeThresholdUniqueness.witness
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [ncard_edgeSet_completeGraph]
  · intro v
    exact completeGraph_exists_adj (by decide) v
  · intro h
    exact not_unitDistEmbeddable_complete_of_lt (by decide) ((hasRep_iff _ _).mp h)

theorem edgeThresholdUniqueness.separating.proof : edgeThresholdUniqueness.separating := by
  refine ⟨star28, star28_adj_iff, ncard_star28, star28_exists_adj, ?_, ?_⟩
  · exact (hasRep_iff _ _).mpr star28_unitDist
  · exact not_iso_complete (by decide) star28

theorem edgeThresholdUniqueness.dropHdim.proof : edgeThresholdUniqueness.dropHdim := by
  intro hyp
  exact not_iso_complete (by decide : 4 ≠ 1 + 2) star3
    (hyp 1 4 star3 ncard_star3 star3_exists_adj (by
      intro h
      exact not_star3_unitDist ((hasRep_iff star3 1).mp h)))

theorem edgeThresholdUniqueness.dropHedges.proof : edgeThresholdUniqueness.dropHedges := by
  intro hyp
  exact not_iso_complete (by decide : 9 ≠ 6 + 2) (completeGraph (Fin 9))
    (hyp 6 9 (completeGraph (Fin 9)) (by decide)
      (fun v => completeGraph_exists_adj (by decide) v) (by
        intro h
        exact not_unitDistEmbeddable_complete_of_lt (by decide : 6 + 1 < 9)
          ((hasRep_iff _ _).mp h)))

theorem edgeThresholdUniqueness.dropHneighbors.proof :
    edgeThresholdUniqueness.dropHneighbors := by
  intro hyp
  exact not_iso_complete (by decide : 9 ≠ 6 + 2) k8Plus
    (hyp 6 9 k8Plus (by decide) ncard_k8Plus (by
      intro h
      exact not_k8Plus_unitDist ((hasRep_iff k8Plus 6).mp h)))

theorem edgeThresholdUniqueness.dropHnonrealizable.proof :
    edgeThresholdUniqueness.dropHnonrealizable := by
  intro hyp
  exact not_iso_complete (by decide : 29 ≠ 6 + 2) star28
    (hyp 6 29 star28 (by decide) ncard_star28 star28_exists_adj)

end EdgeThresholdUniqueness.StatementB

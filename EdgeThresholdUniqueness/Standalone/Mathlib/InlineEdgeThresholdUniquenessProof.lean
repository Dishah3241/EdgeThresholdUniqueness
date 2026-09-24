/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness
public import GraphDimension.Basic

import GraphDimension.Extremal.FKS.Uniqueness
import GraphDimension.Geometry.CompleteGraph
import GraphDimension.Geometry.UnitDistanceComap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proof of uniqueness at `C(d + 2, 2)` edges

`UnitDistanceRepresentable` matches `SimpleGraph.UnitDistEmbeddable`. For `d ≥ 6`, a finite simple
graph with `C(d + 2, 2)` edges, no isolated vertex, and no unit-distance placement in `ℝ^d` is
`K_{d+2}`, by `SimpleGraph.nonempty_iso_completeGraph_of_not_unitDistEmbeddable`.
-/

public section

namespace EdgeThresholdUniqueness.Bridge

open SimpleGraph

/-- `UnitDistanceRepresentable` and `SimpleGraph.UnitDistEmbeddable` have the same body. -/
theorem unitDistanceRepresentable_iff {V : Type*} (G : SimpleGraph V) (d : ℕ) :
    Standalone.Mathlib.InlineEdgeThresholdUniqueness.UnitDistanceRepresentable G d ↔
      G.UnitDistEmbeddable d :=
  Iff.rfl

/-- The complete graph on `n` vertices has `n` choose `2` edges. -/
theorem ncard_edgeSet_completeGraph (n : ℕ) :
    (completeGraph (Fin n)).edgeSet.ncard = Nat.choose n 2 := by
  rw [completeGraph_eq_top]
  have hfin : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard =
      Finset.card (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    rw [edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [hfin, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/-- `K_n` has no injective unit-distance placement in `ℝ^d` when `d + 1 < n`. -/
theorem not_unitDistEmbeddable_complete_of_lt {n d : ℕ} (h : d + 1 < n) :
    ¬ (completeGraph (Fin n)).UnitDistEmbeddable d := by
  intro hem
  rw [completeGraph_eq_top] at hem
  have hdim := hasUnitDistDim_completeGraph n
  have hAnd :
      n - 1 ∈ {m | (⊤ : SimpleGraph (Fin n)).UnitDistEmbeddable m} ∧
        n - 1 ∈ lowerBounds {m | (⊤ : SimpleGraph (Fin n)).UnitDistEmbeddable m} := by
    simpa [HasUnitDistDim, IsLeast] using hdim
  rw [mem_lowerBounds] at hAnd
  have hle : n - 1 ≤ d := hAnd.2 d hem
  omega

/-- Every vertex of `K_n`, for `n ≥ 2`, has a neighbor. -/
theorem completeGraph_exists_adj {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    ∃ w, (completeGraph (Fin n)).Adj v w := by
  have : NeZero n := ⟨by omega⟩
  by_cases hv : v = 0
  · refine ⟨1, ?_⟩
    rw [completeGraph_eq_top, top_adj, hv]
    intro h
    have hval := congrArg (fun i : Fin n => (i : ℕ)) h
    rw [Fin.val_zero, Fin.val_one'] at hval
    have : (1 : ℕ) % n = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  · refine ⟨0, ?_⟩
    rw [completeGraph_eq_top, top_adj]
    exact hv

/-- Graphs on different numbers of vertices are not isomorphic to `K_m`. -/
theorem not_iso_complete {n m : ℕ} (hnm : n ≠ m) (G : SimpleGraph (Fin n)) :
    ¬ Nonempty (G ≃g completeGraph (Fin m)) := by
  rintro ⟨e⟩
  have hcard := e.card_eq
  simp only [Fintype.card_fin] at hcard
  exact hnm hcard

private lemma dist_fin1 (x y : EuclideanSpace ℝ (Fin 1)) : dist x y = |x 0 - y 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]

private lemma eq_of_coord_fin1 (x y : EuclideanSpace ℝ (Fin 1)) (h : x 0 = y 0) : x = y := by
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  exact h

private lemma line_coord (r : ℝ) : (!₂[r] : EuclideanSpace ℝ (Fin 1)) 0 = r := by
  simp

/-- Three points at distance `1` from one point on the line cannot be distinct. -/
private theorem noThreeOnLine {V : Type*} (f : V → EuclideanSpace ℝ (Fin 1))
    (hf : Function.Injective f) {c : V} {g : Fin 3 → V} (hg : Function.Injective g)
    (hdist : ∀ i, dist (f c) (f (g i)) = 1) : False := by
  let center : ℝ := f c 0
  let coord : Fin 3 → ℝ := fun i => f (g i) 0
  have hcoord (i : Fin 3) : |coord i - center| = 1 := by
    have hdi := hdist i
    rw [dist_fin1, abs_sub_comm] at hdi
    simpa [center, coord] using hdi
  have hslot (i : Fin 3) : coord i = center + 1 ∨ coord i = center - 1 := by
    rcases eq_or_eq_neg_of_abs_eq (hcoord i) with hEq | hEq
    · left
      linarith
    · right
      linarith
  have hne (i j : Fin 3) (hij : i ≠ j) : coord i ≠ coord j := by
    intro hge
    exact hf.ne (hg.ne hij) (eq_of_coord_fin1 _ _ (by simpa [coord] using hge))
  have both_pos (i j : Fin 3) (hi : coord i = center + 1) (hj : coord j = center + 1) :
      i = j := by
    by_contra hij
    exact hne i j hij (hi.trans hj.symm)
  have both_neg (i j : Fin 3) (hi : coord i = center - 1) (hj : coord j = center - 1) :
      i = j := by
    by_contra hij
    exact hne i j hij (hi.trans hj.symm)
  rcases hslot 0 with h0 | h0 <;> rcases hslot 1 with h1 | h1 <;> rcases hslot 2 with h2 | h2
  · exact absurd (both_pos 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)
  · exact absurd (both_pos 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)
  · exact absurd (both_pos 0 2 h0 h2) (by decide : (0 : Fin 3) ≠ 2)
  · exact absurd (both_neg 1 2 h1 h2) (by decide : (1 : Fin 3) ≠ 2)
  · exact absurd (both_pos 1 2 h1 h2) (by decide : (1 : Fin 3) ≠ 2)
  · exact absurd (both_neg 0 2 h0 h2) (by decide : (0 : Fin 3) ≠ 2)
  · exact absurd (both_neg 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)
  · exact absurd (both_neg 0 1 h0 h1) (by decide : (0 : Fin 3) ≠ 1)

/-- The star `K_{1,3}` on `Fin 4`, with center `0`. -/
def star3 : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∨ v = 0) ∧ u ≠ v

/-- Adjacency in `star3` is the star relation with center `0`. -/
theorem star3_adj_iff (u v : Fin 4) :
    star3.Adj u v ↔ (u = 0 ∨ v = 0) ∧ u ≠ v :=
  Iff.rfl

private instance : DecidableRel star3.Adj := fun u v =>
  decidable_of_iff ((u = 0 ∨ v = 0) ∧ u ≠ v) (star3_adj_iff u v)

/-- `K_{1,3}` has `(1 + 2)` choose `2` edges. -/
theorem ncard_star3 : star3.edgeSet.ncard = (1 + 2).choose 2 := by
  have h : star3.edgeSet.ncard = 3 := by
    have hc : Finset.card star3.edgeFinset = 3 := by decide
    rwa [edgeFinset_card, Set.fintypeCard_eq_ncard] at hc
  rw [h]
  decide

/-- Every vertex of `K_{1,3}` has a neighbor. -/
theorem star3_exists_adj (v : Fin 4) : ∃ w, star3.Adj v w := by
  fin_cases v
  · exact ⟨1, (star3_adj_iff 0 1).2 ⟨Or.inl rfl, by decide⟩⟩
  · exact ⟨0, (star3_adj_iff 1 0).2 ⟨Or.inr rfl, by decide⟩⟩
  · exact ⟨0, (star3_adj_iff 2 0).2 ⟨Or.inr rfl, by decide⟩⟩
  · exact ⟨0, (star3_adj_iff 3 0).2 ⟨Or.inr rfl, by decide⟩⟩

/-- `K_{1,3}` has no injective unit-distance placement on the line. -/
theorem not_star3_unitDist : ¬ star3.UnitDistEmbeddable 1 := by
  intro h
  obtain ⟨f, hf, hdist⟩ := h
  exact noThreeOnLine f hf (c := (0 : Fin 4)) (g := fun i : Fin 3 => i.succ)
    (Fin.succ_injective 3) (fun i => by
      apply hdist
      exact (star3_adj_iff 0 i.succ).2 ⟨Or.inl rfl, (Fin.succ_ne_zero i).symm⟩)

/-- `K₈` with one extra isolated vertex, on `Fin 9`. -/
def k8Plus : SimpleGraph (Fin 9) where
  Adj u v := u ≠ v ∧ u ≠ 8 ∧ v ≠ 8

/-- Adjacency in `k8Plus` is the complete relation on `{0,…,7}`. -/
theorem k8Plus_adj_iff (u v : Fin 9) :
    k8Plus.Adj u v ↔ u ≠ v ∧ u ≠ 8 ∧ v ≠ 8 :=
  Iff.rfl

private instance : DecidableRel k8Plus.Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ u ≠ 8 ∧ v ≠ 8) (k8Plus_adj_iff u v)

/-- `K₈` plus an isolated vertex has `(6 + 2)` choose `2` edges. -/
theorem ncard_k8Plus : k8Plus.edgeSet.ncard = (6 + 2).choose 2 := by
  have h : k8Plus.edgeSet.ncard = 28 := by
    have hc : Finset.card k8Plus.edgeFinset = 28 := by decide
    rwa [edgeFinset_card, Set.fintypeCard_eq_ncard] at hc
  rw [h]
  decide

private lemma castSucc_ne_eight (a : Fin 8) : Fin.castSucc a ≠ (8 : Fin 9) := by
  intro h
  have hv : (a : ℕ) = 8 := by
    have := congrArg Fin.val h
    simpa [Fin.val_castSucc] using this
  have : a.val < 8 := a.isLt
  omega

private def k8Hom : completeGraph (Fin 8) →g k8Plus where
  toFun := Fin.castSucc
  map_rel' {a b} hab := by
    rw [completeGraph_eq_top, top_adj] at hab
    refine ⟨?_, castSucc_ne_eight a, castSucc_ne_eight b⟩
    intro h
    exact hab (Fin.castSucc_injective 8 h)

/-- `K₈` plus an isolated vertex has no injective unit-distance placement in `ℝ⁶`. -/
theorem not_k8Plus_unitDist : ¬ k8Plus.UnitDistEmbeddable 6 := by
  intro h
  exact not_unitDistEmbeddable_complete_of_lt (by decide : 6 + 1 < 8)
    (UnitDistEmbeddable.comap k8Hom (Fin.castSucc_injective 8) h)

/-- The star `K_{1,28}` on `Fin 29`, with center `0`. -/
def star28 : SimpleGraph (Fin 29) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)

/-- Adjacency in `star28` is the star relation with center `0`. -/
theorem star28_adj_iff (u v : Fin 29) :
    star28.Adj u v ↔ u ≠ v ∧ (u = 0 ∨ v = 0) :=
  Iff.rfl

private instance : DecidableRel star28.Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ (u = 0 ∨ v = 0)) (star28_adj_iff u v)

private lemma star28_leaf_inj :
    Function.Injective (fun i : Fin 29 => s((0 : Fin 29), i)) := by
  intro a b h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨-, hab⟩ | ⟨hb, ha⟩
  · exact hab
  · exact ha.trans hb

/-- `K_{1,28}` has `(6 + 2)` choose `2` edges. -/
theorem ncard_star28 : star28.edgeSet.ncard = (6 + 2).choose 2 := by
  have hcard :
      ((Finset.univ.erase (0 : Fin 29)).image (fun i => s((0 : Fin 29), i))).card = 28 := by
    rw [Finset.card_image_of_injective _ star28_leaf_inj,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have he : star28.edgeFinset =
      (Finset.univ.erase (0 : Fin 29)).image (fun i => s((0 : Fin 29), i)) := by
    ext e
    simp only [mem_edgeFinset, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    induction e with
    | h u v =>
      rw [mem_edgeSet, star28_adj_iff]
      constructor
      · rintro ⟨hne, hu | hv⟩
        · subst hu
          exact ⟨v, fun hv0 => hne hv0.symm, rfl⟩
        · subst hv
          exact ⟨u, hne, Sym2.eq_swap⟩
      · rintro ⟨i, hi, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · subst hu
          subst hv
          exact ⟨hi.symm, Or.inl rfl⟩
        · subst hu
          subst hv
          exact ⟨hi, Or.inr rfl⟩
  rw [← he] at hcard
  have hn : star28.edgeSet.ncard = 28 := by
    rwa [edgeFinset_card, Set.fintypeCard_eq_ncard] at hcard
  rw [hn]
  decide

/-- Every vertex of `K_{1,28}` has a neighbor. -/
theorem star28_exists_adj (v : Fin 29) : ∃ w, star28.Adj v w := by
  by_cases hv : v = 0
  · subst hv
    exact ⟨1, (star28_adj_iff 0 1).2 ⟨by decide, Or.inl rfl⟩⟩
  · exact ⟨0, (star28_adj_iff v 0).2 ⟨hv, Or.inr rfl⟩⟩

private noncomputable def raw (k : Fin 28) : EuclideanSpace ℝ (Fin 6) :=
  EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (k.val : ℝ)

private lemma raw_at (k : Fin 28) :
    raw k 0 = 1 ∧ raw k 1 = (k.val : ℝ) ∧ raw k 2 = 0 ∧ raw k 3 = 0 ∧ raw k 4 = 0 ∧
      raw k 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [raw, PiLp.add_apply, PiLp.single_eq_same, PiLp.single_eq_of_ne]

private lemma raw_norm_sq (k : Fin 28) : ‖raw k‖ ^ 2 = 1 + (k.val : ℝ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_six]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := raw_at k
  rw [h0, h1, h2, h3, h4, h5]
  ring

private lemma raw_ne_zero (k : Fin 28) : raw k ≠ 0 := by
  intro h
  have := congrArg (fun p => p 0) h
  rw [(raw_at k).1] at this
  norm_num at this

private noncomputable def leaf (k : Fin 28) : EuclideanSpace ℝ (Fin 6) :=
  (‖raw k‖)⁻¹ • raw k

private lemma leaf_norm (k : Fin 28) : ‖leaf k‖ = 1 := by
  have hpos : 0 < ‖raw k‖ := norm_pos_iff.mpr (raw_ne_zero k)
  rw [leaf, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hpos.ne']

private lemma leaf_coord0 (k : Fin 28) : leaf k 0 = (‖raw k‖)⁻¹ := by
  have h0 := (raw_at k).1
  simp [leaf, PiLp.smul_apply, h0]

private lemma leaf_coord1 (k : Fin 28) : leaf k 1 = (‖raw k‖)⁻¹ * (k.val : ℝ) := by
  have h1 := (raw_at k).2.1
  simp [leaf, PiLp.smul_apply, h1]

private lemma leaf_inj : Function.Injective leaf := by
  intro k m h
  have h0 := congrArg (fun p => p 0) h
  have h1 := congrArg (fun p => p 1) h
  rw [leaf_coord0, leaf_coord0] at h0
  rw [leaf_coord1, leaf_coord1] at h1
  have hnorm : ‖raw k‖ = ‖raw m‖ := by
    calc
      ‖raw k‖ = (‖raw k‖)⁻¹⁻¹ := (inv_inv _).symm
      _ = (‖raw m‖)⁻¹⁻¹ := by rw [h0]
      _ = ‖raw m‖ := inv_inv _
  rw [hnorm] at h1
  have hmul : (k.val : ℝ) = m.val :=
    mul_left_cancel₀ (inv_ne_zero (norm_ne_zero_iff.mpr (raw_ne_zero m))) h1
  exact Fin.ext (Nat.cast_injective hmul)

private def leafIndex (v : Fin 29) (hv : v ≠ 0) : Fin 28 :=
  ⟨v.val - 1, by
    have h0 : v.val ≠ 0 := fun h => hv (Fin.ext h)
    omega⟩

private noncomputable def star28Place (v : Fin 29) : EuclideanSpace ℝ (Fin 6) :=
  if hv : v = 0 then 0 else leaf (leafIndex v hv)

private lemma star28Place_zero : star28Place 0 = 0 := by
  simp [star28Place]

private lemma star28Place_of_ne (v : Fin 29) (hv : v ≠ 0) :
    star28Place v = leaf (leafIndex v hv) := by
  simp [star28Place, hv]

private lemma dist_zero_leaf (k : Fin 28) :
    dist (0 : EuclideanSpace ℝ (Fin 6)) (leaf k) = 1 := by
  rw [dist_eq_norm, norm_sub_rev, sub_zero, leaf_norm]

private lemma star28Place_inj : Function.Injective star28Place := by
  intro a b h
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · exact ha.trans hb.symm
  · exfalso
    have hb' : b ≠ 0 := hb
    have hzero : star28Place b = 0 := by
      rw [ha] at h
      simpa [star28Place_zero] using h.symm
    rw [star28Place_of_ne b hb'] at hzero
    have hnorm := congrArg norm hzero
    rw [norm_zero, leaf_norm] at hnorm
    norm_num at hnorm
  · exfalso
    have ha' : a ≠ 0 := ha
    have hzero : star28Place a = 0 := by
      rw [hb] at h
      simpa [star28Place_zero] using h
    rw [star28Place_of_ne a ha'] at hzero
    have hnorm := congrArg norm hzero
    rw [norm_zero, leaf_norm] at hnorm
    norm_num at hnorm
  · have ha' : a ≠ 0 := ha
    have hb' : b ≠ 0 := hb
    have hleaf : leaf (leafIndex a ha') = leaf (leafIndex b hb') := by
      simpa [star28Place_of_ne a ha', star28Place_of_ne b hb'] using h
    have hk := leaf_inj hleaf
    apply Fin.ext
    have hval := congrArg Fin.val hk
    simp [leafIndex] at hval
    have ha0 : a.val ≠ 0 := fun h0 => ha (Fin.ext h0)
    have hb0 : b.val ≠ 0 := fun h0 => hb (Fin.ext h0)
    omega

private lemma star28_dist (u v : Fin 29) (huv : star28.Adj u v) :
    dist (star28Place u) (star28Place v) = 1 := by
  rw [star28_adj_iff] at huv
  rcases huv with ⟨hne, hu | hv⟩
  · have hv0 : v ≠ 0 := fun h => hne (hu.trans h.symm)
    subst hu
    rw [star28Place_zero, star28Place_of_ne v hv0, dist_zero_leaf]
  · have hu0 : u ≠ 0 := fun h => hne (h.trans hv.symm)
    subst hv
    rw [_root_.dist_comm, star28Place_zero, star28Place_of_ne u hu0, dist_zero_leaf]

/-- `K_{1,28}` has an injective unit-distance placement in `ℝ⁶`. -/
theorem star28_unitDist : star28.UnitDistEmbeddable 6 :=
  ⟨star28Place, star28Place_inj, star28_dist⟩

private def lineAt (r : ℝ) : EuclideanSpace ℝ (Fin 1) := !₂[r]

private lemma lineAt_coord (r : ℝ) : lineAt r 0 = r := by
  simp [lineAt]

private lemma dist_lineAt (a b : ℝ) : dist (lineAt a) (lineAt b) = |a - b| := by
  rw [dist_fin1, lineAt_coord, lineAt_coord]

private def place12 : (Fin 1 ⊕ Fin 2) → EuclideanSpace ℝ (Fin 1) :=
  Sum.elim (fun _ => lineAt 0) (fun i => if i = 0 then lineAt 1 else lineAt (-1))

private lemma place12_inj : Function.Injective place12 := by
  intro a b h
  have hc := congrArg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr
      exact Subsingleton.elim a b
    | inr j =>
      fin_cases j <;> simp [place12, lineAt, line_coord] at hc
  | inr i =>
    cases b with
    | inl _ =>
      fin_cases i <;> simp [place12, lineAt, line_coord] at hc
    | inr j =>
      fin_cases i <;> fin_cases j
      · rfl
      · have hc' : (1 : ℝ) = -1 := by simpa [place12, lineAt, line_coord] using hc
        norm_num at hc'
      · have hc' : (-1 : ℝ) = 1 := by simpa [place12, lineAt, line_coord] using hc
        norm_num at hc'
      · rfl

private lemma place12_dist (u v : Fin 1 ⊕ Fin 2)
    (huv : (completeBipartiteGraph (Fin 1) (Fin 2)).Adj u v) :
    dist (place12 u) (place12 v) = 1 := by
  simp only [completeBipartiteGraph_adj] at huv
  cases u with
  | inl _ =>
    cases v with
    | inl _ => simp at huv
    | inr j =>
      fin_cases j
      · simp [place12, dist_lineAt]
      · simp [place12, dist_lineAt]
  | inr i =>
    cases v with
    | inl _ =>
      fin_cases i
      · simp [place12, dist_lineAt]
      · simp [place12, dist_lineAt]
    | inr _ => simp at huv

/-- `K_{1,2}` has an injective unit-distance placement on the line. -/
theorem bipartite12_unitDist :
    (completeBipartiteGraph (Fin 1) (Fin 2)).UnitDistEmbeddable 1 :=
  ⟨place12, place12_inj, place12_dist⟩

private lemma normSqFin2 (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private lemma distSqFin2 (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

private lemma eq_one_of_sq {x : ℝ} (hx : 0 ≤ x) (h : x ^ 2 = 1) : x = 1 := by
  calc
    x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ = Real.sqrt 1 := by rw [h]
    _ = 1 := Real.sqrt_one

private noncomputable def pRight : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), 0]

private noncomputable def pApex : EuclideanSpace ℝ (Fin 2) :=
  !₂[((1 : ℝ) / 2), Real.sqrt 3 / 2]

private lemma pRight_norm_sq : ‖pRight‖ ^ 2 = 1 := by
  have h0 : pRight 0 = 1 := by simp [pRight]
  have h1 : pRight 1 = 0 := by simp [pRight]
  rw [normSqFin2, h0, h1]
  norm_num

private lemma pApex_norm_sq : ‖pApex‖ ^ 2 = 1 := by
  have h0 : pApex 0 = 1 / 2 := by simp [pApex]
  have h1 : pApex 1 = Real.sqrt 3 / 2 := by simp [pApex]
  rw [normSqFin2, h0, h1]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h3]
  norm_num

private lemma dist_right_apex_sq : dist pRight pApex ^ 2 = 1 := by
  have hR0 : pRight 0 = 1 := by simp [pRight]
  have hR1 : pRight 1 = 0 := by simp [pRight]
  have hA0 : pApex 0 = 1 / 2 := by simp [pApex]
  have hA1 : pApex 1 = Real.sqrt 3 / 2 := by simp [pApex]
  rw [distSqFin2, hR0, hR1, hA0, hA1]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h3]
  norm_num

private lemma dist_zero_right_eq : dist (0 : EuclideanSpace ℝ (Fin 2)) pRight = 1 := by
  rw [dist_eq_norm, norm_sub_rev, sub_zero]
  exact eq_one_of_sq (norm_nonneg _) pRight_norm_sq

private lemma dist_zero_apex : dist (0 : EuclideanSpace ℝ (Fin 2)) pApex = 1 := by
  rw [dist_eq_norm, norm_sub_rev, sub_zero]
  exact eq_one_of_sq (norm_nonneg _) pApex_norm_sq

private lemma dist_right_apex : dist pRight pApex = 1 :=
  eq_one_of_sq dist_nonneg dist_right_apex_sq

private lemma pRight_ne_zero : pRight ≠ 0 := by
  intro h
  have := congrArg (fun p => p 0) h
  simp [pRight] at this

private lemma pApex_ne_zero : pApex ≠ 0 := by
  intro h
  have hc := congrArg (fun p => p 1) h
  have h1 : pApex 1 = Real.sqrt 3 / 2 := by simp [pApex]
  have hzero : ((0 : EuclideanSpace ℝ (Fin 2)) 1) = 0 := by simp
  rw [h1, hzero] at hc
  exact (by positivity : (0 : ℝ) < Real.sqrt 3 / 2).ne' hc

private lemma pRight_ne_pApex : pRight ≠ pApex := by
  intro h
  have hc := congrArg (fun p => p 1) h
  have hR : pRight 1 = 0 := by simp [pRight]
  have hA : pApex 1 = Real.sqrt 3 / 2 := by simp [pApex]
  rw [hR, hA] at hc
  have : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  linarith

private noncomputable def placeEq : (Fin 1 ⊕ Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  Sum.elim (fun _ => 0) (fun i => if i = 0 then pRight else pApex)

private lemma placeEq_inl (a : Fin 1) : placeEq (Sum.inl a) = 0 := rfl

private lemma placeEq_zero : placeEq (Sum.inr 0) = pRight := by
  simp [placeEq]

private lemma placeEq_one : placeEq (Sum.inr 1) = pApex := by
  simp [placeEq]

private lemma placeEq_inj : Function.Injective placeEq := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr
      exact Subsingleton.elim a b
    | inr j =>
      fin_cases j
      · exfalso
        exact pRight_ne_zero.symm (by simpa [placeEq_inl, placeEq_zero] using h)
      · exfalso
        exact pApex_ne_zero.symm (by simpa [placeEq_inl, placeEq_one] using h)
  | inr i =>
    cases b with
    | inl _ =>
      fin_cases i
      · exfalso
        exact pRight_ne_zero (by simpa [placeEq_inl, placeEq_zero] using h)
      · exfalso
        exact pApex_ne_zero (by simpa [placeEq_inl, placeEq_one] using h)
    | inr j =>
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd (by simpa [placeEq_zero, placeEq_one] using h) pRight_ne_pApex
      · exact absurd (by simpa [placeEq_zero, placeEq_one] using h.symm) pRight_ne_pApex
      · rfl

private lemma placeEq_dist (u v : Fin 1 ⊕ Fin 2)
    (huv : (completeBipartiteGraph (Fin 1) (Fin 2)).Adj u v) :
    dist (placeEq u) (placeEq v) = 1 := by
  simp only [completeBipartiteGraph_adj] at huv
  cases u with
  | inl _ =>
    cases v with
    | inl _ => simp at huv
    | inr j =>
      fin_cases j
      · simpa [placeEq_inl, placeEq_zero] using dist_zero_right_eq
      · simpa [placeEq_inl, placeEq_one] using dist_zero_apex
  | inr i =>
    cases v with
    | inl _ =>
      fin_cases i
      · simpa [placeEq_inl, placeEq_zero, _root_.dist_comm] using dist_zero_right_eq
      · simpa [placeEq_inl, placeEq_one, _root_.dist_comm] using dist_zero_apex
    | inr _ => simp at huv

/-- An equilateral triangle in `ℝ²` places `K_{1,2}` so that the non-edge also has length `1`. -/
theorem bipartite12_equilateral :
    ∃ p : (Fin 1 ⊕ Fin 2) → EuclideanSpace ℝ (Fin 2),
      Function.Injective p ∧
      (∀ u v, (completeBipartiteGraph (Fin 1) (Fin 2)).Adj u v → dist (p u) (p v) = 1) ∧
      ∃ u v, u ≠ v ∧ ¬ (completeBipartiteGraph (Fin 1) (Fin 2)).Adj u v ∧
        dist (p u) (p v) = 1 := by
  refine ⟨placeEq, placeEq_inj, placeEq_dist, Sum.inr 0, Sum.inr 1, ?_, ?_, ?_⟩
  · decide
  · simp [completeBipartiteGraph_adj]
  · simpa [placeEq_zero, placeEq_one] using dist_right_apex

/-- `K_{1,3}` has no injective unit-distance placement on the line. -/
theorem not_bipartite13_unitDist :
    ¬ (completeBipartiteGraph (Fin 1) (Fin 3)).UnitDistEmbeddable 1 := by
  intro h
  obtain ⟨f, hf, hdist⟩ := h
  exact noThreeOnLine f hf (c := Sum.inl (0 : Fin 1)) (g := fun i => Sum.inr i)
    Sum.inr_injective (fun i => hdist _ _ (by simp [completeBipartiteGraph_adj]))

private def collapse13 : (Fin 1 ⊕ Fin 3) → EuclideanSpace ℝ (Fin 1) :=
  Sum.elim (fun _ => lineAt 0) (fun _ => lineAt 1)

/-- Collapsing the leaves of `K_{1,3}` preserves edge lengths and is not injective. -/
theorem bipartite13_collapsed :
    ∃ p : (Fin 1 ⊕ Fin 3) → EuclideanSpace ℝ (Fin 1),
      ¬ Function.Injective p ∧
      ∀ u v, (completeBipartiteGraph (Fin 1) (Fin 3)).Adj u v → dist (p u) (p v) = 1 := by
  refine ⟨collapse13, ?_, ?_⟩
  · intro hinj
    have hsame : collapse13 (Sum.inr 0) = collapse13 (Sum.inr 1) := by simp [collapse13]
    exact (by decide : (Sum.inr 0 : Fin 1 ⊕ Fin 3) ≠ Sum.inr 1) (hinj hsame)
  · intro u v huv
    simp only [completeBipartiteGraph_adj] at huv
    cases u with
    | inl _ =>
      cases v with
      | inl _ => simp at huv
      | inr _ => simp [collapse13, dist_lineAt]
    | inr _ =>
      cases v with
      | inl _ => simp [collapse13, dist_lineAt]
      | inr _ => simp at huv

private def edge01 : SimpleGraph (Fin 3) where
  Adj u v := u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 0

private lemma edge01_adj_iff (u v : Fin 3) :
    edge01.Adj u v ↔ (u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 0) :=
  Iff.rfl

private instance : DecidableRel edge01.Adj := fun u v =>
  decidable_of_iff (u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 0) (edge01_adj_iff u v)

private def place3 : Fin 3 → EuclideanSpace ℝ (Fin 1) :=
  ![!₂[(0 : ℝ)], !₂[(1 : ℝ)], !₂[(2 : ℝ)]]

private lemma place3_coord (i : Fin 3) : place3 i 0 = (i : ℕ) := by
  fin_cases i <;> simp [place3]

private lemma place3_inj : Function.Injective place3 := by
  intro a b h
  have hc := congrArg (fun p => p 0) h
  rw [place3_coord, place3_coord] at hc
  exact Fin.ext (Nat.cast_injective hc)

private lemma place3_dist (u v : Fin 3) (huv : edge01.Adj u v) :
    dist (place3 u) (place3 v) = 1 := by
  rw [edge01_adj_iff] at huv
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [dist_fin1, place3_coord, place3_coord]
    norm_num
  · rw [dist_fin1, place3_coord, place3_coord]
    norm_num

private def placeStar (v : Fin 4) : EuclideanSpace ℝ (Fin 1) :=
  if v = 0 then lineAt 0 else lineAt 1

private lemma placeStar_spec :
    placeStar 0 = !₂[(0 : ℝ)] ∧ placeStar 1 = !₂[(1 : ℝ)] ∧
      placeStar 2 = !₂[(1 : ℝ)] ∧
      placeStar 3 = !₂[(1 : ℝ)] := by
  simp [placeStar, lineAt]

private lemma placeStar_dist (u v : Fin 4) (huv : star3.Adj u v) :
    dist (placeStar u) (placeStar v) = 1 := by
  rw [star3_adj_iff] at huv
  rcases huv with ⟨hu | hv, hne⟩
  · subst hu
    have hv0 : v ≠ 0 := fun h => hne h.symm
    rw [dist_fin1]
    simp [placeStar, hv0, lineAt]
  · subst hv
    have hu0 : u ≠ 0 := fun h => hne h
    rw [_root_.dist_comm, dist_fin1]
    simp [placeStar, hu0, lineAt]

private instance : DecidableRel (pathGraph 29).Adj := fun u v =>
  decidable_of_iff (u.val + 1 = v.val ∨ v.val + 1 = u.val) pathGraph_adj.symm

/-- The path with `28` edges, on `29` vertices, has `(6 + 2)` choose `2` edges. -/
theorem ncard_pathGraph29 : (pathGraph 29).edgeSet.ncard = (6 + 2).choose 2 := by
  have h : (pathGraph 29).edgeSet.ncard = 28 := by
    have hc : Finset.card (pathGraph 29).edgeFinset = 28 := by decide
    rwa [edgeFinset_card, Set.fintypeCard_eq_ncard] at hc
  rw [h]
  decide

/-- Every vertex of the path with `28` edges has a neighbor. -/
theorem pathGraph29_exists_adj (v : Fin 29) : ∃ w, (pathGraph 29).Adj v w := by
  by_cases hv : v = 28
  · subst hv
    refine ⟨27, ?_⟩
    rw [pathGraph_adj]
    decide
  · refine ⟨⟨v.val + 1, ?_⟩, ?_⟩
    · have hvlt := v.isLt
      have hv28 : v.val ≠ 28 := fun h => hv (Fin.ext h)
      omega
    · rw [pathGraph_adj]
      exact Or.inl rfl

end EdgeThresholdUniqueness.Bridge

namespace EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness

open SimpleGraph
open EdgeThresholdUniqueness.Bridge

theorem UnitDistanceRepresentable.separating.proof : UnitDistanceRepresentable.separating := by
  refine ⟨⟨edge01, edge01_adj_iff, ?_, ?_⟩, ⟨star3, star3_adj_iff, ?_, ?_⟩⟩
  · decide
  · refine ⟨place3, rfl, place3_inj, place3_dist, by decide, ?_, ?_, ?_⟩
    · intro h
      rw [edge01_adj_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 (by decide : (1 : Fin 3) ≠ 0)
      · exact absurd h2 (by decide : (2 : Fin 3) ≠ 0)
    · rw [dist_fin1, place3_coord, place3_coord]
      norm_num
    · exact ⟨place3, place3_inj, place3_dist⟩
  · decide
  · refine ⟨placeStar, ?_, ?_, ?_, ?_, ?_⟩
    · exact placeStar_spec.1
    · exact placeStar_spec.2.1
    · exact placeStar_spec.2.2.1
    · exact placeStar_spec.2.2.2
    · refine ⟨?_, placeStar_dist, ?_⟩
      · intro hinj
        have hsame : placeStar 1 = placeStar 2 := by simp [placeStar]
        exact (by decide : (1 : Fin 4) ≠ 2) (hinj hsame)
      · intro h
        exact not_star3_unitDist ((unitDistanceRepresentable_iff star3 1).mp h)

theorem UniqueKComplete.proof : UniqueKComplete := by
  intro d hd n G hcard hdeg hrep
  have hemb : ¬ G.UnitDistEmbeddable d := by
    intro h
    exact hrep ((unitDistanceRepresentable_iff G d).mpr h)
  simpa [completeGraph_eq_top] using
    nonempty_iso_completeGraph_of_not_unitDistEmbeddable G hd hemb hcard hdeg

theorem UniqueKComplete.witness.proof : UniqueKComplete.witness := by
  refine ⟨UniqueKComplete.proof, by decide, ?_, ?_, ?_⟩
  · rw [ncard_edgeSet_completeGraph]
  · intro v
    exact completeGraph_exists_adj (by decide) v
  · intro h
    exact not_unitDistEmbeddable_complete_of_lt (by decide)
      ((unitDistanceRepresentable_iff _ _).mp h)

theorem UniqueKComplete.dropHd.proof : UniqueKComplete.dropHd := by
  intro hyp
  exact not_iso_complete (by decide : 4 ≠ 1 + 2) star3
    (hyp 1 4 star3 ncard_star3 star3_exists_adj (by
      intro h
      exact not_star3_unitDist ((unitDistanceRepresentable_iff star3 1).mp h)))

theorem UniqueKComplete.dropHcard.proof : UniqueKComplete.dropHcard := by
  intro hyp
  exact not_iso_complete (by decide : 9 ≠ 6 + 2) (completeGraph (Fin 9))
    (hyp 6 (by decide) 9 (completeGraph (Fin 9))
      (fun v => completeGraph_exists_adj (by decide) v) (by
        intro h
        exact not_unitDistEmbeddable_complete_of_lt (by decide : 6 + 1 < 9)
          ((unitDistanceRepresentable_iff _ _).mp h)))

theorem UniqueKComplete.dropHdeg.proof : UniqueKComplete.dropHdeg := by
  intro hyp
  exact not_iso_complete (by decide : 9 ≠ 6 + 2) k8Plus
    (hyp 6 (by decide) 9 k8Plus ncard_k8Plus (by
      intro h
      exact not_k8Plus_unitDist ((unitDistanceRepresentable_iff k8Plus 6).mp h)))

theorem UniqueKComplete.dropHrep.proof : UniqueKComplete.dropHrep := by
  intro hyp
  exact not_iso_complete (by decide : 29 ≠ 6 + 2) (pathGraph 29)
    (hyp 6 (by decide) 29 (pathGraph 29) ncard_pathGraph29 pathGraph29_exists_adj)

end EdgeThresholdUniqueness.Standalone.Mathlib.InlineEdgeThresholdUniqueness

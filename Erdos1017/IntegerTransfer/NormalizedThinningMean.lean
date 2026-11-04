module

public import Erdos1017.IntegerTransfer.TransversalBaseDegree
public import Erdos1017.IntegerTransfer.ThinningTypicalBases

/-!
# Normalized thinning to a common pair density

This module defines the normalized thinning probabilities that bring every pair
to a common expected density `α`, together with the resulting common
`degreeScale`, and shows that a typical base has conditional sampled mean close
to that scale with a relative error independent of `α` (`typical_mean_close`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] {t u : ℕ}

/-- Original pair density as a real-valued function of its role labels. -/
def pairDensity (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (e : Fin (t + u) × Fin (t + u)) : ℝ :=
  G.edgeDensity (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2)

/-- Thinning to a common expected pair density α. Unused within-part
coordinates have probability zero. -/
def normalizedProbability (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (α : ℝ) (e : Fin (t + u) × Fin (t + u)) : ℝ :=
  if e.1 = e.2 then 0 else α / pairDensity G e

/-- The common degree scale after normalized thinning. -/
def degreeScale (n u m : ℕ) (α : ℝ) : ℝ := (n : ℝ) ^ u * α ^ m

omit [DecidableEq A] in
/-- Normalized probabilities are valid on every coordinate, including unused ones. -/
theorem normalizedProbability_bounds (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {α δ : ℝ} (hα : 0 ≤ α) (hαδ : α ≤ δ) (hδ : 0 < δ)
    (hd : ∀ i j : Fin (t + u), i < j → δ ≤ pairDensity G (i, j))
    (e : Fin (t + u) × Fin (t + u)) :
    0 ≤ normalizedProbability G α e ∧ normalizedProbability G α e ≤ 1 := by
  by_cases he : e.1 = e.2
  · simp only [normalizedProbability, ite_eq_left he]
    norm_num
  · have hfloor : δ ≤ pairDensity G e := by
      rcases lt_or_gt_of_ne he with hlt | hgt
      · exact hd _ _ hlt
      · simpa only [pairDensity, SimpleGraph.edgeDensity_comm] using hd _ _ hgt
    have hpos : 0 < pairDensity G e := hδ.trans_le hfloor
    rw [normalizedProbability, ite_eq_right he]
    exact ⟨div_nonneg hα hpos.le, (div_le_one hpos).mpr (hαδ.trans hfloor)⟩

omit [DecidableEq A] in
/-- Density and thinning factors cancel exactly on every non-base required edge. -/
theorem prediction_normalized (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (α : ℝ)
    (hd : ∀ i j : Fin (t + u), i < j → 0 < pairDensity G (i, j)) :
    MultipartiteExtension.prediction G * extensionProbability (normalizedProbability G α) =
      degreeScale (Fintype.card A) u (SharedBasePattern.extensionEdges t u).card α := by
  have hpoint (e : Fin (t + u) × Fin (t + u)) (he : e ∈ SharedBasePattern.extensionEdges t u) :
      pairDensity G e * normalizedProbability G α e = α := by
    have hlt := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    have hpos := hd _ _ hlt
    rw [normalizedProbability, ite_eq_right hlt.ne]
    exact mul_div_cancel₀ α hpos.ne'
  unfold MultipartiteExtension.prediction MultipartiteExtension.extensionDensity extensionProbability degreeScale
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  change (Fintype.card A : ℝ) ^ u * (∏ e ∈ SharedBasePattern.extensionEdges t u,
    pairDensity G e * normalizedProbability G α e) = _
  rw [Finset.prod_congr rfl hpoint, Finset.prod_const]

/-- The conditional mean is bounded by a multiplier depending only on δ and
the role pattern, independently of α or a later allocation lower bound. -/
theorem mean_le_uniform_multiplier [Nonempty A]
    (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    (hd : ∀ i j : Fin (t + u), i < j → δ ≤ pairDensity G (i, j))
    (x : Fin t → A) :
    BernoulliFamily.mean (extensions G x) (support x) (partProbability (normalizedProbability G α)) ≤
      (1 + (δ ^ (SharedBasePattern.extensionEdges t u).card)⁻¹) *
        degreeScale (Fintype.card A) u (SharedBasePattern.extensionEdges t u).card α := by
  let m := (SharedBasePattern.extensionEdges t u).card
  let q := normalizedProbability G α
  let P := extensionProbability q
  have hP : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro e _
    dsimp [q, normalizedProbability]
    split_ifs
    · exact le_rfl
    · apply div_nonneg hα
      dsimp only [pairDensity]
      exact_mod_cast G.edgeDensity_nonneg _ _
  have hcard : ((extensions G x).card : ℝ) ≤ (Fintype.card A : ℝ) ^ u := by
    exact_mod_cast family_card_le (extensions G x)
  have hμ := mul_le_mul_of_nonneg_right hcard hP
  have hpred := MultipartiteExtension.prediction_lower G hδ.le hd
  have hpred' := mul_le_mul_of_nonneg_right hpred hP
  have hnorm := prediction_normalized G α (fun i j hij => hδ.trans_le (hd i j hij))
  have hD : 0 ≤ degreeScale (Fintype.card A) u m α := by dsimp [degreeScale]; positivity
  have hδm : 0 < δ ^ m := pow_pos hδ _
  have hbound : (Fintype.card A : ℝ) ^ u * P ≤
      (δ ^ m)⁻¹ * degreeScale (Fintype.card A) u m α := by
    rw [hnorm] at hpred'
    rw [mul_comm ((δ ^ m)⁻¹)]
    apply (le_mul_inv_iff₀ hδm).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpred'
  rw [mean_partProbability]
  change ((extensions G x).card : ℝ) * P ≤ _
  have hfinal := hμ.trans hbound
  nlinarith

/-- A deterministic typical base has its conditional sampled mean close to the
common degree scale with the same relative error, independent of α. -/
theorem typical_mean_close (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (α γ : ℝ) (hα : 0 ≤ α)
    (hd : ∀ i j : Fin (t + u), i < j → 0 < pairDensity G (i, j))
    (x : Fin t → A) (hx : x ∈ typicalBases G γ) :
    |BernoulliFamily.mean (extensions G x) (support x) (partProbability (normalizedProbability G α)) -
      degreeScale (Fintype.card A) u (SharedBasePattern.extensionEdges t u).card α| ≤
      γ * degreeScale (Fintype.card A) u (SharedBasePattern.extensionEdges t u).card α := by
  let q := normalizedProbability G α
  have hq : 0 ≤ extensionProbability q := by
    apply Finset.prod_nonneg
    intro e he
    have hlt := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    change 0 ≤ normalizedProbability G α e
    rw [normalizedProbability, ite_eq_right hlt.ne]
    exact div_nonneg hα (hd _ _ hlt).le
  have htyp := (Finset.mem_filter.mp hx).2
  have h := mul_le_mul_of_nonneg_right htyp.le hq
  rw [mean_partProbability, extensions_card]
  rw [← prediction_normalized G α hd, ← sub_mul, abs_mul, abs_of_nonneg hq]
  nlinarith

end Erdos1017.TransversalThinning

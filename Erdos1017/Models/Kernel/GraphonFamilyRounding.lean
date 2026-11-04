/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer

The rerounding proof below is adapted from
vendor/Graphon/Graphon/Compactness.lean.
The common partition and parent map are chosen before the coefficients.
-/
module

public import Graphon.Compactness

/-!
# Rounding step graphons to a shared equipartition

One equipartition and parent map reround every admissible coefficient function,
depending only on `P` and `q`, and a family of step graphons rerounds on one
shared equipartition with no finiteness assumption on the family.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Graphon
open scoped ENNReal

namespace Erdos1017.GraphonFamily

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- One equipartition and parent map reround every admissible coefficient function.
The partition and parent map depend only on `P` and `q`. -/
theorem exists_common_equipartition_rounding
    (P : MeasurablePartition Ω μ) {q : ℕ} (hq : 0 < q) :
    ∃ (Q : MeasurablePartition Ω μ) (parent : Set Ω → Set Ω)
      (hparent : ∀ A, parent A ∈ P.parts),
      Q.parts.card = q ∧
      (∀ A ∈ Q.parts, μ A = (1 : ℝ≥0∞) / q) ∧
      ∀ (c : Set Ω → Set Ω → ℝ)
        (hc_symm : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T = c T S)
        (hc_mem : ∀ S ∈ P.parts, ∀ T ∈ P.parts, c S T ∈ Set.Icc 0 1),
        cutNormDiff (mkStepGraphon P c hc_symm hc_mem)
          (mkStepGraphon Q (fun A B => c (parent A) (parent B))
            (fun A _ B _ => hc_symm _ (hparent A) _ (hparent B))
            (fun A _ B _ => hc_mem _ (hparent A) _ (hparent B)))
          ≤ 2 * (P.parts.card : ℝ) / q := by
  classical
  obtain ⟨Q, hQcard, hQmu, bad, hbad_meas, hbad_le, hrefine⟩ :=
    exists_equipartition_almost_refining P hq
  -- `Q` is nonempty (it has `q > 0` cells), giving a fallback parent `S₀ ∈ P.parts`.
  have hQne : Q.parts.Nonempty := by rw [← Finset.card_pos, hQcard]; exact hq
  obtain ⟨A₀, hA₀⟩ := hQne
  obtain ⟨S₀, hS₀, -⟩ := hrefine A₀ hA₀
  -- For each `Q`-cell `A`, pick a parent `P`-cell `par A` with `A \ bad ⊆ par A`.
  choose par hpar_mem hpar_sub using hrefine
  -- Total parent map (fallback to `S₀` off `Q.parts`, never actually used a.e.).
  set parentOf : Set Ω → Set Ω := fun A => if hA : A ∈ Q.parts then par A hA else S₀
    with hpar_def
  have hparentOf_mem : ∀ A, parentOf A ∈ P.parts := by
    intro A
    simp only [hpar_def]
    by_cases hA : A ∈ Q.parts
    · rw [dite_eq_left hA]; exact hpar_mem A hA
    · rw [dite_eq_right hA]; exact hS₀
  have hparentOf_sub : ∀ A, A ∈ Q.parts → A \ bad ⊆ parentOf A := by
    intro A hA
    simp only [hpar_def]
    rw [dite_eq_left hA]; exact hpar_sub A hA
  refine ⟨Q, parentOf, hparentOf_mem, hQcard, hQmu, ?_⟩
  intro c hc_symm hc_mem
  -- Re-rounded coefficients: inherit the parent `P`-cell coefficient.
  set cQ : Set Ω → Set Ω → ℝ := fun A B => c (parentOf A) (parentOf B) with hcQ_def
  have hcQ_symm : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ A B = cQ B A := by
    intro A _ B _
    simp only [hcQ_def]
    exact hc_symm _ (hparentOf_mem A) _ (hparentOf_mem B)
  have hcQ_mem : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ A B ∈ Set.Icc 0 1 := by
    intro A _ B _
    simp only [hcQ_def]
    exact hc_mem _ (hparentOf_mem A) _ (hparentOf_mem B)

  -- Connect the graphons' `AEEqFun`s to the underlying step functions.
  have hU_eq : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon P c hc_symm hc_mem).toAEEqFun p = mkStepFun P c p :=
    AEEqFun.coeFn_mk (mkStepFun P c) (mkStepFun_measurable P c).aestronglyMeasurable
  have hW_eq : ∀ᵐ p ∂(μ.prod μ),
      (mkStepGraphon Q cQ hcQ_symm hcQ_mem).toAEEqFun p = mkStepFun Q cQ p :=
    AEEqFun.coeFn_mk (mkStepFun Q cQ) (mkStepFun_measurable Q cQ).aestronglyMeasurable
  have hAcov : ∀ᵐ p ∂(μ.prod μ), ∃ A ∈ Q.parts, p.1 ∈ A :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst Q.ae_covers
  have hBcov : ∀ᵐ p ∂(μ.prod μ), ∃ B ∈ Q.parts, p.2 ∈ B :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd Q.ae_covers
  refine le_trans (cutNormDiff_le_of_ae_agree_off_strip _ _ bad hbad_meas ?_) ?_
  · -- Off the strip, both step graphons equal `c` of the shared parent cells.
    filter_upwards [hU_eq, hW_eq, hAcov, hBcov] with p hPeq hQeq hAc hBc h1 h2
    obtain ⟨A, hA, hpA⟩ := hAc
    obtain ⟨B, hB, hpB⟩ := hBc
    have hp1par : p.1 ∈ parentOf A := hparentOf_sub A hA ⟨hpA, h1⟩
    have hp2par : p.2 ∈ parentOf B := hparentOf_sub B hB ⟨hpB, h2⟩
    rw [hPeq, hQeq,
      mkStepFun_eq_at P c (hparentOf_mem A) (hparentOf_mem B)
        (Set.mem_prod.mpr ⟨hp1par, hp2par⟩),
      mkStepFun_eq_at Q cQ hA hB (Set.mem_prod.mpr ⟨hpA, hpB⟩)]
  · -- Convert the measure bound `μ bad ≤ P.card / q` to the real-valued estimate.
    have hqE : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
    have hne : ((P.parts.card : ℝ≥0∞) / q) ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hqE
    have hbad_toReal : (μ bad).toReal ≤ (P.parts.card : ℝ) / q := by
      calc (μ bad).toReal ≤ ((P.parts.card : ℝ≥0∞) / q).toReal :=
            ENNReal.toReal_mono hne hbad_le
        _ = (P.parts.card : ℝ) / q := by
            rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    rw [mul_div_assoc]
    linarith [hbad_toReal]

/-- A family of step graphons rerounds on one shared equipartition.
No finiteness assumption on the family is needed. -/
theorem reround_family_to_equipartition
    (P : MeasurablePartition Ω μ) (c : ι → Set Ω → Set Ω → ℝ)
    (hc_symm : ∀ i, ∀ S ∈ P.parts, ∀ T ∈ P.parts, c i S T = c i T S)
    (hc_mem : ∀ i, ∀ S ∈ P.parts, ∀ T ∈ P.parts, c i S T ∈ Set.Icc 0 1)
    {q : ℕ} (hq : 0 < q) :
    ∃ (Q : MeasurablePartition Ω μ) (cQ : ι → Set Ω → Set Ω → ℝ)
      (hcQ_symm : ∀ i, ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ i A B = cQ i B A)
      (hcQ_mem : ∀ i, ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, cQ i A B ∈ Set.Icc 0 1),
      Q.parts.card = q ∧
      (∀ A ∈ Q.parts, μ A = (1 : ℝ≥0∞) / q) ∧
      ∀ i, cutNormDiff (mkStepGraphon P (c i) (hc_symm i) (hc_mem i))
        (mkStepGraphon Q (cQ i) (hcQ_symm i) (hcQ_mem i))
        ≤ 2 * (P.parts.card : ℝ) / q := by
  obtain ⟨Q, parent, hparent, hQcard, hQmu, happrox⟩ :=
    exists_common_equipartition_rounding P hq
  refine ⟨Q, fun i A B => c i (parent A) (parent B),
    (fun i A _ B _ => hc_symm i _ (hparent A) _ (hparent B)),
    (fun i A _ B _ => hc_mem i _ (hparent A) _ (hparent B)), hQcard, hQmu, ?_⟩
  intro i
  exact happrox (c i) (hc_symm i) (hc_mem i)

end Erdos1017.GraphonFamily

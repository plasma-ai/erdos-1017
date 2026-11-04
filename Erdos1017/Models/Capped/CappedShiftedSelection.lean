module

public import Erdos1017.Models.Capped.CappedSingularKernel

/-!
# Selected kernels of interior capped optimizers

For the averaged optimizer, edge complementarity turns the shifted sampled color
into its deterministic shifted mean kernel, and every interior-density capped
optimizer admits an equally good averaged optimizer with the common regular and
singular kernel properties (`exists_selected_capped_kernel`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- For the actual averaged optimizer, edge complementarity turns
the shifted sampled color into its deterministic shifted mean kernel. -/
theorem shiftedColor_deterministic_of_complementary (W : Model Ω μ) (m : ℝ)
    (hcomplementary : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ p, ∀ᵐ c ∂W.kernel p,
      CappedColor.charge c = conditionalCharge W p * CappedColor.adjacency c) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p := by
  filter_upwards [hcomplementary] with p hp
  have hM := shiftedMoment_eq_conditional W m p
  by_cases hz : conditionalCharge W p - m = 0
  · have heq : conditionalCharge W p = m := sub_eq_zero.mp hz
    filter_upwards [hdet p] with c hc
    rw [shiftedColor, hc, heq, hM, hz, mul_zero, sub_self]
  · rw [hM] at hp
    have hprod : ((1 - W.moment CappedColor.adjacency p) * W.moment CappedColor.adjacency p) *
        (conditionalCharge W p - m) = 0 := by
      convert hp using 1
      ring
    have hA := (mul_eq_zero.mp hprod).resolve_right hz
    rcases mul_eq_zero.mp hA with hone | hzero
    · have hAone : W.moment CappedColor.adjacency p = 1 := by linarith
      filter_upwards [hdet p, ae_adjacency_one_of_moment_one W p hAone] with c hc ha
      rw [shiftedColor, hc, ha, hM, hAone]
      ring
    · filter_upwards [hdet p, ae_adjacency_zero_of_moment_zero W p hzero] with c hc ha
      rw [shiftedColor, hc, ha, hM, hzero]
      ring

/-- Every actual interior-density capped optimizer admits an actual
equally good averaged optimizer with the common regular/singular kernel
properties. The selected kernel and sampled shifted color agree almost
surely; no deterministic adjacency assumption is made. -/
theorem exists_selected_capped_kernel [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ (V : Model Ω μ) (m ν : ℝ), IsMaximizer r V ∧ density V = density W ∧
      objective V = objective W ∧ m ∈ Set.Icc (-3) 1 ∧
      (∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂V.kernel p, shiftedColor m c = shiftedMoment V m p) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment V m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - V.moment CappedColor.adjacency p) * shiftedMoment V m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel V m x y ∂μ) = ν) ∧
      ν = 2 * (objective V - m * density V) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ≤ 2 := by
  let V := averaged W
  have hV : IsMaximizer r V := averaged_isMaximizer W hW
  have hdV : density V = density W := density_averaged W
  have hcV : objective V = objective W := objective_averaged W
  have hdet (p : Ω × Ω) : ∀ᵐ c ∂V.kernel p,
      CappedColor.charge c = conditionalCharge V p * CappedColor.adjacency c := by
    change ∀ᵐ c ∂(averaged W).kernel p,
      CappedColor.charge c = conditionalCharge (averaged W) p * CappedColor.adjacency c
    rw [conditionalCharge_averaged]
    exact averaged_deterministic W p
  have hex : ∃ m ν : ℝ, m ∈ Set.Icc (-3) 1 ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment V m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - V.moment CappedColor.adjacency p) * shiftedMoment V m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel V m x y ∂μ) = ν) ∧
      ν = 2 * (objective V - m * density V) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ≤ 2 := by
    by_cases hs : Variation.weightFirstVariation (adjacencyOperator V) = 0
    · obtain ⟨m, ν, hm, _, _, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
        exists_singular_kernel V hV hs (hdV.symm ▸ hd0) (hdV.symm ▸ hdhalf)
      exact ⟨m, ν, hm, hmem, hcomp, hrow, hν, hfinite, hindex.trans (by norm_num)⟩
    · obtain ⟨m, ν, hm, _, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
        exists_regular_kernel V hV hs (hdV.symm ▸ hd0) (hdV.symm ▸ hdhalf)
      exact ⟨m, ν, hm, hmem, hcomp, hrow, hν, hfinite, hindex⟩
  obtain ⟨m, ν, hm, hmem, hcomp, hrow, hν, hfinite, hindex⟩ := hex
  exact ⟨V, m, ν, hV, hdV, hcV, hm,
    shiftedColor_deterministic_of_complementary V m hcomp hdet,
    hmem, hcomp, hrow, hν, hfinite, hindex⟩

end Erdos1017.CappedModel

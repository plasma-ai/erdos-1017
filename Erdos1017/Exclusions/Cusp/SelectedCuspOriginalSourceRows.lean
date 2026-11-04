module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceTangent
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.SelectedModel.Flows.OriginalForwardPeakLargest

/-!
# Original-law rows of the cusp source remainder

On the original law the whole source remainder joins every point outside its own
square and the original head, its degree integral is exact, and its missing mass
is below peak mass times remainder mass by the strict atomic gap.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open WholeSourceChild KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private theorem row_of_missing_block {ν : Measure Ω} [IsProbabilityMeasure ν]
    (G : Ω → Ω → ℝ) (hG : AEStronglyMeasurable (Function.uncurry G) (ν.prod ν))
    (hbound : ∀ᵐ p ∂ν.prod ν, ‖G p.1 p.2‖ ≤ 1)
    (C P D : Set Ω) (hC : MeasurableSet C) (hP : MeasurableSet P) (hD : MeasurableSet D)
    (he : ∀ᵐ p ∂ν.prod ν, p.1 ∈ C → G p.1 p.2 =
      1 - P.indicator (fun _ => 1) p.2 - D.indicator (fun _ => 1) p.2 * (1 - G p.1 p.2)) :
    rowIntegral ν G C = ν.real C * (1 - ν.real P) -
      crossIntegral ν (fun x y => 1 - G x y) C D := by
  let f := C.indicator (fun _ => (1 : ℝ))
  let g := P.indicator (fun _ => (1 : ℝ))
  let h := D.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f ν := (integrable_const 1).indicator hC
  have hg : Integrable g ν := (integrable_const 1).indicator hP
  have hh : Integrable h ν := (integrable_const 1).indicator hD
  have hb : ∀ᵐ p ∂ν.prod ν, ‖1 - G p.1 p.2‖ ≤ 2 := by
    filter_upwards [hbound] with p hp
    calc
      ‖1 - G p.1 p.2‖ ≤ ‖(1 : ℝ)‖ + ‖G p.1 p.2‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num at *; linarith
  have heq : (fun p : Ω × Ω => G p.1 p.2 * 1 * f p.1) =ᵐ[ν.prod ν]
      fun p => f p.1 * 1 - f p.1 * g p.2 - (1 - G p.1 p.2) * h p.2 * f p.1 := by
    filter_upwards [he] with p hp
    by_cases hc : p.1 ∈ C
    · have hv := hp hc
      dsimp [f, g, h]
      rw [indicator_of_mem hc]
      linear_combination hv
    · simp only [f, indicator_of_notMem hc, mul_zero, zero_mul, sub_self]
  have hi : Integrable (fun p : Ω × Ω => (1 - G p.1 p.2) * h p.2 * f p.1) (ν.prod ν) :=
    integrable_kernel_bilinear (K := fun x y => 1 - G x y)
      (aestronglyMeasurable_const.sub hG) hb hh hf
  have hs₁ : (∫ p : Ω × Ω, f p.1 * 1 - f p.1 * g p.2 -
      (1 - G p.1 p.2) * h p.2 * f p.1 ∂ν.prod ν) =
      (∫ p : Ω × Ω, f p.1 * 1 - f p.1 * g p.2 ∂ν.prod ν) -
        ∫ p : Ω × Ω, (1 - G p.1 p.2) * h p.2 * f p.1 ∂ν.prod ν :=
    integral_sub ((hf.mul_prod (integrable_const 1)).sub (hf.mul_prod hg)) hi
  have hs₂ : (∫ p : Ω × Ω, f p.1 * 1 - f p.1 * g p.2 ∂ν.prod ν) =
      (∫ p : Ω × Ω, f p.1 * 1 ∂ν.prod ν) - ∫ p : Ω × Ω, f p.1 * g p.2 ∂ν.prod ν :=
    integral_sub (hf.mul_prod (integrable_const 1)) (hf.mul_prod hg)
  have hs₃ : (∫ p : Ω × Ω, f p.1 * 1 ∂ν.prod ν) =
      (∫ x, f x ∂ν) * ∫ _ : Ω, (1 : ℝ) ∂ν := integral_prod_mul f (fun _ : Ω => (1 : ℝ))
  rw [← pairing_one_indicator G hG hbound C hC, kernelPairing,
    integral_congr_ae heq, hs₁, hs₂, hs₃, integral_prod_mul]
  have hint (T : Set Ω) (hT : MeasurableSet T) :
      (∫ x, T.indicator (fun _ => (1 : ℝ)) x ∂ν) = ν.real T := by
    rw [integral_indicator hT, setIntegral_const, smul_eq_mul, mul_one]
  change (∫ x, f x ∂ν) * (∫ _ : Ω, (1 : ℝ) ∂ν) - (∫ x, f x ∂ν) * (∫ x, g x ∂ν) -
    kernelPairing (μ := ν) (fun x y => 1 - G x y) h f = _
  rw [show (∫ x, f x ∂ν) = ν.real C from hint C hC,
    show (∫ x, g x ∂ν) = ν.real P from hint P hP,
    pairing_indicator _ C D hC hD]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- On the original law, the whole source remainder joins every point
outside its own square and the old head. Source membership is constant
on each whole row fiber, so no same-label mass is lost outside the source. -/
theorem cusp_original_remainder_row_event (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ R.cuspSourceRemainder i → adjacencyKernel W p.1 p.2 =
      1 - {x | S.ρ x = r.val}.indicator (fun _ => 1) p.2 -
        (R.cuspSourceRemainder i).indicator (fun _ => 1) p.2 *
          (1 - adjacencyKernel W p.1 p.2) := by
  let : Countable S.I := S.hI.to_subtype
  have hf : ∀ᵐ x ∂μ, ∀ k : S.I, S.ρ x = k.val →
      (x ∈ R.cuspSource ↔ S.fiberCompulsoryPredicate k {r}) := by
    apply ae_all_iff.mpr
    intro k
    have h := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp
      (S.ae_compulsorySource_iff_fiberPredicate k {r} hW)
    simpa only [cuspSource, hr, mem_ofPred_eq] using h
  have hs := S.ae_collapsed_half_support hW hd hgap true
  rw [Measure.prod_restrict] at hs
  have hs := (ae_restrict_iff' ((S.measurableSet_half true).prod
    (S.measurableSet_half true))).mp hs
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hc] at hg
  filter_upwards [hs, hg.joined_CO, adjacencyKernel_symm W,
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC,
    Measure.quasiMeasurePreserving_fst.ae hf, Measure.quasiMeasurePreserving_snd.ae hf]
    with p hh hjoin hsym hz hfx hfy hx
  have hJnotP : p.2 ∈ R.cuspSourceRemainder i → S.ρ p.2 ≠ r.val :=
    fun hy hp => disjoint_left.mp hg.disjoint_IC hp hy.1
  by_cases hp : S.ρ p.2 = r.val
  · rw [indicator_of_mem (show p.2 ∈ {x | S.ρ x = r.val} from hp),
      indicator_of_notMem (fun hy => hJnotP hy hp),
      hsym.trans (hz hp hx.1)]
    norm_num
  · rw [indicator_of_notMem (show p.2 ∉ {x | S.ρ x = r.val} from hp)]
    by_cases hy : p.2 ∈ R.cuspSourceRemainder i
    · rw [indicator_of_mem hy]
      ring
    · rw [indicator_of_notMem hy]
      have hG : adjacencyKernel W p.1 p.2 = 1 := by
        by_cases hH : p.2 ∈ S.H
        · have hh := hh ⟨Or.inl hx.1.1, Or.inl hH⟩
          have hlabel : S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨
              S.collapsedPartLabel p.1 = none := by
            by_cases he : S.collapsedPartLabel p.1 = S.collapsedPartLabel p.2
            · right
              cases hl : S.collapsedPartLabel p.1 with
              | none => rfl
              | some k =>
                have hkx : S.ρ p.1 = k.val := by
                  have hm : p.1 ∈ S.collapsedPartLabel ⁻¹' {some k} := hl
                  rwa [S.collapsedPartLabel_fiber] at hm
                have hky : S.ρ p.2 = k.val := by
                  have hm : p.2 ∈ S.collapsedPartLabel ⁻¹' {some k} := he.symm.trans hl
                  rwa [S.collapsedPartLabel_fiber] at hm
                have hsrc := (hfy k hky).mpr ((hfx k hkx).mp hx.1)
                exact False.elim (hy ⟨hsrc, fun hi => hx.2 (hkx.trans (hky.symm.trans hi))⟩)
            · exact Or.inl he
          change adjacencyKernel W p.1 p.2 = _ at hh
          simpa only [ite_eq_left hlabel] using hh
        · exact hjoin hx.1 ⟨hH, hp⟩
      rw [hG]
      norm_num

/-- The exact original remainder degree integral, with the literal
original missing-square mass. No changed-law degree is substituted. -/
theorem cusp_original_adjacency_row_remainder (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    rowIntegral μ (adjacencyKernel W) (R.cuspSourceRemainder i) =
      μ.real (R.cuspSourceRemainder i) * (1 - S.originalAtomMass r) - R.cuspRemainderMissing i := by
  exact row_of_missing_block (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) _ _ _ (R.measurableSet_cuspSourceRemainder i)
    (S.hfibers r.val r.property).1 (R.measurableSet_cuspSourceRemainder i)
    (R.cusp_original_remainder_row_event r i hW hd hgap hr)

/-- The original whole-remainder missing mass is strictly below peak
mass times remainder mass. This uses the original strict atomic gap,
including every countable class and genuine dust. -/
theorem cusp_remainder_missing_lt_peak_mul_mass (R : S.ReverseRecovery) (i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hpos : 0 < μ.real (R.cuspSourceRemainder i)) :
    R.cuspRemainderMissing i < S.originalAtomMass i * μ.real (R.cuspSourceRemainder i) := by
  let J := R.cuspSourceRemainder i
  let A := S.originalAtomMass i
  have hJ : MeasurableSet J := R.measurableSet_cuspSourceRemainder i
  obtain ⟨hΔ, k, hA, _, hk, _, _, ⟨ε, hε, hεgap⟩, _⟩ :=
    S.exists_unique_largest_original_forward_peak hW hd hgap
  have hki : k = i := (hk S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst k
  let η := min ε (A / 2)
  have hη : 0 < η := lt_min hε (by dsimp [A]; positivity)
  have hcap : 0 ≤ A - η := by have := min_le_right ε (A / 2); dsimp [η]; linarith
  have hbound : ∀ k : S.I, k ≠ i → S.originalAtomMass k ≤ A - η := by
    intro k hki
    have h := hεgap k hki
    have he : η ≤ ε := min_le_left _ _
    change S.originalAtomMass k ≤ A - ε at h
    linarith
  have hs := S.ae_collapsed_half_support hW hd hgap true
  rw [Measure.prod_restrict] at hs
  have hs := (ae_restrict_iff' ((S.measurableSet_half true).prod
    (S.measurableSet_half true))).mp hs
  have hsJ : ∀ᵐ p ∂(μ.restrict J).prod (μ.restrict J),
      adjacencyKernel W p.1 p.2 =
        if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨
          S.collapsedPartLabel p.1 = none then 1 else 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hJ.prod hJ)).mpr
    exact hs.mono (fun _ hp hx => hp ⟨Or.inl hx.1.1.1, Or.inl hx.2.1.1⟩)
  have hrow : ∀ᵐ x ∂μ.restrict J,
      (∫ y in J, 1 - adjacencyKernel W x y ∂μ) ≤ A - η := by
    filter_upwards [ae_restrict_mem hJ, Measure.ae_ae_of_ae_prod hsJ] with x hx he
    cases hl : S.collapsedPartLabel x with
    | none =>
      have hz : (∫ y in J, 1 - adjacencyKernel W x y ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [he] with y hy
        rw [hy, hl]
        simp
      rw [hz]
      exact hcap
    | some k =>
      have hkx : S.ρ x = k.val := by
        have hm : x ∈ S.collapsedPartLabel ⁻¹' {some k} := hl
        rwa [S.collapsedPartLabel_fiber] at hm
      have hki : k ≠ i := by intro he; subst k; exact hx.2 hkx
      have hint : (∫ y in J, 1 - adjacencyKernel W x y ∂μ) =
          (μ.restrict J).real {y | S.ρ y = k.val} := by
        calc
          _ = ∫ y in J, {y | S.ρ y = k.val}.indicator (fun _ => (1 : ℝ)) y ∂μ := by
            apply integral_congr_ae
            filter_upwards [he] with y hy
            have hf : S.collapsedPartLabel y = some k ↔ S.ρ y = k.val := by
              change y ∈ S.collapsedPartLabel ⁻¹' {some k} ↔ _
              rw [S.collapsedPartLabel_fiber]
              rfl
            rw [hy, hl]
            by_cases hk : S.ρ y = k.val
            · rw [hf.mpr hk, indicator_of_mem (show y ∈ {y | S.ρ y = k.val} from hk)]
              norm_num
            · rw [indicator_of_notMem (show y ∉ {y | S.ρ y = k.val} from hk),
                ite_eq_left (Or.inl (Ne.symm (mt hf.mp hk)))]
              norm_num
          _ = _ := by rw [integral_indicator (S.hfibers k.val k.property).1,
            setIntegral_const, smul_eq_mul, mul_one]
      rw [hint]
      calc
        _ ≤ S.originalAtomMass k := by
          exact ENNReal.toReal_mono (measure_ne_top μ _) (Measure.restrict_le_self _)
        _ ≤ A - η := hbound k hki
  have hK : Integrable (fun p : Ω × Ω => 1 - adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
      simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
        (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
    exact (integrable_const 1).sub hG
  have hKJ : Integrable (fun p : Ω × Ω => 1 - adjacencyKernel W p.1 p.2)
      ((μ.restrict J).prod (μ.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hK.integrableOn
  have hle := integral_mono_ae hKJ.integral_prod_left (integrable_const (A - η)) hrow
  rw [← integral_prod _ hKJ, Measure.prod_restrict, integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ] at hle
  change R.cuspRemainderMissing i ≤ μ.real J * (A - η) at hle
  change R.cuspRemainderMissing i < A * μ.real J
  nlinarith [mul_pos hpos hη]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

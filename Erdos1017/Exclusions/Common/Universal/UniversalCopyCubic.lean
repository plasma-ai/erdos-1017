module

public import Erdos1017.Exclusions.Common.Universal.UniversalCopyBody

/-!
# Cubic copy inequality and trace on the positive body

The copied-row inequality dominates the positive-body composition, the
missing-body square energy retains the density and atom mass, and the positive
body satisfies the cubic copy inequality and the universal trace, a common
forward peak in the recovered plateau supplying its own premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual copied-row inequality dominates the actual positive-body
composition on one product-AE event. Signed old charges are only enlarged. -/
theorem ae_universal_positive_body_row (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
      {x | S.ρ x = r.val}
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      {x | S.ρ x = r.val}
    ∀ᵐ p ∂μ.prod μ, μ.real {x | S.ρ x = r.val} * (K p.1 p.2) ^ 2 +
      (2 * (c - m * d) + m) * K p.1 p.2 ≤
      K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
        KernelOperator.composedKernel (μ := μ) J K p.2 p.1) := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let K := IndependentAtomCopy.positiveBody Y I
  let J := IndependentAtomCopy.missingBody A I
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hI := (S.hfibers r.val r.property).1
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have huniv := S.neutral_atom_physical_adjacency r hW hd hgap hN
  have hreverse :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae huniv
  have hrows : ∀ᵐ x ∂μ, x ∉ I → ∀ᵐ z ∂μ, z ∈ I → A x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod hreverse] with x hx hxi
    filter_upwards [hx] with z hz hzi
    change PhysicalRepresentative.adjacency W m x z = true
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact (hz hzi).mpr hxi
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  filter_upwards [S.ae_universal_copy_inequality r hW hd hgap hN,
    Measure.quasiMeasurePreserving_fst.ae hrows, Measure.quasiMeasurePreserving_snd.ae hrows]
    with p hp hx hy
  change μ.real I * (K p.1 p.2) ^ 2 + (2 * (c - m * d) + m) * K p.1 p.2 ≤
    K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
      KernelOperator.composedKernel (μ := μ) J K p.2 p.1)
  by_cases hpos : 0 < K p.1 p.2
  · have hout : p.1 ∉ I ∧ p.2 ∉ I := by
      by_contra h
      simp [K, IndependentAtomCopy.positiveBody, h] at hpos
    have hKeq : K p.1 p.2 = Y p.1 p.2 := by
      have hmax : 0 < max (Y p.1 p.2) 0 := by
        simpa [K, IndependentAtomCopy.positiveBody, hout] using hpos
      have hypos : 0 < Y p.1 p.2 := by
        simpa only [lt_max_iff, lt_self_iff_false, or_false] using hmax
      simp [K, IndependentAtomCopy.positiveBody, hout, max_eq_left hypos.le]
    have hypos : 0 < Y p.1 p.2 := by rwa [hKeq] at hpos
    have hc := hp hout.1 hout.2 hypos
    have h₁ := IndependentAtomCopy.missing_integral_le_body_composed A hA Y hY I hI
      (PhysicalRepresentative.charge_bound W m) hY1 (PhysicalRepresentative.charge_symm W m)
      p.1 p.2 hout.1 hout.2 (hx hout.1)
    have h₂ := IndependentAtomCopy.missing_integral_le_body_composed A hA Y hY I hI
      (PhysicalRepresentative.charge_bound W m) hY1 (PhysicalRepresentative.charge_symm W m)
      p.2 p.1 hout.2 hout.1 (hy hout.2)
    have hmass : 0 ≤ μ.real (IndependentAtomCopy.missingSection A p.1 ∩
        IndependentAtomCopy.missingSection A p.2) := measureReal_nonneg
    have hbound : μ.real I * K p.1 p.2 + (2 * (c - m * d) + m) ≤
        KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
          KernelOperator.composedKernel (μ := μ) J K p.2 p.1 := by
      change μ.real I * Y p.1 p.2 + _ - m * μ.real _ ≤ _ at hc
      rw [hKeq]
      dsimp only [J, K] at *
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hm.le hmass]
    have h := mul_le_mul_of_nonneg_right hbound hpos.le
    nlinarith
  · have hzero : K p.1 p.2 = 0 := le_antisymm (le_of_not_gt hpos)
      (IndependentAtomCopy.positiveBody_mem Y I hY1 p.1 p.2).1
    rw [hzero]
    simp

/-- The actual outside missing-body square energy retains the original
density and original independent-atom mass. -/
theorem universal_missing_body_square_integral (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    (∫ p : Ω × Ω, (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      {x | S.ρ x = r.val} p.1 p.2) ^ 2 ∂μ.prod μ) =
        1 - 2 * d - (μ.real {x | S.ρ x = r.val}) ^ 2 := by
  have he := IndependentAtomCopy.missingBody_square_integral
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.measurable_adjacency W m)
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
    (S.neutral_atom_physical_adjacency r hW hd hgap hN)
    (PhysicalRepresentative.adjacency_symm W m)
  have hdensity := PhysicalRepresentative.density_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  rw [hW.density_eq] at hdensity
  unfold FiniteCappedSamplingCost.physicalDensity at hdensity
  linarith

/-- The actual selected positive body satisfies the cubic copy inequality;
all kernels and all copied-row premises are constructed from the same model. -/
theorem universal_positive_body_cubic (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
      {x | S.ρ x = r.val}
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      {x | S.ρ x = r.val}
    (μ.real {x | S.ρ x = r.val} + (2 * (c - m * d) + m)) *
      (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ≤
        2 * (∫ p : Ω × Ω, J p.1 p.2 *
          KernelOperator.composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ) := by
  let Y := PhysicalRepresentative.charge W m
  let A := PhysicalRepresentative.adjacency W m
  let I := {x | S.ρ x = r.val}
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  apply KernelOperator.integrated_copy_row_bound
    (IndependentAtomCopy.positiveBody Y I) (IndependentAtomCopy.missingBody A I)
    (IndependentAtomCopy.measurable_positiveBody Y (PhysicalRepresentative.measurable_charge W m)
      I (S.hfibers r.val r.property).1)
    (IndependentAtomCopy.measurable_missingBody A (PhysicalRepresentative.measurable_adjacency W m)
      I (S.hfibers r.val r.property).1)
    (IndependentAtomCopy.positiveBody_mem Y I hY1)
    (fun x y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem A I x y).1]
      exact (IndependentAtomCopy.missingBody_mem A I x y).2)
    (IndependentAtomCopy.positiveBody_symm Y I (PhysicalRepresentative.charge_symm W m))
    (μ.real I) (2 * (c - m * d) + m) (hW.strict_gap_structure hd hgap).gamma_pos.le
  exact S.ae_universal_positive_body_row r hW hd hgap hN

/-- The sharp universal trace is proved on the actual positive-body branch.
The zero-body branch is an explicitly separate physical argument. -/
theorem universal_positive_body_trace (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} p.1 p.2) ^ 2 ∂μ.prod μ) :
    3 * (μ.real {x | S.ρ x = r.val}) ^ 2 +
      2 * μ.real {x | S.ρ x = r.val} * (2 * (c - m * d) + m) +
      (2 * (c - m * d) + m) ^ 2 ≤ 2 * (1 - 2 * d) := by
  let Y := PhysicalRepresentative.charge W m
  let A := PhysicalRepresentative.adjacency W m
  let I := {x | S.ρ x = r.val}
  let K := IndependentAtomCopy.positiveBody Y I
  let J := IndependentAtomCopy.missingBody A I
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hgamma := (hW.strict_gap_structure hd hgap).gamma_pos
  have horth : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0 := by
    calc
      _ = ∫ _p : Ω × Ω, (0 : ℝ) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => IndependentAtomCopy.missingBody_positiveBody_mul
          A Y I (PhysicalRepresentative.charge_zero_of_nonedge W m) p.1 p.2)
      _ = 0 := integral_zero _ _
  have htrace := KernelOperator.copy_row_trace_bound K J
    (IndependentAtomCopy.measurable_positiveBody Y (PhysicalRepresentative.measurable_charge W m)
      I (S.hfibers r.val r.property).1)
    (IndependentAtomCopy.measurable_missingBody A (PhysicalRepresentative.measurable_adjacency W m)
      I (S.hfibers r.val r.property).1)
    (IndependentAtomCopy.positiveBody_mem Y I hY1)
    (fun x y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem A I x y).1]
      exact (IndependentAtomCopy.missingBody_mem A I x y).2)
    (IndependentAtomCopy.positiveBody_symm Y I (PhysicalRepresentative.charge_symm W m))
    (μ.real I) (2 * (c - m * d) + m) hgamma.le (by positivity) hpositive horth
    (S.ae_universal_positive_body_row r hW hd hgap hN)
  have hinventory := S.universal_missing_body_square_integral r hW hd hgap hN
  change (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) = 1 - 2 * d - (μ.real I) ^ 2
    at hinventory
  rw [hinventory] at htrace
  nlinarith

/-- An actual common forward peak lying in the recovered original plateau
supplies its own neutral/universal premise for the positive-body trace. -/
theorem ReverseRecovery.common_peak_head_positive_body_trace
    {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery)
    (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c r)
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} p.1 p.2) ^ 2 ∂μ.prod μ) :
    3 * (μ.real {x | S.ρ x = r.val}) ^ 2 +
      2 * μ.real {x | S.ρ x = r.val} * (2 * (c - m * d) + m) +
      (2 * (c - m * d) + m) ^ 2 ≤ 2 * (1 - 2 * d) :=
  S.universal_positive_body_trace r hW hd hgap (R.common_peak_head_neutral r hr hpeak) hpositive

end Erdos1017.CappedModel.SelectedHighLowStructure

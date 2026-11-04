module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceChild
public import Erdos1017.Exclusions.Cusp.SelectedCuspAdjacencyRows
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceCredits
public import Erdos1017.Exclusions.Cusp.CuspWholeSourceChildAccounting
public import Erdos1017.SelectedModel.Selection.FullReweightRows

/-!
# Charge rows of the partial cusp endpoint

The partial law keeps the original source restrictions, the signed
remainder-to-peak block and the whole remainder square, and its shifted and
charge rows follow from the original flat row, the complementary-flow pairing
and the current adjacency row, with no endpoint stationarity assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open WholeSourceChild KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private theorem pairing_indicator_row (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (f : Ω → ℝ) (hf : Integrable f μ) (C : Set Ω) (hC : MeasurableSet C) :
    kernelPairing (μ := μ) K f (C.indicator (fun _ => 1)) =
      ∫ x in C, applyKernel (μ := μ) K f x ∂μ := by
  rw [kernelPairing, integral_prod _
    (integrable_kernel_bilinear hK hB hf ((integrable_const 1).indicator hC)),
    ← integral_indicator hC]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    by_cases hx : x ∈ C <;> simp [hx, applyKernel])

private theorem pairing_add_left (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (f g h : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    kernelPairing (μ := μ) K (fun x => f x + g x) h =
      kernelPairing (μ := μ) K f h + kernelPairing (μ := μ) K g h := by
  unfold kernelPairing
  simp_rw [mul_add, add_mul]
  exact integral_add (integrable_kernel_bilinear hK hB hf hh)
    (integrable_kernel_bilinear hK hB hg hh)

private theorem charge_row_eq_shifted_add (V : Model Ω μ) (ell : ℝ)
    (C : Set Ω) (hC : MeasurableSet C) :
    rowIntegral μ (chargeKernel V) C = rowIntegral μ (shiftedKernel V ell) C +
      ell * rowIntegral μ (adjacencyKernel V) C := by
  have hi : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hC
  have hY := integrable_kernel_bilinear (chargeKernel_measurable V)
    (chargeKernel_bound V) (integrable_const (1 : ℝ)) hi
  have hG := integrable_kernel_bilinear (adjacencyKernel_measurable V)
    (adjacencyKernel_bound V) (integrable_const (1 : ℝ)) hi
  have hshift : kernelPairing (μ := μ) (shiftedKernel V ell)
      (fun _ => 1) (C.indicator (fun _ => 1)) =
      kernelPairing (μ := μ) (chargeKernel V) (fun _ => 1) (C.indicator (fun _ => 1)) -
        ell * kernelPairing (μ := μ) (adjacencyKernel V)
          (fun _ => 1) (C.indicator (fun _ => 1)) := by
    unfold kernelPairing
    have heq : (fun p : Ω × Ω => shiftedKernel V ell p.1 p.2 * 1 *
        C.indicator (fun _ => (1 : ℝ)) p.1) = fun p =>
        chargeKernel V p.1 p.2 * 1 * C.indicator (fun _ => (1 : ℝ)) p.1 -
          ell * (adjacencyKernel V p.1 p.2 * 1 * C.indicator (fun _ => (1 : ℝ)) p.1) := by
      funext p
      simp only [shiftedKernel, shiftedMoment_eq, chargeKernel, adjacencyKernel]
      ring
    rw [heq, integral_sub hY (hG.const_mul ell), integral_const_mul]
  rw [pairing_one_indicator _ (shiftedKernel_measurable V ell)
    (shiftedKernel_bound V ell) C hC,
    pairing_one_indicator _ (chargeKernel_measurable V) (chargeKernel_bound V) C hC,
    pairing_one_indicator _ (adjacencyKernel_measurable V) (adjacencyKernel_bound V) C hC]
    at hshift
  linarith

private theorem charge_cross_eq_shifted_add (V : Model Ω μ) (m : ℝ)
    (C D : Set Ω) :
    crossIntegral μ (chargeKernel V) C D = crossIntegral μ (shiftedKernel V m) C D +
      m * crossIntegral μ (adjacencyKernel V) C D := by
  have hM : Integrable (fun p : Ω × Ω => shiftedKernel V m p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear
      (shiftedKernel_measurable V m) (shiftedKernel_bound V m)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel V p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear
      (adjacencyKernel_measurable V) (adjacencyKernel_bound V)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have heq : (fun p : Ω × Ω => chargeKernel V p.1 p.2) =
      fun p => shiftedKernel V m p.1 p.2 + m * adjacencyKernel V p.1 p.2 := by
    funext p
    simp only [shiftedKernel, shiftedMoment_eq, chargeKernel, adjacencyKernel]
    ring
  rw [crossIntegral, heq, integral_add hM.integrableOn (hG.const_mul m).integrableOn,
    integral_const_mul]
  rfl

/-- Both source coordinates retain their actual original restrictions.
This identity preserves the entire signed remainder-to-peak block. -/
theorem cuspPartial_cross_remainder_peak (R : S.ReverseRecovery) (i : S.I)
    (K : Ω → Ω → ℝ) :
    crossIntegral R.cuspPartialLaw K (R.cuspSourceRemainder i) (R.cuspSourcePeak i) =
      crossIntegral μ K (R.cuspSourceRemainder i) (R.cuspSourcePeak i) := by
  let : IsProbabilityMeasure R.cuspPartialLaw := R.cuspPartialLaw_probability
  unfold crossIntegral
  rw [← Measure.prod_restrict, R.cuspPartialLaw_restrict_remainder i,
    R.cuspPartialLaw_restrict_peak i, Measure.prod_restrict]

/-- The actual partial law retains the whole original remainder square,
including its signed charge and genuine dust. -/
theorem cuspPartial_cross_remainder_remainder (R : S.ReverseRecovery) (i : S.I)
    (K : Ω → Ω → ℝ) :
    crossIntegral R.cuspPartialLaw K (R.cuspSourceRemainder i) (R.cuspSourceRemainder i) =
      crossIntegral μ K (R.cuspSourceRemainder i) (R.cuspSourceRemainder i) := by
  let : IsProbabilityMeasure R.cuspPartialLaw := R.cuspPartialLaw_probability
  unfold crossIntegral
  rw [← Measure.prod_restrict, R.cuspPartialLaw_restrict_remainder i, Measure.prod_restrict]

/-- The partial endpoint's shifted row is the original flat row plus
the actual complementary-flow pairing. No new stationarity is asserted. -/
theorem cuspPartial_shifted_row_total (R : S.ReverseRecovery)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (C : Set Ω) (hC : MeasurableSet C)
    (hkeep : R.cuspPartialLaw.restrict C = μ.restrict C) :
    rowIntegral R.cuspPartialLaw (shiftedKernel W m) C =
      2 * (c - m * d) * μ.real C +
        kernelPairing (μ := μ) (shiftedKernel W m)
          (MissingFlow.direction μ R.cuspPartialFlow) (C.indicator (fun _ => 1)) := by
  let v := MissingFlow.direction μ R.cuspPartialFlow
  have hv : Integrable v μ := MissingFlow.integrable_direction
    (MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable
      R.measurableSet_source.compl)
  have hbelow : ∀ᵐ x ∂μ, -1 ≤ v x := MissingFlow.direction_ge_neg_one
    (MissingFlow.nonnegative_sourceSlice R.isFullReverseFlow.nonnegative R.cuspSourceᶜ)
    (R.isFullReverseFlow.retained_supply_le_one R.cuspSource)
  have hw := integrableTiltWeight_integrable v hv 1
  have hw0 := integrableTiltWeight_nonnegative v hbelow 1 ⟨by norm_num, le_rfl⟩
  have hwfun : integrableTiltWeight v 1 = fun x => 1 + v x := by
    funext x
    simp only [integrableTiltWeight, one_mul]
  have hrow (x : Ω) : (∫ y, shiftedKernel W m x y ∂R.cuspPartialLaw) =
      applyKernel (μ := μ) (shiftedKernel W m) (fun y => 1 + v y) x := by
    change (∫ y, shiftedKernel W m x y ∂weightedMeasure (μ := μ)
      (integrableTiltWeight v 1)) = _
    simpa only [hwfun] using
      integral_weightedMeasure_eq_applyKernel (integrableTiltWeight v 1)
        hw.aestronglyMeasurable.aemeasurable hw0 (shiftedKernel W m) x
  have heq : rowIntegral R.cuspPartialLaw (shiftedKernel W m) C =
      kernelPairing (μ := μ) (shiftedKernel W m) (fun y => 1 + v y)
        (C.indicator (fun _ => 1)) := by
    unfold rowIntegral
    rw [hkeep]
    simp_rw [hrow]
    exact (pairing_indicator_row _ (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) _ ((integrable_const 1).add hv) C hC).symm
  rw [heq, pairing_add_left _ (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    (fun _ => 1) v _ (integrable_const 1) hv ((integrable_const 1).indicator hC),
    pairing_indicator_row _ (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
      (fun _ => 1) (integrable_const 1) C hC]
  have hflat : (∫ x in C, applyKernel (μ := μ) (shiftedKernel W m) (fun _ => 1) x ∂μ) =
      2 * (c - m * d) * μ.real C := by
    rw [integral_congr_ae (ae_restrict_of_ae (hW.stationary.mono (fun x hx => by
      simpa only [applyKernel, mul_one] using hx))), setIntegral_const, smul_eq_mul, mul_comm]
  rw [hflat]

/-- The actual current charge row follows from the original flat shifted
row and the actual current adjacency row. This is not endpoint stationarity. -/
theorem cuspPartial_charge_row_total (R : S.ReverseRecovery)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (C : Set Ω) (hC : MeasurableSet C)
    (hkeep : R.cuspPartialLaw.restrict C = μ.restrict C) :
    rowIntegral R.cuspPartialLaw (chargeKernel W) C =
      2 * (c - m * d) * μ.real C +
        kernelPairing (μ := μ) (shiftedKernel W m)
          (MissingFlow.direction μ R.cuspPartialFlow) (C.indicator (fun _ => 1)) +
        m * rowIntegral R.cuspPartialLaw (adjacencyKernel W) C := by
  let : IsProbabilityMeasure R.cuspPartialLaw := R.cuspPartialLaw_probability
  have h := charge_row_eq_shifted_add R.cuspPartialModel m C hC
  change rowIntegral R.cuspPartialLaw (chargeKernel W) C =
    rowIntegral R.cuspPartialLaw (shiftedKernel W m) C +
      m * rowIntegral R.cuspPartialLaw (adjacencyKernel W) C at h
  rw [R.cuspPartial_shifted_row_total hW C hC hkeep] at h
  exact h

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The current head charge row uses its original mass and the actual
complementary-flow mean, with no endpoint stationarity hypothesis. -/
theorem cuspPartial_charge_row_head (R : S.ReverseRecovery) (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    rowIntegral R.cuspPartialLaw (chargeKernel W) {x | S.ρ x = r.val} =
      S.originalAtomMass r * (2 * (c - m * d) + m +
        (-m) * (S.originalAtomMass r + μ.real R.cuspSource) + R.cuspFlowPeakMean r) := by
  have hb : S.originalAtomMass r ≠ 0 :=
    (ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top μ _)).ne'
  rw [R.cuspPartial_charge_row_total hW _ (S.hfibers r.val r.property).1
    (R.cuspPartialLaw_restrict_head r hW hr),
    R.cuspPartial_adjacency_row_head r hW hd hgap hr]
  change 2 * (c - m * d) * S.originalAtomMass r + _ + _ = _
  unfold cuspFlowPeakMean
  field_simp [hb]
  ring

/-- The current source-peak row retains the whole original peak mass
and subtracts its actual averaged source credit. -/
theorem cuspPartial_charge_row_peak (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    rowIntegral R.cuspPartialLaw (chargeKernel W) (R.cuspSourcePeak i) =
      S.originalAtomMass i * (2 * (c - m * d) + m +
        (-m) * (S.originalAtomMass r + S.originalAtomMass i) +
        R.cuspFlowPeakMean r - R.cuspPeakCredit r i) := by
  have hA : S.originalAtomMass i ≠ 0 :=
    (ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)).ne'
  rw [R.cuspPartial_charge_row_total hW _ (R.measurableSet_cuspSourcePeak i)
    (R.cuspPartialLaw_restrict_peak i), R.cuspSourcePeak_mass_original i hinside,
    R.cuspPartial_adjacency_row_peak r i hW hd hgap hr hinside]
  unfold cuspPeakCredit
  field_simp [hA]
  ring

/-- The whole current remainder row keeps its original missing integral
and the credit of the entire remaining source, including dust. -/
theorem cuspPartial_charge_row_remainder (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    rowIntegral R.cuspPartialLaw (chargeKernel W) (R.cuspSourceRemainder i) =
      μ.real (R.cuspSourceRemainder i) * (2 * (c - m * d) + m +
        (-m) * S.originalAtomMass r + R.cuspFlowPeakMean r) +
        (-m) * R.cuspRemainderMissing i - R.cuspRemainderCredit r i := by
  rw [R.cuspPartial_charge_row_total hW _ (R.measurableSet_cuspSourceRemainder i)
    (R.cuspPartialLaw_restrict_remainder i),
    R.cuspPartial_adjacency_row_remainder r i hW hd hgap hr]
  unfold cuspRemainderCredit
  ring

/-- The actual signed remainder-to-peak block is normalized by the
original whole peak mass, with the adjacency term retained exactly. -/
theorem cuspPartial_charge_cross_remainder_peak (R : S.ReverseRecovery) (r i : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    crossIntegral R.cuspPartialLaw (chargeKernel W)
      (R.cuspSourceRemainder i) (R.cuspSourcePeak i) =
        S.originalAtomMass i * (R.cuspCrossEnergy i -
          (-m) * μ.real (R.cuspSourceRemainder i)) := by
  let : IsProbabilityMeasure R.cuspPartialLaw := R.cuspPartialLaw_probability
  have hA : S.originalAtomMass i ≠ 0 :=
    (ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)).ne'
  have h := charge_cross_eq_shifted_add R.cuspPartialModel m
    (R.cuspSourceRemainder i) (R.cuspSourcePeak i)
  change crossIntegral R.cuspPartialLaw (chargeKernel W) _ _ =
    crossIntegral R.cuspPartialLaw (shiftedKernel W m) _ _ +
      m * crossIntegral R.cuspPartialLaw (adjacencyKernel W) _ _ at h
  rw [h, R.cuspPartial_cross_remainder_peak,
    R.cuspPartial_adjacency_cross_remainder_peak r i hW hd hgap hr hinside]
  unfold cuspCrossEnergy
  field_simp [hA]
  ring

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The whole current remainder square retains its exact signed charge.
There is no discarded internal term or separate energy estimate. -/
theorem cuspPartial_charge_cross_remainder_remainder (R : S.ReverseRecovery) (i : S.I) :
    crossIntegral R.cuspPartialLaw (chargeKernel W)
      (R.cuspSourceRemainder i) (R.cuspSourceRemainder i) =
        R.cuspRemainderEnergy i - (-m) *
          ((μ.real (R.cuspSourceRemainder i)) ^ 2 - R.cuspRemainderMissing i) := by
  let : IsProbabilityMeasure R.cuspPartialLaw := R.cuspPartialLaw_probability
  have h := charge_cross_eq_shifted_add R.cuspPartialModel m
    (R.cuspSourceRemainder i) (R.cuspSourceRemainder i)
  change crossIntegral R.cuspPartialLaw (chargeKernel W) _ _ =
    crossIntegral R.cuspPartialLaw (shiftedKernel W m) _ _ +
      m * crossIntegral R.cuspPartialLaw (adjacencyKernel W) _ _ at h
  rw [h, R.cuspPartial_cross_remainder_remainder,
    R.cuspPartial_adjacency_cross_remainder_remainder]
  unfold cuspRemainderEnergy
  ring

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

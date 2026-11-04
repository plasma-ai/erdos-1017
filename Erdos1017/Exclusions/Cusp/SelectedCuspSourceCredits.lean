module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceChild
public import Erdos1017.Exclusions.Cusp.CuspWholeSourceChildAccounting

/-!
# Credits and energies of the cusp source

The per-unit peak credit, the remainder credit and the partial-flow peak mean
are defined and shown nonnegative, as are the cross and remainder shifted
energies. The full-source mixed credit splits into peak and remainder credits,
and the unhalved full-flow energy keeps the partial energy, both mixed credits
and the entire original source energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The original recipient-fiber mean of the actual partial-flow shifted row. -/
def cuspFlowPeakMean (R : S.ReverseRecovery) (r : S.I) : ℝ :=
  kernelPairing (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
    ({x | S.ρ x = r.val}.indicator (fun _ => 1)) / S.originalAtomMass r

/-- The actual per-unit source-peak credit, under the original measure. -/
def cuspPeakCredit (R : S.ReverseRecovery) (r i : S.I) : ℝ :=
  R.cuspFlowPeakMean r -
    kernelPairing (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
      ((R.cuspSourcePeak i).indicator (fun _ => 1)) / S.originalAtomMass i

/-- The credit of the entire remaining source, including its original dust. -/
def cuspRemainderCredit (R : S.ReverseRecovery) (r i : S.I) : ℝ :=
  μ.real (R.cuspSourceRemainder i) * R.cuspFlowPeakMean r -
    kernelPairing (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
      ((R.cuspSourceRemainder i).indicator (fun _ => 1))

/-- The original source-peak/remainder cross energy, normalized by peak mass. -/
def cuspCrossEnergy (R : S.ReverseRecovery) (i : S.I) : ℝ :=
  WholeSourceChild.crossIntegral μ (shiftedKernel W m)
    (R.cuspSourceRemainder i) (R.cuspSourcePeak i) / S.originalAtomMass i

/-- The literal unhalved shifted energy of the entire original remainder. -/
def cuspRemainderEnergy (R : S.ReverseRecovery) (i : S.I) : ℝ :=
  WholeSourceChild.crossIntegral μ (shiftedKernel W m)
    (R.cuspSourceRemainder i) (R.cuspSourceRemainder i)

private theorem pairing_congr_right (K : Ω → Ω → ℝ) (f : Ω → ℝ)
    {g h : Ω → ℝ} (he : g =ᵐ[μ] h) :
    kernelPairing (μ := μ) K f g = kernelPairing (μ := μ) K f h := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae he] with p hp
  simp only [hp]

private theorem pairing_sourceDirection (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) (f : Ω → ℝ) (hf : Integrable f μ)
    (P T : Set Ω) (hP : MeasurableSet P) (hT : MeasurableSet T) :
    kernelPairing (μ := μ) K f (MissingFlow.OneCenter.sourceDirection μ P T) =
      μ.real T * (kernelPairing (μ := μ) K f (P.indicator (fun _ => 1)) / μ.real P) -
        kernelPairing (μ := μ) K f (T.indicator (fun _ => 1)) := by
  have he : (fun p : Ω × Ω => K p.1 p.2 * f p.2 *
      MissingFlow.OneCenter.sourceDirection μ P T p.1) =
      (fun p => (μ.real T / μ.real P) *
        (K p.1 p.2 * f p.2 * P.indicator (fun _ => 1) p.1) -
        K p.1 p.2 * f p.2 * T.indicator (fun _ => 1) p.1) := by
    funext p
    by_cases hp : p.1 ∈ P
    · simp only [MissingFlow.OneCenter.sourceDirection,
        MissingFlow.AtomicAssignment.recipientDensity, indicator_of_mem hp, mul_one]
      ring
    · simp [MissingFlow.OneCenter.sourceDirection,
        MissingFlow.AtomicAssignment.recipientDensity, hp]
  rw [kernelPairing, he, integral_sub
    ((integrable_kernel_bilinear hK hB hf ((integrable_const 1).indicator hP)).const_mul _)
    (integrable_kernel_bilinear hK hB hf ((integrable_const 1).indicator hT)), integral_const_mul]
  dsimp only [kernelPairing]
  ring

private theorem pairing_add_right (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) (f g h : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    kernelPairing (μ := μ) K f (fun x => g x + h x) =
      kernelPairing (μ := μ) K f g + kernelPairing (μ := μ) K f h := by
  have he : (fun p : Ω × Ω => K p.1 p.2 * f p.2 * (g p.1 + h p.1)) =
      (fun p => K p.1 p.2 * f p.2 * g p.1 + K p.1 p.2 * f p.2 * h p.1) := by
    funext p
    ring
  rw [kernelPairing, he, integral_add (integrable_kernel_bilinear hK hB hf hg)
    (integrable_kernel_bilinear hK hB hf hh)]
  rfl

private theorem integrable_partial_direction (R : S.ReverseRecovery) :
    Integrable (MissingFlow.direction μ R.cuspPartialFlow) μ :=
  MissingFlow.integrable_direction
    (MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable R.measurableSet_source.compl)

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Every measurable subregion of the entire singleton source has the
actual normalized recipient columns, with its literal original supply. -/
theorem cusp_source_subset_direction (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r : S.I) (hr : R.plateau = {r})
    (T : Set Ω) (hT : MeasurableSet T) (hTC : T ⊆ R.cuspSource) :
    MissingFlow.direction μ (MissingFlow.sourceSlice T R.flow) =ᵐ[μ]
      MissingFlow.OneCenter.sourceDirection μ {x | S.ρ x = r.val} T := by
  have hP := S.hfibers r.val r.property
  have hpos : 0 < μ.real {x | S.ρ x = r.val} :=
    ENNReal.toReal_pos hP.2.1.ne' (measure_ne_top μ _)
  apply MissingFlow.OneCenter.direction_sourceSlice hP.1 hpos hT
  have hfactor := R.sourceSlice_singleton hW r hr
  filter_upwards [hfactor] with p hp
  by_cases ht : p.2 ∈ T
  · have hc : p.2 ∈ S.reverseCompulsorySource {r} := by
      simpa only [cuspSource, hr] using hTC ht
    simpa only [MissingFlow.sourceSlice, ht, hc, ite_true,
      MissingFlow.OneCenter.sourceDensity, indicator_of_mem ht, indicator_of_mem hc] using hp
  · simp only [MissingFlow.sourceSlice, ht, ite_false, MissingFlow.OneCenter.sourceDensity,
      indicator_of_notMem ht, mul_zero]

/-- The genuine subflow mixed energy equals its original averaged credit. -/
theorem cusp_source_subset_pairing (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r : S.I) (hr : R.plateau = {r})
    (T : Set Ω) (hT : MeasurableSet T) (hTC : T ⊆ R.cuspSource) :
    kernelPairing (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
        (MissingFlow.direction μ (MissingFlow.sourceSlice T R.flow)) =
      μ.real T * R.cuspFlowPeakMean r -
        kernelPairing (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
          (T.indicator (fun _ => 1)) := by
  rw [pairing_congr_right _ _ (R.cusp_source_subset_direction hW r hr T hT hTC)]
  exact pairing_sourceDirection _ (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    _ R.integrable_partial_direction _ _ (S.hfibers r.val r.property).1 hT

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Nonnegative mutual energy applies to the actual two reverse subflows. -/
theorem cusp_source_subset_credit_nonnegative (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r})
    (T : Set Ω) (hT : MeasurableSet T) (hTC : T ⊆ R.cuspSource) :
    0 ≤ μ.real T * R.cuspFlowPeakMean r -
      kernelPairing (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
        (T.indicator (fun _ => 1)) := by
  rw [← R.cusp_source_subset_pairing hW r hr T hT hTC]
  exact hW.reverse_missing_flow_pairing_nonnegative hd hgap _ _
    (MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable R.measurableSet_source.compl)
    (MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable hT)
    (MissingFlow.nonnegative_sourceSlice R.isFullReverseFlow.nonnegative _)
    (MissingFlow.nonnegative_sourceSlice R.isFullReverseFlow.nonnegative _)
    (R.isFullReverseFlow.sourceSlice_oriented_support _)
    (R.isFullReverseFlow.sourceSlice_oriented_support _)

/-- The whole original peak fiber has nonnegative per-unit credit. -/
theorem cuspPeakCredit_nonnegative (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r i : S.I) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    0 ≤ R.cuspPeakCredit r i := by
  have h := R.cusp_source_subset_credit_nonnegative hW hd hgap r hr
    (R.cuspSourcePeak i) (R.measurableSet_cuspSourcePeak i) inter_subset_left
  rw [R.cuspSourcePeak_mass_original i hinside] at h
  have hpos : 0 < S.originalAtomMass i :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  dsimp only [cuspPeakCredit]
  exact sub_nonneg.mpr ((div_le_iff₀ hpos).mpr (by linarith))

/-- No atomicity or positive-mass condition is imposed on the remainder. -/
theorem cuspRemainderCredit_nonnegative (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r i : S.I) (hr : R.plateau = {r}) :
    0 ≤ R.cuspRemainderCredit r i :=
  R.cusp_source_subset_credit_nonnegative hW hd hgap r hr
    (R.cuspSourceRemainder i) (R.measurableSet_cuspSourceRemainder i) sdiff_subset

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Nonnegativity of the original shifted kernel pays the actual cross energy. -/
theorem cuspCrossEnergy_nonnegative (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (i : S.I) : 0 ≤ R.cuspCrossEnergy i := by
  apply div_nonneg _ (measureReal_nonneg : 0 ≤ S.originalAtomMass i)
  apply integral_nonneg_of_ae
  exact ae_restrict_of_ae (hW.moment_mem.mono (fun _ hx => hx.1))

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The entire original remainder, including dust, has nonnegative shifted energy. -/
theorem cuspRemainderEnergy_nonnegative (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (i : S.I) : 0 ≤ R.cuspRemainderEnergy i := by
  apply integral_nonneg_of_ae
  exact ae_restrict_of_ae (hW.moment_mem.mono (fun _ hx => hx.1))

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem cusp_source_indicator (R : S.ReverseRecovery) (i : S.I) :
    R.cuspSource.indicator (fun _ => (1 : ℝ)) =
      fun x => (R.cuspSourcePeak i).indicator (fun _ => 1) x +
        (R.cuspSourceRemainder i).indicator (fun _ => 1) x := by
  funext x
  by_cases hx : x ∈ R.cuspSource <;> by_cases hi : S.ρ x = i.val <;>
    simp [cuspSourcePeak, cuspSourceRemainder, hx, hi]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The actual full-source mixed credit is the sum of the peak and whole-remainder credits. -/
theorem cusp_source_credit_decomposition (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r i : S.I) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    kernelPairing (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
        (MissingFlow.direction μ (MissingFlow.sourceSlice R.cuspSource R.flow)) =
      S.originalAtomMass i * R.cuspPeakCredit r i + R.cuspRemainderCredit r i := by
  rw [R.cusp_source_subset_pairing hW r hr _ R.measurableSet_cuspSource Subset.rfl,
    R.cusp_source_indicator i, pairing_add_right _ (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) _ _ _ R.integrable_partial_direction
      ((integrable_const 1).indicator (R.measurableSet_cuspSourcePeak i))
      ((integrable_const 1).indicator (R.measurableSet_cuspSourceRemainder i))]
  have hm := R.cuspSource_mass_decomposition i
  rw [R.cuspSourcePeak_mass_original i hinside] at hm
  have hpos : 0 < S.originalAtomMass i :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  rw [← hm]
  dsimp only [cuspPeakCredit, cuspRemainderCredit]
  field_simp
  ring

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The original independent peak contributes no square term. The source
energy retains its cross term and the literal whole-remainder square. -/
theorem cusp_source_internal_energy (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (i : S.I) :
    WholeSourceChild.crossIntegral μ (shiftedKernel W m) R.cuspSource R.cuspSource =
      2 * S.originalAtomMass i * R.cuspCrossEnergy i + R.cuspRemainderEnergy i := by
  let K := shiftedKernel W m
  let f := (R.cuspSourcePeak i).indicator (fun _ => (1 : ℝ))
  let g := (R.cuspSourceRemainder i).indicator (fun _ => (1 : ℝ))
  have hf : Integrable f μ := (integrable_const 1).indicator (R.measurableSet_cuspSourcePeak i)
  have hg : Integrable g μ :=
    (integrable_const 1).indicator (R.measurableSet_cuspSourceRemainder i)
  have hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hx => hx.symm)
  have hff : kernelEnergy (μ := μ) K f = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hW.complementary, singleton_zero_II (S := S) i] with p hc hz
    change K p.1 p.2 * f p.2 * f p.1 = 0
    by_cases hx : p.1 ∈ R.cuspSourcePeak i
    · by_cases hy : p.2 ∈ R.cuspSourcePeak i
      · have hzero : K p.1 p.2 = 0 := by
          change (1 - adjacencyKernel W p.1 p.2) * K p.1 p.2 = 0 at hc
          simpa only [hz hx.2 hy.2, sub_zero, one_mul] using hc
        simp only [hzero, zero_mul]
      · simp [f, hy]
    · simp [f, hx]
  have he := kernelEnergy_sub_mul K (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) hsym f g hf hg (-1)
  have hfg : (fun x => f x - -1 * g x) = R.cuspSource.indicator (fun _ => 1) := by
    rw [R.cusp_source_indicator i]
    funext x
    dsimp [f, g]
    ring
  dsimp only [g] at he
  rw [hfg, hff, MissingFlow.OneCenter.energy_indicator K R.measurableSet_cuspSource,
    MissingFlow.OneCenter.energy_indicator K (R.measurableSet_cuspSourceRemainder i)] at he
  have hcross := WholeSourceChild.pairing_indicator (ν := μ) K _ _
    (R.measurableSet_cuspSourceRemainder i) (R.measurableSet_cuspSourcePeak i)
  change kernelPairing (μ := μ) K f g = _ at hcross
  rw [hcross] at he
  have hpos : 0 < S.originalAtomMass i :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  change _ = 2 * S.originalAtomMass i * (_ / S.originalAtomMass i) + _
  have hc : S.originalAtomMass i *
      (WholeSourceChild.crossIntegral μ K (R.cuspSourceRemainder i) (R.cuspSourcePeak i) /
        S.originalAtomMass i) =
      WholeSourceChild.crossIntegral μ K (R.cuspSourceRemainder i) (R.cuspSourcePeak i) := by
    field_simp
  rw [mul_assoc, hc]
  dsimp only [WholeSourceChild.crossIntegral, cuspRemainderEnergy, K] at he ⊢
  linarith

/-- The actual full-source flow pays exactly both original source energy terms. -/
theorem cusp_source_flow_energy (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r i : S.I) (hr : R.plateau = {r}) :
    kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice R.cuspSource R.flow)) =
      2 * S.originalAtomMass i * R.cuspCrossEnergy i + R.cuspRemainderEnergy i := by
  have h := R.singleton_source_energy hW hd hgap r hr
  have he : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← he] at h
  exact h.trans (R.cusp_source_internal_energy hW i)

/-- Exact unhalved full-flow accounting: partial energy, both mixed credits,
and the entire original source energy are retained. -/
theorem cusp_full_flow_energy (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r i : S.I) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) =
      kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow) +
        2 * (S.originalAtomMass i * R.cuspPeakCredit r i + R.cuspRemainderCredit r i) +
        2 * S.originalAtomMass i * R.cuspCrossEnergy i + R.cuspRemainderEnergy i := by
  let f := MissingFlow.direction μ R.cuspPartialFlow
  let g := MissingFlow.direction μ (MissingFlow.sourceSlice R.cuspSource R.flow)
  have hg : Integrable g μ := MissingFlow.integrable_direction
    (MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable R.measurableSet_cuspSource)
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hx => hx.symm)
  have hexpand := kernelEnergy_sub_mul (shiftedKernel W m) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) hsym f g R.integrable_partial_direction hg (-1)
  have he : kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) =
      kernelEnergy (μ := μ) (shiftedKernel W m) (fun x => f x - -1 * g x) := by
    apply integral_congr_ae
    have ha := MissingFlow.direction_sourceSlice_add_compl R.isFullReverseFlow.integrable
      R.measurableSet_cuspSource
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha,
      Measure.quasiMeasurePreserving_snd.ae ha] with p hp hq
    dsimp only [Pi.add_apply] at hp hq
    rw [hp, hq]
    dsimp [f, g, cuspPartialFlow]
    ring
  rw [he, hexpand]
  change _ = kernelEnergy (μ := μ) (shiftedKernel W m) f + _ + _ + _
  have hc := R.cusp_source_credit_decomposition hW r i hr hinside
  have hs := R.cusp_source_flow_energy hW hd hgap r i hr
  change kernelPairing (μ := μ) (shiftedKernel W m) f g = _ at hc
  change kernelEnergy (μ := μ) (shiftedKernel W m) g = _ at hs
  rw [hc, hs]
  ring

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

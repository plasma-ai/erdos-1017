module

public import Erdos1017.Exclusions.Common.TwoCenter.OneCenterSourceCredit
public import Erdos1017.Exclusions.Common.SelectedReverseSourceColumns
public import Erdos1017.Exclusions.Common.SelectedReverseSingletonGeometry

/-!
# Source credit of the selected singleton recovery

For the singleton recovery, the recovered height is the recipient mass plus the
whole source mass, the density drop between the endpoint models is the internal
edge mass of that source, and the one-center bound retains its internal shifted
energy and the partial-flow energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The entire original singleton source is measurable. -/
theorem singleton_measurableSet_source (R : S.ReverseRecovery) (r : S.I)
    (hr : R.plateau = {r}) : MeasurableSet (S.reverseCompulsorySource {r}) := by
  simpa only [hr] using R.measurableSet_source

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual recovered singleton height is its original recipient mass
plus its entire original source mass, including a null source. -/
theorem singleton_height_eq_mass_add_source (R : S.ReverseRecovery) (r : S.I)
    (hr : R.plateau = {r}) :
    R.height = μ.real {x | S.ρ x = r.val} + μ.real (S.reverseCompulsorySource {r}) := by
  have h := R.original_source_balance
  simpa only [hr, Finset.card_singleton, Nat.cast_one, one_mul, Finset.sum_singleton] using h

/-- The constructed physical singleton columns give the actual source
receipt-minus-supply direction; no factorization is an input. -/
theorem singleton_source_direction (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r : S.I) (hr : R.plateau = {r}) :
    MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource {r}) R.flow) =ᵐ[μ]
      MissingFlow.OneCenter.sourceDirection μ {x | S.ρ x = r.val} (S.reverseCompulsorySource {r}) := by
  have hI := S.hfibers r.val r.property
  have hIpos : 0 < μ.real {x | S.ρ x = r.val} :=
    ENNReal.toReal_pos hI.2.1.ne' (measure_ne_top μ _)
  exact MissingFlow.OneCenter.direction_sourceSlice hI.1 hIpos
    (R.singleton_measurableSet_source r hr) (R.sourceSlice_singleton hW r hr)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The same physical singleton source slice has exactly its original
internal shifted energy, with no supplied zero block or factorization. -/
theorem singleton_source_energy (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r}) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource {r}) R.flow)) =
      ∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
        shiftedKernel W m p.1 p.2 ∂μ.prod μ := by
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hII : ∀ᵐ p ∂μ.prod μ, p.1 ∈ {x | S.ρ x = r.val} → p.2 ∈ {x | S.ρ x = r.val} →
      shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hW.complementary, hg.zero_II] with p hc hz hx hy
    change (1 - adjacencyKernel W p.1 p.2) * shiftedKernel W m p.1 p.2 = 0 at hc
    simpa only [hz hx hy, sub_zero, one_mul] using hc
  have hIC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ {x | S.ρ x = r.val} → p.2 ∈ S.reverseCompulsorySource {r} →
      shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hW.complementary, hg.zero_IC] with p hc hz hx hy
    change (1 - adjacencyKernel W p.1 p.2) * shiftedKernel W m p.1 p.2 = 0 at hc
    simpa only [hz hx hy, sub_zero, one_mul] using hc
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hx => hx.symm)
  exact MissingFlow.OneCenter.energy_sourceSlice (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym hg.measurable_I hg.positive_I
    hg.measurable_C (R.sourceSlice_singleton hW r hr) hII hIC

/-- The actual full recovery retains both original energy credits in the
one-center case, including when the entire source has zero mass. -/
theorem singleton_energy_credits (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r}) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource {r})ᶜ R.flow)) +
      (∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
        shiftedKernel W m p.1 p.2 ∂μ.prod μ) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) := by
  have h := R.isFullReverseFlow.sourceSlice_energy_add_le hW hd hgap
    (R.singleton_measurableSet_source r hr)
  rw [R.singleton_source_energy hW hd hgap r hr] at h
  linarith

/-- The density difference of the two actual endpoint models is exactly
the original internal edge mass of the entire singleton source. -/
theorem singleton_density_drop (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r}) :
    density (R.isFullReverseFlow.retainedEndpoint (R.singleton_measurableSet_source r hr)) -
        density R.isFullReverseFlow.endpoint =
      (∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
        adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 := by
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  simp only [retainedWeight, hr] at hg
  have h := R.isFullReverseFlow.endpoint_density_eq_retained_sub hg (R.sourceSlice_singleton hW r hr)
  linarith

/-- The actual singleton recovery pays its source's original internal edges
and retains both source and partial-flow shifted-energy credits. -/
theorem singleton_credit (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r}) :
    c + (-m) * ((∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2) +
      (KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource {r})ᶜ R.flow)) +
          ∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
            shiftedKernel W m p.1 p.2 ∂μ.prod μ) / 2 ≤
      (μ.real {x | S.ρ x = r.val} + μ.real (S.reverseCompulsorySource {r})) ^ 2 := by
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  simp only [retainedWeight, hr] at hg
  have h := R.isFullReverseFlow.one_center_source_credit hW hd hgap (R.classMass_le hW) hg
    (R.sourceSlice_singleton hW r hr)
  rwa [R.singleton_height_eq_mass_add_source r hr] at h

/-- Dropping only the nonnegative partial-flow credit retains the entire
source's original internal shifted energy in the actual one-center bound. -/
theorem singleton_source_credit (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r}) :
    c + (-m) * ((∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2) +
      (∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
        shiftedKernel W m p.1 p.2 ∂μ.prod μ) / 2 ≤
      (μ.real {x | S.ρ x = r.val} + μ.real (S.reverseCompulsorySource {r})) ^ 2 := by
  have h := R.singleton_credit hW hd hgap r hr
  have hnonneg := R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap
    (R.singleton_measurableSet_source r hr).compl
  linarith

/-- Dropping only the nonnegative source self-energy retains the actual
partial-flow energy in the one-center bound. -/
theorem singleton_retained_credit (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r}) :
    c + (-m) * ((∫ p in (S.reverseCompulsorySource {r}) ×ˢ (S.reverseCompulsorySource {r}),
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2) +
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource {r})ᶜ R.flow)) / 2 ≤
      (μ.real {x | S.ρ x = r.val} + μ.real (S.reverseCompulsorySource {r})) ^ 2 := by
  have h := R.singleton_credit hW hd hgap r hr
  have hnonneg := R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap
    (R.singleton_measurableSet_source r hr)
  rw [R.singleton_source_energy hW hd hgap r hr] at hnonneg
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

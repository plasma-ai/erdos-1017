module

public import Erdos1017.Exclusions.Cusp.SelectedCuspPositiveSource
public import Erdos1017.Exclusions.Cusp.SelectedCuspAdjacencyRows
public import Erdos1017.Exclusions.Cusp.BenchmarkCuspRecoveryEnvelope

/-!
# Height, adjacency and budget of the cusp recovery

The capped endpoint and the same reverse budget force the recovery height above
the reciprocal cusp, the entire source adjacency is computed from the retained
peak and remainder, and endpoint collision with the original energy gives the
cusp source budget with the current outside squares.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator WholeSourceChild

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

private theorem cusp_value (k : ℕ) (hk : 4 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) :
    benchmark d = ((k : ℝ) - 1) / (k : ℝ) ^ 3 := by
  have hband : d ∈ Ioo (1 / 2 - Benchmark.epsilonStar) (1 / 2) := by
    rw [hdk]
    exact Benchmark.split_cusp_mem_band k (by omega)
  have hsqrt : Real.sqrt (1 - 2 * d) = 1 / (k : ℝ) := by
    rw [hdk]
    have he : 1 - 2 * ((1 - 1 / (k : ℝ) ^ 2) / 2) = (1 / (k : ℝ)) ^ 2 := by ring
    rw [he, Real.sqrt_sq (by positivity)]
  rw [(Benchmark.benchmark_split_eventually hband).eq_of_nhds, hsqrt]
  exact Benchmark.splitValue_reciprocal k (by omega)

/-- The actual capped endpoint and same reverse budget force its height
above the reciprocal cusp, without any assumption on the source edges. -/
theorem cusp_height_gt_reciprocal (R : S.ReverseRecovery) (k : ℕ) (hk : 4 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    1 / (k : ℝ) < R.height := by
  obtain ⟨hd, hslope, _, _, _⟩ := hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  obtain ⟨r, hr⟩ := R.cusp_plateau_singleton k hk hdk hW hgap hglobal
  by_contra hgt
  have hcap : R.height ≤ 1 / (k : ℝ) := le_of_not_gt hgt
  let ν := missingFlowEndpointLaw μ R.flow
  let := R.isFullReverseFlow.endpoint_probability
  let : NullSingletonClass ν := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hmass : MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = R.height :=
    (R.classMass_eq_iff hW r).mpr (by rw [hr]; exact Finset.mem_singleton_self r)
  have hcost := MultipartiteClassMasses.objective_le_cusp_cap R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [R.isFullReverseFlow.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp)
    r (hmass ▸ R.height_pos) (by
      intro j
      rw [hmass]
      exact R.classMass_le hW j) k hk (hmass ▸ hcap)
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have henergy := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hdrop := R.isFullReverseFlow.endpoint_density_lt hW hd hgap
  have hcredit := mul_pos (sub_pos.mpr hslope.1) (sub_pos.mpr hdrop)
  rw [cusp_value k hk hdk] at hgap
  rw [hdk] at hbudget hcredit
  nlinarith

/-- The entire source adjacency is computed from the literal retained
peak and remainder, including the same original qJ missing integral. -/
theorem cuspSource_adjacency_integral (R : S.ReverseRecovery) (r i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    (∫ p in R.cuspSource ×ˢ R.cuspSource, adjacencyKernel W p.1 p.2 ∂μ.prod μ) =
      (μ.real R.cuspSource) ^ 2 - (S.originalAtomMass i) ^ 2 - R.cuspRemainderMissing i := by
  let ν := R.cuspPartialLaw
  let := R.cuspPartialLaw_probability
  let I := R.cuspSourcePeak i
  let J := R.cuspSourceRemainder i
  let f := I.indicator (fun _ => (1 : ℝ))
  let g := J.indicator (fun _ => (1 : ℝ))
  have hI := R.measurableSet_cuspSourcePeak i
  have hJ := R.measurableSet_cuspSourceRemainder i
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have hz : kernelEnergy (μ := ν) (adjacencyKernel W) f = 0 := by
    have hzero : ∀ᵐ p ∂ν.prod ν, p.1 ∈ I → p.2 ∈ I → adjacencyKernel W p.1 p.2 = 0 := by
      filter_upwards [hac.ae_le (singleton_zero_II (S := S) i)] with p hp hx hy
      exact hp hx.2 hy.2
    have he := MissingFlow.OneCenter.pairing_eq_const_of_supported (μ := ν) (adjacencyKernel W) f f I I 0
      (Eventually.of_forall (fun _ hx => indicator_of_notMem hx _))
      (Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)) hzero
    simpa only [zero_mul, kernelEnergy, kernelPairing] using he
  have hcross : kernelPairing (μ := ν) (adjacencyKernel W) f g =
      S.originalAtomMass i * μ.real J := by
    rw [pairing_indicator _ J I hJ hI]
    exact R.cuspPartial_adjacency_cross_remainder_peak r i hW hd hgap hr hinside
  have hJJ : kernelEnergy (μ := ν) (adjacencyKernel W) g =
      (μ.real J) ^ 2 - R.cuspRemainderMissing i := by
    rw [MissingFlow.OneCenter.energy_indicator _ hJ]
    exact R.cuspPartial_adjacency_cross_remainder_remainder i
  have hsum : R.cuspSource.indicator (fun _ => (1 : ℝ)) = fun x => f x + g x := by
    funext x
    by_cases hc : x ∈ R.cuspSource <;> by_cases hi : S.ρ x = i.val <;>
      simp [I, J, f, g, cuspSourcePeak, cuspSourceRemainder, hc, hi]
  have he := kernelEnergy_sub_mul (adjacencyKernel W) ((adjacencyKernel_measurable W).mono_ac hac)
    (hac.ae_le (adjacencyKernel_bound W)) (hac.ae_le (adjacencyKernel_symm W)) f g
    ((integrable_const 1).indicator hI) ((integrable_const 1).indicator hJ) (-1)
  simp only [neg_mul, one_mul, sub_neg_eq_add, neg_sq, one_pow] at he
  rw [← hsum, hz, hcross, hJJ, MissingFlow.OneCenter.energy_indicator _ R.measurableSet_cuspSource] at he
  have hkeep : (∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂ν.prod ν) =
      ∫ p in R.cuspSource ×ˢ R.cuspSource, adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
    rw [← Measure.prod_restrict, R.cuspPartialLaw_restrict_source, Measure.prod_restrict]
  rw [hkeep] at he
  have hmass := R.cuspSource_mass_decomposition i
  rw [R.cuspSourcePeak_mass_original i hinside] at hmass
  change S.originalAtomMass i + μ.real J = μ.real R.cuspSource at hmass
  rw [← hmass]
  nlinarith only [he]

/-- The full endpoint missing density uses the same current outside
class-square sum as the whole-source child. -/
theorem cuspEndpoint_missing_eq (R : S.ReverseRecovery) (r i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    1 - 2 * density R.isFullReverseFlow.endpoint = R.height ^ 2 + R.cuspOutsideSquares r i := by
  have hpartial := R.cuspPartialLaw_missing_density r i hW hd hgap hr hinside
  have hsource := R.cuspSource_adjacency_integral r i hW hd hgap hr hinside
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  rw [← hSource] at hg
  have hf : MissingFlow.sourceSlice R.cuspSource R.flow =ᵐ[μ.prod μ]
      MissingFlow.OneCenter.sourceDensity μ {x | S.ρ x = r.val} R.cuspSource := by
    filter_upwards [R.sourceSlice_singleton hW r hr] with p hp
    change MissingFlow.sourceSlice R.cuspSource R.flow p =
      MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} p.1 *
        R.cuspSource.indicator (fun _ => 1) p.2
    simpa only [hSource] using hp
  have hdrop : density R.cuspPartialModel - density R.isFullReverseFlow.endpoint =
      (∫ p in R.cuspSource ×ˢ R.cuspSource, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 := by
    have he := R.isFullReverseFlow.endpoint_density_eq_retained_sub (C := R.cuspSource) hg hf
    change density R.isFullReverseFlow.endpoint = density R.cuspPartialModel - _ at he
    linarith
  rw [hsource] at hdrop
  have hheight := R.singleton_height_eq_mass_add_source r hr
  rw [← hSource] at hheight
  change R.height = S.originalAtomMass r + μ.real R.cuspSource at hheight
  rw [hheight]
  nlinarith only [hpartial, hdrop]

/-- Actual endpoint collision and original energy give the source budget
with the literal current outside squares. This holds already for k≥4. -/
theorem cusp_endpoint_source_budget (R : S.ReverseRecovery) (r i : S.I)
    (k : ℕ) (hk : 4 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    c - ((k : ℝ) - 1) / (k : ℝ) ^ 3 +
        kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) / 2 +
        (-m - 1) * R.cuspOutsideSquares r i / 2 ≤
      (2 - 2 / (k : ℝ) + m) * (R.height ^ 2 - 1 / (k : ℝ) ^ 2) / 2 := by
  have hd := (hW.cusp_contact_parameters k (by omega) hdk hgap hglobal).1
  let ν := missingFlowEndpointLaw μ R.flow
  let := R.isFullReverseFlow.endpoint_probability
  let : NullSingletonClass ν := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hmass : MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = R.height :=
    (R.classMass_eq_iff hW r).mpr (by rw [hr]; exact Finset.mem_singleton_self r)
  have hcost := MultipartiteClassMasses.objective_le_split_add_tail R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [R.isFullReverseFlow.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp)
    r (hmass ▸ R.height_pos) (by
      intro j
      rw [hmass]
      exact R.classMass_le hW j)
  rw [hmass, R.cuspEndpoint_missing_eq r i hW hd hgap hr hinside] at hcost
  have hcurve := Benchmark.splitValue_le_reciprocal_mass_cap k (by omega)
    (R.cusp_height_gt_reciprocal k hk hdk hW hgap hglobal).le
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  rw [hdk, R.cuspEndpoint_missing_eq r i hW hd hgap hr hinside] at hbudget
  have hid : ((k : ℝ) - 1) / (k : ℝ) ^ 3 = (1 - 1 / (k : ℝ)) / (k : ℝ) ^ 2 := by
    field_simp
  rw [hid]
  linear_combination hcost + hcurve + hbudget / 2

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

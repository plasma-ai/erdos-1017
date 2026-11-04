module

public import Erdos1017.Exclusions.Cusp.SelectedCuspRecoveryBounds

/-!
# Whole-source inventory of the full cusp endpoint

The current outside squares `cuspWholeOutsideSquares` depend only on the head
and the entire source, every source cut gives the same value, and the full
endpoint inventory and full-flow source budget hold without any original peak
being contained in the compulsory source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator WholeSourceChild

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- Current outside squares depend on the head and entire source only. -/
def cuspWholeOutsideSquares (R : S.ReverseRecovery) (r : S.I) : ℝ :=
  ∑' j : S.I, (R.cuspPartialLaw.real ((S.collapsedPartLabel ⁻¹' {some j}) \
    ({x | S.ρ x = r.val} ∪ R.cuspSource))) ^ 2

/-- Every literal source cut gives the same whole-source outside squares,
without any containment assumption on the original atom used to cut it. -/
theorem cuspOutsideSquares_eq_whole (R : S.ReverseRecovery) (r i : S.I) :
    R.cuspOutsideSquares r i = R.cuspWholeOutsideSquares r := by
  apply tsum_congr
  intro j
  congr 2
  ext x
  simp only [outsideClass, Set.mem_sdiff, mem_preimage, mem_singleton_iff, mem_union,
    cuspSourcePeak, cuspSourceRemainder, mem_inter_iff, mem_ofPred_eq]
  tauto

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The current partial and full endpoint laws agree off the retained head
and entire source, by their actual complementary source directions. -/
theorem cuspEndpoint_restrict_outside (R : S.ReverseRecovery) (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hr : R.plateau = {r}) :
    (missingFlowEndpointLaw μ R.flow).restrict ({x | S.ρ x = r.val} ∪ R.cuspSource)ᶜ =
      R.cuspPartialLaw.restrict ({x | S.ρ x = r.val} ∪ R.cuspSource)ᶜ := by
  have hO : MeasurableSet ({x | S.ρ x = r.val} ∪ R.cuspSource)ᶜ :=
    ((S.hfibers r.val r.property).1.union R.measurableSet_cuspSource).compl
  change (μ.withDensity (fun x => ENNReal.ofReal (integrableTiltWeight
      (MissingFlow.direction μ R.flow) 1 x))).restrict _ =
    (μ.withDensity (fun x => ENNReal.ofReal (R.retainedWeight x))).restrict _
  rw [restrict_withDensity hO, restrict_withDensity hO]
  apply withDensity_congr_ae
  apply (ae_restrict_iff' hO).mpr
  have hd := MissingFlow.direction_sourceSlice_add_compl R.isFullReverseFlow.integrable R.measurableSet_cuspSource
  have hs := R.singleton_source_direction hW r hr
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hSource] at hs
  filter_upwards [hd, hs] with x hx hsx ho
  have hnP : x ∉ {x | S.ρ x = r.val} := fun h => ho (Or.inl h)
  have hnS : x ∉ R.cuspSource := fun h => ho (Or.inr h)
  have hzero : MissingFlow.direction μ (MissingFlow.sourceSlice R.cuspSource R.flow) x = 0 := by
    rw [hsx]
    simp only [MissingFlow.OneCenter.sourceDirection, MissingFlow.AtomicAssignment.recipientDensity,
      indicator_of_notMem hnP, indicator_of_notMem hnS, mul_zero, sub_self]
  simp only [Pi.add_apply] at hx
  rw [hzero, zero_add] at hx
  simp only [integrableTiltWeight, one_mul, retainedWeight]
  rw [hx]
  rfl

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Actual full HIGH supply removes the entire compulsory source under
the full endpoint law, including its original diffuse points. -/
theorem cuspEndpoint_source_null (R : S.ReverseRecovery) :
    (missingFlowEndpointLaw μ R.flow) R.cuspSource = 0 := by
  let := R.isFullReverseFlow.endpoint_probability
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  apply MissingFlow.endpoint_real_set_eq_zero R.flow R.isFullReverseFlow.integrable
    R.isFullReverseFlow.nonnegative R.isFullReverseFlow.supply_le_one _ R.measurableSet_cuspSource
  filter_upwards [R.isFullReverseFlow.endpoint_removes_high] with x hx hs
  exact hx hs.1

/-- Every non-head full endpoint class has exactly its current outside
mass; the original source is genuinely removed rather than identified
with an endpoint atom. -/
theorem cuspEndpoint_classMass_eq_outside (R : S.ReverseRecovery) (r j : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hr : R.plateau = {r}) (hjr : j ≠ r) :
    S.reverseClassMass R.flow j = R.cuspPartialLaw.real
      ((S.collapsedPartLabel ⁻¹' {some j}) \
        ({x | S.ρ x = r.val} ∪ R.cuspSource)) := by
  let C := S.collapsedPartLabel ⁻¹' {some j}
  let O := ({x | S.ρ x = r.val} ∪ R.cuspSource)ᶜ
  have hC : MeasurableSet C := S.measurable_collapsedPartLabel (measurableSet_singleton (some j))
  have hkeep := congrArg (fun ν : Measure Ω => ν.real C) (R.cuspEndpoint_restrict_outside r hW hr)
  rw [measureReal_restrict_apply hC, measureReal_restrict_apply hC] at hkeep
  have hcut : S.reverseClassMass R.flow j =
      (missingFlowEndpointLaw μ R.flow).real (C ∩ O) := by
    apply measureReal_congr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp R.cuspEndpoint_source_null] with x hx
    apply propext
    change (S.collapsedPartLabel x = some j) ↔ (S.collapsedPartLabel x = some j ∧ x ∈ O)
    constructor
    · intro hj
      refine ⟨hj, ?_⟩
      rintro (hp | hs)
      · have hf : x ∈ S.collapsedPartLabel ⁻¹' {some r} := by
          rw [S.collapsedPartLabel_fiber]
          exact hp
        exact hjr (Option.some_injective _ (hj.symm.trans hf))
      · exact hx hs
    · exact And.left
  rw [hcut]
  exact hkeep

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The actual full endpoint inventory holds without any original peak
being contained in the compulsory source. -/
theorem cuspEndpoint_missing_eq_whole (R : S.ReverseRecovery) (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    1 - 2 * density R.isFullReverseFlow.endpoint = R.height ^ 2 + R.cuspWholeOutsideSquares r := by
  have hmissing := R.isFullReverseFlow.missing_density_eq_classMass_sq hW hd hgap
  have hsplit := R.isFullReverseFlow.classMass_sq_summable.tsum_eq_add_tsum_ite r
  have hhead := (R.classMass_eq_iff hW r).mpr (by rw [hr]; exact Finset.mem_singleton_self r)
  rw [hmissing, hsplit, hhead]
  congr 1
  apply tsum_congr
  intro j
  by_cases hj : j = r
  · subst j
    rw [ite_eq_left rfl]
    have he : ((S.collapsedPartLabel ⁻¹' {some r}) \
        ({x | S.ρ x = r.val} ∪ R.cuspSource)) = ∅ := by
      rw [S.collapsedPartLabel_fiber]
      exact sdiff_eq_empty.mpr subset_union_left
    rw [he, measureReal_empty]
    norm_num
  · rw [ite_eq_right hj, R.cuspEndpoint_classMass_eq_outside r j hW hr hj]

/-- The whole-source inventory pays the actual full-flow source budget
without containment of any original peak in that source. -/
theorem cusp_endpoint_source_budget_whole (R : S.ReverseRecovery) (r : S.I)
    {d c : ℝ} (k : ℕ) (hk : 4 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r}) :
    c - ((k : ℝ) - 1) / (k : ℝ) ^ 3 +
        kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) / 2 +
        (-m - 1) * R.cuspWholeOutsideSquares r / 2 ≤
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
  rw [hmass, R.cuspEndpoint_missing_eq_whole r hW hd hgap hr] at hcost
  have hcurve := Benchmark.splitValue_le_reciprocal_mass_cap k (by omega)
    (R.cusp_height_gt_reciprocal k hk hdk hW hgap hglobal).le
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  rw [hdk, R.cuspEndpoint_missing_eq_whole r hW hd hgap hr] at hbudget
  have hid : ((k : ℝ) - 1) / (k : ℝ) ^ 3 = (1 - 1 / (k : ℝ)) / (k : ℝ) ^ 2 := by
    field_simp
  rw [hid]
  linear_combination hcost + hcurve + hbudget / 2

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

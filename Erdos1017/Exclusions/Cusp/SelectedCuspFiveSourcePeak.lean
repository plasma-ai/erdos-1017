module

public import Erdos1017.Exclusions.Cusp.SelectedCuspFiveBounds
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceScore
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceTangent
public import Erdos1017.Exclusions.Cusp.CuspFiveSourcePeakPayment

/-!
# No source peak at the fifth cusp

At the fifth reciprocal cusp, the original common peak cannot lie in the entire
source of its singleton reverse recovery, using the correlated tangent and the
original head bound (`no_cusp_five_source_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- At the fifth reciprocal cusp, the original common peak cannot lie in
the entire source of its singleton reverse recovery. The correlated tangent,
original head bound, child score and shared budget are derived internally. -/
theorem no_cusp_five_source_peak (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 12 / 25) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) : False := by
  let e := c - (1 - 1 / 5 : ℝ) * (1 / 5 : ℝ) ^ 2
  let b := S.originalAtomMass r
  let A := S.originalAtomMass i
  let z := μ.real (R.cuspSourceRemainder i)
  have hdk' : d = (1 - 1 / (5 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  have hparameters := hW.cusp_contact_parameters 5 (by norm_num) hdk' hgap hglobal
  have hd := hparameters.1
  have hell : -m ∈ Ioo (19 / 15 : ℝ) (8 / 5) := by
    norm_num at hparameters
    exact hparameters.2.1
  have hmissing : 1 - 2 * d = (1 / 5 : ℝ) ^ 2 := by norm_num [hdk]
  have hvalue : c = (1 - 1 / 5 : ℝ) * (1 / 5 : ℝ) ^ 2 + e := by dsimp [e]; ring
  have hmargin := hparameters.2.2.2.2
  have he : 0 < e := by
    dsimp [e]
    norm_num at hmargin
    rw [hdk] at hmargin
    linarith only [hmargin]
  have hsourceEdge := R.cusp_source_edge_integral_pos 5 (by norm_num) hdk' hW hgap hglobal
  change 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
    adjacencyKernel W p.1 p.2 ∂μ.prod μ at hsourceEdge
  have hA : 0 < A := ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne'
    (measure_ne_top μ _)
  have hz : 0 < z := R.cuspSourceRemainder_mass_pos i hsourceEdge
  have hs : A + z = μ.real R.cuspSource := by
    have h := R.cuspSource_mass_decomposition i
    rw [R.cuspSourcePeak_mass_original i hinside] at h
    exact h
  have hheight : b + A + z = R.height := by
    have h := R.singleton_height_eq_mass_add_source r hr
    have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
    rw [← hc] at h
    change R.height = b + μ.real R.cuspSource at h
    linarith only [h, hs]
  obtain ⟨_, hone, htwo⟩ := R.cusp_five_endpoint_bounds hdk hW hgap hglobal
  obtain ⟨_, hsquare, hreserve⟩ :=
    R.cusp_source_peak_guards r i 5 (by norm_num) hdk' hW hgap hglobal hr hinside hpeak
  have hsquare' : (A + b) ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    simpa only [A, b, add_comm, Nat.cast_ofNat, one_div_pow] using hsquare
  have hreserve' : (8 / 5 - (-m)) * (1 / 5 : ℝ) ^ 2 < (2 - (-m)) * A ^ 2 := by
    convert hreserve using 1 <;> dsimp [A] <;> norm_num
    ring
  have hheadSq :=
    R.cusp_source_head_sq_bound r i 5 (by norm_num) hdk' hW hgap hglobal hr hinside hpeak
  have hhead : b < A / 2 := by
    change ((5 : ℝ) - 1) * b ^ 2 < A ^ 2 at hheadSq
    nlinarith only [hheadSq, hA, sq_nonneg (b - A / 2)]
  have htrace := R.cusp_source_tangent_energy_le r i hW hd hgap hr hinside hsourceEdge
  rw [← hs] at htrace
  have hV := R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap
    R.measurableSet_source.compl
  change 0 ≤ kernelEnergy (μ := μ) (shiftedKernel W m)
    (MissingFlow.direction μ R.cuspPartialFlow) at hV
  have hQO : 0 ≤ R.cuspOutsideSquares r i := tsum_nonneg (fun _ => sq_nonneg _)
  have hE := R.cusp_full_flow_energy hW hd hgap r i hr hinside
  have hbudget :=
    R.cusp_endpoint_source_budget r i 5 (by norm_num) hdk' hW hgap hglobal hr hinside
  rw [← hheight] at hbudget
  obtain ⟨child, _, hcost, hscore⟩ :=
    R.exists_cusp_source_child_score r i hW hd hgap hr hmissing hvalue hinside hsourceEdge
  apply CuspFiveSourcePeakPayment.source_peak_false
    (ell := -m) (e := e) (b := b) (A := A) (z := z)
    (E := kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow))
    (V := kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow))
    (cI := R.cuspPeakCredit r i) (CJ := R.cuspRemainderCredit r i)
    (Phi := R.cuspCrossEnergy i) (FJ := R.cuspRemainderEnergy i)
    (QO := R.cuspOutsideSquares r i) (child := objective child)
    (r := R.height / 2)
    hell he hV measureReal_nonneg hA hz
    (R.cuspPeakCredit_nonnegative hW hd hgap r i hr hinside)
    (R.cuspRemainderCredit_nonnegative hW hd hgap r i hr)
    (R.cuspCrossEnergy_nonnegative hW i) (R.cuspRemainderEnergy_nonnegative hW i)
    hQO (by rw [hheight]) (by rwa [hheight]) (by rwa [hheight])
    hsquare' hhead hreserve' htrace
    (by dsimp [A]; linear_combination hE)
    (by convert hbudget using 1 <;> dsimp [e] <;> norm_num)
    (by simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hcost)
  convert hscore using 1 <;>
    simp only [hheight, b, A, z, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
  ring

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

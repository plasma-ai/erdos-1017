module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourcePeakGuards
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceScore
public import Erdos1017.Exclusions.Cusp.SelectedCuspRemainderEnergy
public import Erdos1017.Exclusions.Cusp.SelectedCuspEndpointRange
public import Erdos1017.Exclusions.Cusp.CuspSourcePeakPayment

/-!
# No source peak at cusps with at least six parts

At every reciprocal cusp with at least six parts, the original common peak
cannot lie in the entire source of its singleton reverse recovery
(`no_cusp_source_peak`).
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

/-- At every reciprocal cusp with at least six parts, the actual original
common peak cannot lie in the entire source of its singleton reverse recovery.
The child, all four source resources, the trace cap and both endpoint bounds
are derived from that same model. -/
theorem no_cusp_source_peak (R : S.ReverseRecovery) (r i : S.I)
    (k : ℕ) (hk : 6 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) : False := by
  let a : ℝ := 1 / (k : ℝ)
  let e := c - (1 - a) * a ^ 2
  let b := S.originalAtomMass r
  let A := S.originalAtomMass i
  let z := μ.real (R.cuspSourceRemainder i)
  have hparameters := hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  have hd := hparameters.1
  obtain ⟨ha, hell, hdelta, hrho⟩ := CuspSourcePeakPayment.slope_constants hk hparameters.2.1
  have hmissing : 1 - 2 * d = a ^ 2 := by dsimp [a]; rw [hdk]; ring
  have hvalue : c = (1 - a) * a ^ 2 + e := by dsimp [e]; ring
  have hmargin : (2 - 2 * a + m) * a ^ 2 < 2 * (c - m * d) + m := by
    convert hparameters.2.2.2.2 using 1
    dsimp [a]
    ring
  have he : 0 < e := by
    have hid : 2 * (c - m * d) + m - (2 - 2 * a + m) * a ^ 2 = 2 * e := by
      dsimp [e]
      linear_combination m * hmissing
    linarith only [hmargin, hid]
  have hsourceEdge := R.cusp_source_edge_integral_pos k (by omega) hdk hW hgap hglobal
  change 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
    adjacencyKernel W p.1 p.2 ∂μ.prod μ at hsourceEdge
  have hA : 0 < A := ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne'
    (measure_ne_top μ _)
  obtain ⟨hz, htrace, htraceStrict⟩ :=
    R.cuspRemainderEnergy_bound_of_positive_source hW hd hgap i hsourceEdge hell hparameters.2.2.1.2.le
  change 0 < z at hz
  have htraceCap : R.cuspRemainderEnergy i ≤ (-m + 1 / 50) * z ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hz)).mp (htrace.trans htraceStrict.le)
  have hheight : b + A + z = R.height := by
    have h := R.singleton_height_eq_mass_add_source r hr
    have hs := R.cuspSource_mass_decomposition i
    rw [R.cuspSourcePeak_mass_original i hinside] at hs
    have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
    rw [← hc] at h
    change R.height = b + μ.real R.cuspSource at h
    change A + z = μ.real R.cuspSource at hs
    linarith only [h, hs]
  have hrange := R.cusp_endpoint_normalized_range k hk hdk hW hgap hglobal
  have htwo : b + A + z ≤ 2 * a := by
    rw [hheight]
    simpa only [a, div_eq_mul_inv, one_mul] using hrange.2.2.2.1.le
  obtain ⟨hhead, hsquare, hreserve⟩ :=
    R.cusp_source_peak_guards r i k (by omega) hdk hW hgap hglobal hr hinside hpeak
  have hsquare' : (A + b) ^ 2 ≤ a ^ 2 := by
    simpa only [A, b, a, add_comm, one_div_pow] using hsquare
  have hreserve' : (2 - 2 * a - (-m)) * a ^ 2 ≤ (2 - (-m)) * A ^ 2 := by
    convert hreserve.le using 1 <;> dsimp [a, A] <;> ring
  have hV := R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap
    R.measurableSet_source.compl
  change 0 ≤ kernelEnergy (μ := μ) (shiftedKernel W m)
    (MissingFlow.direction μ R.cuspPartialFlow) at hV
  have hQO : 0 ≤ R.cuspOutsideSquares r i := by
    exact tsum_nonneg (fun _ => sq_nonneg _)
  have hE := R.cusp_full_flow_energy hW hd hgap r i hr hinside
  have hbudget := R.cusp_endpoint_source_budget r i k (by omega) hdk hW hgap hglobal hr hinside
  have hcusp : ((k : ℝ) - 1) / (k : ℝ) ^ 3 = (1 - a) * a ^ 2 := by
    dsimp [a]
    field_simp
  rw [hcusp, ← hheight] at hbudget
  obtain ⟨child, _, hcost, hscore⟩ :=
    R.exists_cusp_source_child_score r i hW hd hgap hr hmissing hvalue hinside hsourceEdge
  apply CuspSourcePeakPayment.source_peak_false
    (a := a) (ell := -m) (e := e) (b := b) (A := A) (z := z)
    (E := kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow))
    (V := kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow))
    (cI := R.cuspPeakCredit r i) (CJ := R.cuspRemainderCredit r i)
    (Phi := R.cuspCrossEnergy i) (FJ := R.cuspRemainderEnergy i)
    (QO := R.cuspOutsideSquares r i) (child := objective child)
    (r := R.height / 2)
    ha hell hdelta hrho he hV measureReal_nonneg hA hz
    (R.cuspPeakCredit_nonnegative hW hd hgap r i hr hinside)
    (R.cuspRemainderCredit_nonnegative hW hd hgap r i hr)
    (R.cuspCrossEnergy_nonnegative hW i) (R.cuspRemainderEnergy_nonnegative hW i)
    hQO (by rw [hheight]) htwo hsquare' hhead.le hreserve' htraceCap
    (by dsimp [A]; linear_combination hE)
    (by convert hbudget using 1; dsimp [e, a]; ring)
    (by simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hcost)
  simpa only [hheight, b, A, z, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hscore

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

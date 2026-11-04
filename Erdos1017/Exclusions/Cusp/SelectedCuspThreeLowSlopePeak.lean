module

public import Erdos1017.Exclusions.Cusp.BenchmarkCuspThreePeakFloor
public import Erdos1017.Exclusions.Cusp.SelectedCuspAtomGuards
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.Exclusions.Common.MultipartiteCollisionEnvelope

/-!
# Peak bounds at the low-slope third cusp

At the low-slope third cusp the original common peak exceeds `11/39`, and the
avoiding forward endpoint keeps this mass (`cusp_three_low_slope_peak_bounds`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

/-- At the low-slope third cusp, the actual original common peak exceeds
11/39. The avoiding forward endpoint retains this same original mass;
its actual missing density pays the positive tail coefficient. -/
theorem cusp_three_low_slope_peak_bounds (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i) :
    -m ∈ Ioo (5 / 6 : ℝ) 1 ∧ 11 / 39 < S.originalAtomMass i ∧
      2 / 9 < 3 * (S.originalAtomMass i) ^ 2 := by
  have hdk' : d = (1 - 1 / (3 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  obtain ⟨hd, hslope, _, _, hmargin⟩ := hW.cusp_contact_parameters 3 (by norm_num) hdk' hgap hglobal
  norm_num at hslope hmargin
  have hc : 2 / 27 < c := by rw [hdk] at hmargin; nlinarith only [hmargin]
  obtain ⟨hDelta, j, hA, hside, hj, _, _, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hret := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  change S.forwardClassMass q i = S.originalAtomMass i at hret
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hmax (j : S.I) : S.forwardClassMass q j ≤ S.forwardClassMass q i := by
    by_cases hji : j = i
    · rw [hji]
    · have hsep := (hpeak q hq).2.2 j hji
      linarith only [hsep, hDelta]
  have hcost := MultipartiteClassMasses.objective_le_split_add_tail hq.endpoint
    (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp) i (hpeak q hq).1 hmax
  change objective hq.endpoint ≤ Benchmark.splitValue (S.forwardClassMass q i) +
    (1 - 2 * density hq.endpoint - (S.forwardClassMass q i) ^ 2) / 2 at hcost
  rw [hret] at hcost
  have hbudget := hq.endpoint_budget hW
  have henergy := hq.energy_nonnegative hW hd hgap
  have hdensity := hq.endpoint_density_gt hW hd hgap
  have htail := mul_pos (by linarith only [hell] : 0 < 1 + m)
    (by rw [hdk] at hdensity; linarith only [hdensity] :
      0 < 1 / 9 - (1 - 2 * density hq.endpoint))
  have hforward : 2 * c + kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ q) ≤
      (2 * Benchmark.splitValue (S.originalAtomMass i) - (S.originalAtomMass i) ^ 2) + 1 / 9 := by
    rw [hdk] at hbudget
    nlinarith only [hcost, hbudget, htail]
  have hmass : 11 / 39 < S.originalAtomMass i := by
    by_contra hn
    have hcurve := Benchmark.splitValue_theta_le_one_twentySeventh ⟨hA.le, le_of_not_gt hn⟩
    linarith only [hc, hforward, henergy, hcurve]
  refine ⟨⟨hslope.1, hell⟩, hmass, ?_⟩
  nlinarith only [hmass, hA]

end Erdos1017.CappedModel.SelectedHighLowStructure

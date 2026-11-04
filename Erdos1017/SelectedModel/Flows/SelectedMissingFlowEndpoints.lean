module

public import Erdos1017.SelectedModel.Flows.SelectedMissingFlowConstruction
public import Erdos1017.SelectedModel.Structure.SelectedMultipartiteHalves

/-!
# Endpoints of the constructed full flows

Both full-flow endpoints are probability laws that keep every original finite
clique test, have multipartite partition support with the same original
independent classes, satisfy the benchmark at their own densities, and move
density strictly up (forward) and down (reverse).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

namespace SelectedHighLowStructure

variable {W : Model Ω μ} {m : ℝ}

/-- The original decorated kernel under the constructed full forward law. -/
def forwardEndpoint (S : SelectedHighLowStructure W m) :
    Model Ω (missingFlowEndpointLaw μ S.forwardFlow) :=
  missingFlowEndpoint W S.forwardFlow S.integrable_flows.1
    (Eventually.of_forall (fun p => (S.flows_nonnegative p).1))
    (Eventually.of_forall (fun x => (S.supply_le_one x).1))

/-- The original decorated kernel under the constructed full reverse law. -/
def reverseEndpoint (S : SelectedHighLowStructure W m) :
    Model Ω (missingFlowEndpointLaw μ S.reverseFlow) :=
  missingFlowEndpoint W S.reverseFlow S.integrable_flows.2
    (Eventually.of_forall (fun p => (S.flows_nonnegative p).2))
    (Eventually.of_forall (fun x => (S.supply_le_one x).2))

/-- Both actual full-flow endpoint laws are probability laws. -/
theorem endpoint_probabilities (S : SelectedHighLowStructure W m) :
    IsProbabilityMeasure (missingFlowEndpointLaw μ S.forwardFlow) ∧
      IsProbabilityMeasure (missingFlowEndpointLaw μ S.reverseFlow) :=
  ⟨missingFlowEndpoint_probability S.forwardFlow S.integrable_flows.1
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).1))
      (Eventually.of_forall (fun x => (S.supply_le_one x).1)),
    missingFlowEndpoint_probability S.reverseFlow S.integrable_flows.2
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).2))
      (Eventually.of_forall (fun x => (S.supply_le_one x).2))⟩

/-- Every old finite clique test survives both constructed full flows. -/
theorem endpoints_fullFeasible (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    FullFeasible S.forwardEndpoint ∧ FullFeasible S.reverseEndpoint :=
  ⟨fullFeasible_missingFlowEndpoint W hW.full S.forwardFlow S.integrable_flows.1
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).1))
      (Eventually.of_forall (fun x => (S.supply_le_one x).1)),
    fullFeasible_missingFlowEndpoint W hW.full S.reverseFlow S.integrable_flows.2
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).2))
      (Eventually.of_forall (fun x => (S.supply_le_one x).2))⟩

/-- Removal of the supplied class puts each actual endpoint law on its
original multipartite half, with no measure-support premise supplied. -/
theorem endpoint_laws_ac_halves (S : SelectedHighLowStructure W m) :
    missingFlowEndpointLaw μ S.forwardFlow ≪ μ.restrict (S.half true) ∧
      missingFlowEndpointLaw μ S.reverseFlow ≪ μ.restrict (S.half false) := by
  constructor
  · apply weightedMeasure_ac_restrict_of_ae_zero _ _ (S.measurableSet_half true)
    filter_upwards [S.endpoints_remove_sources.1] with x hx hnot
    have hcover : x ∈ S.H ∪ S.L ∪ S.N := by
      rw [S.hpartition.2.2.2.1]
      exact mem_univ x
    have hlow : x ∈ S.L := by
      rcases hcover with (hh | hl) | hn
      · exact False.elim (hnot (Or.inl hh))
      · exact hl
      · exact False.elim (hnot (Or.inr hn))
    simpa only [integrableTiltWeight, one_mul] using hx hlow
  · apply weightedMeasure_ac_restrict_of_ae_zero _ _ (S.measurableSet_half false)
    filter_upwards [S.endpoints_remove_sources.2] with x hx hnot
    have hcover : x ∈ S.H ∪ S.L ∪ S.N := by
      rw [S.hpartition.2.2.2.1]
      exact mem_univ x
    have hhigh : x ∈ S.H := by
      rcases hcover with (hh | hl) | hn
      · exact hh
      · exact False.elim (hnot (Or.inl hl))
      · exact False.elim (hnot (Or.inr hn))
    simpa only [integrableTiltWeight, one_mul] using hx hhigh

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Genuine original class labels give actual conditional multipartite
support at both constructed endpoints. -/
theorem endpoint_partition_support (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (∀ᵐ p ∂(missingFlowEndpointLaw μ S.forwardFlow).prod
      (missingFlowEndpointLaw μ S.forwardFlow), ∀ᵐ z ∂W.kernel p,
      CappedColor.adjacency z = 1 ↔ S.atomicDustPartLabel p.1 ≠ S.atomicDustPartLabel p.2) ∧
    (∀ᵐ p ∂(missingFlowEndpointLaw μ S.reverseFlow).prod
      (missingFlowEndpointLaw μ S.reverseFlow), ∀ᵐ z ∂W.kernel p,
      CappedColor.adjacency z = 1 ↔ S.atomicDustPartLabel p.1 ≠ S.atomicDustPartLabel p.2) := by
  let := S.endpoint_probabilities.1
  let := S.endpoint_probabilities.2
  exact ⟨S.ae_atomicDust_color_support_of_half_ac hW hd hgap true S.endpoint_laws_ac_halves.1,
    S.ae_atomicDust_color_support_of_half_ac hW hd hgap false S.endpoint_laws_ac_halves.2⟩

/-- The same original independent classes give the actual endpoint scalar
profiles, with clique dust retained under the collapsed none label. -/
theorem endpoint_collapsed_support (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (∀ᵐ p ∂(missingFlowEndpointLaw μ S.forwardFlow).prod
      (missingFlowEndpointLaw μ S.forwardFlow), S.forwardEndpoint.moment CappedColor.adjacency p =
      if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
      then 1 else 0) ∧
    (∀ᵐ p ∂(missingFlowEndpointLaw μ S.reverseFlow).prod
      (missingFlowEndpointLaw μ S.reverseFlow), S.reverseEndpoint.moment CappedColor.adjacency p =
      if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
      then 1 else 0) := by
  let := S.endpoint_probabilities.1
  let := S.endpoint_probabilities.2
  exact ⟨(S.endpoint_laws_ac_halves.1.prod S.endpoint_laws_ac_halves.1).ae_le
      (S.ae_collapsed_half_support hW hd hgap true),
    (S.endpoint_laws_ac_halves.2.prod S.endpoint_laws_ac_halves.2).ae_le
      (S.ae_collapsed_half_support hW hd hgap false)⟩

/-- The actual full-flow endpoints satisfy the benchmark at their own
densities; neither endpoint is asserted optimal or stationary. -/
theorem endpoint_benchmark_bounds (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    objective S.forwardEndpoint ≤ benchmark (density S.forwardEndpoint) ∧
      objective S.reverseEndpoint ≤ benchmark (density S.reverseEndpoint) := by
  let := S.endpoint_probabilities.1
  let := S.endpoint_probabilities.2
  exact ⟨objective_le_benchmark_of_partition_support _ (S.endpoints_fullFeasible hW).1
      S.atomicDustPartLabel (S.endpoint_partition_support hW hd hgap).1,
    objective_le_benchmark_of_partition_support _ (S.endpoints_fullFeasible hW).2
      S.atomicDustPartLabel (S.endpoint_partition_support hW hd hgap).2⟩

/-- Actual full forward density increases strictly and actual full reverse
density decreases strictly. All mass, energy and partition premises are derived. -/
theorem endpoint_densities_strict (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    d < density S.forwardEndpoint ∧ density S.reverseEndpoint < d := by
  have hpos := S.high_low_mass_pos hW hd hgap
  have hmassF : 0 < ∫ p, S.forwardFlow p ∂μ.prod μ := by
    rw [S.integral_flows.1]
    exact ENNReal.toReal_pos hpos.2.ne' (measure_ne_top μ _)
  have hmassR : 0 < ∫ p, S.reverseFlow p ∂μ.prod μ := by
    rw [S.integral_flows.2]
    exact ENNReal.toReal_pos hpos.1.ne' (measure_ne_top μ _)
  exact ⟨hW.forward_missing_flow_endpoint_density_gt_of_partition_support hd hgap
      S.forwardFlow S.integrable_flows.1
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).1)) hmassF
      (Eventually.of_forall (fun x => (S.supply_le_one x).1)) S.forward_support
      S.atomicDustPartLabel (S.endpoint_partition_support hW hd hgap).1,
    hW.reverse_missing_flow_endpoint_density_lt_of_partition_support hd hgap
      S.reverseFlow S.integrable_flows.2
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).2)) hmassR
      (Eventually.of_forall (fun x => (S.supply_le_one x).2)) S.reverse_support
      S.atomicDustPartLabel (S.endpoint_partition_support hW hd hgap).2⟩

end SelectedHighLowStructure

/-- The actual selected original optimum constructs both full-flow endpoints
with strict density directions and nonnegative original energies. No selected
structure, flow, endpoint, energy or partition-support hypothesis is used. -/
theorem FullStationaryClass.exists_selected_full_flow_endpoints
    [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    ∃ S : SelectedHighLowStructure W m,
      FullFeasible S.forwardEndpoint ∧ FullFeasible S.reverseEndpoint ∧
      d < density S.forwardEndpoint ∧ density S.reverseEndpoint < d ∧
      0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ S.forwardFlow) ∧
      0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ S.reverseFlow) := by
  obtain ⟨S⟩ := hW.exists_selected_high_low_structure hd hgap hmin hmax
  exact ⟨S, (S.endpoints_fullFeasible hW).1, (S.endpoints_fullFeasible hW).2,
    (S.endpoint_densities_strict hW hd hgap).1, (S.endpoint_densities_strict hW hd hgap).2,
    (S.energies_nonnegative hW hd hgap).1, (S.energies_nonnegative hW hd hgap).2⟩

end Erdos1017.CappedModel

module

public import Erdos1017.SelectedModel.Flows.FullMissingFlowEnergy
public import Erdos1017.SelectedModel.Recovery.MissingFlowReversal
public import Erdos1017.SelectedModel.Flows.IntegrableDensityReturnStrict
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteModelComparison

/-!
# Endpoints of oriented missing flows

The endpoint of a missing flow is the original decorated kernel under the
receipt-minus-supply law; for a full stationary strict-gap optimum, forward
endpoints have density at least the original and reverse endpoints at most,
strictly so under multipartite partition support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual endpoint law of receipt minus supply, on the original carrier. -/
def missingFlowEndpointLaw (μ : Measure Ω) (q : Ω × Ω → ℝ) : Measure Ω :=
  weightedMeasure (μ := μ) (integrableTiltWeight (MissingFlow.direction μ q) 1)

/-- The original decorated kernel under the actual endpoint probability law. -/
def missingFlowEndpoint (W : Model Ω μ) (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1) :
    Model Ω (missingFlowEndpointLaw μ q) :=
  integrableTilt W (MissingFlow.direction μ q) (MissingFlow.integrable_direction hq)
    (MissingFlow.integral_direction hq) (MissingFlow.direction_ge_neg_one hq0 hsupply)
    1 ⟨by norm_num, le_rfl⟩

theorem missingFlowEndpoint_probability (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1) :
    IsProbabilityMeasure (missingFlowEndpointLaw μ q) :=
  integrableTilt_probability (MissingFlow.direction μ q) (MissingFlow.integrable_direction hq)
    (MissingFlow.integral_direction hq) (MissingFlow.direction_ge_neg_one hq0 hsupply)
    1 ⟨by norm_num, le_rfl⟩

theorem missingFlowEndpoint_kernel (W : Model Ω μ) (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1) :
    (missingFlowEndpoint W q hq hq0 hsupply).kernel = W.kernel := rfl

/-- Every original finite-order clique constraint survives at this actual
endpoint, including when its receipt density is unbounded. -/
theorem fullFeasible_missingFlowEndpoint (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1) :
    FullFeasible (missingFlowEndpoint W q hq hq0 hsupply) :=
  fullFeasible_integrableTilt W hW (MissingFlow.direction μ q)
    (MissingFlow.integrable_direction hq) (MissingFlow.integral_direction hq)
    (MissingFlow.direction_ge_neg_one hq0 hsupply) 1 ⟨by norm_num, le_rfl⟩

/-- The exact endpoint budget uses the original scalar multiplier and
unhalved original shifted energy, without endpoint stationarity. -/
theorem FullStationaryClass.missing_flow_endpoint_budget
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1) :
    (2 * (c - m * d) + m) +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) =
      2 * objective (missingFlowEndpoint W q hq hq0 hsupply) +
        m * (1 - 2 * density (missingFlowEndpoint W q hq hq0 hsupply)) := by
  have h := hW.objective_integrableTilt (MissingFlow.direction μ q)
    (MissingFlow.integrable_direction hq) (MissingFlow.integral_direction hq)
    (MissingFlow.direction_ge_neg_one hq0 hsupply) 1 ⟨by norm_num, le_rfl⟩
  change objective (missingFlowEndpoint W q hq hq0 hsupply) = c +
    m * (density (missingFlowEndpoint W q hq hq0 hsupply) - d) +
      1 ^ 2 * KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ q) / 2 at h
  linarith

/-- Any objective cap on the actual endpoint gives the original
state's budget; no endpoint optimality or changed-density gap is used. -/
theorem FullStationaryClass.missing_flow_endpoint_budget_le
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (U : ℝ) (hU : objective (missingFlowEndpoint W q hq hq0 hsupply) ≤ U) :
    (2 * (c - m * d) + m) +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) ≤
      2 * U + m * (1 - 2 * density (missingFlowEndpoint W q hq hq0 hsupply)) := by
  rw [hW.missing_flow_endpoint_budget q hq hq0 hsupply]
  linarith

/-- An actual endpoint with multipartite partition support and nonnegative
original shifted energy cannot have the old strict-gap density. This
comparison uses the endpoint's full feasibility, not its optimality. -/
theorem FullStationaryClass.missing_flow_endpoint_density_ne_of_partition_support
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (hE : 0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ q))
    {ι : Type*} (π : Ω → ι)
    (hpart : ∀ᵐ p ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q),
      ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔ π p.1 ≠ π p.2) :
    density (missingFlowEndpoint W q hq hq0 hsupply) ≠ d := by
  intro heq
  let := missingFlowEndpoint_probability q hq hq0 hsupply
  have hupper := objective_le_benchmark_of_partition_support (missingFlowEndpoint W q hq hq0 hsupply)
    (fullFeasible_missingFlowEndpoint W hW.full q hq hq0 hsupply) π hpart
  have hbudget := hW.missing_flow_endpoint_budget q hq hq0 hsupply
  rw [heq] at hupper hbudget
  nlinarith

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Reverse-oriented missing flows also have nonnegative original shifted
energy, by symmetry and exact reversal of the actual product density. -/
theorem FullStationaryClass.reverse_missing_flow_energy_nonnegative
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) := by
  have hreverse : ∀ᵐ p ∂μ.prod μ, MissingFlow.swapDensity q p ≠ 0 →
      shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae hqs,
      shiftedMoment_symm W m] with p hp hs hne
    have h := hp hne
    exact ⟨hs.symm.trans h.1, sub_pos.mpr h.2⟩
  have h := hW.missing_flow_energy_nonnegative hd hgap (MissingFlow.swapDensity q)
    (MissingFlow.integrable_swapDensity hq) (MissingFlow.nonnegative_swapDensity hq0) hreverse
  rwa [MissingFlow.kernelEnergy_direction_swapDensity] at h

/-- A positive-mass forward flow with supply at most the original law has
an actual full-feasible endpoint of density at least the original density. -/
theorem FullStationaryClass.forward_missing_flow_endpoint_density_ge
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hmass : 0 < ∫ p, q p ∂μ.prod μ)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    d ≤ density (missingFlowEndpoint W q hq hq0 hsupply) := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hgBound : g ∈ KernelOperator.boundedL2Submodule μ :=
    KernelOperator.operator_range_bounded _ _ _ _ _
  obtain ⟨Cg, _, hgBound⟩ := hgBound
  have hL := MissingFlow.degree_pairing_pos hq hq0 hmass (g : Ω → ℝ)
    (Lp.memLp g).aestronglyMeasurable hgBound
    (hqs.mono (fun _ hp hne => sub_pos.mp (hp hne).2))
  have hsign := hW.endpoint_density_sign hd hgap (MissingFlow.direction μ q)
    (MissingFlow.integrable_direction hq) (MissingFlow.integral_direction hq)
    (MissingFlow.direction_ge_neg_one hq0 hsupply) hL.ne'
    (hW.missing_flow_energy_nonnegative hd hgap q hq hq0 hqs)
  change 0 ≤ (∫ x, g x * MissingFlow.direction μ q x ∂μ) *
    (density (missingFlowEndpoint W q hq hq0 hsupply) - d) at hsign
  nlinarith

/-- A positive-mass decreasing-degree flow has an actual full-feasible
endpoint of density at most the original density. -/
theorem FullStationaryClass.reverse_missing_flow_endpoint_density_le
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hmass : 0 < ∫ p, q p ∂μ.prod μ)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    density (missingFlowEndpoint W q hq hq0 hsupply) ≤ d := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hgBound : g ∈ KernelOperator.boundedL2Submodule μ :=
    KernelOperator.operator_range_bounded _ _ _ _ _
  obtain ⟨Cg, _, hgBound⟩ := hgBound
  have hL := MissingFlow.degree_pairing_neg hq hq0 hmass (g : Ω → ℝ)
    (Lp.memLp g).aestronglyMeasurable hgBound (hqs.mono (fun _ hp hne => (hp hne).2))
  have hsign := hW.endpoint_density_sign hd hgap (MissingFlow.direction μ q)
    (MissingFlow.integrable_direction hq) (MissingFlow.integral_direction hq)
    (MissingFlow.direction_ge_neg_one hq0 hsupply) hL.ne
    (hW.reverse_missing_flow_energy_nonnegative hd hgap q hq hq0 hqs)
  change 0 ≤ (∫ x, g x * MissingFlow.direction μ q x ∂μ) *
    (density (missingFlowEndpoint W q hq hq0 hsupply) - d) at hsign
  nlinarith

/-- An objective cap on a reverse endpoint gives explicit nonnegative
energy and density-change credits against the original optimum. -/
theorem FullStationaryClass.reverse_missing_flow_endpoint_credit
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hmass : 0 < ∫ p, q p ∂μ.prod μ)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2)
    (U : ℝ) (hU : objective (missingFlowEndpoint W q hq hq0 hsupply) ≤ U) :
    c ≤ U - KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ q) / 2 + m * (d - density (missingFlowEndpoint W q hq hq0 hsupply)) ∧
      U - KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ q) / 2 + m * (d - density (missingFlowEndpoint W q hq hq0 hsupply)) ≤
          U := by
  have hbudget := hW.missing_flow_endpoint_budget_le q hq hq0 hsupply U hU
  have hE := hW.reverse_missing_flow_energy_nonnegative hd hgap q hq hq0 hqs
  have hden := hW.reverse_missing_flow_endpoint_density_le hd hgap q hq hq0 hmass hsupply hqs
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hcredit := mul_nonpos_of_nonpos_of_nonneg hm.le (sub_nonneg.mpr hden)
  constructor <;> nlinarith

/-- Multipartite support at the actual forward endpoint makes its
density increase strict; its original energy sign is derived internally. -/
theorem FullStationaryClass.forward_missing_flow_endpoint_density_gt_of_partition_support
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hmass : 0 < ∫ p, q p ∂μ.prod μ)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2)
    {ι : Type*} (π : Ω → ι)
    (hpart : ∀ᵐ p ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q),
      ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔ π p.1 ≠ π p.2) :
    d < density (missingFlowEndpoint W q hq hq0 hsupply) :=
  lt_of_le_of_ne (hW.forward_missing_flow_endpoint_density_ge hd hgap q hq hq0 hmass hsupply hqs)
    (hW.missing_flow_endpoint_density_ne_of_partition_support hgap q hq hq0 hsupply
      (hW.missing_flow_energy_nonnegative hd hgap q hq hq0 hqs) π hpart).symm

/-- Multipartite support at the actual reverse endpoint makes its
density decrease strict, with no assumed reverse energy or endpoint optimum. -/
theorem FullStationaryClass.reverse_missing_flow_endpoint_density_lt_of_partition_support
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hmass : 0 < ∫ p, q p ∂μ.prod μ)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2)
    {ι : Type*} (π : Ω → ι)
    (hpart : ∀ᵐ p ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q),
      ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔ π p.1 ≠ π p.2) :
    density (missingFlowEndpoint W q hq hq0 hsupply) < d :=
  lt_of_le_of_ne (hW.reverse_missing_flow_endpoint_density_le hd hgap q hq hq0 hmass hsupply hqs)
    (hW.missing_flow_endpoint_density_ne_of_partition_support hgap q hq hq0 hsupply
      (hW.reverse_missing_flow_energy_nonnegative hd hgap q hq hq0 hqs) π hpart)

end Erdos1017.CappedModel

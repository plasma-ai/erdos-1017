module

public import Erdos1017.SelectedModel.Flows.SelectedMissingFlowConstruction
public import Erdos1017.SelectedModel.Structure.SelectedMultipartiteHalves

/-!
# The class of full reverse flows

`IsFullReverseFlow` collects the full reverse flows on the original law and
selected relation; each transports exactly the high-class mass, has nonnegative
shifted energy and the same budget, and an endpoint of strictly smaller density
with the original collapsed class labels. The normalized reverse flow shows the
class is nonempty.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- All actual full reverse flows, on the original probability law and
selected relation. The original HIGH marginal is supplied exactly. -/
structure IsFullReverseFlow (S : SelectedHighLowStructure W m) (q : Ω × Ω → ℝ) : Prop where
  integrable : Integrable q (μ.prod μ)
  nonnegative : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p
  supply : MissingFlow.supply μ q =ᵐ[μ] S.H.indicator (fun _ => 1)
  support : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 →
    p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.L ∧ p.2 ∈ S.H

namespace IsFullReverseFlow

variable {S : SelectedHighLowStructure W m} {q r : Ω × Ω → ℝ}

/-- Full supply is dominated by the original measure. -/
theorem supply_le_one (hq : S.IsFullReverseFlow q) :
    ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1 := by
  filter_upwards [hq.supply] with x hx
  rw [hx]
  by_cases h : x ∈ S.H
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]
    exact zero_le_one

/-- Every full reverse flow transports exactly the original HIGH mass. -/
theorem integral_eq_high_mass (hq : S.IsFullReverseFlow q) :
    (∫ p, q p ∂μ.prod μ) = μ.real S.H := by
  rw [← (MissingFlow.integral_marginals hq.integrable).2, integral_congr_ae hq.supply,
    integral_indicator S.hpartition.1, setIntegral_const, smul_eq_mul, mul_one]

/-- The actual selected crossing theorem determines the strict original
degree decrease from each HIGH source to its LOW recipient. -/
theorem oriented_support (hq : S.IsFullReverseFlow q) :
    ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
  filter_upwards [hq.support, S.hrelation] with p hp hr hne
  obtain ⟨hZ, hL, _⟩ := hp hne
  refine ⟨hZ.1, ?_⟩
  rcases hr hZ with h | h
  · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 h.1 hL)
  · exact h.2.2

/-- Actual Fubini shows that a full reverse flow has zero receipt off LOW. -/
theorem receipt_zero_off_low (hq : S.IsFullReverseFlow q) :
    ∀ᵐ x ∂μ, x ∉ S.L → MissingFlow.receipt μ q x = 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod hq.support] with x hx hnot
  apply integral_eq_zero_of_ae
  filter_upwards [hx] with y hy
  by_contra hne
  exact hnot (hy hne).2.1

/-- Exact original HIGH supply and zero HIGH receipt remove every HIGH point
almost everywhere from the actual endpoint law. -/
theorem endpoint_removes_high (hq : S.IsFullReverseFlow q) :
    ∀ᵐ x ∂μ, x ∈ S.H → 1 + MissingFlow.direction μ q x = 0 := by
  filter_upwards [hq.supply, hq.receipt_zero_off_low] with x hs hr hx
  have hxH : x ∉ S.L := fun h => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx h
  change 1 + (MissingFlow.receipt μ q x - MissingFlow.supply μ q x) = 0
  rw [hr hxH, hs, indicator_of_mem hx]
  ring

/-- The endpoint weight vanishes outside the original LOW-plus-neutral half. -/
theorem endpoint_weight_zero_off_half (hq : S.IsFullReverseFlow q) :
    ∀ᵐ x ∂μ, x ∉ S.half false →
      integrableTiltWeight (MissingFlow.direction μ q) 1 x = 0 := by
  filter_upwards [hq.endpoint_removes_high] with x hx hnot
  have hxL : x ∈ S.H := by
    have hc : x ∈ S.H ∪ S.L ∪ S.N := by rw [S.hpartition.2.2.2.1]; exact mem_univ x
    rcases hc with (hH | hL) | hN
    · exact hH
    · exact False.elim (hnot (Or.inl hL))
    · exact False.elim (hnot (Or.inr hN))
  simpa only [integrableTiltWeight, one_mul] using hx hxL

/-- The actual endpoint law is supported on the original multipartite half. -/
theorem endpointLaw_ac_half (hq : S.IsFullReverseFlow q) :
    missingFlowEndpointLaw μ q ≪ μ.restrict (S.half false) :=
  weightedMeasure_ac_restrict_of_ae_zero _ _ (S.measurableSet_half false)
    hq.endpoint_weight_zero_off_half

/-- The actual unchanged decorated model at this full flow's endpoint. -/
def endpoint (hq : S.IsFullReverseFlow q) : Model Ω (missingFlowEndpointLaw μ q) :=
  missingFlowEndpoint W q hq.integrable hq.nonnegative hq.supply_le_one

theorem endpoint_probability (hq : S.IsFullReverseFlow q) :
    IsProbabilityMeasure (missingFlowEndpointLaw μ q) :=
  missingFlowEndpoint_probability q hq.integrable hq.nonnegative hq.supply_le_one

/-- Full feasibility of the original model survives this actual endpoint. -/
theorem endpoint_fullFeasible (hq : S.IsFullReverseFlow q) (hW : FullFeasible W) :
    FullFeasible hq.endpoint :=
  fullFeasible_missingFlowEndpoint W hW q hq.integrable hq.nonnegative hq.supply_le_one

/-- The actual class is convex, including exact HIGH supply and the original
relation support, at every parameter of the closed unit interval. -/
theorem convex (hq : S.IsFullReverseFlow q) (hr : S.IsFullReverseFlow r)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    S.IsFullReverseFlow (fun p => (1 - θ) * q p + θ * r p) := by
  refine ⟨(hq.integrable.const_mul _).add (hr.integrable.const_mul _), ?_, ?_, ?_⟩
  · filter_upwards [hq.nonnegative, hr.nonnegative] with p hp hpr
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hθ.2) hp) (mul_nonneg hθ.1 hpr)
  · filter_upwards [hq.integrable.prod_left_ae, hr.integrable.prod_left_ae,
      hq.supply, hr.supply] with x hqx hrx hqs hrs
    change (∫ y, (1 - θ) * q (y, x) + θ * r (y, x) ∂μ) = _
    rw [integral_add (hqx.const_mul _) (hrx.const_mul _), integral_const_mul, integral_const_mul]
    change (1 - θ) * MissingFlow.supply μ q x + θ * MissingFlow.supply μ r x = _
    rw [hqs, hrs]
    ring
  · filter_upwards [hq.support, hr.support] with p hp hpr hne
    by_cases hqz : q p = 0
    · have hrz : r p ≠ 0 := by intro hz; apply hne; rw [hqz, hz]; ring
      exact hpr hrz
    · exact hp hqz

/-- Interpolating actual product densities interpolates their original
receipt-minus-supply directions almost everywhere. -/
theorem direction_affine (hq : S.IsFullReverseFlow q) (hr : S.IsFullReverseFlow r) (θ : ℝ) :
    MissingFlow.direction μ (fun p => (1 - θ) * q p + θ * r p) =ᵐ[μ]
      fun x => (1 - θ) * MissingFlow.direction μ q x + θ * MissingFlow.direction μ r x := by
  filter_upwards [hq.integrable.prod_right_ae, hr.integrable.prod_right_ae,
    hq.integrable.prod_left_ae, hr.integrable.prod_left_ae] with x hqx hrx hqy hry
  dsimp only [MissingFlow.direction, MissingFlow.receipt, MissingFlow.supply]
  rw [integral_add (hqx.const_mul _) (hrx.const_mul _),
    integral_add (hqy.const_mul _) (hry.const_mul _)]
  simp only [integral_const_mul]
  ring

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Positive original HIGH mass makes every full reverse flow nonzero. -/
theorem integral_pos (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < ∫ p, q p ∂μ.prod μ := by
  rw [hq.integral_eq_high_mass]
  exact ENNReal.toReal_pos (S.high_low_mass_pos hW hd hgap).1.ne' (measure_ne_top _ _)

/-- Every actual full reverse endpoint has the same original collapsed
class labels and actual scalar clique-dust support under its own law. -/
theorem endpoint_collapsed_support (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q),
      hq.endpoint.moment CappedColor.adjacency p =
        if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
        then 1 else 0 := by
  let := hq.endpoint_probability
  exact (hq.endpointLaw_ac_half.prod hq.endpointLaw_ac_half).ae_le
    (S.ae_collapsed_half_support hW hd hgap false)

/-- The actual endpoint has conditional clique-dust support with the same
original collapsed labels, under its own probability law. -/
theorem endpoint_collapsed_color_support (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q),
      ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔
        S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none := by
  let := hq.endpoint_probability
  exact S.ae_collapsed_color_support_of_half_ac hW hd hgap false hq.endpointLaw_ac_half

/-- Genuine singleton dust yields actual conditional partition support for
this endpoint, without assuming a multipartite endpoint. -/
theorem endpoint_partition_support (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q),
      ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔
        S.atomicDustPartLabel p.1 ≠ S.atomicDustPartLabel p.2 := by
  let := hq.endpoint_probability
  exact S.ae_atomicDust_color_support_of_half_ac hW hd hgap false hq.endpointLaw_ac_half

/-- Every actual full reverse endpoint has density strictly below the
original density, from its derived multipartite support and energy sign. -/
theorem endpoint_density_lt (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    density hq.endpoint < d :=
  hW.reverse_missing_flow_endpoint_density_lt_of_partition_support hd hgap q
    hq.integrable hq.nonnegative (hq.integral_pos hW hd hgap) hq.supply_le_one hq.oriented_support
    S.atomicDustPartLabel (hq.endpoint_partition_support hW hd hgap)

/-- The original shifted energy is nonnegative for every actual full flow. -/
theorem energy_nonnegative (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) :=
  hW.reverse_missing_flow_energy_nonnegative hd hgap q hq.integrable hq.nonnegative hq.oriented_support

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The exact budget of every actual full flow uses the same original multiplier. -/
theorem endpoint_budget (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    (2 * (c - m * d) + m) +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) =
      2 * objective hq.endpoint + m * (1 - 2 * density hq.endpoint) :=
  hW.missing_flow_endpoint_budget q hq.integrable hq.nonnegative hq.supply_le_one

end IsFullReverseFlow

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The explicitly normalized original reverse flow witnesses nonemptiness
of the entire actual full-reverse-flow class. -/
theorem reverseFlow_isFullReverseFlow (S : SelectedHighLowStructure W m) :
    S.IsFullReverseFlow S.reverseFlow :=
  ⟨S.integrable_flows.2, Eventually.of_forall (fun p => (S.flows_nonnegative p).2),
    Eventually.of_forall (congrFun S.reverse_supply), S.reverse_class_support⟩

theorem exists_fullReverseFlow (S : SelectedHighLowStructure W m) :
    ∃ q, S.IsFullReverseFlow q := ⟨S.reverseFlow, S.reverseFlow_isFullReverseFlow⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

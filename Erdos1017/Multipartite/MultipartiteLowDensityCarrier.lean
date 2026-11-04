module

public import Erdos1017.Multipartite.MultipartiteLowDensity
public import Erdos1017.Multipartite.MultipartiteCarrierMass
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Unit dust coefficients on the carrier

Unit-charge demand in a strict-head homogeneous dual must lie between the
anchor and positive dust. The unit-edge bound therefore supplies the unit
dust coefficients needed by the fixed-moment promotion argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.MultipartiteCountableMeasure

local instance lowDensityCarrierMeasurableSpaceLabel : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω]

private def positiveLabel (p : ℕ → ℝ) (s : ℝ) : Label → Prop
  | .inl none => True
  | .inl (some i) => 0 < p i
  | .inr _ => 0 < s

private theorem ae_positive_label (ν : Measure Ω) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s) :
    ∀ᵐ v ∂vertexMeasure ν p s, positiveLabel p s v.1 := by
  have hm : MeasurableSet {v : Label × Ω | positiveLabel p s v.1} :=
    (Set.to_countable {i : Label | positiveLabel p s i}).measurableSet.preimage measurable_fst
  have hc (i : Label) (hi : positiveLabel p s i) :
      ∀ᵐ v ∂component ν i, positiveLabel p s v.1 := by
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
    exact Filter.Eventually.of_forall (fun _ => hi)
  rw [vertexMeasure, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨hc (.inl none) trivial, ?_⟩, ?_⟩
  · by_cases hs0 : 0 < s
    · rw [Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hs0))]
      exact hc (.inr ()) hs0
    · have heq : s = 0 := le_antisymm (le_of_not_gt hs0) hs
      simp [heq]
  · apply Measure.ae_sum_iff.mpr
    intro i
    by_cases hpi : 0 < p i
    · unfold headMeasure
      rw [Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hpi))]
      exact hc (.inl (some i)) hpi
    · have heq : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp i)
      simp [headMeasure, heq]

private theorem unit_kernel_forces_dust {p : ℕ → ℝ} {s : ℝ}
    {D : MultipartiteCountableDual.Coefficients} (hD : D ∈ MultipartiteCountableDual.feasible)
    (hhead : ∀ i, 0 < p i → MultipartiteCountableDual.head D i < 1)
    (a b : Label) (ha : positiveLabel p s a) (hb : positiveLabel p s b)
    (hunit : kernel D a b = 1) :
    0 < s ∧ MultipartiteCountableDual.linear D = 1 := by
  rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
  · cases a with
    | none =>
      cases b with
      | none => norm_num [kernel] at hunit
      | some j => exact False.elim ((ne_of_lt (hhead j hb)) hunit)
    | some i =>
      cases b with
      | none => exact False.elim ((ne_of_lt (hhead i ha)) hunit)
      | some j =>
        have hnonneg : 0 ≤ if i < j then MultipartiteCountableDual.pair D i j
            else if j < i then MultipartiteCountableDual.pair D j i else 0 := by
          split_ifs <;> first | exact hD.1.1 _ | exact le_rfl
        dsimp only [kernel] at hunit
        linarith
  · cases a with
    | none => exact ⟨hb, hunit⟩
    | some i =>
      have hnonneg := hD.1.1 (.inr (.inr (.inl i)))
      change 0 ≤ D (.inr (.inr (.inl i))) at hnonneg
      change -D (.inr (.inr (.inl i))) = 1 at hunit
      linarith
  · cases b with
    | none => exact ⟨ha, hunit⟩
    | some i =>
      have hnonneg := hD.1.1 (.inr (.inr (.inl i)))
      change 0 ≤ D (.inr (.inr (.inl i))) at hnonneg
      change -D (.inr (.inr (.inl i))) = 1 at hunit
      linarith
  · have hnonneg := hD.1.1 (.inr (.inr (.inr true)))
    change 0 ≤ D (.inr (.inr (.inr true))) at hnonneg
    change -D (.inr (.inr (.inr true))) = 1 at hunit
    linarith

/-- Positive unit-charge demand forces positive dust and unit anchor-dust charge. -/
theorem unit_dust_of_unit_mass (ν : Measure Ω) [IsProbabilityMeasure ν]
    [MeasurableEq Ω] (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    (s : ℝ) (hs : 0 ≤ s) {D : MultipartiteCountableDual.Coefficients}
    (hD : D ∈ MultipartiteCountableDual.feasible)
    (hhead : ∀ i, 0 < p i → MultipartiteCountableDual.head D i < 1)
    (hunit : 0 < (PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet).real
      {z | physicalKernel D z = 1}) :
    0 < s ∧ MultipartiteCountableDual.linear D = 1 := by
  have := vertexMeasure_finite ν p hsum s
  have hP := ae_positive_label ν p hp s hs
  have hm : MeasurableSet {z : (Label × Ω) × (Label × Ω) |
      positiveLabel p s z.1.1 ∧ positiveLabel p s z.2.1} := by
    have hlabel : MeasurableSet {v : Label × Ω | positiveLabel p s v.1} :=
      (Set.to_countable {i : Label | positiveLabel p s i}).measurableSet.preimage measurable_fst
    exact (hlabel.preimage measurable_fst).inter (hlabel.preimage measurable_snd)
  have hprod : ∀ᵐ z ∂(vertexMeasure ν p s).prod (vertexMeasure ν p s),
      positiveLabel p s z.1.1 ∧ positiveLabel p s z.2.1 := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hP] with v hv
    filter_upwards [hP] with w hw
    exact ⟨hv, hw⟩
  have hpair : ∀ᵐ z ∂PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet,
      positiveLabel p s z.1.1 ∧ positiveLabel p s z.2.1 :=
    ae_mono (Measure.restrict_le_self) hprod
  by_contra hfail
  have hn : ∀ᵐ z ∂PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet,
      physicalKernel D z ≠ 1 := by
    filter_upwards [hpair] with z hz
    change ¬physicalKernel D z = 1
    intro h
    exact hfail (unit_kernel_forces_dust hD hhead z.1.1 z.2.1 hz.1 hz.2 h)
  have hzero : (PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet)
      {z | physicalKernel D z = 1} = 0 := by
    simpa only [not_not] using ae_iff.mp hn
  rw [measureReal_def, hzero, ENNReal.toReal_zero] at hunit
  exact (lt_irrefl 0) hunit

end Erdos1017.MultipartiteCountableMeasure

namespace Erdos1017.MultipartiteCountableDual

local instance unitDustLabelMeasurableSpace : MeasurableSpace MultipartiteCountableMeasure.Label := ⊤

/-- The two-dust-point clique test forces the unit internal penalty. -/
theorem penalty_eq_one_of_linear_eq_one {D : Coefficients} (hD : D ∈ feasible)
    (hlinear : linear D = 1) : penalty D = 1 := by
  have ht := hD.2 0 (fun _ => false) 2
  norm_num [MultipartiteDust.charge, MultipartiteDust.linear, MultipartiteDust.penalty,
    restrict] at ht
  change 2 * linear D ≤ 1 + penalty D at ht
  rw [hlinear] at ht
  have hupper : penalty D ≤ 1 := hD.1.2 _
  linarith

/-- The actual unit-edge theorem and strict head charges supply the unit
dust coefficients, with the physical carrier mass computed explicitly. -/
theorem unit_dust_of_value_gt_third {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (hhead : ∀ i, 0 < x.2 i → head D i < 1)
    (hlarge : (x.1 + (x.1 ^ 2 - ∑' i, (x.2 i) ^ 2) / 2) / 3 <
      MultipartiteProfiles.limitValue x) :
    0 < MultipartiteProfiles.dust x ∧ linear D = 1 ∧ penalty D = 1 := by
  let ν : Measure ℝ := volume.restrict (Set.Icc 0 1)
  have : IsProbabilityMeasure ν := by
    constructor
    simp [ν, Real.volume_Icc]
  have hbound := MultipartiteCountableMeasure.unit_edge_mass_lower_bound ν hx hD hopt
  dsimp only at hbound
  rw [MultipartiteCountableMeasure.profile_graphDemand_mass ν hx] at hbound
  have hpositive : 0 < (PhysicalPrimal.graphDemand
      (MultipartiteCountableMeasure.vertexMeasure ν x.2 (MultipartiteProfiles.dust x))
        MultipartiteCountableMeasure.edgeSet).real
          {z | MultipartiteCountableMeasure.physicalKernel D z = 1} := by
    linarith
  obtain ⟨hs, hlinear⟩ := MultipartiteCountableMeasure.unit_dust_of_unit_mass ν x.2 hx.1.1.2
    (MultipartiteProfiles.atoms_summable hx) (MultipartiteProfiles.dust x)
    (MultipartiteProfiles.dust_nonneg hx) hD hhead hpositive
  exact ⟨hs, hlinear, penalty_eq_one_of_linear_eq_one hD hlinear⟩

end Erdos1017.MultipartiteCountableDual

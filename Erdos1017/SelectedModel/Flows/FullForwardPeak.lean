module

public import Erdos1017.SelectedModel.Flows.FullForwardFlowClass
public import Erdos1017.SelectedModel.Flows.FlowClassMasses
public import Erdos1017.SelectedModel.Structure.SeparatedPeakInterpolation

/-!
# The common forward peak

Every full forward flow has an attained positive separated peak, and one and
only one original independent-class label is the uniformly separated peak for
all of them (`exists_unique_common_forward_peak`); the endpoint budget also
forces the positive slope below two.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel

/-- The original model's common positive forward separation gap. -/
def forwardPeakGap (d c m : ℝ) : ℝ :=
  ForwardPeak.peakGap (-m) (2 * (c - m * d) + m) (2 * c - (1 - 2 * d))

namespace SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Actual endpoint masses retain the same original independent-class labels
for every full forward flow, including classes removed by the flow. -/
def forwardClassMass (S : SelectedHighLowStructure W m) (q : Ω × Ω → ℝ) (i : S.I) : ℝ :=
  (missingFlowEndpointLaw μ q).real (S.collapsedPartLabel ⁻¹' {some i})

namespace IsFullForwardFlow

variable {S : SelectedHighLowStructure W m} {q r : Ω × Ω → ℝ}
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual original-label endpoint masses are summable, nonnegative, and
have total at most one. No peak or finiteness premise is needed. -/
theorem classMass_properties (hq : S.IsFullForwardFlow q) :
    (∀ i, S.forwardClassMass q i ∈ Icc (0 : ℝ) 1) ∧
      Summable (S.forwardClassMass q) ∧ (∑' i, S.forwardClassMass q i) ≤ 1 := by
  let := hq.endpoint_probability
  let : Countable S.I := S.hI.to_subtype
  exact ⟨fun i => ⟨MultipartiteClassMasses.classMass_nonneg _ _ i,
      MultipartiteClassMasses.classMass_le_one _ i⟩,
    MultipartiteClassMasses.classMass_summable _ S.measurable_collapsedPartLabel,
    MultipartiteClassMasses.tsum_classMass_le_one _ S.measurable_collapsedPartLabel⟩

/-- Actual original-class endpoint masses interpolate affinely under the
proved convex combination of physical full-forward-flow densities. -/
theorem classMass_affine (hq : S.IsFullForwardFlow q) (hr : S.IsFullForwardFlow r)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (i : S.I) :
    S.forwardClassMass (fun p => (1 - θ) * q p + θ * r p) i =
      ForwardPeak.affineMass (S.forwardClassMass q) (S.forwardClassMass r) θ i := by
  let A := S.collapsedPartLabel ⁻¹' {some i}
  have hA : MeasurableSet A := S.measurable_collapsedPartLabel (by trivial)
  have hmass (u : Ω × Ω → ℝ) (hu : S.IsFullForwardFlow u) :
      S.forwardClassMass u i = μ.real A + ∫ x in A, MissingFlow.direction μ u x ∂μ := by
    have h := integrableTilt_real_set (MissingFlow.direction μ u)
      (MissingFlow.integrable_direction hu.integrable)
      (MissingFlow.direction_ge_neg_one hu.nonnegative hu.supply_le_one)
      1 ⟨by norm_num, le_rfl⟩ A hA
    simpa only [forwardClassMass, missingFlowEndpointLaw, A, one_mul] using h
  have hdir : (∫ x in A, MissingFlow.direction μ (fun p => (1 - θ) * q p + θ * r p) x ∂μ) =
      (1 - θ) * (∫ x in A, MissingFlow.direction μ q x ∂μ) +
        θ * ∫ x in A, MissingFlow.direction μ r x ∂μ := by
    rw [integral_congr_ae (Measure.absolutelyContinuous_restrict.ae_le (hq.direction_affine hr θ)),
      integral_add ((MissingFlow.integrable_direction hq.integrable).restrict.const_mul _)
        ((MissingFlow.integrable_direction hr.integrable).restrict.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hmass _ (hq.convex hr θ hθ), hdir]
  unfold ForwardPeak.affineMass
  rw [hmass q hq, hmass r hr]
  ring

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The actual endpoint missing density is the sum of squares of these
same original class masses, with genuine clique dust contributing zero. -/
theorem missing_density_eq_classMass_sq (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    1 - 2 * density hq.endpoint = ∑' i, (S.forwardClassMass q i) ^ 2 := by
  let := hq.endpoint_probability
  let : Countable S.I := S.hI.to_subtype
  apply MultipartiteClassMasses.one_sub_two_density_eq_tsum_classMass_sq
    hq.endpoint S.collapsedPartLabel S.measurable_collapsedPartLabel
  filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
  split_ifs at hp ⊢ <;> exact hp

/-- The actual physical own-profile comparison bounds the endpoint objective
by its actual supremum class mass squared, including the pure-dust case. -/
theorem objective_le_peak_sq (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    objective hq.endpoint ≤ (ForwardPeak.massPeak (S.forwardClassMass q)) ^ 2 := by
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hbdd : BddAbove (insert (0 : ℝ) (range (S.forwardClassMass q))) := by
    refine ⟨1, ?_⟩
    rintro x (rfl | ⟨i, rfl⟩)
    · exact zero_le_one
    · exact (hq.classMass_properties.1 i).2
  apply MultipartiteClassMasses.objective_le_class_bound_sq hq.endpoint (hq.endpoint_fullFeasible hW.full)
    S.collapsedPartLabel S.measurable_collapsedPartLabel
  · filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
    split_ifs at hp ⊢ <;> exact hp
  · intro i
    exact le_csSup hbdd (Or.inr (mem_range_self i))

/-- Every actual full forward flow has an attained positive separated peak.
Both gap signs and the original multiplier sign are derived from the same
strict-gap model; no additional slope range is assumed. -/
theorem exists_separated_peak (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ i, 0 < S.forwardClassMass q i ∧
      ForwardPeak.massPeak (S.forwardClassMass q) = S.forwardClassMass q i ∧
      0 < forwardPeakGap d c m ∧
      ForwardPeak.IsSeparatedPeak (S.forwardClassMass q) (forwardPeakGap d c m) i := by
  have hs := hW.strict_gap_structure hd hgap
  have hgamma : 0 < 2 * (c - m * d) + m := hs.gamma_pos
  have hbase := Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩
  have hdelta : 0 < 2 * c - (1 - 2 * d) := by linarith
  have hE := hq.energy_nonnegative hW hd hgap
  have hbudget := hq.endpoint_budget hW
  have hcost := hq.objective_le_peak_sq hW hd hgap
  have hreturn := hq.endpoint_density_gt hW hd hgap
  have hmass := hq.classMass_properties
  exact ForwardPeak.exists_separated_peak_of_summable_budget (S.forwardClassMass q)
    hmass.2.1 (fun i => (hmass.1 i).1) hmass.2.2 hgamma hdelta (neg_nonneg.mpr hs.multiplier_neg.le)
    (hq.missing_density_eq_classMass_sq hW hd hgap).symm.le
    (show 1 - 2 * density hq.endpoint < 1 - 2 * d by linarith)
    (show 2 * (c - m * d) + m = (1 - -m) * (1 - 2 * d) + (2 * c - (1 - 2 * d)) by ring)
    (show 2 * (c - m * d) + m ≤
      2 * (ForwardPeak.massPeak (S.forwardClassMass q)) ^ 2 - -m * (1 - 2 * density hq.endpoint) by
      nlinarith)

end IsFullForwardFlow

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- One and only one original independent-class label is the positive,
uniformly separated peak for every actual full forward flow. Convexity,
affine actual class masses, and all endpoint budgets are proved internally. -/
theorem exists_unique_common_forward_peak (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < forwardPeakGap d c m ∧ ∃! i : S.I, ∀ (q : Ω × Ω → ℝ), S.IsFullForwardFlow q →
      0 < S.forwardClassMass q i ∧
      ForwardPeak.massPeak (S.forwardClassMass q) = S.forwardClassMass q i ∧
      ForwardPeak.IsSeparatedPeak (S.forwardClassMass q) (forwardPeakGap d c m) i := by
  obtain ⟨q₀, hq₀⟩ := S.exists_fullForwardFlow
  obtain ⟨i₀, _, _, hΔ, hi₀⟩ := hq₀.exists_separated_peak hW hd hgap
  have hall (q : Ω × Ω → ℝ) (hq : S.IsFullForwardFlow q) :
      0 < S.forwardClassMass q i₀ ∧
      ForwardPeak.massPeak (S.forwardClassMass q) = S.forwardClassMass q i₀ ∧
      ForwardPeak.IsSeparatedPeak (S.forwardClassMass q) (forwardPeakGap d c m) i₀ := by
    have hpeak (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
        ∃ i, ForwardPeak.IsSeparatedPeak
          (ForwardPeak.affineMass (S.forwardClassMass q₀) (S.forwardClassMass q) θ)
          (forwardPeakGap d c m) i := by
      obtain ⟨i, _, _, _, hi⟩ := (hq₀.convex hq θ hθ).exists_separated_peak hW hd hgap
      have heq : S.forwardClassMass (fun p => (1 - θ) * q₀ p + θ * q p) =
          ForwardPeak.affineMass (S.forwardClassMass q₀) (S.forwardClassMass q) θ :=
        funext (hq₀.classMass_affine hq θ hθ)
      rw [heq] at hi
      exact ⟨i, hi⟩
    obtain ⟨i, hi⟩ := ForwardPeak.exists_common_separated_peak
      (S.forwardClassMass q₀) (S.forwardClassMass q) hq₀.classMass_properties.1
      hq.classMass_properties.1 (forwardPeakGap d c m) hΔ hpeak
    have hstart : ForwardPeak.IsSeparatedPeak (S.forwardClassMass q₀) (forwardPeakGap d c m) i := by
      intro j hj
      simpa only [ForwardPeak.affineMass, sub_zero, one_mul, zero_mul, add_zero] using
        hi 0 ⟨le_rfl, zero_le_one⟩ j hj
    have heq : i = i₀ := hstart.unique hi₀ hΔ
    have hend : ForwardPeak.IsSeparatedPeak (S.forwardClassMass q) (forwardPeakGap d c m) i₀ := by
      have hh := hi 1 ⟨zero_le_one, le_rfl⟩
      rw [heq] at hh
      intro j hj
      simpa only [ForwardPeak.affineMass, sub_self, zero_mul, one_mul, zero_add] using hh j hj
    obtain ⟨j, hj, hmax, _, hsep⟩ := hq.exists_separated_peak hW hd hgap
    have hjEq : j = i₀ := hsep.unique hend hΔ
    exact ⟨hjEq ▸ hj, hjEq ▸ hmax, hend⟩
  refine ⟨hΔ, i₀, hall, ?_⟩
  intro j hj
  exact (hj q₀ hq₀).2.2.unique hi₀ hΔ

/-- The actual full-forward endpoint budget also forces the original
positive slope below two. The slope range is a conclusion in this selected
structure, not a premise of the common-peak theorem. -/
theorem forward_slope_mem_Ioo (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    -m ∈ Ioo (0 : ℝ) 2 := by
  have hs := hW.strict_gap_structure hd hgap
  refine ⟨neg_pos.mpr hs.multiplier_neg, ?_⟩
  obtain ⟨q, hq⟩ := S.exists_fullForwardFlow
  obtain ⟨i, _, hpeak, _, _⟩ := hq.exists_separated_peak hW hd hgap
  have hmass := hq.classMass_properties
  have hsumSq : Summable (fun j => (S.forwardClassMass q j) ^ 2) :=
    hmass.2.1.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => by
      nlinarith [(hmass.1 j).1, (hmass.1 j).2])
  have hsingle : (S.forwardClassMass q i) ^ 2 ≤ 1 - 2 * density hq.endpoint :=
    (hsumSq.le_tsum i (fun j _ => sq_nonneg _)).trans_eq
      (hq.missing_density_eq_classMass_sq hW hd hgap).symm
  have hE := hq.energy_nonnegative hW hd hgap
  have hbudget := hq.endpoint_budget hW
  have hcost := hq.objective_le_peak_sq hW hd hgap
  rw [hpeak] at hcost
  have hgamma : 0 < 2 * (c - m * d) + m := hs.gamma_pos
  by_contra hnot
  have hlarge : 2 ≤ -m := le_of_not_gt hnot
  have hmissing : 0 ≤ 1 - 2 * density hq.endpoint := (sq_nonneg _).trans hsingle
  nlinarith [mul_nonneg (sub_nonneg.mpr hlarge) hmissing]

end SelectedHighLowStructure

end Erdos1017.CappedModel

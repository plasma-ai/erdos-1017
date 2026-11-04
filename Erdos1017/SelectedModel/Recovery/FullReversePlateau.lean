module

public import Erdos1017.SelectedModel.Recovery.FullReverseFlowClass
public import Erdos1017.SelectedModel.Flows.FlowClassMasses

/-!
# Plateau of the full reverse endpoint

Reverse-endpoint class masses on the original labels are summable with total at
most one; a positive endpoint plateau has fewer than two divided by the slope
members, and at most two in either slope regime
(`plateau_card_le_two_of_neg_multiplier_ge_two_thirds`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Actual reverse-endpoint masses on the same original independent-class
labels, including original classes removed by full HIGH supply. -/
def reverseClassMass (S : SelectedHighLowStructure W m) (q : Ω × Ω → ℝ) (i : S.I) : ℝ :=
  (missingFlowEndpointLaw μ q).real (S.collapsedPartLabel ⁻¹' {some i})

namespace IsFullReverseFlow

variable {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual endpoint class masses are nonnegative, summable and have total
at most one, with no finite-plateau or positive-anchor hypothesis. -/
theorem classMass_properties (hq : S.IsFullReverseFlow q) :
    (∀ i, S.reverseClassMass q i ∈ Icc (0 : ℝ) 1) ∧
      Summable (S.reverseClassMass q) ∧ (∑' i, S.reverseClassMass q i) ≤ 1 := by
  let := hq.endpoint_probability
  let : Countable S.I := S.hI.to_subtype
  exact ⟨fun i => ⟨MultipartiteClassMasses.classMass_nonneg _ _ i,
      MultipartiteClassMasses.classMass_le_one _ i⟩,
    MultipartiteClassMasses.classMass_summable _ S.measurable_collapsedPartLabel,
    MultipartiteClassMasses.tsum_classMass_le_one _ S.measurable_collapsedPartLabel⟩

/-- The actual endpoint independent-class square masses form a summable
family on the same countable original labels. -/
theorem classMass_sq_summable (hq : S.IsFullReverseFlow q) :
    Summable (fun i => (S.reverseClassMass q i) ^ 2) := by
  let := hq.endpoint_probability
  let : Countable S.I := S.hI.to_subtype
  exact MultipartiteClassMasses.classMass_sq_summable _ S.measurable_collapsedPartLabel

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Actual multipartite support identifies the reverse endpoint missing
density with the squares of these same original-label endpoint masses. -/
theorem missing_density_eq_classMass_sq (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    1 - 2 * density hq.endpoint = ∑' i, (S.reverseClassMass q i) ^ 2 := by
  let := hq.endpoint_probability
  let : Countable S.I := S.hI.to_subtype
  apply MultipartiteClassMasses.one_sub_two_density_eq_tsum_classMass_sq
    hq.endpoint S.collapsedPartLabel S.measurable_collapsedPartLabel
  filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
  split_ifs at hp ⊢ <;> exact hp

/-- An actual bound on every original-label reverse-endpoint mass bounds
the actual unchanged feasible endpoint objective, including pure dust. -/
theorem objective_le_mass_bound_sq (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (t : ℝ) (hbound : ∀ i, S.reverseClassMass q i ≤ t) : objective hq.endpoint ≤ t ^ 2 := by
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  apply MultipartiteClassMasses.objective_le_class_bound_sq hq.endpoint (hq.endpoint_fullFeasible hW.full)
    S.collapsedPartLabel S.measurable_collapsedPartLabel
  · filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
    split_ifs at hp ⊢ <;> exact hp
  · exact hbound

/-- A finite actual endpoint plateau pays its literal mass and square
mass in the full probability profile; no relaxed assignment is used. -/
theorem plateau_mass_bounds (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (P : Finset S.I) (t : ℝ) (hplateau : ∀ i ∈ P, S.reverseClassMass q i = t) :
    (P.card : ℝ) * t ≤ 1 ∧ (P.card : ℝ) * t ^ 2 ≤ 1 - 2 * density hq.endpoint := by
  have hsum : (∑ i ∈ P, S.reverseClassMass q i) = (P.card : ℝ) * t := by
    calc
      _ = ∑ _i ∈ P, t := Finset.sum_congr rfl hplateau
      _ = _ := by simp
  have hsq : (∑ i ∈ P, (S.reverseClassMass q i) ^ 2) = (P.card : ℝ) * t ^ 2 := by
    calc
      _ = ∑ _i ∈ P, t ^ 2 := Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => x ^ 2) (hplateau i hi))
      _ = _ := by simp
  refine ⟨?_, ?_⟩
  · rw [← hsum]
    exact (hq.classMass_properties.2.1.sum_le_tsum P
      (fun i _ => (hq.classMass_properties.1 i).1)).trans hq.classMass_properties.2.2
  · rw [hq.missing_density_eq_classMass_sq hW hd hgap, ← hsq]
    exact hq.classMass_sq_summable.sum_le_tsum P (fun i _ => sq_nonneg _)

/-- The old original-model budget of an actual reverse endpoint is bounded
by its actual mass cap, retaining the full endpoint square moment and energy. -/
theorem plateau_budget (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (P : Finset S.I) (t : ℝ) (hbound : ∀ i, S.reverseClassMass q i ≤ t)
    (hplateau : ∀ i ∈ P, S.reverseClassMass q i = t) :
    (2 * (c - m * d) + m) +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) ≤
      2 * t ^ 2 + m * (1 - 2 * density hq.endpoint) ∧
      2 * t ^ 2 + m * (1 - 2 * density hq.endpoint) ≤ (2 + m * P.card) * t ^ 2 := by
  have hcost := hq.objective_le_mass_bound_sq hW hd hgap t hbound
  have hbudget := hq.endpoint_budget hW
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hsq := (hq.plateau_mass_bounds hW hd hgap P t hplateau).2
  refine ⟨by linarith, ?_⟩
  have hmul := mul_le_mul_of_nonpos_left hsq hm.le
  nlinarith

/-- A positive actual endpoint plateau is strictly smaller than two divided
by the original positive slope. Its mass cap and equalities are physical. -/
theorem plateau_card_lt_two_div_neg_multiplier (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (P : Finset S.I) (t : ℝ) (ht : 0 < t)
    (hbound : ∀ i, S.reverseClassMass q i ≤ t)
    (hplateau : ∀ i ∈ P, S.reverseClassMass q i = t) :
    (P.card : ℝ) < 2 / (-m) := by
  have hs := hW.strict_gap_structure hd hgap
  have hE := hq.energy_nonnegative hW hd hgap
  have hb := hq.plateau_budget hW hd hgap P t hbound hplateau
  have hprod : 0 < (2 + m * P.card) * t ^ 2 := lt_of_lt_of_le
    (lt_of_lt_of_le hs.gamma_pos (le_add_of_nonneg_right hE)) (hb.1.trans hb.2)
  have hcoef : 0 < 2 + m * P.card := (mul_pos_iff.mp hprod).elim And.left
    (fun h => False.elim ((not_lt_of_ge (sq_pos_of_pos ht).le) h.2))
  apply (lt_div_iff₀ (neg_pos.mpr hs.multiplier_neg)).mpr
  nlinarith

/-- The actual reverse endpoint pays both its original nonnegative energy
and its strictly positive density-decrease credit against the mass cap. -/
theorem endpoint_credit (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (t : ℝ) (hbound : ∀ i, S.reverseClassMass q i ≤ t) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) ∧
      density hq.endpoint < d ∧
      c + KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) / 2 +
          (-m) * (d - density hq.endpoint) ≤ t ^ 2 ∧ c < t ^ 2 := by
  have hE := hq.energy_nonnegative hW hd hgap
  have hdend := hq.endpoint_density_lt hW hd hgap
  have hcost := hq.objective_le_mass_bound_sq hW hd hgap t hbound
  have hbudget := hq.endpoint_budget hW
  have hcredit : 0 < (-m) * (d - density hq.endpoint) :=
    mul_pos (neg_pos.mpr (hW.strict_gap_structure hd hgap).multiplier_neg) (sub_pos.mpr hdend)
  refine ⟨hE, hdend, ?_, ?_⟩ <;> nlinarith

/-- The actual plateau has at most two members when the original slope
is at least two thirds. No plateau premise is inferred from a relaxation. -/
theorem plateau_card_le_two_of_neg_multiplier_ge_two_thirds (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (P : Finset S.I) (t : ℝ) (ht : 0 < t)
    (hbound : ∀ i, S.reverseClassMass q i ≤ t)
    (hplateau : ∀ i ∈ P, S.reverseClassMass q i = t)
    (hslope : (2 / 3 : ℝ) ≤ -m) : P.card ≤ 2 := by
  have hcard := hq.plateau_card_lt_two_div_neg_multiplier hW hd hgap P t ht hbound hplateau
  have hm := neg_pos.mpr (hW.strict_gap_structure hd hgap).multiplier_neg
  have hmul := (lt_div_iff₀ hm).mp hcard
  by_contra hn
  have hn' : (3 : ℝ) ≤ P.card := by exact_mod_cast (show 3 ≤ P.card by omega)
  have hmono := mul_le_mul_of_nonneg_left hslope (show (0 : ℝ) ≤ P.card by positivity)
  nlinarith

/-- In the smaller-slope regime, original missing density above one twelfth
and the genuine strict benchmark gap also force at most two plateau members. -/
theorem plateau_card_le_two_of_half_lt_neg_multiplier (hq : S.IsFullReverseFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (P : Finset S.I) (t : ℝ) (ht : 0 < t)
    (hbound : ∀ i, S.reverseClassMass q i ≤ t)
    (hplateau : ∀ i ∈ P, S.reverseClassMass q i = t)
    (hslope : (1 / 2 : ℝ) < -m) (hmissing : (1 / 12 : ℝ) < 1 / 2 - d) :
    P.card ≤ 2 := by
  by_cases hlarge : (2 / 3 : ℝ) ≤ -m
  · exact hq.plateau_card_le_two_of_neg_multiplier_ge_two_thirds hW hd hgap P t ht hbound hplateau hlarge
  have hsmall : -m < 2 / 3 := lt_of_not_ge hlarge
  have hc : 1 / 2 - d < c :=
    (Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩).trans_lt hgap
  have hprod := mul_lt_mul_of_pos_right (show (1 / 3 : ℝ) < 1 + m by linarith)
    (show 0 < 1 / 2 - d by linarith)
  have hprod' := mul_lt_mul_of_pos_left hmissing (show (0 : ℝ) < 1 / 3 by norm_num)
  have hgamma : (1 / 18 : ℝ) < 2 * (c - m * d) + m := by nlinarith
  by_contra hn
  have hn' : (3 : ℝ) ≤ P.card := by exact_mod_cast (show 3 ≤ P.card by omega)
  have hmass := (hq.plateau_mass_bounds hW hd hgap P t hplateau).1
  have htbound : t ≤ 1 / 3 := by nlinarith
  have hsq : t ^ 2 ≤ 1 / 9 := by nlinarith
  have hb := hq.plateau_budget hW hd hgap P t hbound hplateau
  have hE := hq.energy_nonnegative hW hd hgap
  have hcoeff : 2 + m * P.card ≤ 2 + 3 * m := by
    nlinarith [mul_le_mul_of_nonpos_left hn' (by linarith : m ≤ 0)]
  have hfirst := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg t)
  have hsecond := mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ 2 + 3 * m)
  nlinarith

end IsFullReverseFlow

end Erdos1017.CappedModel.SelectedHighLowStructure

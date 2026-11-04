module

public import Erdos1017.Exclusions.Common.Flows.FullForwardSharpSelector
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.Exclusions.SmoothW.SmoothWScalarExclusion
public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.Benchmark.BenchmarkHeadCountGuards

/-!
# Sharp peak estimates at the smooth `W` contact

Strict activity selects the smooth mixed benchmark derivative, the strictly
active smooth-`W` contact derives its original multiplier, family interval and
intercept floor from global comparison (`smoothW_contact_parameters`), and the
same-peak avoiding flow with the sharp selector bounds forces the quantitative
smooth-`W` peak estimates (`exists_sharp_smoothW_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical Topology

namespace Erdos1017.Benchmark

/-- Strict activity selects the actual smooth mixed benchmark derivative. -/
theorem benchmark_mixed_hasDerivAt_strict {d : ℝ} (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (he : 1 / 2 - d ∈ Ioo epsilonStar epsilonD)
    (hactive : twoHeadCurve (1 / 2 - d) < mixedCurve (1 / 2 - d)) :
    HasDerivAt benchmark (-((mixedInverse (1 / 2 - d) + 1) /
      (3 * mixedInverse (1 / 2 - d)))) d := by
  have hedom : 1 / 2 - d ∈ Ioo (0 : ℝ) (1 / 4) := by constructor <;> linarith [hd.1, hd.2]
  have hm := (mixedCurve_continuousOn _ ⟨hedom.1.le, hedom.2.le⟩).continuousAt
    (Icc_mem_nhds hedom.1 hedom.2)
  have ht := (twoHeadCurve_continuousOn _ ⟨hedom.1.le, hedom.2.le⟩).continuousAt
    (Icc_mem_nhds hedom.1 hedom.2)
  have hnear := (ht.comp (by fun_prop : ContinuousAt (fun x : ℝ => 1 / 2 - x) d)).eventually_lt
    (hm.comp (by fun_prop : ContinuousAt (fun x : ℝ => 1 / 2 - x) d)) hactive
  have hder : HasDerivAt (fun x : ℝ => mixedCurve (1 / 2 - x))
      (-((mixedInverse (1 / 2 - d) + 1) / (3 * mixedInverse (1 / 2 - d)))) d := by
    convert (mixedCurve_hasDerivAt he).comp d
      ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)) using 1
    · rfl
    · ring
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hd.1 hd.2, hnear] with x hx hact
  change twoHeadCurve (1 / 2 - x) < mixedCurve (1 / 2 - x) at hact
  simp only [Erdos1017.benchmark, not_le.mpr hx.1, ite_false, hx.2, ite_true]
  exact max_eq_left hact.le

end Erdos1017.Benchmark

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m : ℝ}

/-- The actual strictly active smooth-W contact derives its original
multiplier, family interval and intercept floor from global comparison. -/
theorem FullStationaryClass.smoothW_contact_parameters (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    m = -((Benchmark.mixedInverse (1 / 2 - d) + 1) /
      (3 * Benchmark.mixedInverse (1 / 2 - d))) ∧
      Benchmark.mixedInverse (1 / 2 - d) ∈ Ioo (7 / 6 : ℝ) (19 / 15) ∧
      -m ∈ Ioo (1 / 2 : ℝ) (2 / 3) ∧ 1 + m < 101 / 250 ∧
      103 / 1000 < 2 * (c - m * d) + m ∧ 1 - 2 * d < 1163 / 5000 := by
  have hstructure := hW.strict_gap_structure hd hgap
  have hder := Benchmark.benchmark_mixed_hasDerivAt_strict hd he hactive
  have hm := full_stationary_multiplier_eq_benchmark_deriv W hW.full hglobal
    (by simpa only [hW.density_eq] using hder) m _ hW.stationary hstructure.nonconstant_degree
  have hguards := Benchmark.active_mixed_parameter_guards ⟨he.1.le, he.2.le⟩ hactive.le
  have hinverse := Benchmark.mixedInverse_spec ⟨he.1.le, he.2.le⟩
  let s := Benchmark.mixedInverse (1 / 2 - d)
  have hs : s ∈ Ioo (7 / 6 : ℝ) (19 / 15) :=
    ⟨hguards.1, hinverse.1.2.trans_lt Benchmark.sigmaZero_lt_nineteen_fifteenths⟩
  have hs0 : 0 < s := by linarith [hs.1]
  have hden : 0 < 3 * s := by positivity
  have hell : (s + 1) / (3 * s) ∈ Ioo (1 / 2 : ℝ) (2 / 3) := by
    constructor
    · apply (lt_div_iff₀ hden).mpr
      linarith [hs.2]
    · apply (div_lt_iff₀ hden).mpr
      linarith [hs.1]
  have heta : 1 - (s + 1) / (3 * s) < 101 / 250 := by
    have hlo : (149 / 250 : ℝ) < (s + 1) / (3 * s) := by
      apply (lt_div_iff₀ hden).mpr
      linarith [hs.2]
    linarith
  have hB : benchmark d = Benchmark.mixedValue s := by
    simp only [Erdos1017.benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true,
      max_eq_left hactive.le]
    simp only [Benchmark.mixedCurve, not_le.mpr he.1, ite_false, he.2.le, ite_true]
    rfl
  have hfloor := SmoothWScalar.mixed_intercept_gt ⟨hs.1.le, hs.2.le⟩
  rw [hinverse.2] at hfloor
  refine ⟨hm, hs, ?_, ?_, ?_, by linarith [hguards.2]⟩
  · simpa only [hm, neg_neg] using hell
  · rw [hm]
    change 1 + -((s + 1) / (3 * s)) < 101 / 250
    linarith
  · rw [hB] at hgap
    rw [hm]
    change 103 / 1000 < 2 * (c - -((s + 1) / (3 * s)) * d) - (s + 1) / (3 * s)
    nlinarith

/-- The actual same-peak avoiding flow and the derived sharp selector
bounds force the quantitative smooth-W peak estimates. No profile-cost,
multiplier, forward comparison, or original-largest hypothesis is supplied. -/
theorem SelectedHighLowStructure.exists_sharp_smoothW_peak
    (S : SelectedHighLowStructure W m) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      357 / 1000 < S.originalAtomMass i ∧
      103 / 1000 < 2 * (c - m * d) + m ∧
      2 * (c - m * d) + m < S.originalAtomMass i ∧
      (∀ r : Ω × Ω → ℝ, S.IsFullForwardFlow r →
        0 < S.forwardClassMass r i ∧
        ForwardPeak.massPeak (S.forwardClassMass r) = S.forwardClassMass r i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass r) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2 := by
  obtain ⟨_, _, hell, heta, hgamma, _⟩ := hW.smoothW_contact_parameters hd hgap he hactive hglobal
  obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hret := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  change S.forwardClassMass q i = S.originalAtomMass i at hret
  have hmax (k : S.I) : S.forwardClassMass q k ≤ S.forwardClassMass q i := by
    by_cases hki : k = i
    · rw [hki]
    · have hsep := (hpeak q hq).2.2 k hki
      linarith
  have hb := hq.endpoint_sharp_selector_bounds hW hd hgap i (hpeak q hq).1 hmax
  dsimp only at hb
  rw [hret] at hb
  have hbudget := hq.endpoint_budget hW
  have henergy := hq.energy_nonnegative hW hd hgap
  have hforward : 2 * (c - m * d) + m ≤
      2 * objective hq.endpoint - (-m) * (1 - 2 * density hq.endpoint) := by nlinarith
  have hell' : -m ∈ Icc (0 : ℝ) (2 / 3) := ⟨by linarith [hell.1], hell.2.le⟩
  have hthird : 1 / 3 < S.originalAtomMass i := by
    by_contra h
    have hsmall := hb.2.2.1 (le_of_not_gt h)
    have hc := hsmall.trans (min_le_left _ _)
    have hh := hsmall.trans (min_le_right _ _)
    have hscalar := SmoothWScalar.selector_intercept_bound (A := (1 / 3 : ℝ))
      (hF := 1 - 2 * density hq.endpoint) hell'
      (by norm_num; exact hc) (by norm_num; linarith)
    nlinarith
  have hlarge := hb.2.2.2.1 hthird.le
  have hscalar := SmoothWScalar.selector_intercept_bound
    (hF := 1 - 2 * density hq.endpoint) hell' hb.1 (by linarith [hlarge])
  have hsharp : 2 * (c - m * d) + m ≤ 2 * (1 + m) * (S.originalAtomMass i) ^ 2 := by
    nlinarith
  have hsq : (103 / 808 : ℝ) < (S.originalAtomMass i) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr heta.le) (sq_nonneg (S.originalAtomMass i))
    nlinarith
  have hmass : 357 / 1000 < S.originalAtomMass i := by
    by_contra h
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h))
      (show 0 ≤ S.originalAtomMass i + 357 / 1000 by linarith)
    nlinarith
  have hunit := (hq.classMass_properties.1 i).2
  rw [hret] at hunit
  have hstrict : 2 * (1 + m) * (S.originalAtomMass i) ^ 2 < (S.originalAtomMass i) ^ 2 := by
    have hp := mul_lt_mul_of_pos_right (show 2 * (1 + m) < 1 by linarith [hell.1])
      (sq_pos_of_pos hA)
    simpa only [one_mul] using hp
  have hsmallSq : (S.originalAtomMass i) ^ 2 ≤ S.originalAtomMass i := by nlinarith
  exact ⟨hΔ, i, hmass, hgamma, hsharp.trans_lt (hstrict.trans_le hsmallSq), hpeak, hlargest, hreserve⟩

end Erdos1017.CappedModel

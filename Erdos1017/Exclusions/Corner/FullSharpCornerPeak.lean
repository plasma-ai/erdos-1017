module

public import Erdos1017.Exclusions.Corner.BenchmarkWCornerContact
public import Erdos1017.Exclusions.Corner.CornerSharpSelector
public import Erdos1017.Exclusions.Common.Flows.FullForwardSharpSelector
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.ContactLocation.FullCuspContact

/-!
# Sharp corner peak of the selected model

The `W`/`E₂` crossing constrains the original multiplier by its one-sided slopes
and gives the rational corner intercept floor, and the corner contact with an
original-peak avoiding endpoint forces `A > 1/3`, with the sharp selector,
feasibility, energy and multiplier premises derived.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m : ℝ}

/-- The actual W/E2 crossing constrains the original multiplier by its
own one-sided slopes and derives the rational corner intercept floor.
No smooth-W multiplier identification is made at this corner. -/
theorem FullStationaryClass.corner_contact_parameters (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    -m ∈ Icc (363 / 589 : ℝ) (9 / 11) ∧
      (138261458236451 : ℝ) / 1116960975000000 < c ∧
      1 - 2 * d < 23243417 / 10 ^ 8 ∧
      2 * (138261458236451 / 1116960975000000 : ℝ) - (-m) * (23243417 / 10 ^ 8) <
        2 * (c - m * d) + m := by
  have hbox := (Benchmark.crossing_contact_location he heq).1
  have hder := Benchmark.benchmark_corner_one_sided_derivatives hd he heq
  have hbracket := hW.multiplier_mem_one_sided_slopes_of_strict_gap hd hgap hglobal hder.1 hder.2
  have hslopes := Benchmark.crossing_box_slope_guards ⟨hbox.1.le, hbox.2.le⟩
  have hell : -m ∈ Icc (363 / 589 : ℝ) (9 / 11) := by
    constructor <;> linarith [hbracket.1, hbracket.2, hslopes.1, hslopes.2.2]
  have hB : benchmark d = Benchmark.mixedCurve (1 / 2 - d) := by
    simp only [Erdos1017.benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true, heq, max_self]
  have hc : (138261458236451 : ℝ) / 1116960975000000 < c := by
    rw [hB] at hgap
    exact (Benchmark.crossing_box_value_lower hbox).trans hgap
  have hh : 1 - 2 * d < (23243417 / 10 ^ 8 : ℝ) := by linarith [hbox.2]
  refine ⟨hell, hc, hh, ?_⟩
  have hp := mul_pos (show 0 < -m by linarith [hell.1]) (sub_pos.mpr hh)
  nlinarith

/-- The actual corner contact and same original-peak avoiding endpoint
force A>1/3. All sharp selector, feasibility, energy and multiplier
premises are derived. The reverse-recovery, private and saturated exits are not
covered here. -/
theorem SelectedHighLowStructure.exists_sharp_corner_peak
    (S : SelectedHighLowStructure W m) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      1 / 3 < S.originalAtomMass i ∧
      (∀ r : Ω × Ω → ℝ, S.IsFullForwardFlow r →
        0 < S.forwardClassMass r i ∧
        ForwardPeak.massPeak (S.forwardClassMass r) = S.forwardClassMass r i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass r) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2 := by
  obtain ⟨hell, _, _, hfloor⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
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
  have hthird := CornerSelector.third_lt_of_sharp_cells hell hA hb.2.1 hb.1 hforward hfloor
    hb.2.2.2.2.1 hb.2.2.2.2.2
  exact ⟨hΔ, i, hthird, hpeak, hlargest, hreserve⟩

end Erdos1017.CappedModel

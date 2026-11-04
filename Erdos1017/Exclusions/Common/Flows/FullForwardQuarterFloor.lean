module

public import Erdos1017.Exclusions.Common.Flows.ForwardSelectorQuarterBound
public import Erdos1017.Exclusions.Common.E2.FullE2ContactCurvature

/-!
# Quarter floor from the forward selector

At smooth `E₂` contact the multiplier comes with a strict gamma floor, a forward
selector envelope forces the quarter floor in the upper lower-`E₂` interval, and
the common peak of a selected high-low structure has mass greater than one
quarter with its reserve and strict square majority.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

/-- The original multiplier and strict gamma floor belong to the same
actual smooth E2 contact. Global comparison derives the multiplier identity. -/
theorem FullStationaryClass.e2_gamma_floor (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    m = -LowerE2Scalar.multiplier q ∧ -m ∈ Ioo (0 : ℝ) 1 ∧
      LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m := by
  have hm := (hW.e2_contact_curvature hq hdq hgap hglobal).1
  have hbounds : LowerE2Scalar.multiplier q ∈ Ioo (0 : ℝ) 1 := by
    have hden : 0 < 2 + q := by linarith [hq.1]
    constructor
    · exact div_pos (by linarith [hq.2]) hden
    · exact (div_lt_one hden).mpr (by linarith [hq.1])
  refine ⟨hm, by simpa only [hm, neg_neg] using hbounds, ?_⟩
  have hB : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3) := by
    rw [hdq]
    exact Benchmark.benchmark_e2_q hq
  rw [LowerE2Scalar.gapFloor_eq_twoHeadValue hq.1.le, hm, hdq]
  rw [hB] at hgap
  nlinarith

/-- Any proved forward selector envelope forces the quarter floor in the
upper lower-E2 interval. The actual selected wrapper below derives that envelope. -/
theorem FullStationaryClass.e2_selector_quarter_floor (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (2 / 15 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    {A : ℝ} (hA : 0 ≤ A)
    (henvelope : 2 * (c - m * d) + m ≤ ForwardPeak.selectorEnvelope (-m) A) :
    1 / 4 < A := by
  obtain ⟨hm, hell, hfloor⟩ := hW.e2_gamma_floor ⟨by linarith [hq.1], hq.2⟩ hdq hgap hglobal
  by_contra h
  have hbound := ForwardPeak.selectorEnvelope_le_quarter ⟨hell.1.le, hell.2.le⟩
    ⟨hA, le_of_not_gt h⟩
  have hstrict := LowerE2Scalar.quarter_gap_pos hq.1
  rw [hm] at hfloor
  rw [hm, neg_neg] at henvelope
  rw [hm, neg_neg] at hbound
  linarith

/-- The same actual original common peak has mass greater than one quarter,
with its original reserve and strict square majority retained. No envelope,
profile, saturation, or nonuniversality premise is supplied. -/
theorem SelectedHighLowStructure.exists_original_forward_quarter_peak
    (S : SelectedHighLowStructure W m) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (2 / 15 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      1 / 4 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      (∀ (r : Ω × Ω → ℝ), S.IsFullForwardFlow r →
        0 < S.forwardClassMass r i ∧
        ForwardPeak.massPeak (S.forwardClassMass r) = S.forwardClassMass r i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass r) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2) ∧
      ((∑' k : {k : S.I // k ≠ i}, (S.originalAtomMass k.val) ^ 2) <
        (S.originalAtomMass i) ^ 2) ∧
      2 * (c - m * d) + m ≤ ForwardPeak.selectorEnvelope (-m) (S.originalAtomMass i) := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith [hq.1], hq.2⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq'
  have hell := (hW.e2_gamma_floor hq' hdq hgap hglobal).2.1.2
  obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, hmajority, henvelope⟩ :=
    S.exists_original_forward_selector_envelope hW hd hgap hell
  exact ⟨hΔ, i, hW.e2_selector_quarter_floor hq hdq hgap hglobal hA.le henvelope,
    hside, hpeak, hlargest, hreserve, hmajority, henvelope⟩

end Erdos1017.CappedModel

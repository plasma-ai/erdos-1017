module

public import Erdos1017.Exclusions.E2.Upper.UpperE2ParameterGuards
public import Erdos1017.Exclusions.Common.Flows.ForwardSelectorQuarterBound
public import Erdos1017.Exclusions.Common.Flows.FullForwardSharpSelector
public import Erdos1017.SelectedModel.Selection.FullSmoothContact

/-!
# Upper `E₂` forward peak exceeds one third

At an upper-`E₂` two-head benchmark contact, the same original forward peak
exceeds one third, with explicit value and derivative contact guards
(`exists_original_upper_e2_peak_gt_third`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace Erdos1017.LowerE2Scalar

private theorem upper_third_gap {q : ℝ}
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000)) :
    (4 - 3 * multiplier q) / 27 < gapFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hq2 : q + 2 ≠ 0 := by linarith
  have hid : (gapFloor q - (4 - 3 * multiplier q) / 27) *
      (54 * denominator q * (q + 2)) =
      40 * q ^ 3 + 33 * q ^ 2 + 12 * q - 4 := by
    unfold gapFloor multiplier
    field_simp
    unfold denominator
    ring
  have h2 : (1 / 5 : ℝ) ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hq.1 2
  have h3 : (1 / 5 : ℝ) ^ 3 ≤ q ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hq.1 3
  have hpoly : 0 < 40 * q ^ 3 + 33 * q ^ 2 + 12 * q - 4 := by
    nlinarith [h2, h3, hq.1]
  rw [← hid] at hpoly
  have hden : 0 < 54 * denominator q * (q + 2) := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hpoly)

private theorem upper_D_le_third {ell A : ℝ}
    (hell : ell ∈ Ioc (4 / 5 : ℝ) (9 / 11))
    (hA : A ∈ Icc (1 / 4 : ℝ) (1 / 3)) :
    (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 ≤
      (4 - 3 * ell) / 27 := by
  have hcoef : 0 ≤ 7 + 6 * ell := by linarith [hell.1]
  have hsum : A + 1 / 3 ≤ (2 / 3 : ℝ) := by linarith [hA.2]
  have hprod := mul_le_mul_of_nonneg_left hsum hcoef
  have hbracket : 0 ≤ 8 - (7 + 6 * ell) * (A + 1 / 3) := by
    nlinarith [hprod, hell.2]
  have hnonneg := mul_nonneg (sub_nonneg.mpr hA.2) hbracket
  nlinarith [hnonneg]

end Erdos1017.LowerE2Scalar

namespace Erdos1017.CappedModel

private theorem upper_gamma_floor {q d c m : ℝ}
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hm : m = -LowerE2Scalar.multiplier q)
    (hgap : benchmark d < c) :
    LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m := by
  have hid := LowerE2Scalar.gapFloor_eq_twoHeadValue (show 0 ≤ q by linarith [hq.1])
  rw [hvalue] at hgap
  rw [hm, hdq]
  nlinarith [hid, hgap]

end Erdos1017.CappedModel

namespace Erdos1017.LowerE2Scalar

private theorem upper_D_of_sharp_budget {A ell σ C γ E : ℝ}
    (hA : 0 < A) (hell : 4 / 5 < ell) (hσ : 0 ≤ σ) (hE : 0 ≤ E)
    (hC : C ≤ A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12 + σ / 3)
    (hbudget : γ + E = 2 * C - ell * (A ^ 2 + σ)) :
    γ ≤ (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hid : 2 * (A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12) -
      ell * A ^ 2 = (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 := by
    field_simp
    ring
  have hσterm : (2 / 3 - ell) * σ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hσ
  nlinarith [hid, hC, hbudget, hE, hσterm]

end Erdos1017.LowerE2Scalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- At a genuine upper-E2 two-head benchmark contact, the same original
forward peak exceeds one third. The value and derivative contact guards are
explicit because activity beyond one fifth is not asserted here. -/
theorem exists_original_upper_e2_peak_gt_third
    (S : SelectedHighLowStructure W m)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      1 / 3 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      (∀ (v : Ω × Ω → ℝ), S.IsFullForwardFlow v →
        0 < S.forwardClassMass v i ∧
        ForwardPeak.massPeak (S.forwardClassMass v) = S.forwardClassMass v i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass v) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2) ∧
      ((∑' k : {k : S.I // k ≠ i}, (S.originalAtomMass k.val) ^ 2) <
        (S.originalAtomMass i) ^ 2) := by
  have hmass := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith [hmass.1, hmass.2]
  have hs := hW.strict_gap_structure hd hgap
  have hderivW : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) (density W) := by
    rw [hW.density_eq]
    exact hderiv
  have hm : m = -LowerE2Scalar.multiplier q :=
    full_stationary_multiplier_eq_benchmark_deriv W hW.full hglobal hderivW
      m _ hW.stationary hs.nonconstant_degree
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hell := UpperE2Parameter.multiplier_mem hq
  have hellm : -m < 1 := by rw [hm]; linarith [hell.2]
  have hγfloor := upper_gamma_floor hq hdq hvalue hm hgap
  obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, hmajority, henv⟩ :=
    S.exists_original_forward_selector_envelope hW hd hgap hellm
  let A := S.originalAtomMass i
  have hAqu : 1 / 4 < A := by
    by_contra hn
    have hAquarter : A ∈ Icc (0 : ℝ) (1 / 4) := ⟨hA.le, le_of_not_gt hn⟩
    have henvbound := ForwardPeak.selectorEnvelope_le_quarter
      (ell := -m) (A := A)
      ⟨by rw [hm]; linarith [hell.1], by rw [hm]; linarith [hell.2]⟩ hAquarter
    have hgapquarter := LowerE2Scalar.quarter_gap_pos (q := q) (by linarith [hq.1])
    rw [hneg] at henv henvbound
    change 2 * (c - m * d) + m ≤
      ForwardPeak.selectorEnvelope (LowerE2Scalar.multiplier q) A at henv
    nlinarith [hγfloor, henv, henvbound, hgapquarter]
  have hAthird : 1 / 3 < A := by
    by_contra hn
    have hAinterval : A ∈ Icc (1 / 4 : ℝ) (1 / 3) :=
      ⟨hAqu.le, le_of_not_gt hn⟩
    have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L := by
      rcases hside with hH | hN
      · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
      · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
    obtain ⟨v, hv, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
    have hret := hv.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
    have hmax (k : S.I) : S.forwardClassMass v k ≤ S.forwardClassMass v i := by
      by_cases hki : k = i
      · rw [hki]
      · have hsep := (hpeak v hv).2.2 k hki
        linarith
    obtain ⟨_, hσraw, _, _, hmiddle, _⟩ :=
      hv.endpoint_sharp_selector_bounds hW hd hgap i (hpeak v hv).1 hmax
    let σ := 1 - 2 * density hv.endpoint - A ^ 2
    rw [hret] at hσraw hmiddle
    have hσ : 0 ≤ σ := by
      change 0 ≤ σ at hσraw
      exact hσraw
    have hT : (1 - A) / A ∈ Icc (2 : ℝ) 3 := by
      constructor
      · apply (le_div_iff₀ hA).mpr
        nlinarith [hAinterval.2]
      · apply (div_le_iff₀ hA).mpr
        nlinarith [hAinterval.1]
    have hC : objective hv.endpoint ≤
        A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12 + σ / 3 := by
      change (1 - A) / A ∈ Icc (2 : ℝ) 3 →
        objective hv.endpoint ≤
          A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12 + σ / 3
        at hmiddle
      exact hmiddle hT
    let γ := 2 * (c - m * d) + m
    let E := KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ v)
    let ell := LowerE2Scalar.multiplier q
    have hE : 0 ≤ E := hv.energy_nonnegative hW hd hgap
    have hbudget : γ + E = 2 * objective hv.endpoint - ell * (A ^ 2 + σ) := by
      have hb := hv.endpoint_budget hW
      have hmul := congrArg (fun z : ℝ => z * (1 - 2 * density hv.endpoint)) hm
      dsimp [γ, E, ell, A, σ]
      nlinarith [hb, hmul]
    have hD := LowerE2Scalar.upper_D_of_sharp_budget hA hell.1 hσ hE hC hbudget
    have hDthird := LowerE2Scalar.upper_D_le_third hell hAinterval
    have hgapthird := LowerE2Scalar.upper_third_gap hq
    dsimp [γ, ell, A] at hD hDthird
    nlinarith [hγfloor, hD, hDthird, hgapthird]
  exact ⟨hΔ, i, hAthird, hside, hpeak, hlargest, hreserve, hmajority⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

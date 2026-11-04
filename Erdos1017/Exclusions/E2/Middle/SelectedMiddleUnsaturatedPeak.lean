module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedCount
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2Joined
public import Erdos1017.Exclusions.Common.Flows.FullForwardSelectorEnvelope
public import Erdos1017.Exclusions.Common.Flows.ForwardSelectorQuarterBound
public import Erdos1017.Exclusions.Common.Flows.FullForwardSharpSelector

/-!
# No-saturation entry and peak bound on the middle range

With the original saturated set product-null, the selected model has
`q > 187/1000` and `3c ≤ d` (`exists_middle_unsaturated_entry`), and on the
closed range `187/1000 ≤ q ≤ 1/5` the original common peak exceeds `3/10`
(`middle_unsaturated_peak_gt_three_tenths`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

/-- On the closed remaining no-saturation range `187/1000 <= q <= 1/5`,
the actual original common peak exceeds `3/10`. The quarter floor comes
from the original forward selector envelope; the middle sharp count cell
gives `gamma <= D_ell(A)` on `[1/4, 1/3]`, and the closed-range certificate
puts `D_ell(A)` below the gap floor on `[1/4, 3/10]`. -/
theorem middle_unsaturated_peak_gt_three_tenths (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (k : S.I) (hpeak : S.IsCommonForwardPeak d c k) :
    3 / 10 < S.originalAtomMass k := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hellI, hγfloor⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  obtain ⟨hΔ, i, hA, hside, hpeaki, _, _, _, henv⟩ :=
    S.exists_original_forward_selector_envelope hW hd hgap hellI.2
  have hik : i = k := (hpeaki S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst hik
  let A := S.originalAtomMass i
  have hAqu : 1 / 4 < A := by
    by_contra hn
    have hAquarter : A ∈ Icc (0 : ℝ) (1 / 4) := ⟨hA.le, le_of_not_gt hn⟩
    have henvbound := ForwardPeak.selectorEnvelope_le_quarter
      (ell := -m) (A := A) ⟨by linarith [hellI.1], hellI.2.le⟩ hAquarter
    have hgapquarter := LowerE2Scalar.quarter_gap_pos (q := q) (by linarith [hq.1])
    rw [hneg] at henv henvbound
    change 2 * (c - m * d) + m ≤
      ForwardPeak.selectorEnvelope (LowerE2Scalar.multiplier q) A at henv
    linarith
  by_contra hn
  have hA310 : A ∈ Icc (1 / 4 : ℝ) (3 / 10) := ⟨hAqu.le, le_of_not_gt hn⟩
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨v, hv, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hret := hv.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  have hmax (j : S.I) : S.forwardClassMass v j ≤ S.forwardClassMass v i := by
    by_cases hji : j = i
    · rw [hji]
    · have hsep := (hpeaki v hv).2.2 j hji
      linarith
  obtain ⟨_, hσraw, _, _, hmiddle, _⟩ :=
    hv.endpoint_sharp_selector_bounds hW hd hgap i (hpeaki v hv).1 hmax
  let σ := 1 - 2 * density hv.endpoint - A ^ 2
  rw [hret] at hσraw hmiddle
  have hσ : 0 ≤ σ := hσraw
  have hT : (1 - A) / A ∈ Icc (2 : ℝ) 3 := by
    constructor
    · apply (le_div_iff₀ hA).mpr
      nlinarith [hA310.2]
    · apply (div_le_iff₀ hA).mpr
      nlinarith [hA310.1]
  have hC : objective hv.endpoint ≤
      A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12 + σ / 3 := hmiddle hT
  let E := KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
    (MissingFlow.direction μ v)
  have hE : 0 ≤ E := hv.energy_nonnegative hW hd hgap
  have hbudget : 2 * (c - m * d) + m + E =
      2 * objective hv.endpoint - (-m) * (A ^ 2 + σ) := by
    have hb := hv.endpoint_budget hW
    dsimp only [σ, E]
    linear_combination hb
  have hell23 : 2 / 3 ≤ -m := by
    rw [hneg]
    unfold LowerE2Scalar.multiplier
    rw [le_div_iff₀ (by linarith [hq.1])]
    linarith [hq.2]
  have hD := MiddleUnsaturatedScalar.selectorValue_of_sharp_budget hA hell23 hσ hE hC hbudget
  have hcert := MiddleUnsaturatedScalar.selectorValue_lt_gapFloor hq hA310
  rw [hneg] at hD
  linarith

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual middle-E2 no-saturation entry. With the actual original
saturated set product-null, the same selected model has `q > 187/1000`
and `3c <= d`. Its internally selected original common peak exceeds `3/10`.
It either lies in the positive one-center source with its exact private
row, or is joined to the head. In the joined case the saturated
alternative is excluded, leaving the unsaturated joined masses and the
actual reverse source budget `c + ell e_S + F_S/2 <= t^2` with `t = b+s`.
No mass, cap, cost or row is an input. -/
theorem exists_middle_unsaturated_entry (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0) :
    m = -LowerE2Scalar.multiplier q ∧ 187 / 1000 < q ∧ 3 * c ≤ d ∧
      LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m ∧
      ∃ (R : S.ReverseRecovery) (p k : S.I), R.plateau = {p} ∧
        0 < μ (S.reverseCompulsorySource {p}) ∧ k ≠ p ∧
        S.IsCommonForwardPeak d c k ∧ 3 / 10 < S.originalAtomMass k ∧
        (∀ j : S.I, j ≠ k → S.originalAtomMass j < S.originalAtomMass k) ∧
        (2 * (c - m * d) + m + (-m) * (∑' j, (S.originalAtomMass j) ^ 2) ≤
          2 * (S.originalAtomMass k) ^ 2) ∧
        (((∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.reverseCompulsorySource {p}) ∧
            ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
              adjacencyKernel W z.1 z.2 =
                if S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val then 0 else 1) ∨
          ((∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood p) ∧
            ¬S.IsSaturatedAtomPair k p ∧
            2 * S.originalAtomMass k ≤ μ.real (S.rootNeighborhood p) ∧
            2 * S.originalAtomMass k + R.height ≤ 1 ∧ S.originalAtomMass k < 1 / 3 ∧
            R.height = S.originalAtomMass p + μ.real (S.reverseCompulsorySource {p}) ∧
            c + (-m) * ((∫ z in (S.reverseCompulsorySource {p}) ×ˢ
                (S.reverseCompulsorySource {p}), adjacencyKernel W z.1 z.2 ∂μ.prod μ) / 2) +
              (∫ z in (S.reverseCompulsorySource {p}) ×ˢ (S.reverseCompulsorySource {p}),
                shiftedKernel W m z.1 z.2 ∂μ.prod μ) / 2 ≤ R.height ^ 2)) := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hqgt := hW.middle_unsaturated_q_gt hq hdq hvalue hgap hnull
  have hcount := hW.three_objective_le_density_of_saturation_null hd.2 hgap hnull
  obtain ⟨hm, _, hγ, _, R, p, k, hp, hsource, hkp, hpeak, _, hlargest, hreserve, hloc⟩ :=
    S.exists_middle_e2_one_center_entry hW hq hdq hvalue hderiv hgap hglobal
  obtain ⟨_, hellI, _⟩ := hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hA := S.middle_unsaturated_peak_gt_three_tenths hW ⟨hqgt.le, hq.2.le⟩ hdq hvalue hderiv
    hgap hglobal k hpeak
  refine ⟨hm, hqgt, hcount, hγ, R, p, k, hp, hsource, hkp, hpeak, hA, hlargest, hreserve, ?_⟩
  rcases hloc with hsrc | hjoin
  · exact Or.inl hsrc
  · right
    have hnot := S.not_saturated_atom_pair_of_saturation_null hW hd hgap hellI.2 hnull k p
    rcases R.middle_e2_joined_peak_alternatives hW hq hdq hvalue hderiv hgap hglobal
        p k hp hkp hpeak hjoin with hsat | hunsat
    · exact absurd hsat.1 hnot
    · have hheight := R.singleton_height_eq_mass_add_source p hp
      have hbudget := R.singleton_source_credit hW hd hgap p hp
      rw [← hheight] at hbudget
      exact ⟨hjoin, hnot, hunsat.2.1, hunsat.2.2.1, hunsat.2.2.2, hheight, hbudget⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

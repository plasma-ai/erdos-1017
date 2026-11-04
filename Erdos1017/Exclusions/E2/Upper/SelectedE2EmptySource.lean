module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2SaturatedEmptySource
public import Erdos1017.Exclusions.Common.SelectedEmptySourceExit
public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateRadius
public import Erdos1017.Exclusions.E2.Upper.SelectedE2UnsaturatedZeroBody
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UnsaturatedPositiveBody
public import Erdos1017.SelectedModel.SelectedBodyEnergy

/-!
# No empty source for the `E₂` singleton recovery

The `E₂` singleton recovery cannot have a null source
(`no_e2_one_center_empty_source`); the saturated and unsaturated cases cover
every recovered head.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.LowerE2Scalar

private theorem twoHeadValue_gt_eighth {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 5)) :
    1 / 8 < Benchmark.twoHeadValue ((q + 2) / 3) := by
  have hR := denominator_pos hq.1
  have hq2 : q ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hq.1 hq.2 2
  have hfactor : 0 ≤ 7 * q ^ 3 - (133 / 5) * q ^ 2 + (242 / 25) * q + 1242 / 125 := by
    have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq.1 3
    nlinarith only [hq.1, hq2, hq3]
  have hprod := mul_nonneg (show 0 ≤ 1 / 5 - q by linarith only [hq.2]) hfactor
  have hid : 4 + 20 * q + 87 * q ^ 2 + 56 * q ^ 3 - 5 * q ^ 4 -
      2 * denominator q ^ 2 = 8 / 625 + (1 / 5 - q) *
        (7 * q ^ 3 - (133 / 5) * q ^ 2 + (242 / 25) * q + 1242 / 125) := by
    unfold denominator
    ring
  rw [Erdos1017.EmptySatE2.contact_value_eq hq.1]
  apply (lt_div_iff₀ (show 0 < 16 * denominator q ^ 2 by positivity)).mpr
  nlinarith only [hid, hprod]

end Erdos1017.LowerE2Scalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c q : ℝ} {S : SelectedHighLowStructure W m}

/-- Null entire singleton source is impossible when the actual recovered
head has no saturated partner. The original peak, universal row, physical
quota, scalar margin and both body alternatives are derived internally. -/
theorem no_e2_unsaturated_empty_source (R : S.ReverseRecovery)
    (r : S.I) (hr : R.plateau = {r})
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hnosat : ∀ p : S.I, p ≠ r → ¬S.IsSaturatedAtomPair r p) : False := by
  have hqfull : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨hq.1, by linarith only [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hqfull
  by_cases hq5 : q ≤ 1 / 5
  · obtain ⟨_, hell, _⟩ :=
      hW.e2_general_contact_parameters hqfull hdq hvalue hderiv hgap hglobal
    have hB : 1 / 8 < benchmark d := by
      rw [hvalue]
      exact LowerE2Scalar.twoHeadValue_gt_eighth ⟨hq.1.le, hq5⟩
    have hsq := R.empty_source_objective_le_sq r hr hW hd hgap hnull
    let A := μ.real {x | S.ρ x = r.val}
    have hA0 : 0 ≤ A := measureReal_nonneg
    have hA : 1 / 3 < A := by
      change c ≤ A ^ 2 at hsq
      by_contra hn
      have hp := mul_nonpos_of_nonneg_of_nonpos hA0
        (sub_nonpos.mpr (le_of_not_gt hn))
      nlinarith only [hB, hgap, hsq, hp]
    have hδ : 0 < 1 + m := by linarith only [hell.2]
    have hintercept := hW.e2_intercept_guard ⟨hq.1, hq5⟩ hdq hgap hglobal
    have hmargin : (1 + m) * (1 - A) < 3 * (2 * (c - m * d) + m) := by
      have hp := mul_pos hδ (show 0 < A - 1 / 3 by linarith only [hA])
      nlinarith only [hp, hintercept, hδ]
    have hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
        chargeKernel W p.1 p.2 < 1 := by
      filter_upwards [S.ae_saturated_pair_has_saturated_atom_block hW hd hgap hell.2]
        with p hp hr _
      have hne : chargeKernel W p.1 p.2 ≠ 1 := by
        intro he
        obtain ⟨a, u, hau, ha, _⟩ := hp he
        have har : a = r := Subtype.ext (ha.symm.trans hr)
        subst a
        exact hnosat u hau.1.symm hau
      exact lt_of_le_of_ne
        ((charge_moment_le_adjacency W p).trans (adjacency_moment_mem W p).2) hne
    exact R.entire_source_ne_zero_of_unsaturated_benchmark_ge_eighth r hr hW hd hgap
      hstar hell hmargin hB.le hnull
  have hnonnegative := bodyPositiveEnergy_nonnegative W {x | S.ρ x = r.val}
  by_cases hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0
  · exact S.not_e2_zero_body_of_no_saturated_partner
      r hW hqfull hdq hvalue hderiv hgap hglobal hzero hnosat
  exact S.no_upper_e2_unsaturated_universal_positive_body r hW
    ⟨by linarith only [hq5], hq.2⟩ hdq hvalue hderiv hgap hglobal
    (R.empty_source_is_original_peak r hr hW hd hgap hnull).1
    (R.empty_source_head_adjacency r hr hW hd hgap hnull)
    (lt_of_le_of_ne hnonnegative (Ne.symm hzero)) hnosat

/-- The actual E2 singleton recovery cannot have null entire source.
The saturated and unsaturated cases exhaust the recovered original head;
no body, peak, universality or scalar certificate is an input. -/
theorem no_e2_one_center_empty_source (R : S.ReverseRecovery)
    (r : S.I) (hr : R.plateau = {r})
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) : False := by
  by_cases hsat : ∃ p : S.I, S.IsSaturatedAtomPair r p
  · obtain ⟨p, hp⟩ := hsat
    exact R.no_e2_saturated_empty_source r p hr hp hW hq hdq hvalue hderiv hgap hglobal hnull
  exact R.no_e2_unsaturated_empty_source r hr hW hq hdq hvalue hderiv hgap hglobal hnull
    (fun p _ hp => hsat ⟨p, hp⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PeakThird
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairBlocks
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalRootless
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards
public import Erdos1017.Exclusions.Common.Physical.PhysicalPositiveCover

/-!
# No unsaturated universal peak with positive body

A universal original common peak with positive original body energy cannot be
unsaturated at an upper-`E₂` global contact
(`no_upper_e2_unsaturated_universal_positive_body`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- A literal universal original common peak with positive original body
energy cannot be unsaturated at a genuine upper-E2 global contact. -/
theorem no_upper_e2_unsaturated_universal_positive_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val then 0 else 1)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val})
    (hnosat : ∀ u : S.I, u ≠ r → ¬S.IsSaturatedAtomPair r u) : False := by
  let A := μ.real {x | S.ρ x = r.val}
  let γ := 2 * (c - m * d) + m
  have hmass := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith [hmass.1, hmass.2]
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨hm, hell, hfloor⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hA : 1 / 3 < A := by
    obtain ⟨hΔ, i, hi, _, hpi, _, _, _⟩ :=
      S.exists_original_upper_e2_peak_gt_third hW hq hdq hvalue hderiv hgap hglobal
    have hir : i = r := (hpi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
    subst i
    exact hi
  have hN := S.universal_atom_neutral r hW hd hgap huniv
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
  have hcharge := PhysicalRepresentative.charge_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have henergy : PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} =
      ∫ z : Ω × Ω,
        (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
          {x | S.ρ x = r.val} z.1 z.2) ^ 2 ∂μ.prod μ := by
    rw [PhysicalPrimal.bodyPositiveEnergy,
      ← integral_indicator ((S.hfibers r.val r.property).1.compl.prod
        (S.hfibers r.val r.property).1.compl)]
    apply integral_congr_ae
    filter_upwards [hcharge] with z hz
    by_cases h : z.1 ∉ {x | S.ρ x = r.val} ∧ z.2 ∉ {x | S.ρ x = r.val}
    · simp [IndependentAtomCopy.positiveBody, Function.uncurry, h, hz]
    · by_cases h1 : S.ρ z.1 = r.val <;> by_cases h2 : S.ρ z.2 = r.val <;>
        simp_all [IndependentAtomCopy.positiveBody]
  have htrace := S.universal_positive_body_trace r hW hd hgap hN
    (henergy ▸ hpositive)
  have hAlt : A < 2 / 5 := by
    have hγpos : 0 < γ := (LowerE2Scalar.contact_gapFloor_pos hq'.1).trans hfloor
    have hmissing : 1 - 2 * d = LowerE2Scalar.missingMass q := by rw [hdq]; ring
    have hγnonneg : 0 ≤ 2 * A * γ := mul_nonneg (by linarith [hA]) (by linarith)
    have hγsq : 0 ≤ γ ^ 2 := sq_nonneg γ
    change 3 * A ^ 2 + 2 * A * γ + γ ^ 2 ≤ 2 * (1 - 2 * d) at htrace
    rw [hmissing] at htrace
    by_contra hn
    have hAge : 2 / 5 ≤ A := le_of_not_gt hn
    have hAsq : (2 / 5 : ℝ) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hAge 2
    nlinarith [hmass.2]
  have hmargin : (1 + m) * (1 - A) < 3 * γ := by
    have hδ : 0 < 1 + m := by linarith [hell.2]
    have hδbound : 1 + m < 1 / 5 := by
      rw [hm]
      linarith [UpperE2Parameter.multiplier_mem hq |>.1]
    have hmasscomp : 1 - A < 2 / 3 := by linarith [hA]
    have hprod : (1 + m) * (1 - A) < (1 / 5 : ℝ) * (2 / 3) := by
      have h1 := mul_lt_mul_of_pos_left hmasscomp hδ
      have h2 := mul_lt_mul_of_pos_right hδbound (show (0 : ℝ) < 2 / 3 by norm_num)
      linarith
    have hγ : 7 / 122 < γ := (UpperE2Parameter.gapFloor_ge hq).trans_lt hfloor
    linarith
  have hquota := S.unsaturated_universal_objective_le_half_root_quota r hW hd hgap
    hN hstar hA hell hmargin
  have hB : 123 / 1000 < benchmark d := by
    rw [hvalue]
    exact UpperE2Parameter.twoHeadValue_gt hq
  have hcost : A * (1 - A) / 2 < 3 / 25 := by
    have hp := mul_pos (sub_pos.mpr hAlt) (show 0 < 3 / 5 - A by linarith)
    nlinarith
  change c ≤ A * (1 - A) / 2 at hquota
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure

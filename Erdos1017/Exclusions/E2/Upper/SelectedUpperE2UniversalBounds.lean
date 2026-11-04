module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalCopyCap
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalNegative
public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalTrace

/-!
# Quantitative bounds for the universal upper `E₂` primal

The same original upper-`E₂` contact, singleton recovery and physical primal pay
the universal mass, negative-region and signed-charge bounds
(`universal_upperE2_quantitative_bounds`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The same original upper-E2 contact, singleton recovery and physical
primal pay the universal mass, negative-region and signed-charge bounds. -/
theorem UniversalPhysicalPrimal.universal_upperE2_quantitative_bounds
    (R : S.ReverseRecovery) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c q : ℝ} (P : S.UniversalPhysicalPrimal r c)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {p})
    (hsource : 0 < μ (S.reverseCompulsorySource {p}))
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = r.val then 0 else 1)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val}) :
    1 / 3 < S.originalAtomMass r ∧
      S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r ∧
      2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m) ∧
      S.originalAtomMass r < 93 / 250 ∧
      μ.real (S.universalPartnerCommonRegion r p) < 1 - 2 * S.originalAtomMass r ∧
      0 < μ (S.universalNegativeRegion r p) ∧
      0 < S.universalNegativeChargeMass r p ∧
      S.universalNegativeChargeMass r p <
        (-m) * μ.real (S.universalNegativeRegion r p) := by
  have hmissing := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith [hmissing.1, hmissing.2]
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨hm, hell, hfloor⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hell' : -m ∈ Ioo (4 / 5 : ℝ) 1 := by
    rw [hm]
    have h := UpperE2Parameter.multiplier_mem hq
    constructor
    · simpa only [neg_neg] using h.1
    · simpa only [neg_neg] using lt_of_le_of_lt h.2 (by norm_num :
        (9 / 11 : ℝ) < 1)
  have ⟨hA, hAhi, hmargin⟩ :=
    S.universal_upperE2_initial_guards r hW hq hdq hvalue hderiv
      hgap hglobal huniv hpeak hpositive
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hHpos : 0 < μ (S.universalPartnerHoleRegion r p) :=
    lt_of_lt_of_le hsource (measure_mono_ae
      (S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell.2))
  obtain ⟨x, _, hlow, hupp⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hHpos.ne'
      ((S.ae_universalPartnerHole_degree_ge_twice_mass r p hpair hW hd hgap
        hell.2 hN).and
        (S.ae_universalPartnerHole_degree_le_one_sub_partner_mass r p hW hd hgap))
  have hb : S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r := by
    change 2 * S.originalAtomMass r ≤ ∫ z, adjacencyKernel W x z ∂μ at hlow
    linarith only [hlow, hupp]
  have hratio : (77 / 1098 : ℝ) ≤
      (2 * (c - m * d) + m) / (-m) := by
    have hfloorRatio := UpperE2Parameter.gapFloor_div_multiplier_ge hq
    rw [← neg_eq_iff_eq_neg.mpr hm] at hfloorRatio
    exact hfloorRatio.trans
      (div_le_div_of_nonneg_right hfloor.le (by linarith [hell.1]))
  have hcut : S.originalAtomMass r < 93 / 250 := by
    apply S.universal_upperE2_mass_lt_cutoff_of_body_cap r hW hq hdq hvalue
      hderiv hgap hglobal hN hpositive
    intro hlarge
    have hprice := UpperE2Parameter.body_cap_price_guard_of_mass_ge_cutoff
      (by linarith [hell.1]) hlarge hb hratio
    exact P.ae_universal_positive_body_le_multiplier S r p hpair hW hd hgap
      hN hA (by linarith [hAhi]) hell hmargin hprice
  have hu := R.universal_partner_source_mass_margin r p hpair hW hd hgap
    hell.2 hr hN
  have hU : μ.real (S.universalPartnerCommonRegion r p) <
      1 - 2 * S.originalAtomMass r := by
    linarith only [hu.1, hu.2]
  have hgammaFloor : 7 / 122 < 2 * (c - m * d) + m :=
    (UpperE2Parameter.gapFloor_ge hq).trans_lt hfloor
  have hBpos := P.universal_upperE2_negative_region_pos S R r p hpair hW
    hd hgap hr hN hA hAhi hell' hgammaFloor hmargin
  have hNpos := S.universalNegativeChargeMass_pos r p hW hd hgap hN hBpos
  have hNbound := S.universalNegativeChargeMass_lt_multiplier_mass r p
    hW hd hgap hN hBpos
  exact ⟨hA, hb, hmargin, hcut, hU, hBpos, hNpos, hNbound⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

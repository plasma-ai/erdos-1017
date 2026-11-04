module

public import Erdos1017.Exclusions.Corner.FullSharpCornerPeak
public import Erdos1017.Exclusions.Corner.SelectedCornerZeroBody
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedOneCenterSourceCredit
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalGeometry
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitBudget

/-!
# Geometry of the universal corner entry

A distinct universal atom keeps its original mass under the reverse law and lies
strictly below its singleton top plateau, and the universal saturated corner
entry keeps the recovered law with strict height, positive whole source, own
corner guards and the original mass inventory.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- A distinct universal original atom keeps its original mass under the
actual reverse law and lies strictly below its singleton top plateau. -/
theorem corner_universal_atom_mass_lt_singleton_height (R : S.ReverseRecovery)
    (r p : S.I) (hrp : r ≠ p) (hplateau : R.plateau = {p})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = r.val then 0 else 1) :
    S.originalAtomMass r < R.height := by
  have hneutral := S.universal_atom_neutral r hW hd hgap huniv
  have hmarg := R.reverse_marginals_zero_on_neutral r hneutral
  have he := MissingFlow.endpoint_real_set_eq_original R.flow R.isFullReverseFlow.integrable
    R.isFullReverseFlow.nonnegative R.isFullReverseFlow.supply_le_one
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
    (hmarg.mono (fun _ h hx => (h hx).1))
    (hmarg.mono (fun _ h hx => (h hx).2))
  have hmass : S.reverseClassMass R.flow r = S.originalAtomMass r := by
    rw [reverseClassMass, S.collapsedPartLabel_fiber r, he]
    rfl
  have hne : S.reverseClassMass R.flow r ≠ R.height := by
    intro h
    have hr := (R.classMass_eq_iff hW r).mp h
    rw [hplateau] at hr
    exact hrp (Finset.mem_singleton.mp hr)
  rw [← hmass]
  exact lt_of_le_of_ne (R.classMass_le hW r) hne

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual universal saturated corner entry keeps the same recovered law.
Its strict height, positive entire source, own corner guards and original
mass inventory are derived without a supplied body or price certificate. -/
theorem corner_universal_entry (R : S.ReverseRecovery) (r p : S.I)
    (hplateau : R.plateau = {p})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r p) (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = r.val then 0 else 1) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let s := μ.real (S.reverseCompulsorySource {p})
    let eta := μ.real (S.universalPartnerHoleRegion r p)
    let u := μ.real (S.universalPartnerCommonRegion r p)
    let kappa := μ.real (S.universalPartnerHoleRegion r p \ S.reverseCompulsorySource {p})
    let gamma := 2 * (c - m * d) + m
    (-m) ∈ Icc (363 / 589 : ℝ) (9 / 11) ∧
      (138261458236451 : ℝ) / 1116960975000000 < c ∧
      1 - 2 * d < 23243417 / 10 ^ 8 ∧
      1 / 3 < A ∧ A < 3 / 8 ∧ 0 < gamma ∧
      2 * A * (1 + m) < 3 * gamma ∧
      0 < PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
        {x | S.ρ x = r.val} ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) ∧
      A < R.height ∧ R.height = b + s ∧ A < b + s ∧
      0 < μ (S.reverseCompulsorySource {p}) ∧
      A + b + eta + u = 1 ∧ u + kappa < 1 - 2 * A := by
  let A := S.originalAtomMass r
  let gamma := 2 * (c - m * d) + m
  let Bm : ℝ := 138261458236451 / 1116960975000000
  let hU : ℝ := 23243417 / 10 ^ 8
  obtain ⟨hell, hc, hh, hcornerFloor⟩ :=
    hW.corner_contact_parameters hd hgap he heq hglobal
  obtain ⟨hDelta, i, hi, hpi, hlargest, _⟩ :=
    S.exists_sharp_corner_peak hW hd hgap he heq hglobal
  have hir : i = r := (hpi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst i
  have hA : 1 / 3 < A := hi
  have hneutral := S.universal_atom_neutral r hW hd hgap huniv
  have hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} := by
    apply lt_of_le_of_ne (bodyPositiveEnergy_nonnegative W _)
    intro hzero
    exact S.no_corner_saturated_zero_body r p hW hd hgap he heq hglobal hpair hzero.symm
  have hbody := hW.bodyPositiveEnergy_eq_physicalBody hd hgap
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
  have hphysical : 0 < ∫ z : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} z.1 z.2) ^ 2 ∂μ.prod μ := by
    rw [hbody] at hpositive
    exact hpositive
  have htrace := S.universal_positive_body_trace r hW hd hgap hneutral hphysical
  change 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 2 * (1 - 2 * d) at htrace
  have hgamma : 0 < gamma := (hW.strict_gap_structure hd hgap).gamma_pos
  have hownfloor : 2 * Bm - (-m) * hU < gamma := by
    exact hcornerFloor
  let gmin := 2 * Bm - (9 / 11 : ℝ) * hU
  have hgmin : 0 < gmin := by norm_num [gmin, Bm, hU]
  have hfloor : gmin < gamma := by
    have hmul := mul_le_mul_of_nonneg_right hell.2
      (show 0 ≤ hU by norm_num [hU])
    exact (sub_le_sub_left hmul (2 * Bm)).trans_lt hownfloor
  have hAlt : A < 3 / 8 := by
    by_contra hn
    have hge : 3 / 8 ≤ A := le_of_not_gt hn
    have hsq : (3 / 8 : ℝ) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hge 2
    have hprod : (3 / 8 : ℝ) * gmin < A * gamma := by
      calc
        _ ≤ A * gmin := mul_le_mul_of_nonneg_right hge hgmin.le
        _ < A * gamma := mul_lt_mul_of_pos_left hfloor (by linarith only [hA])
    have hgsq : gmin ^ 2 < gamma ^ 2 := by
      nlinarith only [mul_pos (sub_pos.mpr hfloor) (add_pos hgamma hgmin)]
    dsimp only [gmin, Bm, hU] at *
    nlinarith only [htrace, hsq, hprod, hgsq, hh]
  have hmargin : 2 * A * (1 + m) < 3 * gamma := by
    have hline : 0 < 3 * (2 * Bm - (-m) * hU) - (3 / 4 : ℝ) * (1 + m) := by
      dsimp only [Bm, hU]
      linarith only [hell.1]
    have hmul := mul_lt_mul_of_pos_right hAlt
      (show 0 < 1 + m by linarith only [hell.2])
    calc
      2 * A * (1 + m) = 2 * (A * (1 + m)) := by ring
      _ < 2 * ((3 / 8 : ℝ) * (1 + m)) :=
        mul_lt_mul_of_pos_left hmul (by norm_num)
      _ = (3 / 4 : ℝ) * (1 + m) := by ring
      _ < 3 * (2 * Bm - (-m) * hU) := by linarith only [hline]
      _ < 3 * gamma := mul_lt_mul_of_pos_left hownfloor (by norm_num)
  have ht := R.corner_universal_atom_mass_lt_singleton_height r p hpair.1 hplateau
    hW hd hgap huniv
  have hheight := R.singleton_height_eq_mass_add_source p hplateau
  change R.height = S.originalAtomMass p + μ.real (S.reverseCompulsorySource {p}) at hheight
  have hba := hlargest p hpair.1.symm
  have hsreal : 0 < μ.real (S.reverseCompulsorySource {p}) := by
    linarith only [ht, hheight, hba]
  have hsource : 0 < μ (S.reverseCompulsorySource {p}) := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) zero_le
    simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hsreal
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hsubset := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap
    (show -m < 1 by linarith only [hell.2])
  have heqsource : S.universalPartnerHoleRegion r p ∩ S.reverseCompulsorySource {p} =ᵐ[μ]
      S.reverseCompulsorySource {p} := hsubset.mono (fun x hx =>
        propext ⟨And.right, fun hs => ⟨hx hs, hs⟩⟩)
  have hparts := measureReal_inter_add_sdiff (μ := μ)
    (s := S.universalPartnerHoleRegion r p) (R.singleton_measurableSet_source p hplateau)
  rw [measureReal_congr heqsource] at hparts
  refine ⟨hell, hc, hh, hA, hAlt, hgamma, hmargin, hpositive, hneutral,
    ht, hheight, ?_, hsource, hmass, ?_⟩
  · linarith only [ht, hheight]
  · dsimp only [A] at *
    nlinarith only [hmass, hparts, ht, hheight]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

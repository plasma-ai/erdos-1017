module

public import Erdos1017.SelectedModel.Flows.OriginalForwardPeakLargest

/-!
# Missing-mass cap at the largest forward peak

This module defines the cap radius `missingMassCapRadius`; the largest forward
peak has unconditional atomic high and neutral radius bounds, while the diffuse
high and low bounds need a strict gamma guard, supplied by a multiplier at most
minus one or by a missing-density lower bound of twice the peak square.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- The original scalar cap radius; its radicand sign is proved from an
actual peak-avoiding endpoint, rather than assumed in its definition. -/
def missingMassCapRadius (d c m A : ℝ) : ℝ :=
  Real.sqrt (((2 + m) * A ^ 2 - (2 * (c - m * d) + m)) / (-m))

/-- An actual peak-avoiding flow retains the original peak mass and gives
its original budget, including the current endpoint missing density. -/
theorem IsFullForwardFlow.avoiding_common_peak_budget
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
    (hq : S.IsFullForwardFlow q) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L)
    (hpeak : ForwardPeak.massPeak (S.forwardClassMass q) = S.forwardClassMass q i)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    S.forwardClassMass q i = S.originalAtomMass i ∧
      2 * (c - m * d) + m ≤ 2 * (S.originalAtomMass i) ^ 2 +
        m * (1 - 2 * density hq.endpoint) := by
  have hmass := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  have hcost := hq.objective_le_peak_sq hW hd hgap
  rw [hpeak, hmass] at hcost
  change objective hq.endpoint ≤ (S.originalAtomMass i) ^ 2 at hcost
  have he := hq.energy_nonnegative hW hd hgap
  have hb := hq.endpoint_budget hW
  exact ⟨hmass, by nlinarith⟩

/-- Retaining the two distinct endpoint squares sharpens the avoiding
budget by the actual mass of any other endpoint class. -/
theorem IsFullForwardFlow.avoiding_common_peak_pair_budget
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
    (hq : S.IsFullForwardFlow q) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L)
    (hpeak : ForwardPeak.massPeak (S.forwardClassMass q) = S.forwardClassMass q i)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) (k : S.I) (hki : k ≠ i) :
    2 * (c - m * d) + m ≤ (2 + m) * (S.originalAtomMass i) ^ 2 +
      m * (S.forwardClassMass q k) ^ 2 := by
  have hp := hq.classMass_properties
  have hsq : Summable (fun j => (S.forwardClassMass q j) ^ 2) :=
    hp.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      nlinarith [(hp.1 j).1, (hp.1 j).2])
  have htwo := (hsq.sum_le_tsum {i, k} (fun _ _ => sq_nonneg _)).trans_eq
    (hq.missing_density_eq_classMass_sq hW hd hgap).symm
  simp only [Finset.sum_pair hki.symm] at htwo
  obtain ⟨hmass, hbudget⟩ := hq.avoiding_common_peak_budget hW hd hgap i hnonlow hpeak havoid
  rw [hmass] at htwo
  have hmul := mul_le_mul_of_nonpos_left htwo (hW.strict_gap_structure hd hgap).multiplier_neg.le
  nlinarith

/-- Actual endpoint feasibility and peak retention prove the radius is
real and give its exact original shifted-budget identity. -/
theorem IsFullForwardFlow.missingMassCapRadius_properties
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
    (hq : S.IsFullForwardFlow q) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L)
    (hpeak : ForwardPeak.massPeak (S.forwardClassMass q) = S.forwardClassMass q i)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    0 ≤ ((2 + m) * (S.originalAtomMass i) ^ 2 - (2 * (c - m * d) + m)) / (-m) ∧
      0 ≤ missingMassCapRadius d c m (S.originalAtomMass i) ∧
      2 * (c - m * d) + m = (2 + m) * (S.originalAtomMass i) ^ 2 +
        m * (missingMassCapRadius d c m (S.originalAtomMass i)) ^ 2 := by
  have hp := hq.classMass_properties
  have hsq : Summable (fun j => (S.forwardClassMass q j) ^ 2) :=
    hp.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      nlinarith [(hp.1 j).1, (hp.1 j).2])
  have hsingle := (hsq.le_tsum i (fun _ _ => sq_nonneg _)).trans_eq
    (hq.missing_density_eq_classMass_sq hW hd hgap).symm
  obtain ⟨hmass, hbudget⟩ := hq.avoiding_common_peak_budget hW hd hgap i hnonlow hpeak havoid
  rw [hmass] at hsingle
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hmul := mul_le_mul_of_nonpos_left hsingle hm.le
  have hnum : 0 ≤ (2 + m) * (S.originalAtomMass i) ^ 2 - (2 * (c - m * d) + m) := by
    nlinarith
  have hrad := div_nonneg hnum (neg_nonneg.mpr hm.le)
  refine ⟨hrad, Real.sqrt_nonneg _, ?_⟩
  have hsqrt := Real.sq_sqrt hrad
  have hdiv := (div_mul_cancel₀
    ((2 + m) * (S.originalAtomMass i) ^ 2 - (2 * (c - m * d) + m)) (neg_ne_zero.mpr hm.ne))
  change (missingMassCapRadius d c m (S.originalAtomMass i)) ^ 2 = _ at hsqrt
  rw [← hsqrt] at hdiv
  nlinarith

/-- A nonnegative radius with the exact original budget identity bounds
any mass satisfying the corresponding two-class budget. -/
private theorem mass_le_radius_of_budget {gamma m A R b : ℝ}
    (hm : m < 0) (hR : 0 ≤ R)
    (hidentity : gamma = (2 + m) * A ^ 2 + m * R ^ 2)
    (hbudget : gamma ≤ (2 + m) * A ^ 2 + m * b ^ 2) : b ≤ R := by
  by_contra h
  have hb : R < b := lt_of_not_ge h
  have hsq : R ^ 2 < b ^ 2 := by nlinarith
  have hmul := mul_lt_mul_of_neg_left hsq hm
  linarith

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The diffuse tail cap needs the strict original gamma guard. Rational
thresholds apply the actual controlled comparison below the original peak. -/
theorem ae_diffuse_missing_le_radius_of_guard (S : SelectedHighLowStructure W m)
    {d c A R : ℝ} (hA : 0 < A) (hm : m < 0) (hR : 0 ≤ R)
    (hidentity : 2 * (c - m * d) + m = (2 + m) * A ^ 2 + m * R ^ 2)
    (hguard : 2 * (1 + m) * A ^ 2 < 2 * (c - m * d) + m)
    (hcontrolled : ∀ b ∈ Ioc (0 : ℝ) A,
      0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x}) →
        2 * (c - m * d) + m ≤ (2 + m) * A ^ 2 + m * b ^ 2) :
    R < A ∧ ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → S.outsideSectionMass x ≤ R := by
  have hRA : R < A := by
    by_contra h
    have hAR := le_of_not_gt h
    have hsq : A ^ 2 ≤ R ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonpos_left hsq hm.le
    nlinarith
  refine ⟨hRA, ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ b : ℚ, R < (b : ℝ) → (b : ℝ) < A →
      x ∈ S.D → x ∈ S.H → S.outsideSectionMass x ≤ (b : ℝ) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : R < (b : ℝ) ∧ (b : ℝ) < A
    · have hnull : μ (S.D ∩ S.H ∩ {x | (b : ℝ) < S.outsideSectionMass x}) = 0 := by
        by_contra hn
        have hp : 0 < μ (S.D ∩ S.H ∩ {x | (b : ℝ) < S.outsideSectionMass x}) :=
          pos_iff_ne_zero.mpr hn
        have hbudget := hcontrolled b ⟨hR.trans_lt hb.1, hb.2.le⟩ hp
        exact (not_lt_of_ge (mass_le_radius_of_budget hm hR hidentity hbudget)) hb.1
      have hnot : ∀ᵐ x ∂μ, x ∉ S.D ∩ S.H ∩ {x | (b : ℝ) < S.outsideSectionMass x} := by
        rw [ae_iff]
        have he : {x | ¬x ∉ S.D ∩ S.H ∩ {x | (b : ℝ) < S.outsideSectionMass x}} =
            S.D ∩ S.H ∩ {x | (b : ℝ) < S.outsideSectionMass x} := by
          ext x
          simp only [mem_ofPred_eq, not_not]
        rw [he]
        exact hnull
      filter_upwards [hnot] with x hx _ _ hxD hxH
      exact le_of_not_gt (fun hlt => hx ⟨⟨hxD, hxH⟩, hlt⟩)
    · exact Eventually.of_forall (fun _ h₁ h₂ => False.elim (hb ⟨h₁, h₂⟩))
  filter_upwards [hall] with x hx hxD hxH
  by_contra h
  have hlt : R < min A (S.outsideSectionMass x) := lt_min hRA (lt_of_not_ge h)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn hlt
  have hbA := hb₂.trans_le (min_le_left _ _)
  have hbs := hb₂.trans_le (min_le_right _ _)
  exact (not_lt_of_ge (hx b hb₁ hbA hxD hxH)) hbs

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Atomic and diffuse bounds give the actual outside-section bound on
HIGH points outside the displayed original atom, on one common AE set. -/
theorem ae_nonpeak_high_outside_le (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (i : S.I) (R : ℝ)
    (hatomic : ∀ k : S.I, k ≠ i →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
      S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤ R)
    (hdiffuse : ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → S.outsideSectionMass x ≤ R) :
    ∀ᵐ x ∂μ, x ∈ S.H → S.ρ x ≠ i → S.outsideSectionMass x ≤ R := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ k : S.I, S.ρ x = k → x ∈ S.H → k ≠ i →
      S.outsideSectionMass x ≤ R := by
    rw [ae_all_iff]
    intro k
    rcases S.hfiberClass k k.property with hH | hL | hN
    · have he := (ae_restrict_iff' (S.hfibers k k.property).1).mp
        (S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW k k.property)
      filter_upwards [he] with x hx hxk _ hki
      rw [hx hxk]
      have hb := hatomic k hki hH
      have hn := S.originalAtomMass_summable.1 k
      linarith
    · have hl := (ae_restrict_iff' (S.hfibers k k.property).1).mp hL
      filter_upwards [hl] with x hx hxk hxH _
      exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxH (hx hxk))
    · have hn := (ae_restrict_iff' (S.hfibers k k.property).1).mp hN
      filter_upwards [hn] with x hx hxk hxH _
      exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hxH (hx hxk))
  filter_upwards [hall, hdiffuse] with x ha hd hxH hxi
  by_cases hxD : x ∈ S.D
  · exact hd hxD hxH
  · have hxU : x ∈ ⋃ r ∈ S.I, {x | S.ρ x = r} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
    obtain ⟨r, hr⟩ := mem_iUnion.mp hxU
    obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
    exact ha ⟨r, hrI⟩ hxr hxH (fun he => hxi (hxr.trans (congrArg Subtype.val he)))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Full LOW supply in an actual avoiding flow transfers the actual
nonpeak HIGH section bound to every original LOW atom's mass. -/
theorem IsFullForwardFlow.low_atom_mass_le_of_recipient_bound
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
    (hq : S.IsFullForwardFlow q) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (i : S.I) (R : ℝ)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i)
    (hrecipients : ∀ᵐ x ∂μ, x ∈ S.H → S.ρ x ≠ i → S.outsideSectionMass x ≤ R)
    (j : S.I) (hjL : ∀ᵐ y ∂μ.restrict {y | S.ρ y = j}, y ∈ S.L) :
    S.originalAtomMass j ≤ R := by
  by_contra h
  have hpair : ∀ᵐ p ∂μ.prod μ, S.ρ p.2 = j → q p = 0 := by
    filter_upwards [hq.support, havoid, hq.ae_atom_source_mass_le_recipient_missing hW j,
      Measure.quasiMeasurePreserving_fst.ae hrecipients] with p hs ha hm hr hyj
    by_contra hq0
    exact h ((hm hq0 hyj).trans (hr (hs hq0).2.1 (ha hq0)))
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hpair
  have hnested := Measure.ae_ae_of_ae_prod hswap
  obtain ⟨y, hyj, hyL, hys, hyp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j j.property).2.1.ne'
    (hjL.and ((ae_restrict_of_ae hq.supply).and (ae_restrict_of_ae hnested)))
  have hz : MissingFlow.supply μ q y = 0 :=
    integral_eq_zero_of_ae (hyp.mono (fun _ hx => hx hyj))
  rw [indicator_of_mem hyL] at hys
  linarith

/-- The same original unique largest forward peak has unconditional
atomic HIGH/NEUTRAL radius bounds. Diffuse HIGH and all LOW bounds require
the displayed strict original gamma guard; no small-slope cap is inferred. -/
theorem exists_conditional_missing_mass_cap (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ i : S.I,
      0 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      (∀ (u : Ω × Ω → ℝ), S.IsFullForwardFlow u →
        0 < S.forwardClassMass u i ∧
        ForwardPeak.massPeak (S.forwardClassMass u) = S.forwardClassMass u i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass u) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ k : S.I, k ≠ i →
        S.originalAtomMass k ≤ S.originalAtomMass i - ε) ∧
      0 ≤ ((2 + m) * (S.originalAtomMass i) ^ 2 - (2 * (c - m * d) + m)) / (-m) ∧
      (∀ k : S.I, k ≠ i →
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
        S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
          missingMassCapRadius d c m (S.originalAtomMass i)) ∧
      (∀ k : S.I, k ≠ i →
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.N) →
        S.originalAtomMass k ≤ missingMassCapRadius d c m (S.originalAtomMass i)) ∧
      (2 * (1 + m) * (S.originalAtomMass i) ^ 2 < 2 * (c - m * d) + m →
        missingMassCapRadius d c m (S.originalAtomMass i) < S.originalAtomMass i ∧
        (∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H →
          S.outsideSectionMass x ≤ missingMassCapRadius d c m (S.originalAtomMass i)) ∧
        ∀ j : S.I, (∀ᵐ y ∂μ.restrict {y | S.ρ y = j}, y ∈ S.L) →
          S.originalAtomMass j ≤ missingMassCapRadius d c m (S.originalAtomMass i)) := by
  obtain ⟨_, i, hA, hside, hpeak, _, hlarge, hgapOriginal, hcontrolled⟩ :=
    S.exists_unique_largest_original_forward_peak hW hd hgap
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  obtain ⟨hrad, hR, hidentity⟩ := hq.missingMassCapRadius_properties
    hW hd hgap i hnonlow (hpeak q hq).2.1 havoid
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hhigh : ∀ k : S.I, k ≠ i →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
      S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
        missingMassCapRadius d c m (S.originalAtomMass i) := by
    intro k hki hkH
    have hu := hq.atomRedirect_of_stationary hW k k.property hkH
    have hne : (k : Lp ℝ 2 μ) ≠ i := fun he => hki (Subtype.ext he)
    have hstill := S.atomRedirect_avoids k i hne q havoid
    have hb := hu.avoiding_common_peak_pair_budget hW hd hgap i hnonlow
      (hpeak _ hu).2.1 hstill k hki
    have hmass : S.forwardClassMass (S.atomRedirect k q) k =
        S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) := by
      rw [S.forwardClassMass_eq_fiber]
      exact hq.atomRedirect_endpoint_mass hW k k.property hkH
    rw [hmass] at hb
    exact mass_le_radius_of_budget hm hR hidentity hb
  refine ⟨i, hA, hside, hpeak, hlarge, hgapOriginal, hrad, hhigh, ?_, ?_⟩
  · intro k hki hkN
    have hb := hq.avoiding_common_peak_pair_budget hW hd hgap i hnonlow
      (hpeak q hq).2.1 havoid k hki
    have hmass : S.forwardClassMass q k = S.originalAtomMass k :=
      hq.classMass_eq_original_of_neutral k hkN
    rw [hmass] at hb
    exact mass_le_radius_of_budget hm hR hidentity hb
  · intro hguard
    obtain ⟨hRA, hdiffuse⟩ := S.ae_diffuse_missing_le_radius_of_guard
      hA hm hR hidentity hguard hcontrolled
    have hrecipients := S.ae_nonpeak_high_outside_le hW i _ hhigh hdiffuse
    exact ⟨hRA, hdiffuse, fun j hjL =>
      hq.low_atom_mass_le_of_recipient_bound hW i _ havoid hrecipients j hjL⟩

/-- At multiplier at most minus one, original gamma positivity alone
supplies the strict guard, for every peak mass. -/
theorem gamma_guard_of_multiplier_le_neg_one (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hm : m ≤ -1) (i : S.I) :
    2 * (1 + m) * (S.originalAtomMass i) ^ 2 < 2 * (c - m * d) + m := by
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (show 1 + m ≤ 0 by linarith)
    (sq_nonneg (S.originalAtomMass i))
  linarith [(hW.strict_gap_structure hd hgap).gamma_pos]

/-- The actual original missing-density lower bound by twice the peak
square also supplies the strict guard, including slopes below one. -/
theorem gamma_guard_of_two_peak_sq_le_missing (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (hsq : 2 * (S.originalAtomMass i) ^ 2 ≤ 1 - 2 * d) :
    2 * (1 + m) * (S.originalAtomMass i) ^ 2 < 2 * (c - m * d) + m := by
  by_cases hm : m ≤ -1
  · exact S.gamma_guard_of_multiplier_le_neg_one hW hd hgap hm i
  · have hmpos : 0 < 1 + m := by linarith
    have hbase := Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩
    have hdelta : 0 < 2 * c - (1 - 2 * d) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsq hmpos.le
    nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure

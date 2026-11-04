module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleLargeUniversalGuards
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitTangents
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPrice
public import Erdos1017.Exclusions.E2.Middle.UniversalDeficitRefinedFloor
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleLargeSharpMissingCap
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleLargeSharpDiffuseCap
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalGoodError
public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalContract

/-!
# Necessary system for the large universal branch

The certificate point `middleLargeUniversalPoint` is built from the two heads
and common region of the selected model, and the open middle `E₂` universal
branch supplies the closed certificate box and every necessary condition
(`middle_large_universal_necessary_system`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

/-- The certificate point uses the original two heads and literal common
region of this selected model. -/
def middleLargeUniversalPoint (S : SelectedHighLowStructure W m) (r p : S.I) (q : ℝ) :
    MiddleE2LargeUniversal.Point :=
  ⟨q, S.originalAtomMass r, S.originalAtomMass p,
    μ.real (S.universalPartnerCommonRegion r p)⟩

private theorem large_family_parameters (q : ℝ) :
    MiddleE2LargeUniversal.ellq q = LowerE2Scalar.multiplier q ∧
      MiddleE2LargeUniversal.gq q = LowerE2Scalar.gapFloor q ∧
      MiddleE2LargeUniversal.hq q = LowerE2Scalar.missingMass q ∧
      MiddleE2LargeUniversal.yq q = 9 * q / (2 * LowerE2Scalar.denominator q) ∧
      MiddleE2LargeUniversal.kq q = LowerE2Scalar.universalPeakGapFloor q := by
  have hR : MiddleE2LargeUniversal.rq q = LowerE2Scalar.denominator q := by
    unfold MiddleE2LargeUniversal.rq LowerE2Scalar.denominator
    ring
  unfold MiddleE2LargeUniversal.ellq MiddleE2LargeUniversal.gq MiddleE2LargeUniversal.hq
    MiddleE2LargeUniversal.yq MiddleE2LargeUniversal.kq LowerE2Scalar.multiplier
    LowerE2Scalar.gapFloor LowerE2Scalar.missingMass LowerE2Scalar.universalPeakGapFloor
  rw [hR]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · ring
  constructor
  · rfl
  · ring

private theorem large_gap_min_identity {A b eta u K T y : ℝ}
    (hmass : A + b + eta + u = 1) :
    eta - min (min (1 - 2 * A - b) (A - b - K)) (T - b) =
        max (max (A - u) (1 - 2 * A - u + K)) (1 - A - u - T) ∧
      eta - min (min (1 - 2 * A - b) (A - b - K)) (T - b) - (y - u) =
        max (max (A - y) (1 - 2 * A - y + K)) (1 - A - T - y) := by
  constructor
  · rw [← max_sub_sub_left, ← max_sub_sub_left]
    congr 1
    · congr 1 <;> linarith only [hmass]
    · linarith only [hmass]
  · rw [show eta - min (min (1 - 2 * A - b) (A - b - K)) (T - b) - (y - u) =
        (eta - (y - u)) - min (min (1 - 2 * A - b) (A - b - K)) (T - b) by ring]
    rw [← max_sub_sub_left, ← max_sub_sub_left]
    congr 1
    · congr 1 <;> linarith only [hmass]
    · linarith only [hmass]
private theorem large_pair_gap_of_reserve {A b ell delta gamma q : ℝ}
    (hA : 1 / 3 < A) (hb : b ≤ 1 - 2 * A) (hell : 0 < ell)
    (hdelta : 0 < delta) (hdeq : delta = 1 - ell) (hq : 157 / 1000 < q)
    (hqmul : ell * q ≤ delta) (hgamma : delta * (631 / 2000) < gamma)
    (hreserve : gamma + ell * (A ^ 2 + b ^ 2) ≤ 2 * A ^ 2) :
    3 / 200 < A - b := by
  by_cases hlarge : 17 / 50 ≤ A
  · linarith only [hlarge, hb]
  have hAhi : A ≤ 17 / 50 := (lt_of_not_ge hlarge).le
  have hbA : b ≤ A := by linarith only [hb, hA]
  have hA2 : A ^ 2 ≤ (17 / 50 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hA]) hAhi 2
  have hscaled := mul_nonneg hdelta.le (sub_nonneg.mpr hA2)
  have hbase : delta * (843 / 10000) < ell * (A ^ 2 - b ^ 2) := by
    nlinarith only [hgamma, hreserve, hscaled, hdeq]
  by_contra hn
  have hgap : A - b ≤ 3 / 200 := le_of_not_gt hn
  have hprod := mul_nonneg (sub_nonneg.mpr hbA)
    (show 0 ≤ 17 / 25 - (A + b) by linarith only [hAhi, hbA])
  have hprodEll := mul_nonneg hell.le hprod
  have hgapEll := mul_nonneg hell.le (sub_nonneg.mpr hgap)
  have hupper : ell * (A ^ 2 - b ^ 2) ≤ ell * (51 / 5000) := by
    nlinarith only [hprodEll, hgapEll]
  have hqStrict := mul_pos hell (sub_pos.mpr hq)
  have hdeltaStrict : ell * (157 / 1000) < delta := by linarith only [hqmul, hqStrict]
  have hmargin := mul_pos (sub_pos.mpr hdeltaStrict) (by norm_num : (0 : ℝ) < 843 / 10000)
  nlinarith only [hbase, hupper, hmargin, hell]

private theorem large_whole_degree_add_closed_missing (S : SelectedHighLowStructure W m)
    (j : S.I) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    wholeRowDegree j.val + S.originalAtomMass j +
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) = 1 := by
  have hdegree := ae_degree_eq_wholeRowDegree W m S.ρ S.hrow
    (hW.strict_gap_structure hd hgap).strict_support
  obtain ⟨x, hx, ⟨hdeg, hdec⟩, hout⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j.val j.property).2.1.ne'
    (((ae_restrict_of_ae hdegree).and (ae_restrict_of_ae
      (S.ae_missing_mass_decomposition hW hd hgap))).and
      (S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW j j.property))
  rw [hx] at hdeg
  rw [hdeg, S.ownIndependentMass_eq_fiber j j.property x hx, hout] at hdec
  change 1 - wholeRowDegree j.val = S.originalAtomMass j +
    μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) at hdec
  linarith only [hdec]

private theorem large_universal_head_whole_degrees (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    wholeRowDegree r.val = 1 - S.originalAtomMass r ∧
      wholeRowDegree p.val = S.originalAtomMass r +
        μ.real (S.universalPartnerCommonRegion r p) := by
  have hIr := S.hfibers r.val r.property
  have hNr : μ.real (S.rootNeighborhood r) = μ.real {x | S.ρ x = r.val}ᶜ := by
    apply measureReal_congr
    filter_upwards [S.ae_universal_rootNeighborhood_iff r hW hd hgap hN] with x hx
    exact propext hx
  have hdegR : wholeRowDegree r.val = 1 - S.originalAtomMass r := by
    rw [S.wholeRowDegree_eq_neighborhood_mass r, hNr, measureReal_compl hIr.1, probReal_univ]
    rfl
  have hSAT := (ae_restrict_iff' hIr.1).mp hpair.symm.row_on_other
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hsets : KernelOperator.wholeFiberMissingSet S.ρ p.val =ᵐ[μ]
      S.universalPartnerHoleRegion r p := by
    filter_upwards [hSAT] with x hx
    apply propext
    constructor
    · intro hmissing
      have hnotr : S.ρ x ≠ r.val := by
        intro he
        have hp := hx he
        linarith only [hp, hmissing.2, hmneg]
      intro hbad
      rcases hbad with (hr | hp) | hn
      · exact hnotr hr
      · exact hmissing.1 hp
      · exact (not_lt_of_ge hmissing.2) hn.2
    · intro hxH
      refine ⟨fun he => hxH (Or.inl (Or.inr he)), ?_⟩
      apply le_of_not_gt
      intro hp
      exact hxH (Or.inr ⟨fun he => hxH (Or.inl (Or.inr he)), hp⟩)
  have hmissing : μ.real (KernelOperator.wholeFiberMissingSet S.ρ p.val) =
      μ.real (S.universalPartnerHoleRegion r p) := measureReal_congr hsets
  have hdegP := S.large_whole_degree_add_closed_missing p hW hd hgap
  rw [hmissing] at hdegP
  have hmass := S.universalPartner_regions_mass r p hpair.1
  exact ⟨hdegR, by linarith only [hdegP, hmass]⟩

private theorem large_closed_hole_le_two_head_cap (S : SelectedHighLowStructure W m)
    (r p j : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hj : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.universalPartnerHoleRegion r p) :
    S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤
      1 - 2 * S.originalAtomMass r := by
  have hrowDegree : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      (∫ z, adjacencyKernel W x z ∂μ) = wholeRowDegree j.val := by
    filter_upwards [(S.hfibers j.val j.property).2.2.2.rows] with x hx
    exact integral_congr_ae hx.2.1
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hdegree := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_degree_ge_twice_mass r p hpair hW hd hgap hell hN)
  obtain ⟨x, _, hxH, hxDegree, hxRow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j.val j.property).2.1.ne'
    (hj.and ((ae_restrict_of_ae hdegree).and hrowDegree))
  have hlow := hxDegree hxH
  rw [hxRow] at hlow
  have hclosed := S.large_whole_degree_add_closed_missing j hW hd hgap
  change 2 * S.originalAtomMass r ≤ wholeRowDegree j.val at hlow
  linarith only [hlow, hclosed]

private theorem large_high_closed_le_peak_gap (S : SelectedHighLowStructure W m)
    (r j : S.I) (hjr : j ≠ r) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H) :
    S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤
      S.originalAtomMass r - forwardPeakGap d c m := by
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∉ S.L :=
    hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨f, hf, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap r
  have hredirect := hf.atomRedirect_of_stationary hW j j.property hhigh
  have hne : (j : Lp ℝ 2 μ) ≠ r := fun he => hjr (Subtype.ext he)
  have hstill := S.atomRedirect_avoids j r hne f havoid
  have hret := hredirect.classMass_eq_original_of_avoids_nonlow r hnonlow hstill
  have hmassJ : S.forwardClassMass (S.atomRedirect j f) j =
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
    rw [S.forwardClassMass_eq_fiber]
    exact hf.atomRedirect_endpoint_mass hW j j.property hhigh
  have hsep := (hpeak (S.atomRedirect j f) hredirect).2.2 j hjr
  rw [hret, hmassJ] at hsep
  change S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) +
    forwardPeakGap d c m ≤ S.originalAtomMass r at hsep
  change _ ≤ S.originalAtomMass r - forwardPeakGap d c m
  linarith only [hsep]

/-- Actual closed-missing caps pay the original normalized degree-tangent
floor on every positive missing section of the entire partner hole.
Zero sections are retained without constructing a diffuse atom. -/
theorem universal_hole_tangent_floor_of_closed_caps
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hy : 1 / 3 ≤ (1 - m - 4 * (c - m * d)) / (1 + m)) {C : ℝ}
    (hclosed : ∀ j : S.I, (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) →
        S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤
          S.originalAtomMass p + C) :
    let eta := μ.real (S.universalPartnerHoleRegion r p)
    let u := μ.real (S.universalPartnerCommonRegion r p)
    let v := 1 - 2 * (1 - 2 * d) - u
    0 < v ∧ ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      0 < S.universalPartnerHoleMissingMass r p x →
        (1 + m) * (max (eta - C) 0 / (3 * v)) ≤ S.universalRootDeficit r x := by
  dsimp only
  let eta := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let v := 1 - 2 * (1 - 2 * d) - u
  let delta := 1 + m
  let Delta := 1 - m - 4 * (c - m * d)
  obtain ⟨hdegR, hdegP⟩ := S.large_universal_head_whole_degrees r p hpair hW hd hgap hN
  have hvRaw := hpair.degree_sum_lt_four_density_of_multiplier_lt_one hW hd hgap hell
  rw [hdegR, hdegP] at hvRaw
  have hv : 0 < v := by dsimp only [v, u]; linarith only [hvRaw]
  have hdelta : 0 < delta := by dsimp only [delta]; linarith only [hell]
  have hDelta : delta / 3 ≤ Delta := by
    have hh := (le_div_iff₀ hdelta).mp hy
    change (1 / 3 : ℝ) * delta ≤ Delta at hh
    linarith only [hh]
  refine ⟨hv, ?_⟩
  filter_upwards [S.ae_universalPartnerHole_atom_of_missing_mass_pos
    r p hpair hW hd hgap hell] with x hx hpos
  obtain ⟨j, _, hj, _, hconst⟩ := hx hpos
  obtain ⟨hgapPos, _, htangent⟩ :=
    hpair.universal_atomic_deficit_tangent j hW hd hgap hell hN hj
  have hdegreeJ := S.large_whole_degree_add_closed_missing j hW hd hgap
  have hjcap := hclosed j hj
  have hmass := S.universalPartner_regions_mass r p hpair.1
  change S.originalAtomMass r + S.originalAtomMass p + eta + u = 1 at hmass
  have hgapLower : eta - C ≤ wholeRowDegree j.val - wholeRowDegree p.val := by
    rw [hdegP]
    linarith only [hdegreeJ, hjcap, hmass]
  have hgapMax : max (eta - C) 0 ≤ wholeRowDegree j.val - wholeRowDegree p.val :=
    max_le hgapLower hgapPos.le
  have hJpos : 0 < S.originalAtomMass j :=
    ENNReal.toReal_pos (S.hfibers j.val j.property).2.1.ne' (measure_ne_top μ _)
  have haverage : (S.originalAtomMass j)⁻¹ *
      (∫ z in {z | S.ρ z = j.val}, S.universalRootDeficit r z ∂μ) =
        S.universalRootDeficit r x := by
    rw [integral_congr_ae hconst, setIntegral_const, smul_eq_mul]
    change (S.originalAtomMass j)⁻¹ * (S.originalAtomMass j * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ hJpos.ne', one_mul]
  change Delta * (wholeRowDegree j.val - wholeRowDegree p.val) /
    (4 * d - wholeRowDegree r.val - wholeRowDegree p.val) ≤
      (S.originalAtomMass j)⁻¹ *
        (∫ z in {z | S.ρ z = j.val}, S.universalRootDeficit r z ∂μ) at htangent
  have hdenEq : 4 * d - wholeRowDegree r.val - wholeRowDegree p.val = v := by
    rw [hdegR, hdegP]
    dsimp only [v, u]
    ring
  rw [haverage, hdenEq] at htangent
  have hfirst := mul_nonneg (sub_nonneg.mpr hDelta) hgapPos.le
  have hsecond := mul_nonneg hdelta.le (sub_nonneg.mpr hgapMax)
  have hscalar : delta * max (eta - C) 0 / 3 ≤
      Delta * (wholeRowDegree j.val - wholeRowDegree p.val) := by
    nlinarith only [hfirst, hsecond]
  calc
    delta * (max (eta - C) 0 / (3 * v)) =
        (delta * max (eta - C) 0 / 3) / v := by field_simp
    _ ≤ (Delta * (wholeRowDegree j.val - wholeRowDegree p.val)) / v :=
      div_le_div_of_nonneg_right hscalar hv.le
    _ ≤ S.universalRootDeficit r x := htangent

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem large_hole_partner_mass_le_outside
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.originalAtomMass p ≤ S.outsideSectionMass x := by
  filter_upwards [S.ae_partner_row_zero_on_universalHole r p hW,
    ae_restrict_of_ae (S.ae_atomMass_le_outsideSectionMass_on_missing hW p),
    ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)] with x hx hb hxH
  apply hb
  exact ⟨fun he => hxH (Or.inl (Or.inr he)), by rw [hx]⟩

/-- The actual closed caps and original degree tangent give the basic,
refined and joint deficit conditions on one entire hole inventory. The
intermediate cap premise is explicit; the final system derives it from flows. -/
theorem universal_hole_refined_deficit_necessary
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hyLower : 1 / 3 ≤ (1 - m - 4 * (c - m * d)) / (1 + m)) {C ybar : ℝ}
    (hy : (1 - m - 4 * (c - m * d)) / (1 + m) ≤ ybar) (hC : 0 ≤ C)
    (hb : S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r)
    (hclosed : ∀ j : S.I, (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) →
        S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤
          S.originalAtomMass p + C) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let eta := μ.real (S.universalPartnerHoleRegion r p)
    let u := μ.real (S.universalPartnerCommonRegion r p)
    let v := 1 - 2 * (1 - 2 * d) - u
    let P := ybar - u
    let t0 := max (eta - C) 0 / (3 * v)
    let tf := if 0 < eta - 2 * C then max t0 (max 0 ((eta - C - P) / (eta - 2 * C))) else t0
    let Qcap := min (min (C * eta) (eta ^ 2)) (1 - 2 * d - A ^ 2 - b ^ 2 - 2 * b * eta)
    0 < v ∧ min (eta / 2) (eta - C) ≤ P ∧
      min (eta / 2) (eta - C + (2 * C - eta) * min (1 / 2) t0) ≤ P ∧
      0 ≤ Qcap ∧ (1 - A - b - ybar) ^ 2 - (ybar - A) * P - max 0 (1 - 2 * tf) * Qcap ≤ 0 := by
  dsimp only
  let H := S.universalPartnerHoleRegion r p
  let eta := μ.real H
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let D := S.universalRootDeficit r
  let a := S.universalPartnerHoleMissingMass r p
  let delta := 1 + m
  let P := ybar - u
  let Q := ∫ x in H, a x ∂μ
  let T := ∫ x in H, a x * D x ∂μ
  let L := ∫ x in H, S.universalPartnerCommonMissingMass r p x ∂μ
  let t0 := max (eta - C) 0 / (3 * (1 - 2 * (1 - 2 * d) - u))
  let tf := if 0 < eta - 2 * C then max t0 (max 0 ((eta - C - P) / (eta - 2 * C))) else t0
  let Qcap := min (min (C * eta) (eta ^ 2))
    (1 - 2 * d - (S.originalAtomMass r) ^ 2 - (S.originalAtomMass p) ^ 2 -
      2 * S.originalAtomMass p * eta)
  have hdelta : 0 < delta := by dsimp only [delta]; linarith only [hell]
  obtain ⟨hv, htangent⟩ := S.universal_hole_tangent_floor_of_closed_caps
    r p hpair hW hd hgap hell hN hyLower hclosed
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hbOutside := (ae_restrict_iff' hH).mp (S.large_hole_partner_mass_le_outside r p hW)
  have hparts : ∀ j : S.I, (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ H) →
      S.originalAtomMass j ≤ C := by
    intro j hj
    obtain ⟨x, _, hxH, hxb, hxEq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers j.val j.property).2.1.ne'
      (hj.and ((ae_restrict_of_ae hbOutside).and
        (S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW j j.property)))
    have hbmissing : S.originalAtomMass p ≤
        μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
      rw [← hxEq]
      exact hxb hxH
    linarith only [hclosed j hj, hbmissing]
  have htriangle := S.ae_universalPartnerHole_integrated_triangle r p hpair hW hd hgap hell hN
  have hacap := S.ae_universalPartnerHole_missing_mass_le r p hpair hW hd hgap hell hC hparts
  have hrows : ∀ᵐ x ∂μ.restrict H, 0 ≤ D x ∧ a x ≤ C ∧
      delta * ((μ.restrict H).real univ - a x) ≤
        ((μ.restrict H).real univ - 2 * a x) * D x + ∫ y in H, D y ∂μ := by
    filter_upwards [htriangle, hacap] with x hx ha
    exact ⟨(S.universalRootDeficit_mem_Icc r x).1, ha,
      by simpa only [measureReal_restrict_apply_univ] using hx⟩
  have hD : IntegrableOn D H μ := (S.integrable_universalRootDeficit r).integrableOn
  have ha : IntegrableOn a H μ := (S.integrable_universalPartnerHoleMissingMass r p).integrableOn
  have haD : IntegrableOn (fun x => a x * D x) H μ := by
    have hh := Integrable.bdd_mul ha
      (S.measurable_universalRootDeficit r).aestronglyMeasurable (c := 4)
    apply (by simpa only [mul_comm] using hh)
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (S.universalRootDeficit_mem_Icc r x).1]
      exact (S.universalRootDeficit_mem_Icc r x).2)
  have hcap : (∫ x in H, D x ∂μ) ≤ delta * P := by
    have hy' := (div_le_iff₀ hdelta).mp hy
    have hh := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
    change (∫ x in H, D x ∂μ) ≤ _ at hh
    dsimp only [delta, P, u]
    nlinarith only [hy', hh]
  have hbasic := UniversalDeficit.complete_part_lower_of_integrated_rows D a hD hdelta hrows
  have hrefined := UniversalDeficit.refined_complete_part_lower D a hD hdelta hrows htangent
  have hweighted := UniversalDeficit.refined_weighted_atomic_floor D a hD ha haD hdelta hrows
    (Eventually.of_forall (fun x => S.universalPartnerHoleMissingMass_nonneg r p x)) htangent hcap
  simp only [measureReal_restrict_apply_univ] at hbasic hrefined hweighted
  have hPcap : (∫ x in H, D x ∂μ) / delta ≤ P :=
    (div_le_iff₀ hdelta).mpr (by simpa only [mul_comm] using hcap)
  have hbasicP : min (eta / 2) (eta - C) ≤ P :=
    (mul_le_mul_iff_right₀ hdelta).mp (hbasic.trans hcap)
  have hrefinedP : min (eta / 2) (eta - C + (2 * C - eta) * min (1 / 2) t0) ≤ P :=
    hrefined.trans hPcap
  have hQC : Q ≤ C * eta := by
    have hh := integral_mono_ae ha (integrable_const C) hacap
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm] using hh
  have hQeta : Q ≤ eta ^ 2 := S.universalHoleSquareMoment_le_mass_sq r p
  have hQmissing := S.universalPartnerHole_square_le_missing_residual r p hpair hW hd hgap hN
  have hQcap : Q ≤ Qcap := le_min (le_min hQC hQeta) hQmissing
  have hQ : 0 ≤ Q := integral_nonneg (fun x => S.universalPartnerHoleMissingMass_nonneg r p x)
  have hL : 0 ≤ L := integral_nonneg (fun x => S.universalPartnerCommonMissingMass_nonneg r p x)
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hcoef : 0 ≤ eta + u - S.originalAtomMass r := by linarith only [hmass, hb]
  have hjoint := S.universal_integrated_deficit_joint r p hpair hW hd hgap hell hN hy
  have hnecessary := UniversalDeficit.refined_joint_necessary hdelta hcoef hQ hL hcap hQcap
    hweighted hjoint
  have heq : (1 - S.originalAtomMass r - S.originalAtomMass p - ybar) ^ 2 -
      (ybar - S.originalAtomMass r) * P = eta ^ 2 - (2 * eta + u - S.originalAtomMass r) * P := by
    have hw : 1 - S.originalAtomMass r - S.originalAtomMass p - ybar = eta - P := by
      dsimp only [P]
      linarith only [hmass]
    rw [hw]
    dsimp only [P]
    ring
  refine ⟨hv, hbasicP, hrefinedP, hQ.trans hQcap, ?_⟩
  change _ - _ - max 0 (1 - 2 * tf) * Qcap ≤ 0
  rw [heq, max_comm]
  linarith only [hnecessary]

private theorem large_middle_closed_cap_data
    (S : SelectedHighLowStructure W m) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c r)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hq : q ∈ Ioc (157 / 1000 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hm : m = -LowerE2Scalar.multiplier q) (hell : -m < 1)
    (hA : S.originalAtomMass r ∈ Ioo (1 / 3 : ℝ) (369 / 1000))
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hycap : (1 - m - 4 * (c - m * d)) / (1 + m) < 369 / 1000)
    (hb : S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r)
    (hholes : 0 < μ (S.universalPartnerHoleRegion r p)) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let D2 := (-1 + 6 * A - (5 + 3 * (-m)) * A ^ 2) / 3
    let sc := (D2 - LowerE2Scalar.gapFloor q) / (-m - 4 / 5)
    let T := Real.sqrt sc
    let K := LowerE2Scalar.universalPeakGapFloor q
    let C := min (min (1 - 2 * A - b) (A - b - K)) (T - b)
    0 ≤ sc ∧ 0 ≤ C ∧ b ≤ T ∧ ∀ j : S.I,
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.universalPartnerHoleRegion r p) →
        S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤ b + C := by
  dsimp only
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let gamma := 2 * (c - m * d) + m
  let delta := 1 + m
  let D2 := (-1 + 6 * A - (5 + 3 * (-m)) * A ^ 2) / 3
  let sc := (D2 - LowerE2Scalar.gapFloor q) / (-m - 4 / 5)
  let T := Real.sqrt sc
  let K := LowerE2Scalar.universalPeakGapFloor q
  let C := min (min (1 - 2 * A - b) (A - b - K)) (T - b)
  have hq0 : 0 < q := by linarith only [hq.1]
  have hell45 : 4 / 5 < -m := by
    rw [hm, neg_neg]
    unfold LowerE2Scalar.multiplier
    apply (lt_div_iff₀ (by linarith only [hq0])).mpr
    linarith only [hq.2]
  have hcoef : 0 < -m - 4 / 5 := sub_pos.mpr hell45
  have hdelta : 0 < delta := by dsimp only [delta]; linarith only [hell]
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∉ S.L :=
    hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  have hAbox : S.originalAtomMass r ∈ Icc (1 / 3 : ℝ) (2 / 5) :=
    ⟨hA.1.le, by linarith only [hA.2]⟩
  have hD2 : gamma ≤ D2 :=
    S.large_middle_common_peak_sharp_gap_bound r hW hd hgap hpeak hnonlow hAbox hell45.le
  have hsc : 0 < sc := div_pos (by linarith only [hD2, hgamma]) hcoef
  have hT : 0 < T := Real.sqrt_pos.mpr hsc
  have hTsq : T ^ 2 = sc := Real.sq_sqrt hsc.le
  have hidentity : (-m - 4 / 5) * T ^ 2 = D2 - LowerE2Scalar.gapFloor q := by
    rw [hTsq]
    exact mul_div_cancel₀ _ hcoef.ne'
  have hmargin : D2 < gamma + (-m - 4 / 5) * T ^ 2 := by
    linarith only [hidentity, hgamma]
  have hatomic : ∀ j : S.I, j ≠ r →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H) →
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤ T := by
    intro j hjr hjH
    have hbudget := S.large_middle_high_atom_closed_missing_sq_bound
      r j hjr hW hd hgap hpeak hnonlow hjH hAbox hell45.le
    change gamma + (-m - 4 / 5) * _ ≤ D2 at hbudget
    have hscaled : (-m - 4 / 5) *
        (S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)) ^ 2 <
          (-m - 4 / 5) * T ^ 2 := by linarith only [hbudget, hmargin]
    have hsquare := (mul_lt_mul_iff_right₀ hcoef).mp hscaled
    nlinarith only [hsquare, hT]
  have hyid : delta * ((1 - m - 4 * (c - m * d)) / (1 + m)) = delta - 2 * gamma := by
    dsimp only [delta, gamma]
    rw [mul_div_cancel₀ _ hdelta.ne']
    ring
  have hgammaLower : delta * (631 / 2000) < gamma := by
    have hscaled := mul_pos hdelta (sub_pos.mpr hycap)
    nlinarith only [hyid, hscaled]
  have hguard : 2 * delta * A ^ 2 < gamma := by
    have hA0 : 0 ≤ A := by dsimp only [A]; linarith only [hA.1]
    have hA2 : A ^ 2 ≤ (369 / 1000 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hA0 hA.2.le 2
    have hscaled := mul_nonneg hdelta.le (sub_nonneg.mpr hA2)
    nlinarith only [hgammaLower, hscaled, hdelta]
  have hdiffuse : ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → S.outsideSectionMass x ≤ T := by
    by_cases hTA : T ≤ A
    · exact S.ae_large_middle_diffuse_high_outside_le r hW hd hgap hpeak hnonlow hAbox
        hell45.le hT hTA hmargin
    · obtain ⟨i, _, _, hi, _, _, _, _, _, hconditional⟩ :=
        S.exists_conditional_missing_mass_cap hW hd hgap
      obtain ⟨hDelta, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
      have hir : i = r := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
        (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
      subst i
      obtain ⟨hRadius, hdiffuse, _⟩ := hconditional hguard
      filter_upwards [hdiffuse] with x hx hxD hxH
      exact (hx hxD hxH).trans (hRadius.le.trans (lt_of_not_ge hTA).le)
  have hrecipients := S.ae_nonpeak_high_outside_le hW r T hatomic hdiffuse
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hHhigh := S.ae_universalPartnerHole_high r p hpair hW hd hgap hell
  have hbT : b ≤ T := by
    obtain ⟨x, hxH, hxb, hxHigh, hxCap⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hholes.ne'
      ((S.large_hole_partner_mass_le_outside r p hW).and
        (hHhigh.and (ae_restrict_of_ae hrecipients)))
    exact hxb.trans (hxCap hxHigh (fun he => hxH (Or.inl (Or.inl he))))
  obtain ⟨hDelta, i, _, _, hi, _, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hir : i = r := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst i
  have hfinite := Summable.sum_le_tsum (s := {r, p})
    (fun j _ => sq_nonneg (S.originalAtomMass j)) S.originalAtomMass_sq_summable
  rw [Finset.sum_pair hpair.1] at hfinite
  have hpaid := mul_le_mul_of_nonneg_left hfinite (show 0 ≤ -m by linarith only [hell45])
  have hpairReserve : gamma + (-m) * (A ^ 2 + b ^ 2) ≤ 2 * A ^ 2 := by
    dsimp only [gamma, A, b]
    linarith only [hreserve, hpaid]
  have hqmul : (-m) * q ≤ delta := by
    change (-m) * q ≤ 1 + m
    rw [hm]
    simpa only [neg_neg, sub_eq_add_neg] using
      LowerE2Scalar.multiplier_gap_ge_parameter hq0.le
  have hgapPair := large_pair_gap_of_reserve hA.1 hb
    (show 0 < -m by linarith only [hell45]) hdelta
    (by dsimp only [delta]; ring) hq.1 hqmul hgammaLower hpairReserve
  have hKbound : K ≤ 54 / 3721 := by
    have hh := LowerE2Scalar.universalPeakGapFloor_strictMonoOn.monotoneOn
      (show q ∈ Icc (0 : ℝ) (1 / 5) from ⟨hq0.le, hq.2⟩)
      (by norm_num : (1 / 5 : ℝ) ∈ Icc (0 : ℝ) (1 / 5)) hq.2
    have he : LowerE2Scalar.universalPeakGapFloor (1 / 5) = 54 / 3721 := by
      norm_num [LowerE2Scalar.universalPeakGapFloor, LowerE2Scalar.denominator]
    rwa [he] at hh
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact le_min (le_min (by linarith only [hb])
      (by linarith only [hgapPair, hKbound])) (sub_nonneg.mpr hbT)
  have hmissing : 1 - 2 * d = LowerE2Scalar.missingMass q := by rw [hdq]; ring
  have hKsharp : K < 2 * c - (1 - 2 * d) := by
    have he := LowerE2Scalar.universalPeakGapFloor_eq_benchmark ⟨hq0, hq.2⟩
    rw [← hdq, ← hmissing] at he
    dsimp only [K]
    linarith only [he, hgap]
  have hgapEq : forwardPeakGap d c m = 2 * c - (1 - 2 * d) := by
    simp [forwardPeakGap, ForwardPeak.peakGap, show ¬1 ≤ -m from not_le.mpr hell]
  refine ⟨hsc.le, hC, hbT, ?_⟩
  intro j hj
  obtain ⟨x, hxj, hxH⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j.val j.property).2.1.ne' hj
  have hjr : j ≠ r := fun he => hxH (Or.inl (Or.inl
    (hxj.trans (congrArg Subtype.val he))))
  have hjH : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H := by
    have hh := (ae_restrict_iff' hH).mp hHhigh
    filter_upwards [hj, ae_restrict_of_ae hh] with x hx hxHigh
    exact hxHigh hx
  have hfirst := S.large_closed_hole_le_two_head_cap r p j hpair hW hd hgap hell hN hj
  have hsecond := S.large_high_closed_le_peak_gap r j hjr hW hd hgap hpeak hN hjH
  rw [hgapEq] at hsecond
  have hthird := hatomic j hjr hjH
  have hmin : S.originalAtomMass j +
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) - b ≤ C := by
    dsimp only [C]
    exact le_min (le_min (by linarith only [hfirst])
      (by linarith only [hsecond, hKsharp])) (by linarith only [hthird])
  linarith only [hmin]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

open MiddleE2LargeUniversal

/-- The actual open middle-E2 universal branch supplies the entire closed
certificate box and every necessary condition. One original physical primal
and its same-partner singleton recovery are retained in the conclusion. -/
theorem middle_large_universal_necessary_system
    (S : SelectedHighLowStructure W m) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1) :
    ∃ (_P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery), R.plateau = {p} ∧
      0 < μ (S.reverseCompulsorySource {p}) ∧
      (S.middleLargeUniversalPoint r p q).InBox ∧
      (S.middleLargeUniversalPoint r p q).Necessary := by
  let X := S.middleLargeUniversalPoint r p q
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let eta := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let ell := -m
  let gamma := 2 * (c - m * d) + m
  let delta := 1 + m
  let g := LowerE2Scalar.gapFloor q
  let Y := 9 * q / (2 * LowerE2Scalar.denominator q)
  let K := LowerE2Scalar.universalPeakGapFloor q
  let D2 := (-1 + 6 * A - (5 + 3 * ell) * A ^ 2) / 3
  let sc := (D2 - g) / (ell - 4 / 5)
  let T := Real.sqrt sc
  let C := min (min (1 - 2 * A - b) (A - b - K)) (T - b)
  let RC := min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * g) / ell)
  let Pcap := Y - u
  let v := 1 - 2 * (1 - 2 * d) - u
  let t0 := max (eta - C) 0 / (3 * v)
  let tf := if 0 < eta - 2 * C then max t0 (max 0 ((eta - C - Pcap) / (eta - 2 * C))) else t0
  let Qcap := min (min (C * eta) (eta ^ 2)) (1 - 2 * d - A ^ 2 - b ^ 2 - 2 * b * eta)
  obtain ⟨P, hcut, hA, hholes, hm, hell, hgamma, hAy, hyupper, hratio,
      hbMass, hb, hu, _, hmargin⟩ :=
    S.middle_large_universal_initial_guards r p hpair hW hq hdq hgap hglobal hpeak huniv
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith only [hq.1], hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ Benchmark.e2_density_mem hq'
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hycap : (1 - m - 4 * (c - m * d)) / (1 + m) < 369 / 1000 := by
    linarith only [hyupper, hratio]
  have hyLower : 1 / 3 ≤ (1 - m - 4 * (c - m * d)) / (1 + m) := by
    linarith only [hA.1, hAy]
  have hAY : A ≤ Y := hAy.trans hyupper.le
  obtain ⟨R, hr, hsource, _, hkappa, huMargin⟩ :=
    S.middle_large_universal_partner_recovery r p hpair hW hq hdq hgap hglobal hpeak huniv hA.1
  have huR : u < 1 - 2 * A := by
    change u + _ < 1 - 2 * A at huMargin
    linarith only [huMargin, hkappa]
  have huThird : u < 1 / 3 := by linarith only [huR, hA.1]
  have hAhalf : S.originalAtomMass r ≤ 1 / 2 := by linarith only [hA.2]
  have hellHalf : -m ∈ Ioo (1 / 2 : ℝ) 1 :=
    ⟨by linarith only [hell.1], hell.2⟩
  have hnegative := P.middle_large_universal_negative_region_pos_of_ratio
    S R r p hpair hW hd hgap hr hN hA.1 hA.2 hell hycap hmargin
  have hnegativeCap := P.ae_universal_upperE2_negative_missing_le
    S r p hpair hW hd hgap hN hA.1 hAhalf hellHalf hmargin huR
  have hGint : Integrable (fun z : Ω × Ω => adjacencyKernel W z.1 z.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  obtain ⟨x, _, hxCap, hxG⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hnegative.ne'
    (hnegativeCap.and (ae_restrict_of_ae hGint.prod_right_ae))
  have hxMissing : 0 ≤ 1 - ∫ z, adjacencyKernel W x z ∂μ := by
    have hh := integral_mono_ae hxG (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun z => (adjacency_moment_mem W (x, z)).2))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_nonneg] using hh
  have hRCactual : 0 ≤ min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell) := by
    have hh := hxMissing.trans hxCap
    change 0 ≤ min (1 - 3 * A + b) ((1 - u + 2 * m * A - 3 * gamma) / ell) at hh
    have he : 1 - u + 2 * m * A - 3 * gamma = 1 - u - 2 * ell * A - 3 * gamma := by
      dsimp only [ell]
      ring
    rwa [he] at hh
  have hB0 : 0 ≤ 1 - 3 * A + b := hRCactual.trans (min_le_left _ _)
  have hbLower : 3 * A - 1 ≤ b := by linarith only [hB0]
  have hell0 : 0 < ell := by dsimp only [ell]; linarith only [hell.1]
  have hrowActual : 0 ≤ (1 - u - 2 * ell * A - 3 * gamma) / ell :=
    hRCactual.trans (min_le_right _ _)
  have hrowNum := mul_nonneg hrowActual hell0.le
  rw [div_mul_cancel₀ _ hell0.ne'] at hrowNum
  have hRC : 0 ≤ RC := le_min hB0 (div_nonneg
    (by linarith only [hrowNum, hgamma] : 0 ≤ 1 - u - 2 * ell * A - 3 * g) hell0.le)
  have huRow := P.negative_common_mass_lt
    S r p hpair hW hd hgap hN hA.1 hAhalf hellHalf hmargin hnegative
  have huRowRelax : u ≤ 1 - 2 * ell * A - 3 * g := by
    dsimp only [u, ell, A, g]
    nlinarith only [huRow, hgamma]
  have hresources := (S.universal_partner_common_good_resources r p hpair hW hd hgap hN).1
  have hRP : ell * (1 - A) - A + g ≤ 2 * ell * u := by
    dsimp only [ell, A, u, g]
    nlinarith only [hresources, hgamma]
  obtain ⟨hsc, hC, _, hclosed⟩ := S.large_middle_closed_cap_data
    r p hpair hW hd hgap hpeak hN ⟨hcut, hq.2.le⟩ hdq hm hell.2 hA hgamma hycap hb hholes
  change 0 ≤ sc at hsc
  change 0 ≤ C at hC
  change ∀ j : S.I, (∀ᵐ z ∂μ.restrict {z | S.ρ z = j.val},
    z ∈ S.universalPartnerHoleRegion r p) →
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤
        b + C at hclosed
  have hCsecond : C ≤ A - b - K := (min_le_left _ _).trans (min_le_right _ _)
  have hbK : b ≤ A - K := by linarith only [hC, hCsecond]
  obtain ⟨hv, hbasic, hlpf, hQ, hjoint⟩ := S.universal_hole_refined_deficit_necessary
    r p hpair hW hd hgap hell.2 hN hyLower hyupper.le hC hb hclosed
  have hmass := S.universalPartner_regions_mass r p hpair.1
  change A + b + eta + u = 1 at hmass
  have heta : 0 ≤ eta := measureReal_nonneg
  obtain ⟨heq, hgq, hhq, hyq, hkq⟩ := large_family_parameters q
  have he : X.ell = ell := by
    change ellq q = -m
    rw [heq, hm]
    ring
  have hde : X.de = delta := by
    change 1 - ellq q = 1 + m
    rw [heq, hm]
    ring
  have hg : X.g = g := hgq
  have hh : X.h = 1 - 2 * d := by
    change MiddleE2LargeUniversal.hq q = 1 - 2 * d
    rw [hhq, hdq]
    ring
  have hY : X.y = Y := hyq
  have hK : X.K = K := hkq
  have hscX : X.sc = sc := by
    dsimp only [Point.sc]
    rw [hde, hg]
    change ((-1 + 6 * A - (8 - 3 * delta) * A ^ 2) / 3 - g) / (1 / 5 - delta) = sc
    dsimp only [sc, D2, ell, delta]
    congr 1 <;> ring
  have hT : X.T = T := congrArg Real.sqrt hscX
  have hCX : X.C = C := by
    dsimp only [Point.C, Point.r0]
    rw [hK, hT]
    rfl
  have hetaX : X.eta = eta := by
    change 1 - A - b - u = eta
    linarith only [hmass]
  have hQX : X.Q = Qcap := by
    dsimp only [Point.Q]
    rw [hCX, hetaX, hh]
    rfl
  have hpX : X.p = Pcap := by dsimp only [Point.p]; rw [hY]; rfl
  have hvX : X.v = v := by dsimp only [Point.v]; rw [hh]; rfl
  obtain ⟨hgapMin, hdgapMin⟩ := large_gap_min_identity (K := K) (T := T) (y := Y) hmass
  have hgapX : X.gap = eta - C := by
    dsimp only [Point.gap]
    rw [hK, hT]
    exact hgapMin.symm
  have ht0X : X.t0 = t0 := by
    dsimp only [Point.t0]
    rw [hgapX, hvX, max_comm (0 : ℝ) (eta - C)]
  have hdenX : X.den = eta - 2 * C := by
    dsimp only [Point.den]
    rw [hgapX, hetaX]
    ring
  have hdgapX : X.dgap = eta - C - Pcap := by
    dsimp only [Point.dgap]
    rw [hY, hK, hT]
    exact hdgapMin.symm
  have htfX : X.tf = tf := by
    dsimp only [Point.tf]
    rw [hdenX, ht0X, hdgapX]
  have hlpfX : X.lpf = min (eta / 2) (eta - C + (2 * C - eta) * min (1 / 2) t0) := by
    dsimp only [Point.lpf]
    rw [hetaX, hgapX, ht0X]
    congr 1
    ring
  have hjointX : X.joint = (1 - A - b - Y) ^ 2 - (Y - A) * Pcap -
      max 0 (1 - 2 * tf) * Qcap := by
    dsimp only [Point.joint]
    rw [hY, hpX, htfX, hQX]
    rfl
  have hRPX : X.RP = ell * (1 - A) - A + g := by
    dsimp only [Point.RP]
    rw [he, hg]
    rfl
  have hRCX : X.RC = RC := by
    dsimp only [Point.RC]
    rw [he, hg]
    rfl
  have hr0X : X.r0 = 1 - 2 * A := rfl
  have hbox : X.InBox := by
    change 157 / 1000 ≤ q ∧ q ≤ 1 / 5 ∧ 1 / 3 ≤ A ∧ A ≤ 369 / 1000 ∧
      0 ≤ b ∧ b ≤ 1 / 3 ∧ 0 ≤ u ∧ u ≤ 1 / 3
    exact ⟨hcut.le, hq.2.le, hA.1.le, hA.2.le, hbMass.1.le, hbMass.2.le, hu, huThird.le⟩
  have hnecessary : X.Necessary := by
    dsimp only [Point.Necessary]
    rw [hY, hr0X, hK, hRPX, he, hg, hetaX, hRCX, hscX, hCX, hQX, hpX, hvX, hlpfX, hjointX]
    exact ⟨hAY, hbLower, hb, hbK, hRP, huR.le, huRowRelax, heta, hRC, hsc, hC,
      hQ, hbasic, hv, hlpf, hjoint⟩
  exact ⟨P, R, hr, hsource, hbox, hnecessary⟩

/-- The actual original middle contact bounds every entire-hole missing
section by the literal certificate cap. Positive sections are actual whole
atoms; zero sections, including genuine dust, use the derived cap sign. -/
theorem ae_middle_large_universal_hole_missing_le_cap
    (S : SelectedHighLowStructure W m) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤ (S.middleLargeUniversalPoint r p q).C := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let D2 := (-1 + 6 * A - (5 + 3 * (-m)) * A ^ 2) / 3
  let sc := (D2 - LowerE2Scalar.gapFloor q) / (-m - 4 / 5)
  let T := Real.sqrt sc
  let K := LowerE2Scalar.universalPeakGapFloor q
  let C := min (min (1 - 2 * A - b) (A - b - K)) (T - b)
  obtain ⟨_, hcut, hA, hholes, hm, hell, hgamma, _, hyupper, hratio,
      _, hb, _, _, _⟩ :=
    S.middle_large_universal_initial_guards r p hpair hW hq hdq hgap hglobal hpeak huniv
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸
    Benchmark.e2_density_mem ⟨by linarith only [hq.1], hq.2.le⟩
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hycap : (1 - m - 4 * (c - m * d)) / (1 + m) < 369 / 1000 := by
    linarith only [hyupper, hratio]
  obtain ⟨_, hC, _, hclosed⟩ := S.large_middle_closed_cap_data
    r p hpair hW hd hgap hpeak hN ⟨hcut, hq.2.le⟩ hdq hm hell.2 hA hgamma hycap hb hholes
  change 0 ≤ C at hC
  change ∀ j : S.I, (∀ᵐ z ∂μ.restrict {z | S.ρ z = j.val},
    z ∈ S.universalPartnerHoleRegion r p) →
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤
        b + C at hclosed
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hbOutside := (ae_restrict_iff' hH).mp (S.large_hole_partner_mass_le_outside r p hW)
  have hparts : ∀ j : S.I, (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) → S.originalAtomMass j ≤ C := by
    intro j hj
    obtain ⟨x, _, hxH, hxb, hxEq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers j.val j.property).2.1.ne'
      (hj.and ((ae_restrict_of_ae hbOutside).and
        (S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW j j.property)))
    have hbmissing : b ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
      rw [← hxEq]
      exact hxb hxH
    linarith only [hclosed j hj, hbmissing]
  have hcap := S.ae_universalPartnerHole_missing_mass_le r p hpair hW hd hgap hell.2 hC hparts
  obtain ⟨heq, hgq, _, _, hkq⟩ := large_family_parameters q
  have hneg : LowerE2Scalar.multiplier q = -m := by linarith only [hm]
  have hscEq :
      ((-1 + 6 * A - (8 - 3 * (1 + m)) * A ^ 2) / 3 - LowerE2Scalar.gapFloor q) /
        (1 / 5 - (1 + m)) = sc := by
    dsimp only [sc, D2]
    congr 1 <;> ring
  have hCX : (S.middleLargeUniversalPoint r p q).C = C := by
    dsimp only [Point.C, Point.r0, Point.T, Point.sc, Point.de, deq, Point.g, Point.K,
      middleLargeUniversalPoint]
    rw [heq, hgq, hkq, hneg, sub_neg_eq_add]
    change min (min (1 - 2 * A - b) (A - b - K))
      (Real.sqrt (((-1 + 6 * A - (8 - 3 * (1 + m)) * A ^ 2) / 3 -
        LowerE2Scalar.gapFloor q) / (1 / 5 - (1 + m))) - b) = C
    rw [hscEq]
  rw [hCX]
  exact hcap

end Erdos1017.CappedModel.SelectedHighLowStructure

module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2OneCenterGeometry
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerBadRegion
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitBudget

/-!
# Negative universal charge from the singleton recovery

The stationary partner row spends its entire non-head mass on the common region,
a singleton recovery forces positive bad-region mass
(`universal_upperE2_bad_region_pos`), and the bad-vertex row forces a negative
universal charge on a set of positive measure
(`universal_upperE2_negative_region_pos`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The actual singleton recovery leaves a neutral original atom outside
its plateau unchanged, so its unique endpoint top is strictly larger. -/
theorem ReverseRecovery.universal_atom_mass_lt_singleton_height
    (R : S.ReverseRecovery) (r p : S.I) (hrp : r ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hr : R.plateau = {p})
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    S.originalAtomMass r < R.height := by
  have hmarg := R.reverse_marginals_zero_on_neutral r hN
  have he := MissingFlow.endpoint_real_set_eq_original R.flow R.isFullReverseFlow.integrable
    R.isFullReverseFlow.nonnegative R.isFullReverseFlow.supply_le_one
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
    (hmarg.mono (fun _ h hx => (h hx).1)) (hmarg.mono (fun _ h hx => (h hx).2))
  have hmass : S.reverseClassMass R.flow r = S.originalAtomMass r := by
    rw [reverseClassMass, S.collapsedPartLabel_fiber r, he]
    rfl
  have hne : S.reverseClassMass R.flow r ≠ R.height := by
    intro h
    have hrmem := (R.classMass_eq_iff hW r).mp h
    rw [hr] at hrmem
    exact hrp (Finset.mem_singleton.mp hrmem)
  rw [← hmass]
  exact lt_of_le_of_ne (R.classMass_le hW r) hne

/-- The same original recovery pays the strict common-plus-extra-hole
mass margin. No endpoint stationarity or displayed resource is assumed. -/
theorem ReverseRecovery.universal_partner_source_mass_margin
    (R : S.ReverseRecovery) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hr : R.plateau = {p})
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    0 ≤ μ.real (S.universalPartnerHoleRegion r p) - μ.real (S.reverseCompulsorySource {p}) ∧
      μ.real (S.universalPartnerCommonRegion r p) +
          (μ.real (S.universalPartnerHoleRegion r p) - μ.real (S.reverseCompulsorySource {p})) <
        1 - 2 * S.originalAtomMass r := by
  have hheight := R.universal_atom_mass_lt_singleton_height r p hpair.1 hW hr hN
  have hsource := R.singleton_height_eq_mass_add_source p hr
  change R.height = S.originalAtomMass p + μ.real (S.reverseCompulsorySource {p}) at hsource
  have hpartition := S.universalPartner_regions_mass r p hpair.1
  have hmono := ENNReal.toReal_mono
    (measure_ne_top μ (S.universalPartnerHoleRegion r p))
    (measure_mono_ae (S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell))
  exact ⟨sub_nonneg.mpr hmono, by linarith⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The original stationary partner row spends its entire non-head mass
on the literal common region. The hole region contributes zero. -/
theorem universal_partner_common_row_integral
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    (∫ x in S.universalPartnerCommonRegion r p, p.val x ∂μ) =
      2 * (c - m * d) - (1 - m) * S.originalAtomMass r := by
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hJ : MeasurableSet J := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hIJ : Disjoint I J := disjoint_left.mpr
    (fun _ hx hy => hpair.1 (Subtype.ext (hx.symm.trans hy)))
  have hIJH : Disjoint (I ∪ J) H := disjoint_left.mpr (fun _ hx hy => hy (Or.inl hx))
  have hIJHU : Disjoint (I ∪ J ∪ H) U := disjoint_left.mpr (fun _ hx hy => hy hx)
  have hwhole : I ∪ J ∪ H ∪ U = univ := S.universalPartner_regions_partition r p
  have hp : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hpart : (∫ x, p.val x ∂μ) = (∫ x in I, p.val x ∂μ) +
      (∫ x in J, p.val x ∂μ) + (∫ x in H, p.val x ∂μ) +
      ∫ x in U, p.val x ∂μ := by
    rw [← setIntegral_univ (f := (p.val : Ω → ℝ)), ← hwhole,
      setIntegral_union hIJHU hU hp.integrableOn hp.integrableOn,
      setIntegral_union hIJH hH hp.integrableOn hp.integrableOn,
      setIntegral_union hIJ hJ hp.integrableOn hp.integrableOn]
  have hhead : (∫ x in I, p.val x ∂μ) = (1 - m) * S.originalAtomMass r := by
    rw [integral_congr_ae hpair.symm.row_on_other, setIntegral_const, smul_eq_mul]
    change S.originalAtomMass r * (1 - m) = _
    ring
  have hself : (∫ x in J, p.val x ∂μ) = 0 := by
    rw [integral_congr_ae (S.root_row_zero_on_fiber p)]
    simp
  have hhole : (∫ x in H, p.val x ∂μ) = 0 :=
    integral_eq_zero_of_ae (S.ae_partner_row_zero_on_universalHole r p hW)
  rw [S.row_integral_of_stationary p hW, hhead, hself, hhole] at hpart
  linarith only [hpart]

/-- A genuine singleton recovery forces positive bad-region mass.
Otherwise the original partner row violates its stationary integral. -/
theorem ReverseRecovery.universal_upperE2_bad_region_pos
    (R : S.ReverseRecovery) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {p})
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhi : S.originalAtomMass r < 2 / 5)
    (hell : -m ∈ Ioo (4 / 5 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    0 < μ (S.universalUpperE2BadRegion r p d c) := by
  by_contra hn
  have hnull : μ (S.universalUpperE2BadRegion r p d c) = 0 :=
    le_antisymm (le_of_not_gt hn) zero_le
  have hnot := measure_eq_zero_iff_ae_notMem.mp hnull
  let A := S.originalAtomMass r
  let gamma := 2 * (c - m * d) + m
  let theta := 3 * gamma / A - (1 + m)
  let U := S.universalPartnerCommonRegion r p
  let ell := -m
  let RP := 2 * (c - m * d) - (1 - m) * A
  have hA0 : 0 < A := by dsimp only [A]; linarith only [hA]
  have hdelta : 0 < 1 + m := by linarith only [hell.2]
  have hu := (R.universal_partner_source_mass_margin r p hpair hW hd hgap hell.2 hr hN).2
  have hk := (R.universal_partner_source_mass_margin r p hpair hW hd hgap hell.2 hr hN).1
  have hu' : μ.real U < 1 - 2 * A := by
    change μ.real U + _ < 1 - 2 * A at hu
    linarith only [hu, hk]
  have hbound : ∀ᵐ x ∂μ.restrict U, p.val x ≤ ell - theta := by
    filter_upwards [ae_restrict_of_ae hnot,
      ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap),
      S.ae_partner_row_pos_on_universalCommon r p,
      ae_restrict_of_ae (S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN),
      ae_restrict_mem (S.measurableSet_universalPartnerCommonRegion r p)]
      with x hx hp hpos hscore hxU
    have hxr : S.ρ x ≠ r.val := fun h => hxU (Or.inl (Or.inl h))
    have hxp : S.ρ x ≠ p.val := fun h => hxU (Or.inl (Or.inr h))
    have htheta : theta ≤ S.rootChargeRow r x := by
      apply le_of_not_gt
      intro h
      apply hx
      constructor
      · change ¬(S.ρ x = r.val ∨ S.ρ x = p.val)
        rintro (hr | hp)
        · exact hxr hr
        · exact hxp hp
      · exact h
    have hs := hscore hxr (S.common_region_mem_rootNeighborhood r p hxU)
    rw [ite_eq_left hpos] at hp
    change 1 - S.rootChargeRow p x = _ at hp
    dsimp only [ell]
    linarith only [htheta, hs, hp]
  have hint := integral_mono_ae
    ((Lp.memLp p.val).integrable (by norm_num)).integrableOn
    (integrable_const (ell - theta)) hbound
  rw [S.universal_partner_common_row_integral r p hpair hW,
    setIntegral_const, smul_eq_mul] at hint
  change RP ≤ μ.real U * (ell - theta) at hint
  have hgamma : 0 < gamma := by
    have := mul_pos hA0 hdelta
    dsimp only [A, gamma] at *
    linarith only [this, hmargin]
  have hRP : 0 < RP := by
    have hprod := mul_pos (show 0 < 2 / 5 - A by exact sub_pos.mpr hAhi)
      (show 0 < 1 - m by linarith only [hell.1])
    dsimp only [RP, gamma, A] at *
    nlinarith only [hprod, hell.1, hgamma]
  have hcoef : 0 < ell - theta := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos (measureReal_nonneg (μ := μ) (s := U))
      (le_of_not_gt h)
    linarith only [hint, hRP, this]
  have hupper := mul_le_mul_of_nonneg_left hu'.le hcoef.le
  have htheta : A * theta = 3 * gamma - A * (1 + m) := by
    dsimp only [theta]
    field_simp [hA0.ne']
  have hpositive := add_pos
    (mul_pos (show 0 < 3 * gamma - 2 * A * (1 + m) by exact sub_pos.mpr hmargin)
      (show 0 < 3 - 5 * A by linarith only [hAhi]))
    (mul_pos (mul_pos hdelta hA0) (show 0 < 3 - 7 * A by linarith only [hAhi]))
  have hidentity : 3 * A * (RP - (ell - theta) * (1 - 2 * A)) =
      (3 * gamma - 2 * A * (1 + m)) * (3 - 5 * A) +
        (1 + m) * A * (3 - 7 * A) := by
    dsimp only [RP, ell, gamma] at *
    have h := congrArg (fun x : ℝ => 3 * (1 - 2 * A) * x) htheta
    nlinarith only [h]
  have hscaled := mul_le_mul_of_nonneg_left
    (le_trans hint (by simpa only [mul_comm] using hupper))
    (mul_pos (by norm_num : (0 : ℝ) < 3) hA0).le
  rw [← hidentity] at hpositive
  linarith only [hscaled, hpositive]

/-- The same original singleton recovery and bad-vertex row force a
negative universal charge on a set of positive original measure. -/
theorem UniversalPhysicalPrimal.universal_upperE2_negative_region_pos
    (S : SelectedHighLowStructure W m) (R : S.ReverseRecovery) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {p})
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhi : S.originalAtomMass r < 2 / 5)
    (hell : -m ∈ Ioo (4 / 5 : ℝ) 1)
    (hfloor : 7 / 122 < 2 * (c - m * d) + m)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    0 < μ (S.universalNegativeRegion r p) := by
  by_contra hn
  have hnull : μ (S.universalNegativeRegion r p) = 0 :=
    le_antisymm (le_of_not_gt hn) zero_le
  have hnot := measure_eq_zero_iff_ae_notMem.mp hnull
  let U := S.universalPartnerCommonRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let A := S.originalAtomMass r
  let gamma := 2 * (c - m * d) + m
  let ell := -m
  let delta := 1 + m
  have hdelta : 0 < delta := by dsimp only [delta]; linarith only [hell.2]
  have hell0 : 0 < ell := by dsimp only [ell]; linarith only [hell.1]
  have hbeta : ∀ᵐ x ∂μ, x ∈ U → 0 ≤ S.rootChargeRow r x := by
    filter_upwards [hnot] with x hx hxU
    exact le_of_not_gt (fun h => hx ⟨hxU, h⟩)
  have hbad := R.universal_upperE2_bad_region_pos r p hpair hW hd hgap hr hN
    hA hAhi hell hmargin
  have hu := R.universal_partner_source_mass_margin r p hpair hW hd hgap hell.2 hr hN
  have hu' : μ.real U < 1 - 2 * A := by
    have h := hu.2
    change μ.real U + _ < 1 - 2 * A at h
    linarith only [h, hu.1]
  have hell' : -m ∈ Ioo (1 / 2 : ℝ) 1 :=
    ⟨by linarith only [hell.1], hell.2⟩
  have hAhalf : S.originalAtomMass r ≤ 1 / 2 := by linarith only [hAhi]
  have hrow := (ae_restrict_iff' (S.measurableSet_universalUpperE2BadRegion r p d c)).mp
    (P.ae_empty_sat_corner_bad_row S r p hpair hW hd hgap hN hA hAhalf hell' hmargin)
  have hsubset := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell' hmargin
  have hGint : Integrable (fun q : Ω × Ω => adjacencyKernel W q.1 q.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  obtain ⟨x, hx, hrx, hb, hs, hg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hbad.ne'
    (ae_restrict_of_ae (hrow.and (hbeta.and (hsubset.and hGint.prod_right_ae))))
  have hxU : x ∈ U := hs hx
  have hmissing : 0 ≤ 1 - ∫ z, adjacencyKernel W x z ∂μ := by
    have h := integral_mono_ae hg (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun z => (adjacency_moment_mem W (x, z)).2))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_nonneg] using h
  have hproduct := mul_nonpos_of_nonneg_of_nonpos (hb hxU)
    (show 2 * A + μ.real U - 1 ≤ 0 by linarith only [hu'])
  have hraw := hrx hx
  have hcap : 3 * gamma ≤ delta * (1 - μ.real U) := by
    have hraw' : gamma + ell * (1 - ∫ z, adjacencyKernel W x z ∂μ) ≤
        S.rootChargeRow r x * (2 * A + μ.real U - 1) +
          1 - m - 4 * (c - m * d) - delta * μ.real U := by
      dsimp only [gamma, ell, A, U, delta]
      nlinarith only [hraw]
    have hm := mul_nonneg hell0.le hmissing
    dsimp only [gamma, delta, ell] at *
    linarith only [hraw', hproduct, hm]
  have hUbound : ∀ᵐ x ∂μ.restrict U, p.val x ≤ ell := by
    filter_upwards [ae_restrict_of_ae hbeta,
      ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap),
      S.ae_partner_row_pos_on_universalCommon r p,
      ae_restrict_of_ae (S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN),
      ae_restrict_mem (S.measurableSet_universalPartnerCommonRegion r p)]
      with y hb hy hp hscore hyU
    have hyr : S.ρ y ≠ r.val := fun h => hyU (Or.inl (Or.inl h))
    have hs := hscore hyr (S.common_region_mem_rootNeighborhood r p hyU)
    rw [ite_eq_left hp] at hy
    change 1 - S.rootChargeRow p y = _ at hy
    dsimp only [ell]
    linarith only [hy, hs, hb hyU]
  have hint := integral_mono_ae
    ((Lp.memLp p.val).integrable (by norm_num)).integrableOn
    (integrable_const ell) hUbound
  rw [S.universal_partner_common_row_integral r p hpair hW,
    setIntegral_const, smul_eq_mul] at hint
  have hstationary := mul_le_mul_of_nonneg_left hint hdelta.le
  have hcapscaled := mul_le_mul_of_nonneg_left hcap hell0.le
  have hpaid : gamma * (1 + 2 * ell) ≤ (1 - ell ^ 2) * A := by
    dsimp only [delta, ell, gamma, A] at *
    nlinarith only [hstationary, hcapscaled]
  have hfloorprod := mul_pos (show 0 < gamma - 7 / 122 by exact sub_pos.mpr hfloor)
    (show 0 < 1 + 2 * ell by linarith only [hell0])
  have hlow : (91 / 610 : ℝ) < gamma * (1 + 2 * ell) := by
    have he : 4 / 5 < ell := hell.1
    nlinarith only [hfloorprod, he]
  have hell2 : (16 / 25 : ℝ) < ell ^ 2 := by
    have h := mul_pos (show 0 < ell - 4 / 5 by exact sub_pos.mpr hell.1)
      (show 0 < ell + 4 / 5 by linarith only [hell0])
    nlinarith only [h]
  have hellsq : ell ^ 2 < 1 := by
    have h := mul_pos (show 0 < 1 - ell by exact sub_pos.mpr hell.2)
      (show 0 < 1 + ell by linarith only [hell0])
    nlinarith only [h]
  have hmassprod := mul_pos (show 0 < 2 / 5 - A by exact sub_pos.mpr hAhi)
    (show 0 < 1 - ell ^ 2 by linarith only [hellsq])
  nlinarith only [hpaid, hlow, hell2, hmassprod]

/-- The actual bad-vertex degree and signed row give one common cap on
the original missing mass of each negative vertex. -/
theorem UniversalPhysicalPrimal.ae_universal_upperE2_negative_missing_le
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hu : μ.real (S.universalPartnerCommonRegion r p) < 1 - 2 * S.originalAtomMass r) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      1 - (∫ z, adjacencyKernel W x z ∂μ) ≤
        min (1 - 3 * S.originalAtomMass r + S.originalAtomMass p)
          ((1 - μ.real (S.universalPartnerCommonRegion r p) +
              2 * m * S.originalAtomMass r - 3 * (2 * (c - m * d) + m)) / (-m)) := by
  have hB := S.measurableSet_universalUpperE2BadRegion r p d c
  have hsub := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (by linarith only [hA]) hmargin (by linarith only [hell.2])
  have hrow := (ae_restrict_iff' hB).mp
    (P.ae_empty_sat_corner_bad_row S r p hpair hW hd hgap hN hA hAhalf hell hmargin)
  have hdegree := (ae_restrict_iff' hB).mp
    (P.ae_universalUpperE2Bad_originalDegree_ge S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hell0 : 0 < -m := by linarith only [hell.1]
  filter_upwards [ae_restrict_of_ae hrow, ae_restrict_of_ae hdegree,
    S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN,
    ae_restrict_mem (S.measurableSet_universalNegativeRegion r p)] with x hr hdg hx hxB
  have hxBad := hsub hxB
  refine le_min (by linarith only [hdg hxBad]) ?_
  apply (le_div_iff₀ hell0).mpr
  have hproduct := mul_le_mul_of_nonneg_right hx.2.le
    (show 0 ≤ 1 - 2 * S.originalAtomMass r -
      μ.real (S.universalPartnerCommonRegion r p) by linarith only [hu])
  nlinarith only [hr hxBad, hproduct]

end Erdos1017.CappedModel.SelectedHighLowStructure

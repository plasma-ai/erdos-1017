module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTwoHeadClique
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPrice
public import Erdos1017.Exclusions.Corner.SelectedCornerZeroBody
public import Erdos1017.Exclusions.Common.SelectedEmptySource
public import Erdos1017.Certificates.EmptySatCorner.EmptySatCornerScalar
public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalTrace

/-!
# Bad region of the empty-source saturated corner

The stationary head rows give a shared budget, the bad-vertex row is paid by the
head charges, triangle and clique tests, a positive corner body makes the bad
region positive, and that region contains negative universal charge with a
strict common-mass cap.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem corner_four_region_integral (S : SelectedHighLowStructure W m)
    (r p : S.I) (hrp : r ≠ p) (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = (∫ x in {x | S.ρ x = r.val}, f x ∂μ) +
      (∫ x in {x | S.ρ x = p.val}, f x ∂μ) +
      (∫ x in S.universalPartnerHoleRegion r p, f x ∂μ) +
      (∫ x in S.universalPartnerCommonRegion r p, f x ∂μ) := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hIP : Disjoint I P := disjoint_left.mpr
    (fun _ hx hy => hrp (Subtype.ext (hx.symm.trans hy)))
  have hIPH : Disjoint (I ∪ P) H := disjoint_left.mpr (fun _ hx hy => hy (Or.inl hx))
  have hIPHU : Disjoint (I ∪ P ∪ H) U := disjoint_left.mpr (fun _ hx hy => hy hx)
  have hwhole : I ∪ P ∪ H ∪ U = univ := S.universalPartner_regions_partition r p
  rw [← setIntegral_univ (f := f), ← hwhole,
    setIntegral_union hIPHU hU hf.integrableOn hf.integrableOn,
    setIntegral_union hIPH hH hf.integrableOn hf.integrableOn,
    setIntegral_union hIP hP hf.integrableOn hf.integrableOn]

private theorem corner_root_charge_shifted (S : SelectedHighLowStructure W m)
    (r : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y =
      r.val y + m * (if 0 < r.val y then 1 else 0) := by
  let I := {x | S.ρ x = r.val}
  have hrows : ∀ᵐ x ∂μ.restrict I, chargeKernel W x =ᵐ[μ]
      fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hpair : ∀ᵐ q ∂μ.prod μ, q.1 ∈ I →
      PhysicalRepresentative.charge W m q.1 q.2 = S.rootChargeRow r q.2 ∧
      PhysicalRepresentative.charge W m q.1 q.2 = chargeKernel W q.1 q.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
      with q hr he hI
    exact ⟨hr hI, he⟩
  obtain ⟨x, hx, hr, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (hrows.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)))
  filter_upwards [hr, hp] with y hy hh
  exact (hh hx).1.symm.trans ((hh hx).2.trans hy)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem corner_integrable_root_charge (S : SelectedHighLowStructure W m)
    (r : S.I) : Integrable (S.rootChargeRow r) μ := by
  apply Integrable.of_bound (S.measurable_rootChargeRow r).aestronglyMeasurable 3
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(S.rootChargeRow_mem_Icc r x).1,
      (S.rootChargeRow_mem_Icc r x).2.trans (by norm_num)⟩)

/-- The two original stationary head rows give an exact shared budget.
The common-neighbor charge remains signed and is paid on the same law. -/
theorem empty_sat_corner_shared_budget (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    (∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ) +
      (∫ x in S.universalPartnerCommonRegion r p,
        -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ) =
      1 - m - 4 * (c - m * d) -
        (1 + m) * μ.real (S.universalPartnerCommonRegion r p) := by
  let f : Ω → ℝ := fun x => 1 - m - r.val x - p.val x
  have hf : Integrable f μ := ((integrable_const (1 - m)).sub
    ((Lp.memLp r.val).integrable (by norm_num))).sub
      ((Lp.memLp p.val).integrable (by norm_num))
  have hpart := S.corner_four_region_integral r p hpair.1 f hf
  have hheadr := (S.root_row_zero_on_fiber r).and hpair.symm.row_on_other
  have hheadp := (S.root_row_zero_on_fiber p).and hpair.row_on_other
  have hzeroR : (∫ x in {x | S.ρ x = r.val}, f x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hheadr] with x hx
    change f x = 0
    dsimp only [f]
    linarith only [hx.1, hx.2]
  have hzeroP : (∫ x in {x | S.ρ x = p.val}, f x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hheadp] with x hx
    change f x = 0
    dsimp only [f]
    linarith only [hx.1, hx.2]
  have hhole : (∫ x in S.universalPartnerHoleRegion r p, f x ∂μ) =
      ∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ := by
    apply integral_congr_ae
    exact (S.ae_universalRootDeficit_eq_score_on_hole r p hW hd hgap hN).mono
      (fun _ hx => hx.symm)
  have hU := S.measurableSet_universalPartnerCommonRegion r p
  have hscore : f =ᵐ[μ.restrict (S.universalPartnerCommonRegion r p)]
      fun x => (1 + m) - (S.rootChargeRow r x + S.rootChargeRow p x) := by
    filter_upwards [ae_restrict_of_ae (S.corner_root_charge_shifted r hW hd hgap),
      ae_restrict_of_ae (S.corner_root_charge_shifted p hW hd hgap),
      ae_restrict_of_ae (S.ae_universal_row_pos_on_outside r hW hd hgap hN),
      S.ae_partner_row_pos_on_universalCommon r p, ae_restrict_mem hU]
      with x hr hp hpos hppos hx
    have hnotr : S.ρ x ≠ r.val := fun h => hx (Or.inl (Or.inl h))
    rw [hr, hp, ite_eq_left (hpos hnotr), ite_eq_left hppos]
    dsimp only [f]
    ring
  have hcommon : (∫ x in S.universalPartnerCommonRegion r p, f x ∂μ) =
      (1 + m) * μ.real (S.universalPartnerCommonRegion r p) +
        ∫ x in S.universalPartnerCommonRegion r p,
          -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ := by
    have hsub := integral_sub (μ := μ.restrict (S.universalPartnerCommonRegion r p))
      (integrable_const (1 + m)) ((S.corner_integrable_root_charge r).add
        (S.corner_integrable_root_charge p)).integrableOn
    simp only [Pi.add_apply] at hsub
    rw [integral_congr_ae hscore, hsub, integral_neg, setIntegral_const, smul_eq_mul]
    ring
  have hwhole := S.integral_universal_pair_score r p hW
  change (∫ x, f x ∂μ) = _ at hwhole
  rw [hwhole, hzeroR, hzeroP, hhole, hcommon] at hpart
  linarith only [hpart]

variable {c : ℝ}

/-- The original bad-vertex row is paid by its actual head charges,
the join of H with the bad region, the universal triangle and the two-head clique test.
No independent conditional body law replaces the old charge. -/
theorem UniversalPhysicalPrimal.ae_empty_sat_corner_bad_row
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalUpperE2BadRegion r p d c),
      2 * (c - m * d) + m - m * (1 - ∫ z, adjacencyKernel W x z ∂μ) ≤
        S.rootChargeRow r x *
          (2 * S.originalAtomMass r + μ.real (S.universalPartnerCommonRegion r p) - 1) +
        1 - m - 4 * (c - m * d) -
          (1 + m) * μ.real (S.universalPartnerCommonRegion r p) := by
  let I := {x | S.ρ x = r.val}
  let Ip := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let sigma : Ω → ℝ := fun x => -(S.rootChargeRow r x + S.rootChargeRow p x)
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hIp : MeasurableSet Ip := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hsigma : Integrable sigma μ :=
    ((S.corner_integrable_root_charge r).add (S.corner_integrable_root_charge p)).neg
  have hYint : Integrable (fun q : Ω × Ω => chargeKernel W q.1 q.2) (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hGint : Integrable (fun q : Ω × Ω => adjacencyKernel W q.1 q.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  have hroot (a : S.I) : ∀ᵐ q ∂μ.prod μ, S.ρ q.2 = a.val →
      chargeKernel W q.1 q.2 = S.rootChargeRow a q.1 := by
    have hr : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = a.val →
        chargeKernel W q.1 q.2 = S.rootChargeRow a q.2 := by
      filter_upwards [S.ae_root_charge a hW hd hgap,
        PhysicalRepresentative.charge_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support] with q hr he hx
      exact he.symm.trans (hr hx)
    filter_upwards [(Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hr,
      chargeKernel_symm W] with q hq hs hx
    exact hs.trans (hq hx)
  have hsubset := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin
  have hpartner := (ae_restrict_iff' hB).mp
    (P.ae_universalUpperE2Bad_partner_charge S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hjoined := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (P.ae_universalUpperE2_hole_bad_join S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have htriangle := S.ae_universal_deficit_triangle r hW hd hgap
    (S.neutral_atom_adjacency r hW hd hgap hN)
  have hboundH : ∀ᵐ q ∂μ.prod μ, q.1 ∈ B → q.2 ∈ H →
      chargeKernel W q.1 q.2 ≤ S.universalRootDeficit r q.2 - S.rootChargeRow r q.1 := by
    filter_upwards [hjoined, htriangle, adjacencyKernel_symm W] with q hj ht hs hx hy
    have hxr : S.ρ q.1 ≠ r.val := fun h => hx.1 (Or.inl h)
    have hyr : S.ρ q.2 ≠ r.val := fun h => hy (Or.inl (Or.inl h))
    have hG : adjacencyKernel W q.1 q.2 = 1 := hs.trans (hj hy hx)
    have h := ht hxr hyr
    rw [hG] at h
    dsimp only [universalRootDeficit] at *
    linarith only [h]
  have hboundU : ∀ᵐ q ∂μ.prod μ, q.1 ∈ B → q.2 ∈ U →
      chargeKernel W q.1 q.2 ≤ sigma q.2 := by
    filter_upwards [S.ae_universal_saturated_common_charge_le r p hpair hW hd hgap hN,
      Measure.quasiMeasurePreserving_fst.ae hsubset,
      Measure.quasiMeasurePreserving_fst.ae hpartner] with q hq hs hp hx hy
    have hxU := hs hx
    have hn (x : Ω) (hx : x ∈ U) : x ∈ S.rootNeighborhood p := by
      by_contra hnot
      apply hx
      right
      intro h
      rcases h with (h | h) | h
      · exact hx (Or.inl (Or.inl h))
      · exact hx (Or.inl (Or.inr h))
      · exact hnot h
    have hxr : S.ρ q.1 ≠ r.val := fun h => hx.1 (Or.inl h)
    have hyr : S.ρ q.2 ≠ r.val := fun h => hy (Or.inl (Or.inl h))
    have hb := hq hxr hyr (hn q.1 hxU) (hn q.2 hy)
    have hp' := hp hx
    dsimp only [sigma]
    linarith only [hb, hp']
  have hshared := S.empty_sat_corner_shared_budget r p hpair hW hd hgap hN
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hcoeff : S.originalAtomMass r - S.originalAtomMass p - μ.real H =
      2 * S.originalAtomMass r + μ.real U - 1 := by
    change S.originalAtomMass r + S.originalAtomMass p + μ.real H + μ.real U = 1 at hmass
    linarith only [hmass]
  filter_upwards [ae_restrict_of_ae hW.stationary,
    ae_restrict_of_ae hYint.prod_right_ae, ae_restrict_of_ae hGint.prod_right_ae,
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod (hroot r)),
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod (hroot p)),
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hboundH),
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hboundU),
    ae_restrict_of_ae hpartner, ae_restrict_mem hB]
    with x hflat hYx hGx hr hp hHx hUx hpx hx
  have hIr : (∫ z in I, chargeKernel W x z ∂μ) =
      S.originalAtomMass r * S.rootChargeRow r x := by
    rw [integral_congr_ae (by
      filter_upwards [ae_restrict_of_ae hr, ae_restrict_mem hI] with z hz hIz
      exact hz hIz), setIntegral_const, smul_eq_mul]
    rfl
  have hIp' : (∫ z in Ip, chargeKernel W x z ∂μ) =
      -S.originalAtomMass p * S.rootChargeRow r x := by
    rw [integral_congr_ae (by
      filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem hIp] with z hz hIz
      exact (hz hIz).trans (hpx hx)), setIntegral_const, smul_eq_mul]
    change μ.real Ip * -S.rootChargeRow r x = -μ.real Ip * S.rootChargeRow r x
    ring
  have hHI : (∫ z in H, chargeKernel W x z ∂μ) ≤
      (∫ z in H, S.universalRootDeficit r z ∂μ) - μ.real H * S.rootChargeRow r x := by
    have hmono := integral_mono_ae hYx.integrableOn
      ((S.integrable_universalRootDeficit r).sub
        (integrable_const (S.rootChargeRow r x))).integrableOn
      (by filter_upwards [ae_restrict_of_ae hHx, ae_restrict_mem hH] with z hz hHz
          exact hz hx hHz)
    simp only [Pi.sub_apply] at hmono
    rw [integral_sub (S.integrable_universalRootDeficit r).integrableOn
      (integrable_const (S.rootChargeRow r x)), setIntegral_const, smul_eq_mul] at hmono
    exact hmono
  have hUI : (∫ z in U, chargeKernel W x z ∂μ) ≤ ∫ z in U, sigma z ∂μ :=
    integral_mono_ae hYx.integrableOn hsigma.integrableOn (by
      filter_upwards [ae_restrict_of_ae hUx, ae_restrict_mem hU] with z hz hUz
      exact hz hx hUz)
  have hpart := S.corner_four_region_integral r p hpair.1 (chargeKernel W x) hYx
  rw [hIr, hIp'] at hpart
  have hshift : (fun z => shiftedKernel W m x z) =
      fun z => chargeKernel W x z - m * adjacencyKernel W x z := by
    funext z
    exact shiftedMoment_eq W m (x, z)
  rw [hshift, integral_sub hYx (hGx.const_mul m), integral_const_mul] at hflat
  have hcoeff' := congrArg (fun a => a * S.rootChargeRow r x) hcoeff
  change (∫ z in H, S.universalRootDeficit r z ∂μ) + (∫ z in U, sigma z ∂μ) = _ at hshared
  change _ ≤ S.rootChargeRow r x * (2 * S.originalAtomMass r + μ.real U - 1) +
    1 - m - 4 * (c - m * d) - (1 + m) * μ.real U
  nlinarith only [hflat, hpart, hHI, hUI, hshared, hcoeff']

/-- A positive negative-star region forces the strict common-mass cap
from an actual original row. No chosen exceptional vertex is a premise. -/
theorem UniversalPhysicalPrimal.negative_common_mass_lt
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hnegative : 0 < μ (S.universalNegativeRegion r p)) :
    μ.real (S.universalPartnerCommonRegion r p) <
      1 + 2 * m * S.originalAtomMass r - 3 * (2 * (c - m * d) + m) := by
  have hdelta : 0 < 1 + m := by linarith only [hell.2]
  have hsubset := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (show 0 < S.originalAtomMass r by linarith only [hA]) hmargin hdelta.le
  have hrow := (ae_restrict_iff'
    (S.measurableSet_universalUpperE2BadRegion r p d c)).mp
    (P.ae_empty_sat_corner_bad_row S r p hpair hW hd hgap hN hA hAhalf hell hmargin)
  have hGint : Integrable (fun q : Ω × Ω => adjacencyKernel W q.1 q.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  obtain ⟨x, hx, hrowx, hroot, hpos, hGx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hnegative.ne' (ae_restrict_of_ae
      (hrow.and ((S.corner_root_charge_shifted r hW hd hgap).and
        ((S.ae_universal_row_pos_on_outside r hW hd hgap hN).and hGint.prod_right_ae))))
  have hxr : S.ρ x ≠ r.val := fun h => hx.1 (Or.inl (Or.inl h))
  have hrootpos := hpos hxr
  rw [ite_eq_left hrootpos] at hroot
  have hmissing : 0 ≤ 1 - ∫ z, adjacencyKernel W x z ∂μ := by
    have h := integral_mono_ae hGx (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun z => (adjacency_moment_mem W (x, z)).2))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    linarith only [h]
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  have hD : (1 + m) * D = (1 + m) - 2 * (2 * (c - m * d) + m) := by
    dsimp only [D]
    rw [mul_div_cancel₀ _ hdelta.ne']
    ring
  have hraw := hrowx (hsubset hx)
  have hraw' : 2 * (c - m * d) + m + (-m) *
      (1 - ∫ z, adjacencyKernel W x z ∂μ) ≤
        (-S.rootChargeRow r x) *
          (1 - 2 * S.originalAtomMass r - μ.real (S.universalPartnerCommonRegion r p)) +
        (1 + m) * (D - μ.real (S.universalPartnerCommonRegion r p)) := by
    nlinarith only [hraw, hD]
  have hxneg : S.rootChargeRow r x < 0 := hx.2
  have hcap := EmptySatCorner.negative_bad_row_mass_lt hdelta
    (show 0 ≤ -m by linarith only [hell.1]) (by ring : (1 + m) + (-m) = 1)
    (neg_nonneg.mpr hxneg.le)
    (show -S.rootChargeRow r x < -m by linarith only [hroot, hrootpos])
    hmissing hmargin hD hraw'
  have hnonnegative := mul_nonneg (show 0 ≤ -m by linarith only [hell.1]) hmissing
  nlinarith only [hcap, hnonnegative]

private theorem corner_body_cap_of_bad_null
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hthreshold : 29 / 100 ≤ 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (hnull : μ (S.universalUpperE2BadRegion r p d c) = 0) :
    ∀ᵐ q ∂μ.prod μ,
      IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} q.1 q.2 ≤ 21 / 50 := by
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hnotB := measure_eq_zero_iff_ae_notMem.mp hnull
  have hbeta : ∀ᵐ x ∂μ, S.ρ x ≠ r.val → S.ρ x ≠ p.val →
      29 / 100 ≤ S.rootChargeRow r x := by
    filter_upwards [hnotB] with x hx hr hp
    apply hthreshold.trans
    by_contra hn
    exact hx ⟨fun h => h.elim hr hp, lt_of_not_ge hn⟩
  have hpzero := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp
    (S.root_row_zero_on_fiber p)
  have hhole := (ae_restrict_iff'
    (S.measurableSet_universalPartnerHoleRegion r p)).mp
      (S.ae_partner_row_zero_on_universalHole r p hW)
  have hqnonpos : ∀ᵐ x ∂μ, S.ρ x ≠ r.val → S.rootChargeRow p x ≤ 0 := by
    filter_upwards [hbeta, S.corner_root_charge_shifted p hW hd hgap,
      hpzero, hhole, S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN]
      with x hb hq hp0 hH hscore hxr
    by_cases hxp : S.ρ x = p.val
    · rw [hq, hp0 hxp]
      simp
    by_cases hxN : x ∈ S.rootNeighborhood p
    · have hs := hscore hxr hxN
      linarith only [hs, hb hxr hxp]
    · have hxH : x ∈ H := by
        intro h
        rcases h with (h | h) | h
        · exact hxr h
        · exact hxp h
        · exact hxN h
      rw [hq, hH hxH]
      simp
  have hroot : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = p.val →
      chargeKernel W q.1 q.2 = S.rootChargeRow p q.2 := by
    filter_upwards [S.ae_root_charge p hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
      with q hp he hx
    exact he.symm.trans (hp hx)
  have hrootSwap :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot
  have htri := S.ae_universal_deficit_triangle r hW hd hgap
    (S.neutral_atom_adjacency r hW hd hgap hN)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbeta,
    Measure.quasiMeasurePreserving_snd.ae hbeta,
    Measure.quasiMeasurePreserving_fst.ae hqnonpos,
    Measure.quasiMeasurePreserving_snd.ae hqnonpos,
    hroot, hrootSwap, chargeKernel_symm W, htri,
    PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
    with q hb1 hb2 hq1 hq2 hroot hrootSwap hsym ht he
  by_cases h1 : S.ρ q.1 = r.val
  · simp only [IndependentAtomCopy.positiveBody, mem_ofPred_eq, h1, not_true_eq_false,
      false_and, ite_false]
    norm_num
  by_cases h2 : S.ρ q.2 = r.val
  · simp only [IndependentAtomCopy.positiveBody, mem_ofPred_eq, h2, not_true_eq_false,
      and_false, ite_false]
    norm_num
  have hraw : chargeKernel W q.1 q.2 ≤ 21 / 50 := by
    by_cases hp1 : S.ρ q.1 = p.val
    · exact (hroot hp1).le.trans ((hq2 h2).trans (by norm_num))
    by_cases hp2 : S.ρ q.2 = p.val
    · exact (hsym.trans (hrootSwap hp2)).le.trans ((hq1 h1).trans (by norm_num))
    have hb1' := hb1 h1 hp1
    have hb2' := hb2 h2 hp2
    have h := ht h1 h2
    have hG0 := (adjacency_moment_mem W q).1
    have hG1 := (adjacency_moment_mem W q).2
    change 0 ≤ adjacencyKernel W q.1 q.2 at hG0
    change adjacencyKernel W q.1 q.2 ≤ 1 at hG1
    have hp := mul_nonneg hG0
      (show 0 ≤ S.rootChargeRow r q.1 + S.rootChargeRow r q.2 - 29 / 50 by
        linarith only [hb1', hb2'])
    dsimp only [universalRootDeficit] at h
    nlinarith only [h, hp, hG1]
  simp only [IndependentAtomCopy.positiveBody, mem_ofPred_eq, h1, h2,
    not_false_eq_true, and_self, ite_true]
  rw [he]
  exact max_le hraw (by norm_num)

private theorem corner_trace_of_constant_cap
    (S : SelectedHighLowStructure W m) (r : S.I) {d C : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hC : 0 < C)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val})
    (hcap : ∀ᵐ q ∂μ.prod μ,
      IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} q.1 q.2 ≤ C) :
    (S.originalAtomMass r + (2 * (c - m * d) + m) / C) ^ 2 ≤
      2 * (1 - 2 * d - (S.originalAtomMass r) ^ 2) := by
  let Y := PhysicalRepresentative.charge W m
  let G := PhysicalRepresentative.adjacency W m
  let I := {x | S.ρ x = r.val}
  let K := IndependentAtomCopy.positiveBody Y I
  let J := IndependentAtomCopy.missingBody G I
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hphysical : 0 < ∫ q : Ω × Ω, (K q.1 q.2) ^ 2 ∂μ.prod μ := by
    rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap I hI] at hpositive
    exact hpositive
  have hgamma := (hW.strict_gap_structure hd hgap).gamma_pos
  have horth : (∫ q : Ω × Ω, J q.1 q.2 * K q.1 q.2 ∂μ.prod μ) = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall (fun q => IndependentAtomCopy.missingBody_positiveBody_mul
      G Y I (PhysicalRepresentative.charge_zero_of_nonedge W m) q.1 q.2)
  have htrace := KernelOperator.copy_row_trace_bound_of_ae_cap K J
    (IndependentAtomCopy.measurable_positiveBody Y
      (PhysicalRepresentative.measurable_charge W m) I hI)
    (IndependentAtomCopy.measurable_missingBody G
      (PhysicalRepresentative.measurable_adjacency W m) I hI)
    (fun x y => (IndependentAtomCopy.positiveBody_mem Y I
      (fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2) x y).1)
    (fun x y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem G I x y).1]
      exact (IndependentAtomCopy.missingBody_mem G I x y).2)
    (IndependentAtomCopy.positiveBody_symm Y I (PhysicalRepresentative.charge_symm W m))
    (S.originalAtomMass r) (2 * (c - m * d) + m) C hC hgamma.le
    (add_nonneg measureReal_nonneg (div_nonneg hgamma.le hC.le)) hcap hphysical horth
    (S.ae_universal_positive_body_row r hW hd hgap hN)
  have hinventory := S.universal_missing_body_square_integral r hW hd hgap hN
  change (∫ q : Ω × Ω, (J q.1 q.2) ^ 2 ∂μ.prod μ) =
    1 - 2 * d - (S.originalAtomMass r) ^ 2 at hinventory
  rw [hinventory] at htrace
  exact htrace

/-- If the original corner body has positive energy, the entire bad
region has positive measure. The alternative gives an actual bounded
body charge and a sharper trace contradiction. -/
theorem corner_bad_region_pos_of_bounds
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 7 / 20 ≤ S.originalAtomMass r)
    (hgamma : 63 / 1000 < 2 * (c - m * d) + m)
    (hh : 1 - 2 * d < 467 / 2000)
    (hthreshold : 29 / 100 ≤ 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val}) :
    0 < μ (S.universalUpperE2BadRegion r p d c) := by
  by_contra hn
  have hz := le_antisymm (le_of_not_gt hn) zero_le
  have hcap := S.corner_body_cap_of_bad_null r p hpair hW hd hgap hN hthreshold hz
  have htrace := S.corner_trace_of_constant_cap r hW hd hgap hN
    (by norm_num : (0 : ℝ) < 21 / 50) hpositive hcap
  let A := S.originalAtomMass r
  let gamma := 2 * (c - m * d) + m
  have hsum : 1 / 2 < A + gamma / (21 / 50) := by
    dsimp only [A, gamma]
    norm_num
    linarith only [hA, hgamma]
  have hsum2 : (1 / 2 : ℝ) ^ 2 < (A + gamma / (21 / 50)) ^ 2 := by
    have hp := mul_pos (show 0 < A + gamma / (21 / 50) - 1 / 2 by linarith only [hsum])
      (show 0 < A + gamma / (21 / 50) + 1 / 2 by linarith only [hsum])
    nlinarith only [hp]
  have hA2 : (7 / 20 : ℝ) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hA 2
  change (A + gamma / (21 / 50)) ^ 2 ≤ 2 * (1 - 2 * d - A ^ 2) at htrace
  nlinarith only [htrace, hsum2, hA2, hh]

/-- A positive original bad region contains negative universal charge
under the sharp corner enclosure. All pointwise rows and head integrals
come from the same original primal and stationary model. -/
theorem UniversalPhysicalPrimal.corner_negative_region_pos_of_bad_pos
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhi : S.originalAtomMass r < 3 / 8)
    (hell : -m ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hfloor : 2 * (138261458236451 / 1116960975000000 : ℝ) -
      (-m) * (23243417 / 10 ^ 8) < 2 * (c - m * d) + m)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hbad : 0 < μ (S.universalUpperE2BadRegion r p d c)) :
    0 < μ (S.universalNegativeRegion r p) := by
  by_contra hn
  have hnull : μ (S.universalNegativeRegion r p) = 0 :=
    le_antisymm (le_of_not_gt hn) zero_le
  have hnot := measure_eq_zero_iff_ae_notMem.mp hnull
  let U := S.universalPartnerCommonRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let delta := 1 + m
  let gamma := 2 * (c - m * d) + m
  let A := S.originalAtomMass r
  have hdelta : 0 < delta := by dsimp only [delta]; linarith only [hell.2]
  have hbeta : ∀ᵐ x ∂μ, x ∈ U → 0 ≤ S.rootChargeRow r x := by
    filter_upwards [hnot] with x hx hU
    exact le_of_not_gt (fun h => hx ⟨hU, h⟩)
  have hell' : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hell.1, hell.2]
  have hAhalf : S.originalAtomMass r ≤ 1 / 2 := by linarith only [hAhi]
  have hrow := (ae_restrict_iff' (S.measurableSet_universalUpperE2BadRegion r p d c)).mp
    (P.ae_empty_sat_corner_bad_row S r p hpair hW hd hgap hN hA hAhalf hell' hmargin)
  have hsubset := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell' hmargin
  have hGint : Integrable (fun q : Ω × Ω => adjacencyKernel W q.1 q.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  obtain ⟨x, hx, hr, hb, hs, hg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hbad.ne'
    (ae_restrict_of_ae (hrow.and (hbeta.and (hsubset.and hGint.prod_right_ae))))
  have hxU : x ∈ U := hs hx
  have hmissing : 0 ≤ 1 - ∫ z, adjacencyKernel W x z ∂μ := by
    have h := integral_mono_ae hg (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun z => (adjacency_moment_mem W (x, z)).2))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_nonneg] using h
  have hthreshold : A * (S.rootChargeRow r x + delta) < 3 * gamma := by
    have h := hx.2
    have hA0 : 0 < A := by dsimp only [A]; linarith only [hA]
    have hdiv : S.rootChargeRow r x + delta < 3 * gamma / A := by
      change S.rootChargeRow r x < 3 * gamma / A - delta at h
      linarith only [h]
    have hscaled := (lt_div_iff₀ hA0).mp hdiv
    nlinarith only [hscaled]
  let D := (1 - m - 4 * (c - m * d)) / delta
  have hD : delta * D = delta - 2 * gamma := by
    dsimp only [D]
    rw [mul_div_cancel₀ _ hdelta.ne']
    dsimp only [delta, gamma]
    ring
  have hraw : gamma + (-m) * (1 - ∫ z, adjacencyKernel W x z ∂μ) ≤
      S.rootChargeRow r x * (2 * A + μ.real U - 1) + delta * (D - μ.real U) := by
    have h := hr hx
    change _ ≤ S.rootChargeRow r x * (2 * A + μ.real U - 1) +
      1 - m - 4 * (c - m * d) - delta * μ.real U at h
    dsimp only [gamma]
    nlinarith only [h, hD]
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hcap : delta * μ.real U ≤ delta - 3 * gamma :=
    EmptySatCorner.nonnegative_bad_row_mass_cap hdelta
      (show 0 ≤ -m by linarith only [hell.1]) (hb hxU) hmissing
      (show μ.real U ≤ 1 - A by
        change A + S.originalAtomMass p + μ.real (S.universalPartnerHoleRegion r p) +
          μ.real U = 1 at hmass
        have hbp : 0 ≤ S.originalAtomMass p := measureReal_nonneg
        linarith only [hmass, hbp,
          measureReal_nonneg (μ := μ) (s := S.universalPartnerHoleRegion r p)])
      hthreshold hmargin hD hraw
  have hU := S.measurableSet_universalPartnerCommonRegion r p
  have hpint : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hUbound : ∀ᵐ x ∂μ.restrict U, p.val x ≤ -m := by
    filter_upwards [ae_restrict_of_ae hbeta,
      ae_restrict_of_ae (S.corner_root_charge_shifted p hW hd hgap),
      S.ae_partner_row_pos_on_universalCommon r p,
      ae_restrict_of_ae (S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN),
      ae_restrict_mem hU] with y hb hy hp hscore hyU
    have hyr : S.ρ y ≠ r.val := fun h => hyU (Or.inl (Or.inl h))
    have hyN : y ∈ S.rootNeighborhood p := by
      change S.ρ y ≠ p.val ∧ 0 < p.val y
      exact ⟨fun h => hyU (Or.inl (Or.inr h)), hp⟩
    have hs := hscore hyr hyN
    rw [ite_eq_left hp] at hy
    linarith only [hy, hs, hb hyU]
  have hUint : (∫ x in U, p.val x ∂μ) ≤ (-m) * μ.real U := by
    have h := integral_mono_ae hpint.integrableOn (integrable_const (-m)) hUbound
    rw [setIntegral_const, smul_eq_mul] at h
    simpa only [mul_comm] using h
  have hIr : (∫ x in {x | S.ρ x = r.val}, p.val x ∂μ) = (1 - m) * A := by
    rw [integral_congr_ae hpair.symm.row_on_other, setIntegral_const, smul_eq_mul]
    dsimp only [A, originalAtomMass]
    ring
  have hIp : (∫ x in {x | S.ρ x = p.val}, p.val x ∂μ) = 0 := by
    rw [integral_congr_ae (S.root_row_zero_on_fiber p)]
    simp
  have hH : (∫ x in S.universalPartnerHoleRegion r p, p.val x ∂μ) = 0 :=
    integral_eq_zero_of_ae (S.ae_partner_row_zero_on_universalHole r p hW)
  have hpart := S.corner_four_region_integral r p hpair.1 (p.val : Ω → ℝ) hpint
  rw [S.row_integral_of_stationary p hW, hIr, hIp, hH] at hpart
  change 2 * (c - m * d) = (1 - m) * A + 0 + 0 + ∫ x in U, p.val x ∂μ at hpart
  have hpartbound : 2 * (c - m * d) ≤ (1 - m) * A + (-m) * μ.real U := by
    linarith only [hpart, hUint]
  have hpartscaled := mul_le_mul_of_nonneg_left hpartbound hdelta.le
  have hcapscaled := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ -m by linarith only [hell.1])
  have hratio := EmptySatCorner.corner_negative_ratio hell hfloor
  have hAprod := mul_pos (sub_pos.mpr hAhi)
    (mul_pos hdelta (show 0 < 1 - m by linarith only [hell.1]))
  dsimp only [delta, gamma, A] at *
  nlinarith only [hpart, hpartscaled, hcapscaled, hratio, hAprod]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual empty-source saturated corner supplies its original
negative-star region and strict common-mass cap on one fixed tight primal.
No bad-region, body, peak or row-bound certificate is an input. -/
theorem ReverseRecovery.empty_sat_corner_bad_region
    {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery) (r p : S.I)
    (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (P : S.UniversalPhysicalPrimal r c) {d : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) (hstrip : 21 / 100 < 1 + m) :
    let A := S.originalAtomMass r
    let gamma := 2 * (c - m * d) + m
    7 / 20 < A ∧ A < 3 / 8 ∧ 2 * A * (1 + m) < 3 * gamma ∧
      0 < μ (S.universalNegativeRegion r p) ∧
      μ.real (S.universalPartnerCommonRegion r p) < 1 + 2 * m * A - 3 * gamma := by
  let A := S.originalAtomMass r
  let gamma := 2 * (c - m * d) + m
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  have hnonnegative := bodyPositiveEnergy_nonnegative W {x | S.ρ x = r.val}
  have hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} := by
    apply lt_of_le_of_ne hnonnegative
    intro hz
    exact S.no_corner_zero_body r hW hd hgap he heq hglobal hz.symm
  have hphysical := hpositive
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap {x | S.ρ x = r.val}
    (S.hfibers r.val r.property).1] at hphysical
  have htrace := S.universal_positive_body_trace r hW hd hgap hN hphysical
  obtain ⟨hell, hc, hh, hfloor⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hcA := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  change c ≤ A ^ 2 at hcA
  change 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 2 * (1 - 2 * d) at htrace
  obtain ⟨hAlo, hAhi, hmargin, hstripbounds⟩ := EmptySatCorner.saturated_initial_guards
    hell hc hh (show 0 ≤ A from measureReal_nonneg) hcA hfloor htrace
  have hstrip' : 21 / 100 < 1 - (-m) := by linarith only [hstrip]
  obtain ⟨hgamma, hthreshold⟩ := hstripbounds hstrip'
  have hmargin' : 2 * A * (1 + m) < 3 * gamma := by
    simpa only [sub_neg_eq_add] using hmargin
  have hBad := S.corner_bad_region_pos_of_bounds r p hpair hW hd hgap hN hAlo.le
    hgamma (by linarith only [hh])
    (by simpa only [sub_neg_eq_add] using hthreshold.le) hpositive
  have hA : 1 / 3 < S.originalAtomMass r := by linarith only [hAlo]
  have hnegative := P.corner_negative_region_pos_of_bad_pos S r p hpair hW hd hgap hN
    hA hAhi hell hfloor hmargin' hBad
  have hell' : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hell.1, hell.2]
  have hcommon := P.negative_common_mass_lt S r p hpair hW hd hgap hN hA
    (by linarith only [hAhi]) hell' hmargin' hnegative
  exact ⟨hAlo, hAhi, hmargin', hnegative, hcommon⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

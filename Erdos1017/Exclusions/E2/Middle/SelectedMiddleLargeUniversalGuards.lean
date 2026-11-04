module

public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalE2SmallHead
public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalMiddleDeficitCases
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalGeometry
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalNegative
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2Joined

/-!
# Guards for the large universal branch

The checked smaller exits force the large universal domain and its guards
(`middle_large_universal_initial_guards`); the middle recovery has the same
saturated partner as its singleton head
(`middle_large_universal_partner_recovery`), and the bad-row argument needs only
a ratio bound in the middle branch.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c q : ℝ}

/-- The checked smaller exits force the actual large universal domain.
The physical primal, original neutral root, entire hole, mass and triangle
margin guards all belong to this same original contact. -/
theorem middle_large_universal_initial_guards (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1) :
    ∃ _P : S.UniversalPhysicalPrimal r c,
      157 / 1000 < q ∧ S.originalAtomMass r ∈ Ioo (1 / 3 : ℝ) (369 / 1000) ∧
      0 < μ (S.universalPartnerHoleRegion r p) ∧
      m = -LowerE2Scalar.multiplier q ∧ -m ∈ Ioo (4 / 5 : ℝ) 1 ∧
      LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m ∧
      S.originalAtomMass r ≤ (1 - m - 4 * (c - m * d)) / (1 + m) ∧
      (1 - m - 4 * (c - m * d)) / (1 + m) <
        9 * q / (2 * LowerE2Scalar.denominator q) ∧
      9 * q / (2 * LowerE2Scalar.denominator q) ≤ 45 / 122 ∧
      S.originalAtomMass p ∈ Ioo (0 : ℝ) (1 / 3) ∧
      S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r ∧
      0 ≤ μ.real (S.universalPartnerCommonRegion r p) ∧
      μ.real (S.universalPartnerCommonRegion r p) ≤
        1 - S.originalAtomMass r - S.originalAtomMass p ∧
      2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m) := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith only [hq.1], hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ Benchmark.e2_density_mem hq'
  have hcut : 157 / 1000 < q := by
    by_contra hn
    have hle := le_of_not_gt hn
    by_cases hsmall : q ≤ 7 / 50
    · exact S.no_universal_middle_small_parameter_saturated_peak r p hpair hW
        ⟨hq'.1, hsmall⟩ hdq hgap hglobal hpeak huniv
    · exact S.no_universal_middle_low_parameter_saturated_peak r p hpair hW
        ⟨(lt_of_not_ge hsmall).le, hle⟩ hdq hgap hglobal hpeak huniv
  have hthird : 1 / 3 < S.originalAtomMass r := by
    by_contra hn
    exact S.no_universal_e2_small_head_saturated_peak r p hpair hW hq' hdq hgap hglobal
      hpeak huniv (le_of_not_gt hn)
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq' hdq hgap hglobal
  have hell45 : 4 / 5 < -m := by
    rw [hm, neg_neg]
    unfold LowerE2Scalar.multiplier
    apply (lt_div_iff₀ (by linarith only [hq.1])).mpr
    linarith only [hq.2]
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  have hholes := S.universal_partner_hole_pos_e2 r p hpair hW hq' hdq hgap hglobal huniv
  have hAy := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap hell.2 hN hholes
  have hdelta : 0 < 1 + m := by linarith only [hell.2]
  have hdef : 1 - m - 4 * (c - m * d) <
      (1 + m) * (9 * q / (2 * LowerE2Scalar.denominator q)) := by
    have href := LowerE2Scalar.deficit_eq_gap_mul_ratio hq'.1.le
    rw [show LowerE2Scalar.multiplier q = -m by linarith only [hm]] at href
    nlinarith only [href, hgamma]
  have hyupper : (1 - m - 4 * (c - m * d)) / (1 + m) <
      9 * q / (2 * LowerE2Scalar.denominator q) :=
    (div_lt_iff₀ hdelta).mpr (by nlinarith only [hdef])
  have hratio : 9 * q / (2 * LowerE2Scalar.denominator q) ≤ 45 / 122 := by
    have hh := LowerE2Scalar.universal_ratio_monotoneOn_middle ⟨hq'.1.le, hq'.2⟩
      (by norm_num : (1 / 5 : ℝ) ∈ Icc (0 : ℝ) (1 / 5)) hq'.2
    norm_num [LowerE2Scalar.denominator] at hh
    simpa only [LowerE2Scalar.denominator] using hh
  have hAcap : S.originalAtomMass r < 369 / 1000 := by
    linarith only [hAy, hyupper, hratio]
  obtain ⟨v, _, hlower, hupper⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hholes.ne'
    ((S.ae_universalPartnerHole_degree_ge_twice_mass r p hpair hW hd hgap hell.2 hN).and
      (S.ae_universalPartnerHole_degree_le_one_sub_partner_mass r p hW hd hgap))
  have hb : S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r := by
    change 2 * S.originalAtomMass r ≤ ∫ z, adjacencyKernel W v z ∂μ at hlower
    linarith only [hlower, hupper]
  have hbpos : 0 < S.originalAtomMass p :=
    ENNReal.toReal_pos (S.hfibers p.val p.property).2.1.ne' (measure_ne_top μ _)
  have hbthird : S.originalAtomMass p < 1 / 3 := by linarith only [hb, hthird]
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hu : 0 ≤ μ.real (S.universalPartnerCommonRegion r p) := measureReal_nonneg
  have heta : 0 ≤ μ.real (S.universalPartnerHoleRegion r p) := measureReal_nonneg
  have hucap : μ.real (S.universalPartnerCommonRegion r p) ≤
      1 - S.originalAtomMass r - S.originalAtomMass p := by linarith only [hmass, heta]
  have hyid : (1 + m) * ((1 - m - 4 * (c - m * d)) / (1 + m)) =
      (1 + m) - 2 * (2 * (c - m * d) + m) := by
    rw [mul_div_cancel₀ _ hdelta.ne']
    ring
  have hscaled := mul_nonneg hdelta.le (sub_nonneg.mpr hAy)
  have hmargin : 2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m) := by
    have hycap : (1 - m - 4 * (c - m * d)) / (1 + m) < 369 / 1000 := by
      linarith only [hyupper, hratio]
    have hpos := mul_pos hdelta
      (show 0 < 3 - 7 * ((1 - m - 4 * (c - m * d)) / (1 + m)) by
        linarith only [hycap])
    nlinarith only [hyid, hscaled, hpos]
  exact ⟨P, hcut, ⟨hthird, hAcap⟩, hholes, hm, ⟨hell45, hell.2⟩, hgamma,
    hAy, hyupper, hratio, ⟨hbpos, hbthird⟩, hb, hu, hucap, hmargin⟩

/-- The actual middle recovery has the same saturated partner as its
singleton head. Literal universality excludes the private-row location;
the large original mass excludes the joined unsaturated alternative. -/
theorem middle_large_universal_partner_recovery (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1)
    (hA : 1 / 3 < S.originalAtomMass r) :
    ∃ R : S.ReverseRecovery, R.plateau = {p} ∧
      0 < μ (S.reverseCompulsorySource {p}) ∧ S.originalAtomMass r < R.height ∧
      0 ≤ μ.real (S.universalPartnerHoleRegion r p) -
        μ.real (S.reverseCompulsorySource {p}) ∧
      μ.real (S.universalPartnerCommonRegion r p) +
          (μ.real (S.universalPartnerHoleRegion r p) -
            μ.real (S.reverseCompulsorySource {p})) < 1 - 2 * S.originalAtomMass r := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith only [hq.1], hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ Benchmark.e2_density_mem hq'
  have hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3) := by
    rw [hdq]
    exact Benchmark.benchmark_e2_q hq'
  have hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d := by
    rw [hdq]
    exact Benchmark.benchmark_hasDerivAt_e2_q hq'
  have hell := (hW.e2_gamma_floor hq' hdq hgap hglobal).2.1.2
  obtain ⟨_, _, _, _, R, j, k, hj, hsource, hkj, hk, _, _, _, hloc⟩ :=
    S.exists_middle_e2_one_center_entry hW hq hdq hvalue hderiv hgap hglobal
  obtain ⟨hDelta, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
  have hkr : k = r := (hk S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst k
  have hjoined : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.rootNeighborhood j := by
    rcases hloc with ⟨_, hprivate⟩ | hjoined
    · have hpos : 0 < (μ.prod μ) ({x | S.ρ x = r.val} ×ˢ {x | S.ρ x = j.val}) := by
        rw [Measure.prod_prod]
        exact pos_iff_ne_zero.mpr (mul_ne_zero (S.hfibers r.val r.property).2.1.ne'
          (S.hfibers j.val j.property).2.1.ne')
      obtain ⟨z, hz, hu, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
        ((ae_restrict_of_ae huniv).and (ae_restrict_of_ae hprivate))
      have hne : S.ρ z.2 ≠ r.val := fun he => hkj (Subtype.ext (he.symm.trans hz.2))
      have hu' := hu hz.1
      have hp' := hp hz.1
      rw [ite_eq_right hne] at hu'
      rw [ite_eq_left (show S.ρ z.2 = r.val ∨ S.ρ z.2 = j.val from Or.inr hz.2)] at hp'
      exact False.elim (by linarith only [hu', hp'])
    · exact hjoined
  have hrj : S.IsSaturatedAtomPair r j := by
    rcases R.middle_e2_joined_peak_alternatives hW hq hdq hvalue hderiv hgap hglobal
        j r hj hkj hpeak hjoined with ⟨hrj, _, _⟩ | ⟨_, _, _, hsmall⟩
    · exact hrj
    · exact False.elim ((not_lt_of_ge hA.le) hsmall)
  have hjp : j = p := by
    rcases hpair.unique hrj hW hd hgap hell with h | h
    · exact h.2.symm
    · exact False.elim (hpair.1 h.2.symm)
  subst j
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hheight := R.universal_atom_mass_lt_singleton_height r p hpair.1 hW hj hN
  have hmargin := R.universal_partner_source_mass_margin r p hpair hW hd hgap hell hj hN
  exact ⟨R, hj, hsource, hheight, hmargin.1, hmargin.2⟩

omit [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
/-- The original bad-row proof needs only the actual ratio bound in
the middle branch. Its final signed contradiction uses that ratio instead
of an upper-E2 lower bound on gamma. The same actual primal is retained. -/
theorem UniversalPhysicalPrimal.middle_large_universal_negative_region_pos_of_ratio
    (S : SelectedHighLowStructure W m) (R : S.ReverseRecovery) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {p})
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhi : S.originalAtomMass r < 369 / 1000)
    (hell : -m ∈ Ioo (4 / 5 : ℝ) 1)
    (hratio : (1 - m - 4 * (c - m * d)) / (1 + m) < 369 / 1000)
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
  have hAhi' : S.originalAtomMass r < 2 / 5 := by linarith only [hAhi]
  have hbad := R.universal_upperE2_bad_region_pos r p hpair hW hd hgap hr hN
    hA hAhi' hell hmargin
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
  have hyid : delta * ((1 - m - 4 * (c - m * d)) / (1 + m)) = delta - 2 * gamma := by
    dsimp only [delta, gamma]
    rw [mul_div_cancel₀ _ hdelta.ne']
    ring
  have hgammaLower : delta * (631 / 2000) < gamma := by
    have hscale := mul_pos hdelta (sub_pos.mpr hratio)
    nlinarith only [hyid, hscale]
  have hbracket : 0 < (631 / 2000 : ℝ) * (1 + 2 * ell) - (1 + ell) * A := by
    have hscale := mul_pos (show 0 < 369 / 1000 - A by exact sub_pos.mpr hAhi)
      (show 0 < 1 + ell by linarith only [hell0])
    have hell45 : 4 / 5 < ell := hell.1
    nlinarith only [hscale, hell45]
  have hstrict := mul_pos hdelta hbracket
  have hgammaStrict := mul_pos (sub_pos.mpr hgammaLower)
    (show 0 < 1 + 2 * ell by linarith only [hell0])
  have hidentity : delta * (1 + ell) = 1 - ell ^ 2 := by dsimp only [delta, ell]; ring
  have hidentityScaled := congrArg (fun t => t * A) hidentity
  nlinarith only [hpaid, hstrict, hgammaStrict, hidentityScaled]

end Erdos1017.CappedModel.SelectedHighLowStructure

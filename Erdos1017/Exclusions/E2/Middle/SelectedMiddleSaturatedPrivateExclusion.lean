module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSaturatedPrivateScore
public import Erdos1017.Exclusions.E2.Middle.MiddleSaturatedPrivateClosureScalar
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateSoleSource
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSaturatedPrivateStarsPositive

/-!
# Exclusion of the saturated private peak

At a middle `E₂` contact, strictly positive stars on the entire private hole
contradict the saturated score and original curvature, so a common peak cannot
be private against one head of a saturated pair outside that peak
(`no_middle_saturated_private_contact`).
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

private theorem saturated_private_peak_high (S : SelectedHighLowStructure W m)
    (i u : S.I) (hiu : i ≠ u) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = u.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H := by
  obtain ⟨hΔ, j, _, hside, hj, _, _, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have heq : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst j
  rcases hside with hH | hN
  · exact hH
  · let I := {x | S.ρ x = i.val}
    let U := {x | S.ρ x = u.val}
    have hI : MeasurableSet I := (S.hfibers i.val i.property).1
    have hU : MeasurableSet U := (S.hfibers u.val u.property).1
    have hprob : 0 < (μ.restrict I).prod (μ.restrict U) Set.univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      have hi : 0 < μ I := (S.hfibers i.val i.property).2.1
      have hu : 0 < μ U := (S.hfibers u.val u.property).2.1
      simpa only [Measure.restrict_apply_univ, show (⊥ : ENNReal) = 0 from rfl] using
        (mul_ne_zero hi.ne' hu.ne').bot_lt
    have hneutral := S.neutral_atom_adjacency i hW hd hgap hN
    have hboth : ∀ᵐ z ∂(μ.restrict I).prod (μ.restrict U), False := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) hprivate,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hneutral,
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hU)] with z hp hn hi hu
      have hzero := hp hi
      have hone := hn hi
      have hzu : S.ρ z.2 = u.val := hu
      have hne : S.ρ z.2 ≠ i.val := fun h => hiu (Subtype.ext (h.symm.trans hzu))
      simp only [hzu, or_true, ite_true] at hzero
      simp only [hne, ite_false] at hone
      exact zero_ne_one (hzero.symm.trans hone)
    have hzero : (μ.restrict I).prod (μ.restrict U) Set.univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using hboth
    exact False.elim ((ne_of_gt hprob) hzero)

private theorem saturated_private_exposure_of_positive_stars
    (S : SelectedHighLowStructure W m) (i u : S.I) (hiu : i ≠ u)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = u.val then 0 else 1)
    (hstars : ∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \
      S.rootNeighborhood u), 0 < S.rootChargeRow i x) :
    (-m) * μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \
      S.rootNeighborhood u) <
      ∫ x in (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \
        S.rootNeighborhood u), (i.val : Ω → ℝ) x ∂μ := by
  let K := ({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \ S.rootNeighborhood u
  have hK : MeasurableSet K := ((S.hfibers i.val i.property).1.union
    (S.hfibers u.val u.property).1).compl.diff (S.measurableSet_rootNeighborhood u)
  have hk : 0 < μ K := S.private_hole_measure_pos i u hiu hW hd hgap hprivate
  have hrows : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      chargeKernel W x =ᵐ[μ]
        fun y => i.val y + m * (if 0 < i.val y then 1 else 0) :=
    (S.hfibers i.val i.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hpair : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      PhysicalRepresentative.charge W m z.1 z.2 = S.rootChargeRow i z.2 ∧
      PhysicalRepresentative.charge W m z.1 z.2 = chargeKernel W z.1 z.2 := by
    filter_upwards [S.ae_root_charge i hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
      with z hr hy hi
    exact ⟨hr hi, hy⟩
  obtain ⟨x, hx, hrow, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers i.val i.property).2.1.ne'
    (hrows.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)))
  have hshift : ∀ᵐ y ∂μ, S.rootChargeRow i y =
      i.val y + m * (if 0 < i.val y then 1 else 0) := by
    filter_upwards [hrow, hsection] with y hy hp
    exact (hp hx).1.symm.trans ((hp hx).2.trans hy)
  have hgt : ∀ᵐ x ∂μ.restrict K, -m < i.val x := by
    filter_upwards [hstars, ae_restrict_mem hK, ae_restrict_of_ae hshift,
      ae_restrict_of_ae (S.ae_private_rootNeighborhood_iff i u hW hd hgap hprivate),
      ae_restrict_of_ae (S.ae_rootNeighborhood_iff i)] with x hc hx hr hN hpos
    have hni : S.ρ x ≠ i.val := fun he => hx.1 (Or.inl he)
    have hnu : S.ρ x ≠ u.val := fun he => hx.1 (Or.inr he)
    have hi : 0 < i.val x := hpos.mp (hN.mpr ⟨hni, hnu⟩)
    rw [ite_eq_left hi, mul_one] at hr
    linarith only [hc, hr]
  have hi : Integrable (fun x => (i.val : Ω → ℝ) x) (μ.restrict K) :=
    ((Lp.memLp i.val).integrable (by norm_num)).restrict
  have hpositive : 0 < ∫ x in K, (i.val x - (-m)) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (hgt.mono (fun _ hx => sub_nonneg.mpr hx.le)) (hi.sub (integrable_const _))]
    have hs : Function.support (fun x => i.val x - (-m)) =ᵐ[μ.restrict K] Set.univ := by
      filter_upwards [hgt] with x hx
      apply propext
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (sub_pos.mpr hx).ne'
    rw [measure_congr hs]
    simpa only [Measure.restrict_apply_univ] using hk
  rw [integral_sub hi (integrable_const _), integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul] at hpositive
  change (-m) * μ.real K < ∫ x in K, (i.val : Ω → ℝ) x ∂μ
  linarith only [hpositive]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- At an actual middle-E2 contact, strictly positive stars on the entire
private hole contradict the saturated score and original curvature. All
numerical guards and the strict integrated exposure are derived here. -/
theorem no_middle_saturated_private_of_positive_stars
    (S : SelectedHighLowStructure W m) (u v i : S.I)
    (hpair : S.IsSaturatedAtomPair u v) (hiu : i ≠ u) (hiv : i ≠ v)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = u.val then 0 else 1)
    (hstars : ∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \
      S.rootNeighborhood u), 0 < S.rootChargeRow i x) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hq5 : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith [hq.1], hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hmrange := MiddleE2Parameter.multiplier_mem hq
  have hhigh := S.saturated_private_peak_high i u hiu hW hd hgap hpeak hprivate
  have hA := S.middle_e2_high_common_peak_quarter i hW ⟨hq.1.le, hq.2.le⟩
    hdq hgap hglobal hpeak hhigh
  have hsector := S.private_peak_large_sector i u hiu hW hq hdq hvalue hderiv hgap hglobal
    hpeak hprivate
  have hthird : S.originalAtomMass i ≤ 1 / 3 := by
    have hb : 0 ≤ μ.real {x | S.ρ x = u.val} := measureReal_nonneg
    change 3 * S.originalAtomMass i + μ.real {x | S.ρ x = u.val} ≤ 1 at hsector
    linarith only [hsector, hb]
  have hnoui : ¬S.IsSaturatedAtomPair u i := by
    intro h
    rcases hpair.unique h hW hd hgap hell.2 with he | he
    · exact hiv he.2.symm
    · exact hiu he.1.symm
  have hnovi : ¬S.IsSaturatedAtomPair v i := by
    intro h
    rcases hpair.unique h hW hd hgap hell.2 with he | he
    · exact hpair.1 he.1
    · exact hiu he.1.symm
  obtain ⟨κ, hmκ, hκ1, hscore⟩ := S.middle_saturated_private_score u v i hpair hiu hiv
    hnoui hnovi hW hd hgap hell.2 hprivate (hstars.mono (fun _ hx => hx.le))
  have hk := S.private_hole_measure_pos i u hiu hW hd hgap hprivate
  have hk0 : 0 < μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \
      S.rootNeighborhood u) := ENNReal.toReal_pos hk.ne' (measure_ne_top μ _)
  have hE := S.saturated_private_exposure_of_positive_stars i u hiu hW hd hgap hprivate hstars
  have hC := E2PrivateCurvature.curvature_pos_lt_six ⟨hq5.1.le, hq5.2⟩
  have hcurv := (hW.e2_contact_curvature hq5 hdq hgap hglobal).2
  have hschur := S.private_curvature_covariance_scaled i u hiu hW hd hgap hprivate hC.1
    (by linarith only [hell.1]) hcurv hk hE
  have hν : 0 < 2 * (c - m * d) := (hW.strict_gap_structure hd hgap).stationary_pos
  have hsmall : -m < 2 * E2PrivateCurvature.curvature q *
      μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \ S.rootNeighborhood u) *
        (μ.real {x | S.ρ x = i.val} +
          μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \ S.rootNeighborhood u)) := by
    have hterm := mul_nonneg (show 0 ≤ (-m) * E2PrivateCurvature.curvature q from
      mul_nonneg (by linarith only [hell.1]) hC.1.le)
      (sq_nonneg (μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = u.val} +
        μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \ S.rootNeighborhood u) -
          (1 - 2 * d)))
    apply (mul_lt_mul_iff_of_pos_right hν).mp
    nlinarith only [hschur, hterm]
  have hrow := S.stationary_row_le_neighborhood hW hd hgap u
  have hdeg := (S.private_wholeRowDegrees_sector i u hiu hW hd hgap hprivate).2
  have hcap := MiddleSaturatedPrivateScalar.score_cap hq5
  have hrm := MiddleE2PrivateScalar.row_margin hq
  rw [← hneg] at hrm hcap
  exact MiddleSaturatedPrivateScalar.saturated_private_false hA hthird measureReal_nonneg hk0
    hdeg (by linarith only [hell.2]) (by linarith only [hmrange.1, hneg]) hgamma hrow
    (by linarith only [hrm]) (by linarith only [hcap]) hmκ hκ1 hscore hC.1 hC.2 hsmall

/-- An actual middle-E2 contact cannot have a common peak private against
one head of a saturated pair outside that peak. The strict stars on the
entire original hole and every numerical guard are derived internally. -/
theorem no_middle_saturated_private_contact
    (S : SelectedHighLowStructure W m) (u v i : S.I)
    (hpair : S.IsSaturatedAtomPair u v) (hiu : i ≠ u) (hiv : i ≠ v)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = u.val then 0 else 1) :
    False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hell := (hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal).2.1.2
  have hcut : 19 / 160 < q := by
    by_contra hn
    obtain ⟨j, hij⟩ := (S.middle_e2_common_peak_universal_cutoff i hW
      ⟨hq.1.le, le_of_not_gt hn⟩ hdq hvalue hderiv hgap hglobal hpeak).1
    rcases hpair.unique hij hW hd hgap hell with he | he
    · exact hiu he.1.symm
    · exact hiv he.2.symm
  have hstars := S.ae_middle_saturated_private_star_pos i u v hiu hiv hpair hW hq
    ⟨hcut.le, hq.2.le⟩ hdq hvalue hderiv hgap hglobal hpeak hprivate
  exact S.no_middle_saturated_private_of_positive_stars u v i hpair hiu hiv hW hq hdq
    hvalue hderiv hgap hglobal hpeak hprivate hstars

end Erdos1017.CappedModel.SelectedHighLowStructure

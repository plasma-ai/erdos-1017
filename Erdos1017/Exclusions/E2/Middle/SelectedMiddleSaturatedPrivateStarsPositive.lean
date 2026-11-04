module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSaturatedPrivateStars
public import Erdos1017.Exclusions.E2.Middle.MiddleSaturatedPrivateStarsScalar
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateCovarianceGeometry

/-!
# Positive stars on the exterior hole

At a middle `E₂` saturated private contact, the original common peak has
strictly positive charge on the entire exterior hole
(`ae_middle_saturated_private_star_pos`); the radius comes from the sharp
selector gap, and the coupled scalar certificate rules out a nonpositive
first-root star anywhere in the complete high hole.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.MiddleSaturatedPrivateRadiusGap

open LowerE2Scalar

/-- The middle selector radius stays below the original peak mass across
the full saturated private interval. -/
private theorem selector_radius_gap (q A gamma : ℝ)
    (hq : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hgamma : gapFloor q < gamma) :
    (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 <
      gamma + (multiplier q - 2 / 3) * A ^ 2 := by
  have hq0 : 0 ≤ q := by linarith only [hq.1]
  have hden := denominator_pos hq0
  have hplus : 0 < 2 + q := by linarith only [hq0]
  by_cases hcut : q ≤ 3 / 20
  · have hell : (6 / 7 : ℝ) ≤ multiplier q := by
      unfold multiplier
      apply (le_div_iff₀ hplus).mpr
      linarith only [hcut]
    have hg : (3 / 80 : ℝ) ≤ gapFloor q := by
      unfold gapFloor
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hden)).mpr
      unfold denominator
      nlinarith only [hq.1, sq_nonneg (q - 19 / 160)]
    have hpay := mul_nonneg (sub_nonneg.mpr hell) (sq_nonneg A)
    have hquad : (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 -
        (multiplier q - 2 / 3) * A ^ 2 ≤ 19 / 558 := by
      nlinarith only [hpay, sq_nonneg (A - 28 / 93)]
    linarith only [hquad, hg, hgamma]
  · have hell : (9 / 11 : ℝ) ≤ multiplier q := by
      unfold multiplier
      apply (le_div_iff₀ hplus).mpr
      linarith only [hq.2]
    have hg : (1 / 24 : ℝ) ≤ gapFloor q := by
      unfold gapFloor
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hden)).mpr
      unfold denominator
      nlinarith only [lt_of_not_ge hcut, sq_nonneg (q - 3 / 20)]
    have hpay := mul_nonneg (sub_nonneg.mpr hell) (sq_nonneg A)
    have hquad : (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 -
        (multiplier q - 2 / 3) * A ^ 2 ≤ 35 / 846 := by
      nlinarith only [hpay, sq_nonneg (A - 44 / 141)]
    linarith only [hquad, hg, hgamma]

private theorem radius_lt_peak (q A gamma T : ℝ)
    (hq : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hA : 0 < A) (hT : 0 ≤ T)
    (hgamma : gapFloor q < gamma)
    (hTcap : (multiplier q - 2 / 3) * T ^ 2 =
      (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 - gamma) :
    T < A := by
  have hgap := selector_radius_gap q A gamma hq hgamma
  have hq0 : 0 ≤ q := by linarith only [hq.1]
  have hell : (9 / 11 : ℝ) ≤ multiplier q := by
    unfold multiplier
    apply (le_div_iff₀ (by linarith only [hq0] : 0 < 2 + q)).mpr
    linarith only [hq.2]
  have hcoef : 0 ≤ multiplier q - 2 / 3 := by linarith only [hell]
  by_contra hn
  have hsq : A ^ 2 ≤ T ^ 2 := by nlinarith only [hA, hT, le_of_not_gt hn]
  have hmul := mul_le_mul_of_nonneg_left hsq hcoef
  linarith only [hgap, hTcap, hmul]

end Erdos1017.MiddleSaturatedPrivateRadiusGap

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The coupled scalar certificate rules out a nonpositive first-root
star anywhere in the complete HIGH hole at its actual sharp radius. -/
theorem PrivatePhysicalPrimal.ae_middle_highRegion_star_pos_of_radius
    {i p u : S.I} {d c q : ℝ} (P : S.PrivatePhysicalPrimal i p c)
    (hip : i ≠ p) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair p u)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hm : -m = LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (T : ℝ) (hT : 0 ≤ T) (hTA : T < S.originalAtomMass i)
    (hTcap : (-m - 2 / 3) * T ^ 2 =
      (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 -
          (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ, x ∈ S.middleSaturatedPrivateHighRegion i p →
      0 < S.rootChargeRow i x := by
  let A := S.originalAtomMass i
  let b := S.originalAtomMass p
  let v := S.originalAtomMass u
  let gamma := 2 * (c - m * d) + m
  let ell := LowerE2Scalar.multiplier q
  let D := MiddleSaturatedPrivateStarsScalar.selectorValue A ell
  have hell : 2 / 3 < -m := by
    rw [hm]
    have hq0 : 0 ≤ q := by linarith only [hq.1]
    have hlow := E2PrivateCurvature.multiplier_ge_nine_elevenths
      (show q ∈ Icc (0 : ℝ) (1 / 5) from ⟨hq0, hq.2⟩)
    linarith only [hlow]
  have hellUpper : -m < 1 := by
    rw [hm]
    unfold LowerE2Scalar.multiplier
    apply (div_lt_iff₀ (by linarith only [hq.1] : 0 < 2 + q)).mpr
    linarith only [hq.1]
  have hnonlow := hhigh.mono (fun _ hh hl =>
    Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hh hl)
  have hhead0 := S.middleSaturatedPrivate_pair_square_sharp_budget i p u
    hip hiu hpair hW hd hgap hpeak hnonlow hA hell.le
  have hhead : (ell - 2 / 3) * (b ^ 2 + v ^ 2) ≤ D - gamma := by
    change gamma + (-m - 2 / 3) * (b ^ 2 + v ^ 2) ≤
      (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 at hhead0
    dsimp only [D, MiddleSaturatedPrivateStarsScalar.selectorValue, ell]
    rw [← hm]
    linarith only [hhead0]
  have hselector : (ell - 2 / 3) * T ^ 2 ≤ D - gamma := by
    change (-m - 2 / 3) * T ^ 2 =
      (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 - gamma at hTcap
    dsimp only [D, MiddleSaturatedPrivateStarsScalar.selectorValue, ell]
    rw [← hm]
    exact hTcap.le
  have hbpos : 0 < b := by
    dsimp only [b, originalAtomMass]
    exact ENNReal.toReal_pos (S.hfibers p.val p.property).2.1.ne' (measure_ne_top μ _)
  have hvpos : 0 < v := by
    dsimp only [v, originalAtomMass]
    exact ENNReal.toReal_pos (S.hfibers u.val u.property).2.1.ne' (measure_ne_top μ _)
  have hcoef : 0 < ell - 2 / 3 := by
    change 0 < LowerE2Scalar.multiplier q - 2 / 3
    rw [← hm]
    linarith only [hell]
  have hTpos : 0 < T := by
    have hpos : 0 < b ^ 2 + v ^ 2 := by nlinarith only [hbpos, hvpos]
    have hmul := mul_pos hcoef hpos
    have hTcap' : (ell - 2 / 3) * T ^ 2 = D - gamma := by
      change (-m - 2 / 3) * T ^ 2 =
        (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 - gamma at hTcap
      dsimp only [D, MiddleSaturatedPrivateStarsScalar.selectorValue, ell]
      rw [← hm]
      exact hTcap
    have hT2 : 0 < T ^ 2 := by
      have hbound : 0 < (ell - 2 / 3) * T ^ 2 := by
        rw [hTcap']
        linarith only [hhead, hmul]
      exact (mul_pos_iff_of_pos_left hcoef).mp hbound
    nlinarith only [hT, hT2]
  have hvtau : v ≤ T := by
    have hTcap' : (ell - 2 / 3) * T ^ 2 = D - gamma := by
      change (-m - 2 / 3) * T ^ 2 =
        (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 - gamma at hTcap
      dsimp only [D, MiddleSaturatedPrivateStarsScalar.selectorValue, ell]
      rw [← hm]
      exact hTcap
    have hsq : b ^ 2 + v ^ 2 ≤ T ^ 2 := by
      apply le_of_mul_le_mul_left _ hcoef
      rw [hTcap']
      exact hhead
    nlinarith only [hsq, sq_nonneg b, hvpos, hT]
  have hproduct := (P.rootExcess_lt_pair_floor_reserve u hW hd hgap
    hellUpper hhigh hpair (by linarith only [hq.1]) hdq hvalue).2
  have hcap := S.ae_middleSaturatedPrivate_forbidden_radius i p hW hd hgap
    hpeak hnonlow hA hell T hT hTA hTcap
  have hfailed := P.ae_failed_insertion_highRegion hW hd hgap hellUpper hhigh hprivate
  have hbeta := S.ae_rootChargeRow_ge i hW hd hgap (by linarith only [hell])
  filter_upwards [hcap, hfailed, hbeta] with x hxcap hxfailed hxlower hxK
  by_contra hn
  have hbetale : S.rootChargeRow i x ≤ 0 := le_of_not_gt hn
  have hf : 0 ≤ μ.real (S.diffuseExtraHole p x) := measureReal_nonneg
  have hL : P.rootExcess ≤
      MiddleSaturatedPrivateStarsScalar.surplusCap q b v := by
    change P.rootExcess ≤
      2 * (μ.real {x | S.ρ x = p.val} * μ.real {x | S.ρ x = u.val} -
        LowerE2Scalar.pairFloor q) / 3
    linarith only [hproduct.2]
  have hbetabox : S.rootChargeRow i x ∈ Icc (-ell) 0 := by
    constructor
    · dsimp only [ell]
      rw [← hm]
      simpa only [neg_neg] using hxlower
    · exact hbetale
  have hins : ((A * (3 * A + b - 1) + P.rootExcess) / 2 +
      A * μ.real (S.diffuseExtraHole p x)) * S.rootChargeRow i x ≥
      (A - 0) * (gamma + ell * (0 + b + μ.real (S.diffuseExtraHole p x))) -
        A * μ.real (S.diffuseExtraHole p x) - P.rootExcess := by
    have h := hxfailed hxK
    simpa only [A, b, gamma, ell, originalAtomMass, ← hm, zero_add,
      sub_zero] using h
  exact MiddleSaturatedPrivateStarsScalar.nonpositive_star_impossible q A gamma T b v
    0 (μ.real (S.diffuseExtraHole p x)) P.rootExcess (S.rootChargeRow i x)
    hq hA hgamma hTpos hTA.le hselector hhead hbpos hvpos
    (by linarith only [hvtau, hTA]) hvtau hproduct.1 (by norm_num) hf
    (by simpa only [b, originalAtomMass, zero_add] using hxcap hxK) hL hbetabox hins

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

omit [BorelSpace Ω] in
/-- The original private peak is HIGH; a neutral peak would join the
distinct second private fiber. -/
private theorem middle_saturated_private_peak_high
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H := by
  obtain ⟨hΔ, j, _, hside, hj, _, _, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have heq : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst j
  rcases hside with hH | hN
  · exact hH
  · let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    have hI : MeasurableSet I := (S.hfibers i.val i.property).1
    have hP : MeasurableSet P := (S.hfibers p.val p.property).1
    have hprob : 0 < (μ.restrict I).prod (μ.restrict P) Set.univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      have hi : 0 < μ I := (S.hfibers i.val i.property).2.1
      have hp : 0 < μ P := (S.hfibers p.val p.property).2.1
      simpa only [Measure.restrict_apply_univ, show (⊥ : ENNReal) = 0 from rfl] using
        (mul_ne_zero hi.ne' hp.ne').bot_lt
    have hneutral := S.neutral_atom_adjacency i hW hd hgap hN
    have hboth : ∀ᵐ z ∂(μ.restrict I).prod (μ.restrict P), False := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) hprivate,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          hneutral,
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with z hp hn hi hj
      have hzero := hp hi
      have hone := hn hi
      have hpi : S.ρ z.2 = p.val := hj
      have hneq : S.ρ z.2 ≠ i.val := by
        intro he
        exact hip (Subtype.ext (he.symm.trans hpi))
      simp only [hpi, or_true, ite_true] at hzero
      simp only [hneq, ite_false] at hone
      exact zero_ne_one (hzero.symm.trans hone)
    have hzero : (μ.restrict I).prod (μ.restrict P) Set.univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using hboth
    exact False.elim ((ne_of_gt hprob) hzero)

/-- The actual sharp selector gap determines the radius used in the
entire-HIGH-hole positive-star comparison; no radius is supplied. -/
theorem ae_middle_highRegion_star_pos
    (S : SelectedHighLowStructure W m) (i p u : S.I)
    (hip : i ≠ p) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair p u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hm : -m = LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ, x ∈ S.middleSaturatedPrivateHighRegion i p →
      0 < S.rootChargeRow i x := by
  let A := S.originalAtomMass i
  let gamma := 2 * (c - m * d) + m
  let D := (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6
  let coeff := -m - 2 / 3
  have hell : 2 / 3 < -m := by
    rw [hm]
    have hq0 : 0 ≤ q := by linarith only [hq.1]
    have hlow := E2PrivateCurvature.multiplier_ge_nine_elevenths
      (show q ∈ Icc (0 : ℝ) (1 / 5) from ⟨hq0, hq.2⟩)
    linarith only [hlow]
  have hcoef : 0 < coeff := by dsimp only [coeff]; linarith only [hell]
  have hnonlow := hhigh.mono (fun _ hh hl =>
    Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hh hl)
  have hhead := S.middleSaturatedPrivate_pair_square_sharp_budget i p u
    hip hiu hpair hW hd hgap hpeak hnonlow hA hell.le
  have hmass : 0 ≤ S.originalAtomMass p ^ 2 + S.originalAtomMass u ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD : 0 ≤ D - gamma := by
    have hmul := mul_nonneg hcoef.le hmass
    change gamma + coeff * (S.originalAtomMass p ^ 2 +
      S.originalAtomMass u ^ 2) ≤ D at hhead
    linarith only [hhead, hmul]
  let T := Real.sqrt ((D - gamma) / coeff)
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = (D - gamma) / coeff :=
    Real.sq_sqrt (div_nonneg hD hcoef.le)
  have hTcap : coeff * T ^ 2 = D - gamma := by
    rw [hTsq, mul_div_cancel₀ _ hcoef.ne']
  have hTA : T < A := by
    apply MiddleSaturatedPrivateRadiusGap.radius_lt_peak q A gamma T hq
      (by dsimp only [A]; linarith only [hA.1]) hT hgamma
    simpa only [coeff, D, A, gamma, ← hm] using hTcap
  let P := Classical.choice (S.exists_private_physical_primal i p hip hW hd hgap hprivate)
  exact P.ae_middle_highRegion_star_pos_of_radius hip hiu hpair hW hd hgap
    hq hdq hvalue hm hgamma hpeak hhigh hA hprivate T hT hTA
    (by simpa only [coeff, D, A, gamma] using hTcap)

/-- At an actual middle-E2 saturated private contact, the original
common peak has strictly positive charge on the entire exterior hole.
The HIGH location, sharp radius, physical primal and insertion payment
are all derived from the same original model. -/
theorem ae_middle_saturated_private_star_pos
    (S : SelectedHighLowStructure W m) (i p u : S.I)
    (hip : i ≠ p) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair p u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hqmid : q ∈ Icc (19 / 160 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p), 0 < S.rootChargeRow i x := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith only [hq.1], by linarith only [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hhigh := S.middle_saturated_private_peak_high i p hip hW hd hgap
    hpeak hprivate
  have hquarter := S.middle_e2_high_common_peak_quarter i hW
    ⟨hq.1.le, hq.2.le⟩ hdq hgap hglobal hpeak hhigh
  have hsector := S.private_peak_large_sector i p hip hW hq hdq hvalue
    hderiv hgap hglobal hpeak hprivate
  have hthird : S.originalAtomMass i ≤ 1 / 3 := by
    have hb : 0 ≤ μ.real {x | S.ρ x = p.val} := measureReal_nonneg
    change 3 * S.originalAtomMass i + μ.real {x | S.ρ x = p.val} ≤ 1 at hsector
    linarith only [hsector, hb]
  have hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3) :=
    ⟨hquarter.le, hthird⟩
  have hstars := S.ae_middle_highRegion_star_pos i p u hip hiu hpair
    hW hd hgap hqmid hdq hvalue hneg hgamma hpeak hhigh hA hprivate
  let K := ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
    S.rootNeighborhood p
  have hK : MeasurableSet K := ((S.hfibers i.val i.property).1.union
    (S.hfibers p.val p.property).1).compl.diff (S.measurableSet_rootNeighborhood p)
  filter_upwards [S.ae_private_hole_high i p hip hW hd hgap hhigh hprivate,
    ae_restrict_mem hK, ae_restrict_of_ae hstars] with x hxH hxK hxPos
  exact hxPos ⟨hxH, hxK⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

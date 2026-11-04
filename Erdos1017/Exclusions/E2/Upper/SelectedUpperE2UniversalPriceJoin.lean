module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalCalibration
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalHoleRow
public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalReduction

/-!
# Price join excluding the universal positive source

The original physical `H` row and the signed copied-row estimate give the
negative-source price, the scalar price contradicts the signed copy in either
endpoint sign, and no positive-body saturated universal pair can satisfy the
original upper-`E₂` contact and its physical tight-primal tests
(`no_upper_e2_universal_positive_source`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original physical H row and the signed copied-row estimate give
the actual negative-source price on the unchanged original law. -/
theorem UniversalPhysicalPrimal.ae_universal_negative_price_row
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (R : S.ReverseRecovery)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hr : R.plateau = {p})
    (huPos : 0 < μ.real (S.universalPartnerCommonRegion r p))
    (hu : μ.real (S.universalPartnerCommonRegion r p) <
      1 - 2 * S.originalAtomMass r)
    (θ α : ℝ) (hθ : 0 ≤ θ)
    (hθeq : θ = 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (ha : ∀ᵐ h ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p h ≤ α)
    (hα : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      α < S.originalAtomMass r - S.universalOwnMass x) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalHoleChargeRow r p x ≤
        UniversalSignedPrice.priceFunction μ
          (S.universalPartnerHoleRegion r p)
          (S.universalPartnerHoleMissingMass r p) (S.universalRootDeficit r)
          (S.originalAtomMass r) (S.originalAtomMass p)
          (2 * (c - m * d) + m) θ (S.universalOwnMass x)
          (S.universalGoodMissingMass r p d c x) (-S.rootChargeRow r x) +
        S.universalExtraHoleCopyError r p d c x := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalNegativeRegion r p
  let G := PhysicalRepresentative.adjacency W m
  have hprod : (μ.restrict H).prod (μ.restrict B) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hrow := ae_mono hprod
    (P.ae_hole_missing_row_le_signed_error S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hrowH : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict B),
      (∫ z in IndependentAtomCopy.missingSection G q.1,
        PhysicalRepresentative.charge W m q.2 z ∂μ) +
        m * μ.real (IndependentAtomCopy.missingSection G q.1 ∩
          IndependentAtomCopy.missingSection G q.2) ≤
          S.universalPartnerHoleMissingMass r p q.1 *
            PhysicalRepresentative.charge W m q.1 q.2 +
          S.originalAtomMass p * (-S.rootChargeRow r q.2) +
          S.universalLowGoodErrorRow r p d c q.1 := by
    filter_upwards [hrow,
      Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)),
      Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (S.measurableSet_universalNegativeRegion r p))]
      with q hq hH hB
    have hbase := hq hH hB
    have hnonpos : m * μ.real (IndependentAtomCopy.missingSection G q.1 ∩
        IndependentAtomCopy.missingSection G q.2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hell.1]) measureReal_nonneg
    nlinarith only [hbase, hnonpos]
  have he : ∀ h, 0 ≤ S.universalLowGoodErrorRow r p d c h := fun h =>
    (S.universalLowGoodErrorRow_mem_Icc r p hpair hW hd hgap hN h).1
  have hbridge := P.ae_universalHoleCopyError_eq_extra S r p hpair R hW hd
    hgap hN hA hAhalf hell hmargin hr huPos
  have hErr := hbridge.mono (fun _ hx => hx.1)
  have hbound := P.ae_hole_negative_charge_row_le_price_of_rows S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin hu
    (S.universalLowGoodErrorRow r p d c) he hrowH θ α hθ hθeq ha hα hErr
  filter_upwards [hbound, hbridge] with x hx herror
  rw [herror.2] at hx
  exact hx

/-- The original scalar price contradicts the signed copy in either
endpoint sign. All resource terms here are later supplied by the same
original H and negative-common law. -/
theorem upperE2_universal_scalar_price_false
    (A b u z q ell gamma R chi Ecap Irec N n TB Zd : ℝ)
    (hA : 1 / 3 < A) (hb : b ∈ Icc (0 : ℝ) (1 - 2 * A))
    (hz : 0 ≤ z) (hzu : z ≤ u) (heta : 0 ≤ 1 - A - b - u)
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : UpperE2UniversalScalar.gammaFloor ell ≤ gamma)
    (hgamma0 : 0 < gamma)
    (hgammaCeil : gamma ≤ (1 - ell) / 2)
    (hR : R = min (1 - 3 * A + b)
      ((1 - u - 2 * ell * A - 3 * gamma) / ell))
    (hzR : z ≤ R) (hq : 0 ≤ q)
    (hpack : q + z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - u))
    (hIrec : Irec = UpperE2UniversalScalar.originalReciprocal A b u z q)
    (hN : 0 < N) (hNn : N < ell * n)
    (hchi : 0 ≤ chi ∧ chi < 1 / 2)
    (hE : 0 ≤ Ecap ∧ Ecap < 3 * gamma / 5)
    (hZd : 0 ≤ Zd) (hown : TB ≤ z * N)
    (hbudget : TB + Zd ≤ R * N)
    (hcopy : ell * ((A - b) * N - TB + gamma * n) ≤
      max (b * ell - gamma) 0 * Irec * N + chi * Zd + ell * Ecap * n) :
    False := by
  have hell0 : 0 < ell := by linarith only [hell.1]
  have hRcap : R ≤ 1 - 3 * A + b := by
    rw [hR]
    exact min_le_left _ _
  by_cases hprice : 0 ≤ b * ell - gamma
  · have hcopy' : ell * ((A - b) * N - TB + gamma * n) ≤
        ((b * ell - gamma) * Irec) * N + chi * Zd + ell * Ecap * n := by
      simpa only [max_eq_left hprice, mul_assoc] using hcopy
    have hnecessary := UniversalSignedPrice.positive_price_necessary A b gamma ell
      Ecap ((b * ell - gamma) * Irec) chi z R N n TB Zd
      (by linarith only [hell.1]) hgamma0 hE.2 hN hNn hchi.2.le hZd
      hown hbudget hcopy'
    have hnegative := UpperE2UniversalScalar.originalPrice_neg hA.le hb hz hzu
      heta hell hgamma hprice (by simpa only [hR] using hzR) hq hpack
    dsimp only [UpperE2UniversalScalar.originalPrice] at hnegative
    rw [← hIrec, ← hR] at hnegative
    linarith only [hnecessary, hnegative]
  · have hprice' : b * ell - gamma < 0 := lt_of_not_ge hprice
    have hbsmall : b < 1 / 8 := by
      have hmul : (4 / 5 : ℝ) * b ≤ ell * b :=
        mul_le_mul_of_nonneg_right hell.1 hb.1
      nlinarith only [hmul, hprice', hgammaCeil, hell.1]
    have hgap : 0 < A - b - R := by
      linarith only [hRcap, hA, hbsmall]
    have hcopy' : ell * ((A - b) * N - TB + gamma * n) ≤
        chi * Zd + ell * Ecap * n := by
      simpa only [max_eq_right hprice'.le, zero_mul, zero_add] using hcopy
    exact UniversalSignedPrice.nonpositive_price_impossible A b gamma ell Ecap
      chi R N n TB Zd hell0 (by linarith only [hE.2, hgamma0]) hgap
      hN hNn (by linarith only [hchi.2, hell.1]) hZd hbudget hcopy'

/-- The same first missing-mass cap keeps the reciprocal pole beyond
the actual H atom cap for every negative source. -/
private theorem upperE2_hole_alpha_gap
    (A b z q ax : ℝ) (hA : 1 / 3 < A)
    (hz : z ≤ 1 - 3 * A + b) (hax : ax ≤ z) :
    min (1 - 2 * A - b) (Real.sqrt q) < A - ax := by
  have hα := min_le_left (1 - 2 * A - b) (Real.sqrt q)
  linarith only [hα, hA, hz, hax]

/-- The original saturated two-head budget bounds the contact gap
without any sign assumption on the endpoint price. -/
private theorem universal_sat_gamma_le_half_delta
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hell : -m < 1) :
    2 * (c - m * d) + m ≤ (1 + m) / 2 := by
  have hbudget := S.empty_sat_corner_shared_budget r p hpair hW hd hgap hN
  have hD : 0 ≤ ∫ h in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r h ∂μ :=
    integral_nonneg (fun h => (S.universalRootDeficit_mem_Icc r h).1)
  have hscore : 0 ≤ ∫ x in S.universalPartnerCommonRegion r p,
      -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae
      (S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN),
      S.ae_partner_row_pos_on_universalCommon r p,
      ae_restrict_mem (S.measurableSet_universalPartnerCommonRegion r p)]
      with x hx hp hU
    have hnotr : S.ρ x ≠ r.val := fun h => hU (Or.inl (Or.inl h))
    have hnotp : S.ρ x ≠ p.val := fun h => hU (Or.inl (Or.inr h))
    exact neg_nonneg.mpr (hx hnotr ⟨hnotp, hp⟩)
  have hmass : 0 ≤ (1 + m) * μ.real (S.universalPartnerCommonRegion r p) :=
    mul_nonneg (by linarith only [hell]) measureReal_nonneg
  linarith only [hbudget, hD, hscore, hmass]

/-- The selected calibration bounds the actual signed price on almost
every negative common row, with the original H square moment retained. -/
theorem UniversalPhysicalPrimal.ae_universal_price_endpoint
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) {d : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hb : S.originalAtomMass p ≤ 1 - 2 * S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (Rcap : ℝ)
    (hRcap : Rcap = min (1 - 3 * S.originalAtomMass r + S.originalAtomMass p)
      ((1 - μ.real (S.universalPartnerCommonRegion r p) +
        2 * m * S.originalAtomMass r - 3 * (2 * (c - m * d) + m)) / (-m)))
    (hu : μ.real (S.universalPartnerCommonRegion r p) <
      1 - 2 * S.originalAtomMass r)
    (hDH : (∫ h in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r h ∂μ) <
        (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) *
          (S.originalAtomMass r - S.universalSharedHoleRadius r p Rcap))
    (hzero : max (1 - 2 * (3 * (2 * (c - m * d) + m) /
      S.originalAtomMass r - (1 + m))) 0 * Rcap <
        2 * (c - m * d) + m) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let ell := -m
    let gamma := 2 * (c - m * d) + m
    let z := S.universalSharedHoleRadius r p Rcap
    let qH := S.universalHoleSquareMoment r p
    let alpha := min (1 - 2 * A - b) (Real.sqrt qH)
    let theta := 3 * gamma / A - (1 + m)
    let DH := ∫ h in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r h ∂μ
    let chi := if theta < 1 / 2 then
      DH * (1 - 2 * theta) / ((A - z) * (1 - theta) - DH) else 0
    let Irec := μ.real (S.universalPartnerHoleRegion r p) / (A - z) +
      qH / ((A - z) * (A - z - alpha))
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      UniversalSignedPrice.priceFunction μ (S.universalPartnerHoleRegion r p)
        (S.universalPartnerHoleMissingMass r p) (S.universalRootDeficit r)
        A b gamma theta (S.universalOwnMass x)
        (S.universalGoodMissingMass r p d c x) (-S.rootChargeRow r x) ≤
          (-S.rootChargeRow r x) / ell *
            (max (b * ell - gamma) 0 * Irec +
              S.universalGoodMissingMass r p d c x * chi) := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let ell := -m
  let gamma := 2 * (c - m * d) + m
  let z := S.universalSharedHoleRadius r p Rcap
  let qH := S.universalHoleSquareMoment r p
  let alpha := min (1 - 2 * A - b) (Real.sqrt qH)
  let theta := 3 * gamma / A - (1 + m)
  let DH := ∫ h in S.universalPartnerHoleRegion r p,
    S.universalRootDeficit r h ∂μ
  let chi := if theta < 1 / 2 then
    DH * (1 - 2 * theta) / ((A - z) * (1 - theta) - DH) else 0
  let Irec := μ.real (S.universalPartnerHoleRegion r p) / (A - z) +
    qH / ((A - z) * (A - z - alpha))
  have htheta : 0 ≤ theta := by
    have hApos : 0 < A := by dsimp only [A] at *; linarith only [hA]
    have hmul : (3 * gamma / A) * A = 3 * gamma := by
      field_simp
    dsimp only [theta, gamma, A] at *
    have hdelta : 0 ≤ 1 + m := by linarith only [hell.2]
    nlinarith only [hmargin, hmul, hApos, hdelta,
      mul_nonneg (le_of_lt hApos) hdelta]
  have hcap := P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin hu
  rw [← hRcap] at hcap
  have hzcap : z ≤ Rcap := S.universalSharedHoleRadius_le_capacity r p Rcap
  have hzbad : z ≤ 1 - 3 * A + b := by
    dsimp only [A, b] at *
    rw [hRcap] at hzcap
    exact hzcap.trans (min_le_left _ _)
  have hk : 0 < A - z := by
    dsimp only [A, b] at *
    linarith only [hzbad, hA, hb]
  have halpha : alpha < A - z := by
    dsimp only [alpha, qH]
    exact upperE2_hole_alpha_gap A b z qH z hA hzbad le_rfl
  have ha := S.ae_hole_missing_mass_le_min_capacity_sqrt r p hpair hW hd
    hgap hell.2 hN
  have hDmax := P.ae_hole_deficit_le_one_sub_threshold S r p hpair hW hd
    hgap hN hA hAhalf hell hmargin
  have hv := S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN
  have hown := P.ae_negative_own_le_shared_radius S r p hpair hW hd
    hgap hN hA hAhalf hell hmargin Rcap hcap
  filter_upwards [hv, hown, hcap] with x hx hax hj
  have hax' : S.universalOwnMass x ≤ z := by simpa only [z] using hax
  have hv' : -S.rootChargeRow r x ∈ Icc (0 : ℝ) ell :=
    ⟨hx.1.le, hx.2.le⟩
  have hj0 := S.universalGoodMissingMass_nonneg r p d c x
  have hjR : S.universalGoodMissingMass r p d c x ≤ Rcap := by
    have hown0 := (S.universalOwnMass_mem_Icc x).1
    linarith only [hj, hown0]
  have he := S.universalSignedPrice_le_endpoint r p hpair hW hd hgap
    hell.2 theta z (S.universalOwnMass x) alpha
    (S.universalGoodMissingMass r p d c x) (-S.rootChargeRow r x)
    b gamma ell Rcap htheta hk hDH hax' halpha ha hDmax
    (by dsimp only [ell]; linarith only [hell.1]) hv' hj0 hjR hzero
  simpa only [A, b, ell, gamma, z, qH, alpha, theta, DH, chi, Irec]
    using he


/-- No positive-body saturated universal pair can satisfy the original
upper-E2 contact and its physical tight-primal tests. -/
theorem UniversalPhysicalPrimal.no_upper_e2_universal_positive_source
    (S : SelectedHighLowStructure W m) (R : S.ReverseRecovery) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c q : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {p}) (hsource : 0 < μ (S.reverseCompulsorySource {p}))
    (huniv : ∀ᵐ v ∂μ.prod μ, S.ρ v.1 = r.val →
      adjacencyKernel W v.1 v.2 = if S.ρ v.2 = r.val then 0 else 1)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val}) : False := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let ell := -m
  let gamma := 2 * (c - m * d) + m
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let B := S.universalNegativeRegion r p
  let Rcap := min (1 - 3 * A + b) ((1 - μ.real U - 2 * ell * A - 3 * gamma) / ell)
  let z := S.universalSharedHoleRadius r p Rcap
  let qH := S.universalHoleSquareMoment r p
  let alpha := min (1 - 2 * A - b) (Real.sqrt qH)
  let theta := 3 * gamma / A - (1 - ell)
  let DH := ∫ h in H, S.universalRootDeficit r h ∂μ
  let chi := if theta < 1 / 2 then
    DH * (1 - 2 * theta) / ((A - z) * (1 - theta) - DH) else 0
  let Irec := μ.real H / (A - z) + qH / ((A - z) * (A - z - alpha))
  let Ecap := (μ.real H - μ.real (S.reverseCompulsorySource {p})) *
    max (ell - theta) 0 * μ.real (S.universalGoodCommonRegion r p d c) / μ.real U
  have hmissing := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith only [hmissing.1, hmissing.2]
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith only [hq.1], by linarith only [hq.2]⟩
  obtain ⟨hm, hellContact, hfloor⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hell : ell ∈ Ioo (1 / 2 : ℝ) 1 := hellContact
  have hellbox : ell ∈ Icc (4 / 5 : ℝ) (9 / 11) := by
    change -m ∈ Icc (4 / 5 : ℝ) (9 / 11)
    rw [hm]
    have h := UpperE2Parameter.multiplier_mem hq
    exact ⟨by simpa only [neg_neg] using h.1.le, by simpa only [neg_neg] using h.2⟩
  have hgammaFloor : UpperE2UniversalScalar.gammaFloor ell ≤ gamma := by
    have h := UpperE2Parameter.gapFloor_ge_correlated hq
    rw [← neg_eq_iff_eq_neg.mpr hm] at h
    dsimp only [UpperE2UniversalScalar.gammaFloor, gamma, ell]
    linarith only [h, hfloor]
  obtain ⟨hA, hb, hmargin, hcut, hu, hBpos, hNpos, hNbound⟩ :=
    P.universal_upperE2_quantitative_bounds R r p hpair hW hq hdq hvalue
      hderiv hgap hglobal hr hsource huniv hpeak hpositive
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hAhalf : A ≤ 1 / 2 := by dsimp only [A] at *; linarith only [hcut]
  have hcal := P.universal_upperE2_price_calibration S R r p hpair hW hq hdq
    hvalue hderiv hgap hglobal hr hsource huniv hpeak hpositive
  change DH < theta * (A - z) ∧ 0 ≤ chi ∧ chi < 1 / 2 ∧
    1 / 200 < gamma - max (1 - 2 * theta) 0 * Rcap ∧
      0 ≤ Ecap ∧ Ecap < 3 * gamma / 5 at hcal
  obtain ⟨hDH, hchi0, hchiHalf, hzero, hE0, hEhi⟩ := hcal
  have hRdef : Rcap = min (1 - 3 * A + b)
      ((1 - μ.real U + 2 * m * A - 3 * gamma) / (-m)) := by
    dsimp only [Rcap, ell]
    congr 1
    ring
  have hcap := P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin hu
  change ∀ᵐ x ∂μ.restrict B,
    S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤
      min (1 - 3 * A + b) ((1 - μ.real U + 2 * m * A - 3 * gamma) / -m) at hcap
  rw [← hRdef] at hcap
  have hR0 : 0 ≤ Rcap :=
    S.universalSharedHoleCapacity_nonneg r p d c Rcap hBpos hcap
  have hz0 : 0 ≤ z := S.universalSharedHoleRadius_nonneg r p Rcap hR0
  have hzu : z ≤ μ.real U := by
    dsimp only [z]
    exact P.universalSharedHoleRadius_le_common_mass S r p hpair hW hd hgap
      hN hA hAhalf hell hmargin Rcap
  have hq0 : 0 ≤ qH := S.universalHoleSquareMoment_nonneg r p
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hmass' : μ.real H = 1 - A - b - μ.real U := by
    dsimp only [H, A, b, U] at *
    linarith only [hmass]
  have heta : 0 ≤ 1 - A - b - μ.real U := by
    rw [← hmass']
    exact measureReal_nonneg
  have hIrec : Irec = UpperE2UniversalScalar.originalReciprocal A b (μ.real U) z qH := by
    dsimp only [Irec, UpperE2UniversalScalar.originalReciprocal, alpha, qH]
    rw [hmass']
  have hpack0 := P.hole_add_shared_radius_sq_le_original_missing S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin Rcap hR0
  have hpack : qH + z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - μ.real U) := by
    rw [hdq, hmass'] at hpack0
    dsimp only [qH, z, A, b]
    nlinarith only [hpack0, hmissing.2]
  have hRle : z ≤ Rcap := S.universalSharedHoleRadius_le_capacity r p Rcap
  have hbbox : b ∈ Icc (0 : ℝ) (1 - 2 * A) :=
    ⟨measureReal_nonneg, hb⟩
  have hgamma0 : 0 < gamma := by
    have h := UpperE2Parameter.gapFloor_ge hq
    dsimp only [gamma]
    linarith only [h, hfloor]
  have hNn : S.universalNegativeChargeMass r p < ell * μ.real B := hNbound
  have htheta : 0 ≤ theta := by
    have hApos : 0 < A := by dsimp only [A] at *; linarith only [hA]
    have hmul : (3 * gamma / A) * A = 3 * gamma := by field_simp
    have hdelta : 0 ≤ 1 + m := by linarith only [hell.2]
    dsimp only [theta, gamma, A] at *
    nlinarith only [hmargin, hmul, hApos, hdelta,
      mul_nonneg (le_of_lt hApos) hdelta]
  have hzero' : max (1 - 2 * theta) 0 * Rcap < gamma := by
    linarith only [hzero]
  have hthetaeq : theta = 3 * gamma / A - (1 + m) := by
    dsimp only [theta, ell]
    ring
  rw [hthetaeq] at hDH hzero'
  have hendpoint := P.ae_universal_price_endpoint S r p hpair hW hd hgap
    hN hA hb hAhalf hell hmargin Rcap hRdef hu
    (by simpa only [DH, A, z, gamma] using hDH)
    (by simpa only [A, gamma] using hzero')
  have hUpos : 0 < μ.real U := by
    have hBreal : 0 < μ.real B :=
      ENNReal.toReal_pos hBpos.ne' (measure_ne_top μ B)
    have hBU : B ⊆ U := by
      intro x hx
      exact hx.1
    exact lt_of_lt_of_le hBreal
      (ENNReal.toReal_mono (measure_ne_top μ U) (measure_mono hBU))
  have ha := S.ae_hole_missing_mass_le_min_capacity_sqrt r p hpair hW hd
    hgap hell.2 hN
  have hown := P.ae_negative_own_le_shared_radius S r p hpair hW hd
    hgap hN hA hAhalf hell hmargin Rcap hcap
  have hzbad : z ≤ 1 - 3 * A + b := hRle.trans (min_le_left _ _)
  have halpha : alpha < A - z := by
    have hmin := min_le_left (1 - 2 * A - b) (Real.sqrt qH)
    dsimp only [alpha]
    linarith only [hmin, hA, hzbad]
  have hαae : ∀ᵐ x ∂μ.restrict B,
      alpha < A - S.universalOwnMass x := by
    filter_upwards [hown] with x hx
    linarith only [halpha, hx]
  have hrow := P.ae_universal_negative_price_row S r p hpair R hW hd
    hgap hN hA hAhalf hell hmargin hr hUpos hu theta alpha htheta
    (by exact hthetaeq)
    (by simpa only [alpha, A, b, qH, H] using ha)
    (by simpa only [A, B, z] using hαae)
  have hpartner := P.ae_partner_copy_lower_row S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hErr := P.integrable_universalExtraHoleCopyError S r p hpair R hW hd hgap
    hN hA hAhalf hell hmargin hr hUpos
  have hErrBound := P.ae_universalExtraHoleCopyError_le S r p hpair R hW hd
    hgap hN hA hAhalf hell hmargin hr hUpos
  have hEmass := S.universal_extra_hole_mass_eq r p hpair hW hd hgap hell.2
  have hErrAE : ∀ᵐ x ∂μ.restrict B,
      S.universalExtraHoleCopyError r p d c x ≤ Ecap := by
    filter_upwards [hErrBound] with x hx
    have h := hx.2
    have htau : -m - (3 * gamma / A - (1 + m)) = ell - theta := by
      dsimp only [ell, theta]
      ring
    change S.universalExtraHoleCopyError r p d c x ≤
      μ.real (S.universalExtraHoleRegion r p) *
        (max (-m - (3 * gamma / A - (1 + m))) 0 *
          μ.real (S.universalGoodCommonRegion r p d c) / μ.real U) at h
    rw [htau, hEmass] at h
    convert h using 1; ring
  rw [hthetaeq] at hrow
  have hpoint : ∀ᵐ x ∂μ.restrict B,
      (A - b) * (-S.rootChargeRow r x) -
        S.universalOwnMass x * (-S.rootChargeRow r x) + gamma ≤
          (max (b * ell - gamma) 0 * Irec * (-S.rootChargeRow r x) +
            chi * ((-S.rootChargeRow r x) * S.universalGoodMissingMass r p d c x)) /
              ell + S.universalExtraHoleCopyError r p d c x := by
    filter_upwards [hpartner, hrow, hendpoint] with x hp hrw he
    calc
      _ ≤ S.universalHoleChargeRow r p x := by
        change (A - b - S.universalOwnMass x) * (-S.rootChargeRow r x) + gamma ≤
          S.universalHoleChargeRow r p x at hp
        nlinarith only [hp]
      _ ≤ UniversalSignedPrice.priceFunction μ H
          (S.universalPartnerHoleMissingMass r p) (S.universalRootDeficit r)
          A b gamma (3 * gamma / A - (1 + m)) (S.universalOwnMass x)
          (S.universalGoodMissingMass r p d c x) (-S.rootChargeRow r x) +
            S.universalExtraHoleCopyError r p d c x := by
              simpa only [H, A, b, gamma] using hrw
      _ ≤ (-S.rootChargeRow r x) / ell *
          (max (b * ell - gamma) 0 * Irec +
            S.universalGoodMissingMass r p d c x * chi) +
            S.universalExtraHoleCopyError r p d c x := by
              convert add_le_add_left he
                (S.universalExtraHoleCopyError r p d c x) using 1;
                simp only [A, b, ell, gamma, H, Irec, qH, alpha, chi, DH, z,
                  hthetaeq]
      _ = _ := by ring
  have hjInt : IntegrableOn (fun x => -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x) B μ := by
    convert (S.integrable_universalWeightedGoodMissing r p d c).integrableOn using 1
    ext x
    ring
  have hswap : (∫ x in B, -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x ∂μ) =
      S.universalWeightedGoodMissingMoment r p d c := by
    change (∫ x in B, -S.rootChargeRow r x *
      S.universalGoodMissingMass r p d c x ∂μ) =
      ∫ x in B, S.universalGoodMissingMass r p d c x * (-S.rootChargeRow r x) ∂μ
    congr 1
    funext x
    ring
  have hcopy0 := UniversalSignedPrice.integrated_signed_copy B
    (fun x => -S.rootChargeRow r x) S.universalOwnMass
    (S.universalGoodMissingMass r p d c)
    (S.universalExtraHoleCopyError r p d c)
    A b gamma ell (max (b * ell - gamma) 0 * Irec) chi
    (by linarith only [hell.1])
    ((S.integrable_universalNegativeCharge r).integrableOn)
    ((S.integrable_universalWeightedOwn r).integrableOn)
    hjInt hErr.1 hpoint
  rw [hswap] at hcopy0
  change ell * ((A - b) * S.universalNegativeChargeMass r p -
    S.universalWeightedOwnMoment r p + gamma * μ.real B) ≤
      max (b * ell - gamma) 0 * Irec * S.universalNegativeChargeMass r p +
        chi * S.universalWeightedGoodMissingMoment r p d c +
          ell * (∫ x in B, S.universalExtraHoleCopyError r p d c x ∂μ) at hcopy0
  have hErrInt : (∫ x in B, S.universalExtraHoleCopyError r p d c x ∂μ) ≤
      Ecap * μ.real B := by
    have hmono := integral_mono_ae hErr.1
      (integrable_const (μ := μ.restrict B) Ecap) hErrAE
    rw [setIntegral_const, smul_eq_mul] at hmono
    simpa only [mul_comm] using hmono
  have hcopy : ell * ((A - b) * S.universalNegativeChargeMass r p -
    S.universalWeightedOwnMoment r p + gamma * μ.real B) ≤
      max (b * ell - gamma) 0 * Irec * S.universalNegativeChargeMass r p +
        chi * S.universalWeightedGoodMissingMoment r p d c +
          ell * Ecap * μ.real B := by
    have hscale := mul_le_mul_of_nonneg_left hErrInt
      (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hell.1))
    nlinarith only [hcopy0, hscale]
  have hownBudget := P.weighted_own_le_shared_radius S r p hpair hW hd
    hgap hN hA hAhalf hell hmargin Rcap hcap
  have htotalBudget := P.weighted_hole_inventory_le_actual S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin hu
  rw [← hRdef] at htotalBudget
  have hZd0 : 0 ≤ S.universalWeightedGoodMissingMoment r p d c := by
    apply integral_nonneg_of_ae
    filter_upwards [S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN]
      with x hx
    exact mul_nonneg (S.universalGoodMissingMass_nonneg r p d c x) hx.1.le
  have hgammaCeil : gamma ≤ (1 - ell) / 2 := by
    have h := universal_sat_gamma_le_half_delta S r p hpair hW hd hgap hN hell.2
    dsimp only [gamma, ell]
    linarith only [h]
  exact upperE2_universal_scalar_price_false A b (μ.real U) z qH ell gamma
    Rcap chi Ecap Irec (S.universalNegativeChargeMass r p) (μ.real B)
    (S.universalWeightedOwnMoment r p)
    (S.universalWeightedGoodMissingMoment r p d c)
    hA hbbox hz0 hzu heta hellbox hgammaFloor hgamma0 hgammaCeil
    rfl hRle hq0 hpack hIrec hNpos hNn ⟨hchi0, hchiHalf⟩
    ⟨hE0, hEhi⟩ hZd0 hownBudget htotalBudget hcopy
end Erdos1017.CappedModel.SelectedHighLowStructure

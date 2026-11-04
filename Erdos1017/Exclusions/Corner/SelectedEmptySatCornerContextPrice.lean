module

public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerCancellation
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerCounts
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerLedger
public import Erdos1017.Exclusions.Common.E2.SelectedEmptySatE2Inventory

/-!
# Context price of the empty-source saturated corner

The whole-source selector and one same-primal negative-load quota pay the
original cost in the nonexceptional corner sector, with all signs and shifted
row identities derived.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private theorem partner_charge_row_integral (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (∫ x, S.rootChargeRow p x ∂μ) =
      2 * (c - m * d) + m * (1 - S.originalAtomMass p -
        μ.real (S.universalPartnerHoleRegion r p)) := by
  let Np := S.rootNeighborhood p
  have hNp : MeasurableSet Np := S.measurableSet_rootNeighborhood p
  have hp : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hind : Integrable (Np.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hNp
  have heq : (S.rootChargeRow p) =ᵐ[μ]
      fun x => p.val x + m * Np.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap,
      S.ae_rootNeighborhood_iff p] with x hx hn
    change 1 - S.rootChargeRow p x = _ at hx
    have hi : (if 0 < p.val x then (1 : ℝ) else 0) = Np.indicator (fun _ => 1) x := by
      by_cases hN : x ∈ Np
      · have hpos : 0 < p.val x := hn.mp hN
        simp only [hpos, ite_true, indicator_of_mem hN]
      · have hnpos : ¬0 < p.val x := fun h => hN (hn.mpr h)
        simp only [hnpos, ite_false, indicator_of_notMem hN]
    rw [hi] at hx
    linarith only [hx]
  rw [integral_congr_ae heq, integral_add hp (hind.const_mul m),
    integral_const_mul, integral_indicator hNp, setIntegral_const, smul_eq_mul, mul_one,
    S.row_integral_of_stationary p hW, S.universal_partner_neighborhood_mass r p hpair hW hd hgap]

private theorem private_charge_shifted_identity (p : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    S.emptySatPrivateCharge p =
      (∫ z, shiftedKernel W m z.1 z.2
        ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
          (μ.restrict (S.reverseCompulsorySource {p}))) / 2 +
        m * S.emptySatPrivateEdgeMass p := by
  let nu := μ.restrict (S.reverseCompulsorySource {p})
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  let M := Function.uncurry (shiftedKernel W m)
  have hY : Integrable Y (nu.prod nu) := Integrable.of_bound
    (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    (Eventually.of_forall (fun z => by
      change ‖PhysicalRepresentative.charge W m z.1 z.2‖ ≤ 3
      simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m z.1 z.2))
  have hG : Integrable G (nu.prod nu) := by
    apply Integrable.of_bound
      (PhysicalCliqueRepresentative.measurable_edgeIndicator
        (PhysicalRepresentative.measurable_adjacency W m)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).1]
      exact (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).2)
  have hae : (fun z => Y z - m * G z) =ᵐ[nu.prod nu] M := by
    have hdom : nu.prod nu ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [ae_mono hdom (PhysicalRepresentative.charge_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support),
      ae_mono hdom (PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support)] with z hy hg
    have hm := shiftedMoment_eq W m z
    change shiftedKernel W m z.1 z.2 = chargeKernel W z.1 z.2 -
      m * adjacencyKernel W z.1 z.2 at hm
    change adjacencyKernel W z.1 z.2 = G z at hg
    rw [← hy, hg] at hm
    exact hm.symm
  have hint := integral_congr_ae hae
  rw [integral_sub hY (hG.const_mul m), integral_const_mul] at hint
  change (∫ z, Y z ∂nu.prod nu) / 2 = (∫ z, M z ∂nu.prod nu) / 2 +
    m * ((∫ z, G z ∂nu.prod nu) / 2)
  linarith only [hint]

private theorem cost_of_joint_context_quota
    {c A b K C0 gap DJ cP cH cU WP sigmaP t eta Uload Rctx : ℝ}
    (hK : 0 < K) (hC0 : 0 < C0) (heta : 0 < eta)
    (hC0K : C0 ≤ K) (ht : 0 ≤ t) (hDJ : 0 ≤ DJ)
    (hcP : 0 ≤ cP) (hcU : 0 ≤ cU) (hWP : 0 ≤ WP)
    (hprice : 2 * K * t ≤ 3 * C0)
    (hcount : c ≤ A * b + K + gap + cP + cH + cU)
    (hcontext : gap * C0 + K * (DJ + cP - sigmaP) ≤ Rctx)
    (hsigma : eta * sigmaP ≤ t * (WP - cP))
    (hquota : 3 * WP + 2 * eta * cH + 12 * eta * cU ≤ Uload) :
    c ≤ A * b + K + Rctx / C0 + Uload / (2 * eta) := by
  have hscale : 0 < 2 * eta * C0 := by positivity
  have hcount' := mul_le_mul_of_nonneg_left hcount hscale.le
  have hcontext' := mul_le_mul_of_nonneg_left hcontext (show 0 ≤ 2 * eta by positivity)
  have hsigma' := mul_le_mul_of_nonneg_left hsigma (show 0 ≤ 2 * K by positivity)
  have hquota' := mul_le_mul_of_nonneg_left hquota hC0.le
  have hcoeff : 0 ≤ K * (eta + t) - eta * C0 := by
    nlinarith only [mul_nonneg hK.le ht, mul_nonneg heta.le (sub_nonneg.mpr hC0K)]
  have hp := mul_nonneg hcoeff hcP
  have hq := mul_nonneg (sub_nonneg.mpr hprice) hWP
  have hr := mul_nonneg (show 0 ≤ eta * C0 by positivity) hcU
  have hs := mul_nonneg (show 0 ≤ eta * K by positivity) hDJ
  have hbound : 2 * eta * C0 * (c - A * b - K) ≤ 2 * eta * Rctx + C0 * Uload := by
    nlinarith only [hcount', hcontext', hsigma', hquota', hp, hq, hr, hs]
  have hid : (Rctx / C0 + Uload / (2 * eta)) * (2 * eta * C0) =
      2 * eta * Rctx + C0 * Uload := by
    field_simp
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith only [hbound, hid]


private theorem private_source_region_integral (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    let I := {x | S.ρ x = r.val}
    let Pset := {x | S.ρ x = p.val}
    let J := S.reverseCompulsorySource {p}
    let Q := ((I ∪ Pset) ∪ J)ᶜ
    (∫ x, f x ∂μ) = (∫ x in I, f x ∂μ) + (∫ x in Pset, f x ∂μ) +
      (∫ x in J, f x ∂μ) + ∫ x in Q, f x ∂μ := by
  dsimp only
  let I := {x | S.ρ x = r.val}
  let Pset := {x | S.ρ x = p.val}
  let J := S.reverseCompulsorySource {p}
  let Q := ((I ∪ Pset) ∪ J)ᶜ
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hQ : MeasurableSet Q := ((hI.union hP).union hJ).compl
  have hpart : f =ᵐ[μ] fun x => I.indicator f x + Pset.indicator f x +
      J.indicator f x + Q.indicator f x := by
    filter_upwards [S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell]
      with x hx
    by_cases hxI : x ∈ I
    · have hxP : x ∉ Pset := fun hp => hpair.1 (Subtype.ext (hxI.symm.trans hp))
      have hxJ : x ∉ J := fun hj => hx hj (Or.inl (Or.inl hxI))
      have hxQ : x ∉ Q := fun hq => hq (Or.inl (Or.inl hxI))
      simp only [indicator_of_mem hxI, indicator_of_notMem hxP,
        indicator_of_notMem hxJ, indicator_of_notMem hxQ, add_zero]
    · by_cases hxP : x ∈ Pset
      · have hxJ : x ∉ J := fun hj => hx hj (Or.inl (Or.inr hxP))
        have hxQ : x ∉ Q := fun hq => hq (Or.inl (Or.inr hxP))
        simp only [indicator_of_notMem hxI, indicator_of_mem hxP,
          indicator_of_notMem hxJ, indicator_of_notMem hxQ, zero_add, add_zero]
      · by_cases hxJ : x ∈ J
        · have hxQ : x ∉ Q := fun hq => hq (Or.inr hxJ)
          simp only [indicator_of_notMem hxI, indicator_of_notMem hxP,
            indicator_of_mem hxJ, indicator_of_notMem hxQ, zero_add, add_zero]
        · have hxQ : x ∈ Q := by
            rintro ((hi | hp) | hj)
            · exact hxI hi
            · exact hxP hp
            · exact hxJ hj
          simp only [indicator_of_notMem hxI, indicator_of_notMem hxP,
            indicator_of_notMem hxJ, indicator_of_mem hxQ, zero_add]
  have hsum1 := integral_add (((hf.indicator hI).add (hf.indicator hP)).add
    (hf.indicator hJ)) (hf.indicator hQ)
  have hsum2 := integral_add ((hf.indicator hI).add (hf.indicator hP)) (hf.indicator hJ)
  have hsum3 := integral_add (hf.indicator hI) (hf.indicator hP)
  simp only [Pi.add_apply] at hsum1 hsum2 hsum3
  rw [integral_congr_ae hpart, hsum1, hsum2, hsum3,
    integral_indicator hI, integral_indicator hP, integral_indicator hJ, integral_indicator hQ]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integrable_source_star (J : Set Ω) (K : Ω × Ω → ℝ) (hK : Measurable K)
    (B : ℝ) (hB : ∀ z, ‖K z‖ ≤ B) :
    Integrable (fun x => ∫ z in J, K (z, x) ∂μ) μ := by
  apply Integrable.of_bound
    hK.stronglyMeasurable.integral_prod_left'.measurable.aestronglyMeasurable
    (B * μ.real J)
  apply Eventually.of_forall
  intro x
  have hi := norm_integral_le_of_norm_le_const (μ := μ.restrict J)
    (Eventually.of_forall (fun z => hB (z, x)))
  simpa only [measureReal_restrict_apply_univ] using hi

private theorem private_source_rest_mass (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    μ.real (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
      S.reverseCompulsorySource {p})ᶜ =
        1 - S.originalAtomMass r - S.originalAtomMass p -
          μ.real (S.reverseCompulsorySource {p}) := by
  have hm := private_source_region_integral r p hpair hW hd hgap hell
    (fun _ => (1 : ℝ)) (integrable_const 1)
  simp only [integral_const, smul_eq_mul, mul_one, probReal_univ,
    measureReal_restrict_apply_univ] at hm
  change _ = 1 - μ.real {x | S.ρ x = r.val} - μ.real {x | S.ρ x = p.val} - _
  linarith only [hm]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem context_sigma_payment_price {A j K C0 ell delta eta : ℝ}
    (hAj : 0 ≤ A * j) (hKcap : K ≤ A * j) (hC0 : ell * A * j / 2 < C0)
    (hell : 0 < ell) (hdelta : 1 / 5 < delta) (hsum : ell + delta = 1)
    (heta : delta < eta) :
    2 * K * max (ell - eta) 0 ≤ 3 * C0 := by
  have ht : 0 ≤ max (ell - eta) 0 := le_max_right _ _
  have hrate : 2 * max (ell - eta) 0 ≤ 3 * ell / 2 := by
    by_cases ha : 0 ≤ ell - eta
    · rw [max_eq_left ha]
      linarith only [heta, hdelta, hsum]
    · rw [max_eq_right (le_of_not_ge ha)]
      linarith only [hell]
  have hfirst := mul_le_mul_of_nonneg_right hKcap ht
  have hsecond := mul_le_mul_of_nonneg_right hrate hAj
  nlinarith only [hC0, hfirst, hsecond]

private theorem ae_source_join_context (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.reverseCompulsorySource {p} →
      q.2 ∉ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
        S.reverseCompulsorySource {p} →
      PhysicalRepresentative.adjacency W m q.1 q.2 = true := by
  filter_upwards [S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
      |> Measure.quasiMeasurePreserving_fst.ae,
    ReverseRecovery.ae_private_source_sameAtom p hW,
    S.ae_universalPartnerHole_missing_iff_sameAtom r p hpair hW hd hgap hell,
    S.ae_partner_compulsorySource_joined_common r p hpair hW hd hgap hell,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support]
    with q hsource hwhole hmissing hcommon hphys hx hq
  by_contra hn
  have hf : PhysicalRepresentative.adjacency W m q.1 q.2 = false :=
    Bool.eq_false_iff.mpr hn
  have hzero : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 = _ at hphys
    rw [hphys, hf]
    norm_num
  by_cases hyH : q.2 ∈ S.universalPartnerHoleRegion r p
  · have hs := (hmissing (hsource hx) hyH).mp hzero
    exact hq (Or.inr ((hwhole hs).mp hx))
  · have hyU : q.2 ∈ S.universalPartnerCommonRegion r p := by
      intro hy
      rcases hy with (hr | hp) | hH
      · exact hq (Or.inl (Or.inl hr))
      · exact hq (Or.inl (Or.inr hp))
      · exact hyH hH
    have hone := hcommon hx hyU
    linarith only [hone, hzero]


omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem constant_source_block (J C : Set Ω) (K : Ω × Ω → ℝ) (k : ℝ)
    (heq : K =ᵐ[(μ.restrict J).prod (μ.restrict C)] fun _ => k) :
    (∫ z, K z ∂(μ.restrict J).prod (μ.restrict C)) = k * μ.real J * μ.real C := by
  rw [integral_congr_ae heq, integral_const, smul_eq_mul, ← univ_prod_univ,
    measureReal_prod_prod, measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]
  ring

private theorem source_star_root_integral (r p : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (∫ x in {x | S.ρ x = r.val}, S.emptySatPrivateStar p x ∂μ) =
      S.originalAtomMass r * ∫ x in S.reverseCompulsorySource {p}, S.rootChargeRow r x ∂μ := by
  let I := {x | S.ρ x = r.val}
  let J := S.reverseCompulsorySource {p}
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  have hY : Integrable Y ((μ.restrict J).prod (μ.restrict I)) := Integrable.of_bound
    (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    (Eventually.of_forall (fun z => by
      change ‖PhysicalRepresentative.charge W m z.1 z.2‖ ≤ 3
      simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m z.1 z.2))
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hrow : Y =ᵐ[(μ.restrict J).prod (μ.restrict I)]
      fun z => S.rootChargeRow r z.1 := by
    filter_upwards [ae_mono
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (hswap.ae (S.ae_root_charge r hW hd hgap)),
      Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (S.hfibers r.val r.property).1)] with z hz hx
    have he := hz hx
    rw [PhysicalRepresentative.charge_symm] at he
    exact he
  calc
    _ = ∫ z, Y z ∂(μ.restrict J).prod (μ.restrict I) :=
      (integral_prod_symm Y hY).symm
    _ = ∫ z, S.rootChargeRow r z.1 ∂(μ.restrict J).prod (μ.restrict I) :=
      integral_congr_ae hrow
    _ = _ := by
      have hm := integral_prod_mul (μ := μ.restrict J) (ν := μ.restrict I)
        (S.rootChargeRow r) (fun _ => (1 : ℝ))
      simp only [mul_one, integral_const, smul_eq_mul,
        measureReal_restrict_apply_univ] at hm
      exact hm.trans (mul_comm _ _)

private theorem source_star_partner_integral_zero (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (∫ x in {x | S.ρ x = p.val}, S.emptySatPrivateStar p x ∂μ) = 0 := by
  have hzero : ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
      S.rootChargeRow p x = 0 := by
    filter_upwards [ae_restrict_of_ae
        (S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell),
      ae_restrict_of_ae (S.rootChargeRow_zero_off_neighborhood p hW hd hgap),
      ae_restrict_mem (S.measurableSet_reverseCompulsorySource {p})] with x hx hz hxJ
    exact hz (fun hn => hx hxJ (Or.inr hn))
  rw [source_star_root_integral p p hW hd hgap, integral_eq_zero_of_ae hzero, mul_zero]

private theorem source_graph_blocks (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let I := {x | S.ρ x = r.val}
    let Pset := {x | S.ρ x = p.val}
    let J := S.reverseCompulsorySource {p}
    let Q := ((I ∪ Pset) ∪ J)ᶜ
    let G := PhysicalCliqueRepresentative.edgeIndicator
      (Function.uncurry (PhysicalRepresentative.adjacency W m))
    (∫ z, G z ∂(μ.restrict J).prod (μ.restrict I)) = μ.real J * S.originalAtomMass r ∧
      (∫ z, G z ∂(μ.restrict J).prod (μ.restrict Pset)) = 0 ∧
      (∫ z, G z ∂(μ.restrict J).prod (μ.restrict Q)) = μ.real J * μ.real Q := by
  dsimp only
  let I := {x | S.ρ x = r.val}
  let Pset := {x | S.ρ x = p.val}
  let J := S.reverseCompulsorySource {p}
  let Q := ((I ∪ Pset) ∪ J)ᶜ
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hQ : MeasurableSet Q := ((hI.union hP).union hJ).compl
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hsource := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  have hroot : G =ᵐ[(μ.restrict J).prod (μ.restrict I)] fun _ => 1 := by
    filter_upwards [ae_mono
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (hswap.ae (S.neutral_atom_physical_adjacency r hW hd hgap hN)),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae hsource),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hJ),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hI)] with z hz hs hx hy
    have hxr : S.ρ z.1 ≠ r.val := fun hh => hs hx (Or.inl (Or.inl hh))
    have ha := (hz hy).mpr hxr
    rw [PhysicalRepresentative.adjacency_symm] at ha
    exact ite_eq_left ha
  have hpartner : G =ᵐ[(μ.restrict J).prod (μ.restrict Pset)] fun _ => 0 := by
    filter_upwards [ae_mono
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (hswap.ae (S.ae_root_adjacency p hW hd hgap)),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae hsource),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hJ),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with z hz hs hx hy
    have hn : z.1 ∉ S.rootNeighborhood p := fun hh => hs hx (Or.inr hh)
    have ha : ¬PhysicalRepresentative.adjacency W m z.1 z.2 = true := by
      intro hh
      rw [PhysicalRepresentative.adjacency_symm] at hh
      exact hn ((hz hy).mp hh)
    exact ite_eq_right ha
  have hrest : G =ᵐ[(μ.restrict J).prod (μ.restrict Q)] fun _ => 1 := by
    filter_upwards [ae_mono
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (ae_source_join_context r p hpair hW hd hgap hell),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hJ),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hQ)] with z hz hx hy
    exact ite_eq_left (hz hx hy)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [I, J, G, originalAtomMass, one_mul] using
      constant_source_block J I G 1 hroot
  · simpa only [zero_mul] using constant_source_block J Pset G 0 hpartner
  · simpa only [one_mul] using constant_source_block J Q G 1 hrest

private theorem private_source_rest_charge_identity (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    S.emptySatPrivateRestCharge r p =
      μ.real (S.reverseCompulsorySource {p}) *
        (2 * (c - m * d) + m - m * (S.originalAtomMass p +
          μ.real (S.reverseCompulsorySource {p})) - S.originalAtomMass r) +
        S.originalAtomMass r *
          (∫ x in S.reverseCompulsorySource {p}, S.universalRootDeficit r x ∂μ) -
        ∫ z, shiftedKernel W m z.1 z.2
          ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
            (μ.restrict (S.reverseCompulsorySource {p})) := by
  let I := {x | S.ρ x = r.val}
  let Pset := {x | S.ρ x = p.val}
  let J := S.reverseCompulsorySource {p}
  let Q := ((I ∪ Pset) ∪ J)ᶜ
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  let starG := fun x => ∫ z in J, G (z, x) ∂μ
  have hYm : Measurable Y := PhysicalRepresentative.measurable_charge W m
  have hGm : Measurable G := PhysicalCliqueRepresentative.measurable_edgeIndicator
    (PhysicalRepresentative.measurable_adjacency W m)
  have hYbound : ∀ z, ‖Y z‖ ≤ 3 := fun z => by
    change ‖PhysicalRepresentative.charge W m z.1 z.2‖ ≤ 3
    simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m z.1 z.2
  have hGbound : ∀ z, ‖G z‖ ≤ 1 := fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).1]
    exact (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).2
  have hYi (rho : Measure (Ω × Ω)) [IsFiniteMeasure rho] : Integrable Y rho :=
    Integrable.of_bound hYm.aestronglyMeasurable 3 (Eventually.of_forall hYbound)
  have hGi (rho : Measure (Ω × Ω)) [IsFiniteMeasure rho] : Integrable G rho :=
    Integrable.of_bound hGm.aestronglyMeasurable 1 (Eventually.of_forall hGbound)
  have hYs : Integrable (S.emptySatPrivateStar p) μ :=
    integrable_source_star J Y hYm 3 hYbound
  have hGs : Integrable starG μ := integrable_source_star J G hGm 1 hGbound
  have hYfull : (∫ x, S.emptySatPrivateStar p x ∂μ) =
      ∫ z, Y z ∂(μ.restrict J).prod μ := (integral_prod_symm Y (hYi _)).symm
  have hYblock (C : Set Ω) : (∫ x in C, S.emptySatPrivateStar p x ∂μ) =
      ∫ z, Y z ∂(μ.restrict J).prod (μ.restrict C) :=
    (integral_prod_symm Y (hYi _)).symm
  have hGfull : (∫ x, starG x ∂μ) =
      ∫ z, G z ∂(μ.restrict J).prod μ := (integral_prod_symm G (hGi _)).symm
  have hGblock (C : Set Ω) : (∫ x in C, starG x ∂μ) =
      ∫ z, G z ∂(μ.restrict J).prod (μ.restrict C) :=
    (integral_prod_symm G (hGi _)).symm
  have hYpart := private_source_region_integral r p hpair hW hd hgap hell
    (S.emptySatPrivateStar p) hYs
  have hGpart := private_source_region_integral r p hpair hW hd hgap hell starG hGs
  have hCJ : (∫ z, Y z ∂(μ.restrict J).prod (μ.restrict J)) =
      2 * S.emptySatPrivateCharge p := by
    dsimp only [emptySatPrivateCharge, J, Y, Function.uncurry]
    ring
  have he : (∫ z, G z ∂(μ.restrict J).prod (μ.restrict J)) =
      2 * S.emptySatPrivateEdgeMass p := by
    dsimp only [emptySatPrivateEdgeMass, J, G]
    ring
  obtain ⟨hGI, hGP, hGQ⟩ := source_graph_blocks r p hpair hW hd hgap hell hN
  dsimp only at hYpart hGpart hGI hGP hGQ
  rw [hYfull, source_star_root_integral r p hW hd hgap,
    source_star_partner_integral_zero r p hpair hW hd hgap hell, hYblock J, hCJ] at hYpart
  rw [hGfull, hGblock I, hGblock Pset, hGblock J, hGblock Q, hGI, hGP, he, hGQ] at hGpart
  have hQmass := private_source_rest_mass r p hpair hW hd hgap hell
  have hrow := S.physical_restricted_row_mean hW hd hgap J
  change (∫ z, Y z ∂(μ.restrict J).prod μ) = μ.real J * (2 * (c - m * d)) +
    m * (∫ z, G z ∂(μ.restrict J).prod μ) at hrow
  have hbeta : Integrable (S.rootChargeRow r) (μ.restrict J) := by
    apply Integrable.of_bound (S.measurable_rootChargeRow r).aestronglyMeasurable 3
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(S.rootChargeRow_mem_Icc r x).1,
        (S.rootChargeRow_mem_Icc r x).2.trans (by norm_num)⟩)
  have hbetaeq : (∫ x in J, S.rootChargeRow r x ∂μ) =
      μ.real J - ∫ x in J, S.universalRootDeficit r x ∂μ := by
    have hi := integral_sub (integrable_const (μ := μ.restrict J) (1 : ℝ)) hbeta
    change (∫ x in J, S.universalRootDeficit r x ∂μ) = _ at hi
    rw [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at hi
    linarith only [hi]
  have hshifted := private_charge_shifted_identity p hW hd hgap
  rw [hYpart, hGpart, hbetaeq, hshifted] at hrow
  change μ.real Q = _ at hQmass
  change S.emptySatPrivateRestCharge r p = _
  change S.originalAtomMass r *
      (μ.real J - ∫ x in J, S.universalRootDeficit r x ∂μ) + 0 +
      2 * ((∫ z, shiftedKernel W m z.1 z.2 ∂(μ.restrict J).prod (μ.restrict J)) / 2 +
        m * S.emptySatPrivateEdgeMass p) + S.emptySatPrivateRestCharge r p =
    μ.real J * (2 * (c - m * d)) + m *
      (μ.real J * S.originalAtomMass r + 0 + 2 * S.emptySatPrivateEdgeMass p +
        μ.real J * μ.real Q) at hrow
  rw [hQmass] at hrow
  nlinarith only [hrow]

private theorem private_selector_charge_identity (r p : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    S.emptySatPrivateSelectorCharge r p =
      (∫ z, shiftedKernel W m z.1 z.2
        ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
          (μ.restrict (S.reverseCompulsorySource {p}))) / 2 +
        m * S.emptySatPrivateEdgeMass p + S.originalAtomMass r *
          (μ.real (S.reverseCompulsorySource {p}) -
            ∫ x in S.reverseCompulsorySource {p}, S.universalRootDeficit r x ∂μ) := by
  let J := S.reverseCompulsorySource {p}
  have hbeta : Integrable (S.rootChargeRow r) (μ.restrict J) := by
    apply Integrable.of_bound (S.measurable_rootChargeRow r).aestronglyMeasurable 3
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(S.rootChargeRow_mem_Icc r x).1,
        (S.rootChargeRow_mem_Icc r x).2.trans (by norm_num)⟩)
  have hbetaeq : (∫ x in J, S.rootChargeRow r x ∂μ) =
      μ.real J - ∫ x in J, S.universalRootDeficit r x ∂μ := by
    have hi := integral_sub (integrable_const (μ := μ.restrict J) (1 : ℝ)) hbeta
    change (∫ x in J, S.universalRootDeficit r x ∂μ) = _ at hi
    rw [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at hi
    linarith only [hi]
  unfold emptySatPrivateSelectorCharge
  rw [private_charge_shifted_identity p hW hd hgap, hbetaeq]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

namespace ReverseRecovery

/-- The entire source selector and one same-primal negative-load quota
pay the original cost in the nonexceptional corner sector. All signs
and original shifted row identities are derived internally. -/
theorem empty_sat_corner_context_price (R : S.ReverseRecovery) (r p : S.I)
    (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (nu : Measure Ω) [IsProbabilityMeasure nu] (V : Model Ω nu),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) (hstrip : 21 / 100 < 1 + m) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let H := S.universalPartnerHoleRegion r p
    let U := S.universalPartnerCommonRegion r p
    let J := S.reverseCompulsorySource {p}
    let j := μ.real J
    let e := S.emptySatPrivateEdgeMass p
    let F := ∫ z, shiftedKernel W m z.1 z.2 ∂(μ.restrict J).prod (μ.restrict J)
    let dJ := ∫ x in J, S.universalRootDeficit r x ∂μ
    let gamma := 2 * (c - m * d) + m
    let eta := 3 * gamma / A - (1 + m)
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real H + μ.real U - D
    let E := D - A
    let K := A * j - e
    let C0 := F / 2 + m * e + A * (j - dJ)
    let RJ := j * (gamma - m * (b + j) - A) + A * dJ - F
    let ZP := gamma - m * (b + μ.real H)
    let Bc := 1 - 3 * A + b
    let Nmax := (2 * (c - m * d) - (1 - m) * A) / 2
    let Uload := S.emptySatNegativeDegreeLoad r p
    0 < L → E < L →
      (∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L) →
      0 < K ∧ 0 < C0 ∧ 0 ≤ Bc ∧ Uload ≤ Bc * Nmax ∧
        c ≤ A * b + K +
          (K * b * ZP - A * b * C0 - (A ^ 2 - K) * RJ) / C0 + Uload / (2 * eta) := by
  dsimp only
  intro hL hEL hsmall
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let H := S.universalPartnerHoleRegion r p
  let J := S.reverseCompulsorySource {p}
  let j := μ.real J
  let e := S.emptySatPrivateEdgeMass p
  let F := ∫ z, shiftedKernel W m z.1 z.2 ∂(μ.restrict J).prod (μ.restrict J)
  let dJ := ∫ x in J, S.universalRootDeficit r x ∂μ
  let gamma := 2 * (c - m * d) + m
  let eta := 3 * gamma / A - (1 + m)
  let K := A * j - e
  let C0 := F / 2 + m * e + A * (j - dJ)
  let RJ := j * (gamma - m * (b + j) - A) + A * dJ - F
  let ZP := gamma - m * (b + μ.real H)
  let gap := P.emptySatRootNoPartnerCost p - K
  let DJ := P.emptySatPrivateDeletionSlack p
  let cP := P.emptySatPartnerCost p
  let cH := P.emptySatHoleCost p
  let cU := P.emptySatCommonCost p
  let WP := P.emptySatPartnerNegativeLoad p
  let sigmaP := P.emptySatPartnerSigmaLoad p
  let Uload := S.emptySatNegativeDegreeLoad r p
  obtain ⟨hell, _, _, _⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have helllt : -m < 1 := by linarith only [hell.2]
  have hellpos : 0 < -m := by linarith only [hell.1]
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  have hKscalar : S.emptySatPrivateSelectorRefund r p = K := rfl
  have hC0scalar : S.emptySatPrivateSelectorCharge r p = C0 :=
    private_selector_charge_identity r p hW hd hgap
  have hRJscalar : S.emptySatPrivateRestCharge r p = RJ :=
    private_source_rest_charge_identity r p hpair hW hd hgap helllt hN
  have hZPscalar : (∫ x, S.rootChargeRow p x ∂μ) = ZP := by
    rw [partner_charge_row_integral r p hpair hW hd hgap]
    dsimp only [ZP, gamma]
    ring
  obtain ⟨hK, hKcap, hC0K, hC0lower⟩ :=
    R.empty_source_selector_bounds r p hr hpair hW hd hgap helllt hnull hL hEL hsmall
  simp only [hKscalar, hC0scalar] at hK hKcap hC0K hC0lower
  have hAj : 0 < A * j := hK.trans_le hKcap
  have hC0 : 0 < C0 := by
    have hp := mul_pos hellpos hAj
    nlinarith only [hp, hC0lower]
  obtain ⟨hAlo, _, hmargin, _, _⟩ :=
    R.empty_sat_corner_bad_region r p hr hpair P hW hd hgap he heq hglobal hnull hstrip
  have hA : 0 < A := by linarith only [hAlo]
  have hratio : 2 * (1 + m) < 3 * gamma / A := (lt_div_iff₀ hA).mpr (by
    nlinarith only [hmargin])
  have hetadelta : 1 + m < eta := by dsimp only [eta]; linarith only [hratio]
  have heta : 0 < eta := by linarith only [hstrip, hetadelta]
  have hprice : 2 * K * max (-m - eta) 0 ≤ 3 * C0 :=
    context_sigma_payment_price hAj.le hKcap hC0lower hellpos
      (show 1 / 5 < 1 + m by linarith only [hstrip]) (by ring) hetadelta
  obtain ⟨_, hBc, _, hUmax, hquota, hsigma⟩ :=
    R.empty_sat_corner_rootless_quota r p hr hpair P hW hd hgap he heq hglobal hnull hstrip
  obtain ⟨_, hDJ, hledger⟩ :=
    R.empty_sat_corner_context_ledger r p hr hpair P hW hd hgap helllt hnull
  simp only [hKscalar, hC0scalar, hRJscalar, hZPscalar] at hledger
  have hcP : 0 ≤ cP := tsum_nonneg (fun _ => measureReal_nonneg)
  have hcU : 0 ≤ cU := tsum_nonneg (fun _ => measureReal_nonneg)
  have hWP : 0 ≤ WP := by
    apply Finset.sum_nonneg
    intro n _
    apply integral_nonneg
    intro v
    exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hcounts := P.emptySat_cost_partition p
  rw [P.emptySatRootPartnerCost_eq p hpair.1.symm hW hd hgap] at hcounts
  have hcount : c ≤ A * b + K + gap + cP + cH + cU := by
    dsimp only [gap, A, b, cP, cH, cU]
    linarith only [hcounts]
  have hcost := cost_of_joint_context_quota hK hC0 heta hC0K (le_max_right _ _)
    hDJ hcP hcU hWP hprice hcount hledger hsigma hquota
  exact ⟨hK, hC0, hBc, hUmax, hcost⟩

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure

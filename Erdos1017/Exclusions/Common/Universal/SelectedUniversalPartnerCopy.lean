module

public import Erdos1017.SelectedModel.Structure.SelectedMultipartiteHalves
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalGeometry
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalBadTopology

/-!
# Partner copy of the universal primal

The partner's missing row is its own atom plus its outside hole, and the signed
partner copy, before spending the remaining missing row, pays the whole hole
row; the topology event rules out a missing outside-own partner-positive
recipient.
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

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integrable_physical_row (x : Ω) :
    Integrable (PhysicalRepresentative.charge W m x) μ :=
  Integrable.of_bound
    ((PhysicalRepresentative.measurable_charge W m).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (PhysicalRepresentative.charge_bound W m x))

/-- The partner's missing row is its own entire atom plus its entire
original outside hole. The charge is kept signed in this exact identity. -/
theorem ae_partner_missing_row_integral
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ.restrict {y | S.ρ y = p.val}, ∀ᵐ x ∂μ,
      (∫ z in IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) y,
        PhysicalRepresentative.charge W m x z ∂μ) =
      S.originalAtomMass p * S.rootChargeRow p x +
        ∫ z in S.universalPartnerHoleRegion r p,
          PhysicalRepresentative.charge W m x z ∂μ := by
  let I : Set Ω := {z | S.ρ z = p.val}
  let H := S.universalPartnerHoleRegion r p
  let Y := PhysicalRepresentative.charge W m
  let G := PhysicalRepresentative.adjacency W m
  have hI : MeasurableSet I := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hProw := Measure.ae_ae_of_ae_prod (S.ae_root_adjacency p hW hd hgap)
  have hPcharge := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_root_charge p hW hd hgap))
  have hRin : ∀ᵐ z ∂μ, S.ρ z = r.val → z ∈ S.rootNeighborhood p := by
    filter_upwards [(ae_restrict_iff' (S.hfibers r.val r.property).1).mp
      hpair.symm.row_on_other] with z hz hr
    exact ⟨fun hp => hpair.1 (Subtype.ext (hr.symm.trans hp)), by
      rw [hz hr]
      linarith [(hW.strict_gap_structure hd hgap).multiplier_neg]⟩
  filter_upwards [ae_restrict_of_ae hProw, ae_restrict_mem hI] with y hy hyI
  filter_upwards [hPcharge] with x hx
  have hsection : ∀ᵐ z ∂μ, G y z = false ↔ z ∈ I ∪ H := by
    filter_upwards [hy, hRin] with z hz hr
    have heq := hz hyI
    have hcomp : z ∉ S.rootNeighborhood p ↔ z ∈ I ∪ H := by
      dsimp only [I, H, universalPartnerHoleRegion]
      have hown : S.ρ z = p.val → z ∉ S.rootNeighborhood p := fun hp h => h.1 hp
      constructor
      · intro hn
        by_cases hp : S.ρ z = p.val
        · exact Or.inl hp
        · exact Or.inr (fun h => h.elim (fun h => h.elim
            (fun hr' => hn (hr hr')) hp) hn)
      · rintro (hp | h)
        · exact hown hp
        · exact fun hn => h (Or.inr hn)
    simpa only [Bool.eq_false_iff] using (not_congr heq).trans hcomp
  have hrowI : (∫ z in I, Y x z ∂μ) = μ.real I * S.rootChargeRow p x := by
    have hc : ∀ᵐ z ∂μ.restrict I, Y x z = S.rootChargeRow p x := by
      filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem hI] with z hz hzI
      dsimp only [Y]
      rw [PhysicalRepresentative.charge_symm W m]
      exact hz hzI
    rw [integral_congr_ae hc, setIntegral_const, smul_eq_mul]
  have hset : IndependentAtomCopy.missingSection G y =ᵐ[μ] I ∪ H :=
    hsection.mono (fun _ hz => propext hz)
  rw [setIntegral_congr_set hset,
    setIntegral_union (by
      apply disjoint_left.mpr
      intro z hzI hzH
      exact hzH (Or.inl (Or.inr hzI))) hH
      (integrable_physical_row x).integrableOn (integrable_physical_row x).integrableOn,
    hrowI]
  rfl

private theorem UniversalPhysicalPrimal.ae_partner_negative_charge
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict
      (S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0}),
        S.rootChargeRow p x = -S.rootChargeRow r x := by
  have hApos : 0 < S.originalAtomMass r := by linarith only [hA]
  have htheta : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) := by
    have hm : (2 * (1 + m)) * S.originalAtomMass r <
        3 * (2 * (c - m * d) + m) := by nlinarith only [hmargin]
    have hmul := (lt_div_iff₀ hApos).mpr hm
    linarith only [hmul, hell.2]
  have hBad := (ae_restrict_iff'
    (S.measurableSet_universalUpperE2BadRegion r p d c)).mp
      (P.ae_universalUpperE2Bad_partner_charge S r p hpair hW hd hgap
        hN hA hAhalf hell hmargin)
  apply (ae_restrict_iff'
    ((S.measurableSet_universalPartnerCommonRegion r p).inter
      (measurableSet_lt (S.measurable_rootChargeRow r) measurable_const))).mpr
  filter_upwards [hBad] with x hx hxNeg
  apply hx
  exact ⟨fun h => hxNeg.1 (Or.inl h), hxNeg.2.trans htheta⟩

/-- The actual signed partner copy before spending its remaining missing
row. This retains the old integral, so no missing-sign estimate is hidden. -/
theorem UniversalPhysicalPrimal.ae_partner_copy_signed_row
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0}),
      S.originalAtomMass r * (-S.rootChargeRow r x) + (2 * (c - m * d) + m) ≤
        S.originalAtomMass p * (-S.rootChargeRow r x) +
          (∫ z in S.universalPartnerHoleRegion r p, chargeKernel W x z ∂μ) +
            ∫ z in IndependentAtomCopy.missingSection
              (PhysicalRepresentative.adjacency W m) x, S.rootChargeRow p z ∂μ := by
  have hcopy := Measure.ae_ae_of_ae_prod (S.ae_universal_copy_inequality r hW hd hgap hN)
  have hrow := Measure.ae_ae_of_ae_prod (S.ae_root_charge p hW hd hgap)
  obtain ⟨y, hy, hcy, hry, hmy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers p.val p.property).2.1.ne'
    ((ae_restrict_of_ae hcopy).and
      ((ae_restrict_of_ae hrow).and
        (S.ae_partner_missing_row_integral r p hpair hW hd hgap)))
  have hyn : S.ρ y ≠ r.val := fun he =>
    hpair.1 (Subtype.ext (he.symm.trans hy))
  have hphys := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [P.ae_partner_negative_charge S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin, ae_restrict_of_ae hcy,
    ae_restrict_of_ae hry, ae_restrict_of_ae hmy, ae_restrict_of_ae hphys,
    ae_restrict_mem ((S.measurableSet_universalPartnerCommonRegion r p).inter
      (measurableSet_lt (S.measurable_rootChargeRow r) measurable_const))]
    with x hpx hcx hrowx hmx hphysx hx
  have hxn : S.ρ x ≠ r.val := fun he => hx.1 (Or.inl (Or.inl he))
  have hyx : PhysicalRepresentative.charge W m y x = -S.rootChargeRow r x :=
    (hrowx hy).trans hpx
  have hpositive : 0 < PhysicalRepresentative.charge W m y x := by
    rw [hyx]
    exact neg_pos.mpr hx.2
  have hc := hcx hyn hxn hpositive
  rw [hyx, hmx, hpx] at hc
  have hremaining : (∫ z in IndependentAtomCopy.missingSection
      (PhysicalRepresentative.adjacency W m) x,
      PhysicalRepresentative.charge W m y z ∂μ) =
        ∫ z in IndependentAtomCopy.missingSection
          (PhysicalRepresentative.adjacency W m) x, S.rootChargeRow p z ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hry] with z hz
    exact hz hy
  have hhole : (∫ z in S.universalPartnerHoleRegion r p,
      PhysicalRepresentative.charge W m x z ∂μ) =
        ∫ z in S.universalPartnerHoleRegion r p, chargeKernel W x z ∂μ :=
    integral_congr_ae (ae_restrict_of_ae hphysx)
  rw [hremaining, hhole] at hc
  have hsign : m * μ.real (IndependentAtomCopy.missingSection
      (PhysicalRepresentative.adjacency W m) y ∩
        IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (hW.strict_gap_structure hd hgap).multiplier_neg.le measureReal_nonneg
  change S.originalAtomMass r * (-S.rootChargeRow r x) +
      (2 * (c - m * d) + m) - m * _ ≤ _ at hc
  linarith only [hc, hsign]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem own_mass_eq_sameAtom_section
    (S : SelectedHighLowStructure W m) (x : Ω) :
    (S.collapsedPartLabel x).elim 0 S.originalAtomMass =
      μ.real {z | (x, z) ∈ S.sameAtomRelation} := by
  have hswap : {z | (x, z) ∈ S.sameAtomRelation} =
      {z | (z, x) ∈ S.sameAtomRelation} := by
    ext z
    change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔
      (S.ρ z = S.ρ x ∧ S.ρ z ∈ S.I)
    constructor <;> rintro ⟨h, hI⟩ <;> exact ⟨h.symm, h ▸ hI⟩
  rw [hswap]
  change (S.collapsedPartLabel x).elim 0 S.originalAtomMass = S.ownIndependentMass x
  by_cases hx : S.ρ x ∈ S.I
  · rw [S.ownIndependentMass_eq_fiber (S.ρ x) hx x rfl]
    simp [collapsedPartLabel, HalfGraphMultipartite.collapsedLabel,
      hx, originalAtomMass]
  · rw [S.ownIndependentMass_eq_zero_of_not_mem x hx]
    simp [collapsedPartLabel, HalfGraphMultipartite.collapsedLabel, hx]

private theorem ae_partner_missing_row_le_own_of_topology
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hcharge : ∀ᵐ x ∂μ.restrict
      (S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0}),
      S.rootChargeRow p x = -S.rootChargeRow r x)
    (htopology : ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0} →
      0 < S.rootChargeRow p q.2 →
        PhysicalRepresentative.adjacency W m q.1 q.2 = false →
          q ∈ S.sameAtomRelation) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0}),
      (∫ z in IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x, S.rootChargeRow p z ∂μ) ≤
          (S.collapsedPartLabel x).elim 0 S.originalAtomMass * (-S.rootChargeRow r x) := by
  have hsame := Measure.ae_ae_of_ae_prod
    (S.ae_universalRootDeficit_eq_on_sameAtom p hW hd hgap)
  have htop := Measure.ae_ae_of_ae_prod htopology
  filter_upwards [hcharge, ae_restrict_of_ae hsame, ae_restrict_of_ae htop,
    ae_restrict_mem ((S.measurableSet_universalPartnerCommonRegion r p).inter
      (measurableSet_lt (S.measurable_rootChargeRow r) measurable_const))]
    with x hpx hs ht hx
  let J : Set Ω := {z | (x, z) ∈ S.sameAtomRelation}
  let M := IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) x
  let dx := -S.rootChargeRow r x
  have hJ : MeasurableSet J := S.measurableSet_sameAtomRelation.preimage
    (measurable_const.prodMk measurable_id)
  have hM : MeasurableSet M := IndependentAtomCopy.measurableSet_missingSection _
    (PhysicalRepresentative.measurable_adjacency W m) x
  have hi : Integrable (S.rootChargeRow p) μ := Integrable.of_bound
    (S.measurable_rootChargeRow p).aestronglyMeasurable 3
    (Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(S.rootChargeRow_mem_Icc p z).1,
        (S.rootChargeRow_mem_Icc p z).2.trans (by norm_num)⟩))
  have hd : 0 ≤ dx := (neg_pos.mpr hx.2).le
  have hpoint : M.indicator (S.rootChargeRow p) ≤ᵐ[μ]
      J.indicator (fun _ => dx) := by
    filter_upwards [hs, ht] with z hz hzt
    by_cases hm : z ∈ M
    · rw [indicator_of_mem hm]
      by_cases hj : z ∈ J
      · rw [indicator_of_mem hj]
        have he := hz hj
        change 1 - S.rootChargeRow p x = 1 - S.rootChargeRow p z at he
        change S.rootChargeRow p z ≤ -S.rootChargeRow r x
        linarith only [he, hpx]
      · rw [indicator_of_notMem hj]
        exact le_of_not_gt (fun hp => hj (hzt hx hp hm))
    · rw [indicator_of_notMem hm]
      exact indicator_nonneg (fun _ _ => hd) z
  have hle := integral_mono_ae (hi.indicator hM) ((integrable_const dx).indicator hJ) hpoint
  rw [integral_indicator hM, integral_indicator hJ, setIntegral_const, smul_eq_mul] at hle
  rw [S.own_mass_eq_sameAtom_section x]
  exact hle

/-- A missing outside-own partner-positive recipient is ruled out by
the explicit original topology event. The only positive remainder is
the negative vertex's own original atom, with dust assigned mass zero. -/
theorem UniversalPhysicalPrimal.ae_partner_missing_row_le_own_of_topology
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (htopology : ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0} →
        0 < S.rootChargeRow p q.2 →
          PhysicalRepresentative.adjacency W m q.1 q.2 = false →
            q ∈ S.sameAtomRelation) :
    ∀ᵐ x ∂μ.restrict
      (S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0}),
      (∫ z in IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x, S.rootChargeRow p z ∂μ) ≤
          (S.collapsedPartLabel x).elim 0 S.originalAtomMass * (-S.rootChargeRow r x) :=
  S.ae_partner_missing_row_le_own_of_topology r p hW hd hgap
    (P.ae_partner_negative_charge S r p hpair hW hd hgap hN hA hAhalf hell hmargin)
    htopology

private theorem ae_negative_partner_positive_missing_sameAtom_of_bad_topology
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (htopology : ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalUpperE2BadRegion r p d c →
        q.2 ∈ S.universalUpperE2BadRegion r p d c →
          adjacencyKernel W q.1 q.2 = 0 → q ∈ S.sameAtomRelation) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0} →
        0 < S.rootChargeRow p q.2 →
          PhysicalRepresentative.adjacency W m q.1 q.2 = false →
            q ∈ S.sameAtomRelation := by
  have hApos : 0 < S.originalAtomMass r := by linarith only [hA]
  have htheta : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) := by
    have hm : (2 * (1 + m)) * S.originalAtomMass r <
        3 * (2 * (c - m * d) + m) := by nlinarith only [hmargin]
    have hmul := (lt_div_iff₀ hApos).mpr hm
    linarith only [hmul, hell.2]
  have hneutral := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_physical_adjacency r hW hd hgap hN)
  filter_upwards [htopology, hneutral,
    Measure.quasiMeasurePreserving_snd.ae
      (S.rootChargeRow_zero_off_neighborhood p hW hd hgap),
    Measure.quasiMeasurePreserving_snd.ae
      (S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN),
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support]
    with q ht hn hz hs ha hx hpositive hmissing
  have hxr : S.ρ q.1 ≠ r.val := fun h => hx.1 (Or.inl (Or.inl h))
  have hzp : q.2 ∈ S.rootNeighborhood p := by
    by_contra h
    exact (ne_of_gt hpositive) (hz h)
  have hzr : S.ρ q.2 ≠ r.val := by
    intro hr
    have hG : PhysicalRepresentative.adjacency W m q.2 q.1 = true := (hn hr).mpr hxr
    rw [PhysicalRepresentative.adjacency_symm W m, hmissing] at hG
    cases hG
  have hscore := hs hzr hzp
  have hznegative : S.rootChargeRow r q.2 < 0 := by linarith only [hscore, hpositive]
  have hxBad : q.1 ∈ S.universalUpperE2BadRegion r p d c :=
    ⟨fun h => hx.1 (Or.inl h), hx.2.trans htheta⟩
  have hzBad : q.2 ∈ S.universalUpperE2BadRegion r p d c :=
    ⟨fun h => h.elim hzr hzp.1, hznegative.trans htheta⟩
  have hzero : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 =
      (if PhysicalRepresentative.adjacency W m q.1 q.2 = true then (1 : ℝ) else 0) at ha
    rw [hmissing] at ha
    simpa only [Bool.false_eq_true, ↓reduceIte] using ha
  exact ht hxBad hzBad hzero

/-- The actual universal partner copy pays the entire original hole row.
All outside-own positive missing contributions are excluded internally by
the original saturated-score topology. -/
theorem UniversalPhysicalPrimal.ae_partner_copy_lower_row
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict
      (S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0}),
      (S.originalAtomMass r - S.originalAtomMass p -
        (S.collapsedPartLabel x).elim 0 S.originalAtomMass) * (-S.rootChargeRow r x) +
          (2 * (c - m * d) + m) ≤
            ∫ z in S.universalPartnerHoleRegion r p, chargeKernel W x z ∂μ := by
  have hbad := (P.ae_universalUpperE2Bad_missing_iff_sameAtom S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin).mono (fun _ h hx hy hz => (h hx hy).mp hz)
  have htopology := S.ae_negative_partner_positive_missing_sameAtom_of_bad_topology r p
    hpair hW hd hgap hN hA hell hmargin hbad
  filter_upwards [P.ae_partner_copy_signed_row S r p hpair hW hd hgap hN hA hAhalf
    hell hmargin, P.ae_partner_missing_row_le_own_of_topology S r p hpair hW hd hgap
      hN hA hAhalf hell hmargin htopology] with x hcopy hmissing
  nlinarith only [hcopy, hmissing]

end Erdos1017.CappedModel.SelectedHighLowStructure

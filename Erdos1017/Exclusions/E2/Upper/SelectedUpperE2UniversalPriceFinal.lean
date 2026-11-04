module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPrice
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalCopyCap
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPartnerCopy
public import Erdos1017.Exclusions.Common.E2.SelectedEmptySatE2Inventory
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalNegative
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalHighJoin
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalBadLowHoles

/-!
# Signed copy price on the partner hole

Every signed copy price is integrable on the partner hole
(`integrable_universalSignedPrice`), a single `H` deficit budget controls the
positive signed endpoint coefficient at every negative vertex, and every signed
`H` price lies below the same chord endpoint
(`universalSignedPrice_le_endpoint`).
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
private theorem disjoint_square_integral_le
    (H B O : Set Ω) (hB : MeasurableSet B)
    (hdis : Disjoint H B) (hHO : H ⊆ O) (hBO : B ⊆ O)
    (f : Ω × Ω → ℝ)
    (hfi : Integrable f ((μ.restrict O).prod (μ.restrict O)))
    (hf : 0 ≤ᵐ[(μ.restrict O).prod (μ.restrict O)] f) :
    (∫ q, f q ∂(μ.restrict H).prod (μ.restrict H)) +
      (∫ q, f q ∂(μ.restrict B).prod (μ.restrict B)) ≤
        ∫ q, f q ∂(μ.restrict O).prod (μ.restrict O) := by
  simp only [Measure.prod_restrict] at hfi hf ⊢
  have hdisSq : Disjoint (H ×ˢ H) (B ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro q hqH hqB
    exact (Set.disjoint_left.mp hdis) hqH.1 hqB.1
  have hsubH : H ×ˢ H ⊆ O ×ˢ O := by
    intro q hq
    exact ⟨hHO hq.1, hHO hq.2⟩
  have hsubB : B ×ˢ B ⊆ O ×ˢ O := by
    intro q hq
    exact ⟨hBO hq.1, hBO hq.2⟩
  have hsub : (H ×ˢ H) ∪ (B ×ˢ B) ≤ᵐ[μ.prod μ] O ×ˢ O :=
    Eventually.of_forall (fun q hq => hq.elim (fun h => hsubH h) (fun h => hsubB h))
  change IntegrableOn f (O ×ˢ O) (μ.prod μ) at hfi
  have hle := setIntegral_mono_set hfi hf hsub
  rw [setIntegral_union hdisSq (hB.prod hB)
    (hfi.mono_set hsubH) (hfi.mono_set hsubB)] at hle
  exact hle

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integral_one_sub_adjacency_eq (x : Ω) :
    (∫ z, 1 - adjacencyKernel W x z ∂μ) =
      1 - ∫ z, adjacencyKernel W x z ∂μ := by
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  rw [integral_sub (integrable_const 1) hi, integral_const, probReal_univ, one_smul]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A signed missing row splits across two disjoint measurable recipient
sections without replacing either coefficient by its positive part. -/
theorem missing_row_le_two_sections
    (M I J : Set Ω) (hM : MeasurableSet M) (hI : MeasurableSet I)
    (hJ : MeasurableSet J) (hdis : Disjoint I J)
    (hcover : M =ᵐ[μ] (M ∩ I) ∪ (M ∩ J))
    (f : Ω → ℝ) (hfi : Integrable f μ) (v w : ℝ)
    (hrowI : ∀ᵐ z ∂μ.restrict (M ∩ I), f z ≤ v)
    (hrowJ : ∀ᵐ z ∂μ.restrict (M ∩ J), f z ≤ w) :
    (∫ z in M, f z ∂μ) ≤
      v * μ.real (M ∩ I) + w * μ.real (M ∩ J) := by
  have hMI : MeasurableSet (M ∩ I) := hM.inter hI
  have hMJ : MeasurableSet (M ∩ J) := hM.inter hJ
  have hdis' : Disjoint (M ∩ I) (M ∩ J) := by
    apply Set.disjoint_left.mpr
    intro z hzI hzJ
    exact (Set.disjoint_left.mp hdis) hzI.2 hzJ.2
  have hboundI := integral_mono_ae hfi.integrableOn
    (integrable_const (μ := μ.restrict (M ∩ I)) v) hrowI
  have hboundJ := integral_mono_ae hfi.integrableOn
    (integrable_const (μ := μ.restrict (M ∩ J)) w) hrowJ
  rw [setIntegral_congr_set hcover,
    setIntegral_union hdis' hMJ hfi.integrableOn hfi.integrableOn]
  rw [setIntegral_const, smul_eq_mul] at hboundI hboundJ
  nlinarith only [hboundI, hboundJ]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalOwnMass_eq_sameAtom_section
    (S : SelectedHighLowStructure W m) (x : Ω) :
    S.universalOwnMass x = μ.real {z | (x, z) ∈ S.sameAtomRelation} := by
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

/-- On almost every original row, the whole-atom section is physically
missing. Its mass is the original atom mass, including zero-mass dust. -/
theorem ae_missing_sameAtom_section_mass
    (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ,
      μ.real (IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x ∩
          {z | (x, z) ∈ S.sameAtomRelation}) = S.universalOwnMass x := by
  let G := PhysicalRepresentative.adjacency W m
  have hzero : ∀ᵐ q ∂μ.prod μ,
      q ∈ S.sameAtomRelation → G q.1 q.2 = false := by
    filter_upwards [S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
      (hW.strict_gap_structure hd hgap).strict_support,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support]
      with q hiff hs hphys hsame
    have hM : shiftedKernel W m q.1 q.2 = 0 := hiff.mpr (Or.inl hsame)
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedKernel W m q.1 q.2 then (1 : ℝ) else 0) at hs
    rw [hM] at hs
    change adjacencyKernel W q.1 q.2 =
      (if G q.1 q.2 = true then (1 : ℝ) else 0) at hphys
    rw [hs] at hphys
    by_cases hg : G q.1 q.2 = true
    · simp [hg] at hphys
    · exact Bool.eq_false_iff.mpr hg
  have hsec := Measure.ae_ae_of_ae_prod hzero
  filter_upwards [hsec] with x hx
  have hmass : μ.real (IndependentAtomCopy.missingSection G x ∩
      {z | (x, z) ∈ S.sameAtomRelation}) =
      μ.real {z | (x, z) ∈ S.sameAtomRelation} := by
    apply measureReal_congr
    filter_upwards [hx] with z hz
    exact propext ⟨fun h => h.2, fun h => ⟨hz h, h⟩⟩
  exact hmass.trans (S.universalOwnMass_eq_sameAtom_section x).symm

/-- The rooted triangle retains the actual H deficit in the allowance
for one good common recipient, including a physical nonedge. -/
theorem ae_hole_good_charge_le_deficit
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalGoodCommonRegion r p d c)),
        chargeKernel W q.1 q.2 ≤
          max (S.universalRootDeficit r q.1 -
            (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) 0 := by
  let H := S.universalPartnerHoleRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  let G := PhysicalRepresentative.adjacency W m
  have hrestricted : (μ.restrict H).prod (μ.restrict Good) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hrestricted (S.ae_universal_root_triangle r hW hd hgap hN),
    ae_mono hrestricted
      (PhysicalRepresentative.charge_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support),
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)),
    Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (S.measurableSet_universalGoodCommonRegion r p d c))]
    with q htri hY hxH hzGood
  have hzθ : θ ≤ S.rootChargeRow r q.2 := by
    apply le_of_not_gt
    intro hh
    exact hzGood.2 ⟨by
      intro hhead
      exact hzGood.1 (Or.inl hhead), hh⟩
  have hxi : S.ρ q.1 ≠ r.val := by
    intro hh
    exact hxH (Or.inl (Or.inl hh))
  have hzi : S.ρ q.2 ≠ r.val := by
    intro hh
    exact hzGood.1 (Or.inl (Or.inl hh))
  by_cases hG : G q.1 q.2 = true
  · have ht := htri hxi hzi hG
    rw [hY] at ht
    have hbound : chargeKernel W q.1 q.2 ≤
        S.universalRootDeficit r q.1 - θ := by
      unfold universalRootDeficit
      linarith [hzθ]
    exact hbound.trans (le_max_left _ _)
  · have hz := PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2
      (Bool.eq_false_iff.mpr hG)
    rw [← hY, hz]
    exact le_max_right _ _

/-- The actual HIGH good recipient joins H, so its triangle allowance
retains the signed value `D_h-θ`, even when that value is negative. -/
theorem ae_hole_high_good_charge_le_signed
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hell : -m < 1) :
    ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalHighGoodRegion r p d c)),
        chargeKernel W q.1 q.2 ≤
          S.universalRootDeficit r q.1 -
            (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) := by
  let H := S.universalPartnerHoleRegion r p
  let HighGood := S.universalHighGoodRegion r p d c
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hrest : (μ.restrict H).prod (μ.restrict HighGood) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hjoin := S.ae_universalHole_highGood_join r p hpair hW hd hgap hell
  have hphysical := PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [ae_mono hrest hjoin,
    ae_mono hrest (S.ae_universal_root_triangle r hW hd hgap hN),
    ae_mono hrest hphysical,
    ae_mono hrest (PhysicalRepresentative.charge_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support),
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)),
    Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (S.measurableSet_universalHighGoodRegion r p d c))]
    with q hjoin htri hphysical hY hxH hzGood
  have hA : adjacencyKernel W q.1 q.2 = 1 := hjoin hxH hzGood
  have hG : PhysicalRepresentative.adjacency W m q.1 q.2 = true := by
    change adjacencyKernel W q.1 q.2 = _ at hphysical
    rw [hA] at hphysical
    cases h : PhysicalRepresentative.adjacency W m q.1 q.2
    · simp [h] at hphysical
    · rfl
  have hzθ : θ ≤ S.rootChargeRow r q.2 := by
    apply le_of_not_gt
    intro hh
    exact hzGood.1.2 ⟨by
      intro hhead
      exact hzGood.1.1 (Or.inl hhead), hh⟩
  have hxi : S.ρ q.1 ≠ r.val := by
    intro hh
    exact hxH (Or.inl (Or.inl hh))
  have hzi : S.ρ q.2 ≠ r.val := by
    intro hh
    exact hzGood.1.1 (Or.inl (Or.inl hh))
  have ht := htri hxi hzi hG
  rw [hY] at ht
  unfold universalRootDeficit
  linarith [hzθ]

/-- A negative common vertex with positive own mass carries a whole
original atom inside the same negative region. -/
theorem UniversalPhysicalPrimal.ae_negative_whole_fiber
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      0 < S.universalOwnMass x →
        ∃ i : S.I, S.ρ x = i.val ∧
          (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val},
            z ∈ S.universalNegativeRegion r p ∧
              S.universalOwnMass z = S.universalOwnMass x) := by
  let B := S.universalNegativeRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  let : Countable S.I := S.hI.to_subtype
  have hallr : ∀ᵐ x ∂μ, ∀ i : S.I, S.ρ x = i.val →
      S.rootChargeRow r x =
        S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl i) := by
    apply ae_all_iff.mpr
    intro i
    exact (ae_restrict_iff' (S.hfibers i.val i.property).1).mp
      (S.ae_atomic_rootChargeRow r i hW hd hgap)
  have hallp : ∀ᵐ x ∂μ, ∀ i : S.I, S.ρ x = i.val →
      S.rootChargeRow p x =
        S.coveredCountableBoundaryCoefficient (Sum.inl p) (Sum.inl i) := by
    apply ae_all_iff.mpr
    intro i
    exact (ae_restrict_iff' (S.hfibers i.val i.property).1).mp
      (S.ae_atomic_rootChargeRow p i hW hd hgap)
  have hpartner := P.ae_universalNegative_partner_charge S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  apply (ae_restrict_iff' hB).mpr
  filter_upwards [hallr, hallp,
    (ae_restrict_iff' hB).mp hpartner,
    S.rootChargeRow_zero_off_neighborhood p hW hd hgap]
    with x hrowr hrowp hpartner hoff hxB hown
  have hi : S.ρ x ∈ S.I := by
    by_contra hn
    have hlabel : S.collapsedPartLabel x = none := by
      simp [collapsedPartLabel, HalfGraphMultipartite.collapsedLabel, hn]
    simp [universalOwnMass, hlabel] at hown
  let i : S.I := ⟨S.ρ x, hi⟩
  have hxI : S.ρ x = i.val := rfl
  have hri := hrowr i hxI
  have hpi := hrowp i hxI
  have hβp : 0 < S.rootChargeRow p x := by
    have hβr : S.rootChargeRow r x < 0 := hxB.2
    linarith [hpartner hxB]
  have hir : i ≠ r := by
    intro he
    exact hxB.1 (Or.inl (Or.inl (hxI.trans (congrArg Subtype.val he))))
  have hip : i ≠ p := by
    intro he
    exact hxB.1 (Or.inl (Or.inr (hxI.trans (congrArg Subtype.val he))))
  refine ⟨i, hxI, ?_⟩
  apply (ae_restrict_iff' (S.hfibers i.val i.property).1).mpr
  filter_upwards [hallr, hallp,
    S.rootChargeRow_zero_off_neighborhood p hW hd hgap]
    with z hzr hzp hoffz hzI
  have hβr : S.rootChargeRow r z < 0 := by
    rw [hzr i hzI, ← hri]
    exact hxB.2
  have hβp : 0 < S.rootChargeRow p z := by
    rw [hzp i hzI, ← hpi]
    exact hβp
  have hzN : z ∈ S.rootNeighborhood p := by
    by_contra hn
    have := hoffz hn
    linarith
  have hzU : z ∈ S.universalPartnerCommonRegion r p := by
    change z ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪
      S.universalPartnerHoleRegion r p
    intro h
    rcases h with (hr | hp) | hH
    · exact hir (Subtype.ext (hzI.symm.trans hr))
    · exact hip (Subtype.ext (hzI.symm.trans hp))
    · exact hH (by
        change z ∈ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪
          S.rootNeighborhood p
        exact Or.inr hzN)
  have hlabelx : S.collapsedPartLabel x = some i := by
    simp [collapsedPartLabel, HalfGraphMultipartite.collapsedLabel, hi, i]
  have hlabelz : S.collapsedPartLabel z = some i := by
    simp [collapsedPartLabel, HalfGraphMultipartite.collapsedLabel, hzI, i.property]
  exact ⟨⟨hzU, hβr⟩, by simp [universalOwnMass, hlabelx, hlabelz]⟩

/-- Every negative common atom spends its own square in the single
original bad-region atom budget. -/
theorem UniversalPhysicalPrimal.ae_negative_own_mass_sq_le_badSquareMoment
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      (S.universalOwnMass x) ^ 2 ≤ S.universalBadSquareMoment r p := by
  let B := S.universalNegativeRegion r p
  have hatom := P.ae_negative_whole_fiber S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  filter_upwards [hatom] with x hx
  by_cases hpos : 0 < S.universalOwnMass x
  · obtain ⟨i, hxi, hwhole⟩ := hx hpos
    let I : Set Ω := {z | S.ρ z = i.val}
    have hI : MeasurableSet I := (S.hfibers i.val i.property).1
    have hIB : I ≤ᵐ[μ] B :=
      (ae_restrict_iff' hI).mp (hwhole.mono (fun _ hz => hz.1))
    have hmass : S.universalOwnMass x = μ.real I := by
      rw [S.universalOwnMass_eq_sameAtom_section x]
      congr 1
      ext z
      change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔ S.ρ z = i.val
      exact ⟨fun hz => hz.1.symm.trans hxi,
        fun hz => ⟨hxi.trans hz.symm, hxi ▸ i.property⟩⟩
    have hconst : S.universalOwnMass =ᵐ[μ.restrict I] fun _ => μ.real I :=
      hwhole.mono (fun _ hz => hz.2.trans hmass)
    have hbound := UniversalSignedPrice.atom_square_le_total μ B I
      S.universalOwnMass S.integrable_universalOwnMass.integrableOn
      (Eventually.of_forall (fun z => (S.universalOwnMass_mem_Icc z).1))
      hIB hconst
    rw [hmass]
    exact hbound
  · have hzero : S.universalOwnMass x = 0 :=
      le_antisymm (le_of_not_gt hpos) (S.universalOwnMass_mem_Icc x).1
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)]
    unfold universalBadSquareMoment
    exact integral_nonneg (fun z => (S.universalOwnMass_mem_Icc z).1)

theorem UniversalPhysicalPrimal.ae_negative_own_mass_le_sqrt_badSquareMoment
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x ≤ Real.sqrt (S.universalBadSquareMoment r p) := by
  filter_upwards [P.ae_negative_own_mass_sq_le_badSquareMoment S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin] with x hx
  exact (Real.le_sqrt (S.universalOwnMass_mem_Icc x).1
    (by unfold universalBadSquareMoment
        exact integral_nonneg (fun z => (S.universalOwnMass_mem_Icc z).1))).mpr hx

/-- The actual missing mass from a negative common point into the
original good common region. -/
def universalGoodMissingMass (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) (x : Ω) : ℝ :=
  ∫ z in S.universalGoodCommonRegion r p d c,
    1 - adjacencyKernel W x z ∂μ

/-- The negative charge weighted by the original mass of its own
whole atom; diffuse dust contributes zero. -/
def universalWeightedOwnMoment (S : SelectedHighLowStructure W m)
    (r p : S.I) : ℝ :=
  ∫ x in S.universalNegativeRegion r p,
    S.universalOwnMass x * (-S.rootChargeRow r x) ∂μ

/-- The one shared outside-own missing allowance weighted by the same
negative original charge. -/
def universalWeightedGoodMissingMoment (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) : ℝ :=
  ∫ x in S.universalNegativeRegion r p,
    S.universalGoodMissingMass r p d c x * (-S.rootChargeRow r x) ∂μ

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem aestronglyMeasurable_universalGoodMissingMass
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    AEStronglyMeasurable (S.universalGoodMissingMass r p d c) μ := by
  let Good := S.universalGoodCommonRegion r p d c
  have hf : AEStronglyMeasurable (fun q : Ω × Ω =>
      (1 : ℝ) - adjacencyKernel W q.1 q.2) (μ.prod μ) :=
    aestronglyMeasurable_const.sub (adjacencyKernel_measurable W)
  have hprod : μ.prod (μ.restrict Good) ≤ μ.prod μ :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hm := (hf.mono_measure hprod).integral_prod_right'
  change AEStronglyMeasurable (S.universalGoodMissingMass r p d c) μ at hm
  exact hm

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalGoodMissingMass_nonneg
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) (x : Ω) :
    0 ≤ S.universalGoodMissingMass r p d c x := by
  unfold universalGoodMissingMass
  exact integral_nonneg (fun z => by
    have hz := adjacency_moment_mem W (x, z)
    change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at hz
    exact sub_nonneg.mpr hz.2)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem ae_universalGoodMissingMass_le_mass
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    ∀ᵐ x ∂μ, S.universalGoodMissingMass r p d c x ≤
      μ.real (S.universalGoodCommonRegion r p d c) := by
  let Good := S.universalGoodCommonRegion r p d c
  have hprod : μ.prod (μ.restrict Good) ≤ μ.prod μ :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hmeas := (adjacencyKernel_measurable W).mono_measure hprod
  filter_upwards [hmeas.prodMk_left] with x hx
  have hint : IntegrableOn (fun z => 1 - adjacencyKernel W x z) Good μ := by
    apply Integrable.of_bound (aestronglyMeasurable_const.sub hx) 1
    exact Eventually.of_forall (fun z => by
      have hz := adjacency_moment_mem W (x, z)
      change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at hz
      change ‖(1 : ℝ) - adjacencyKernel W x z‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hz.2)]
      linarith [hz.1])
  have hle : (fun z : Ω => 1 - adjacencyKernel W x z) ≤ᵐ[μ.restrict Good]
      (fun _ => (1 : ℝ)) :=
    Eventually.of_forall (fun z => by
      have hz := adjacency_moment_mem W (x, z)
      change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at hz
      linarith [hz.1])
  have h := integral_mono_ae hint (integrable_const 1) hle
  simpa only [universalGoodMissingMass, Good, setIntegral_const, smul_eq_mul,
    mul_one] using h

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem integrable_universalGoodMissingMass
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    Integrable (S.universalGoodMissingMass r p d c) μ := by
  apply Integrable.of_bound
    (S.aestronglyMeasurable_universalGoodMissingMass r p d c) 1
  filter_upwards [S.ae_universalGoodMissingMass_le_mass r p d c] with x hx
  have hnonneg := S.universalGoodMissingMass_nonneg r p d c x
  have hmass : μ.real (S.universalGoodCommonRegion r p d c) ≤ 1 := measureReal_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
theorem integrable_universalWeightedOwn
    (S : SelectedHighLowStructure W m) (r : S.I) :
    Integrable (fun x => S.universalOwnMass x * (-S.rootChargeRow r x)) μ := by
  apply Integrable.of_bound
    (S.measurable_universalOwnMass.mul (S.measurable_rootChargeRow r).neg).aestronglyMeasurable 3
  exact Eventually.of_forall (fun x => by
    have ha := S.universalOwnMass_mem_Icc x
    have hb := S.rootChargeRow_mem_Icc r x
    change ‖S.universalOwnMass x * (-S.rootChargeRow r x)‖ ≤ 3
    rw [Real.norm_eq_abs]
    have ha' : |S.universalOwnMass x| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], ha.2⟩
    have hb' : |S.rootChargeRow r x| ≤ 3 := abs_le.mpr ⟨hb.1, by linarith [hb.2]⟩
    calc
      |S.universalOwnMass x * (-S.rootChargeRow r x)| =
          |S.universalOwnMass x| * |S.rootChargeRow r x| := by rw [abs_mul, abs_neg]
      _ ≤ 1 * 3 := mul_le_mul ha' hb' (abs_nonneg _) (by norm_num)
      _ = 3 := by norm_num)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem integrable_universalWeightedGoodMissing
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    Integrable (fun x => S.universalGoodMissingMass r p d c x *
      (-S.rootChargeRow r x)) μ := by
  apply Integrable.of_bound
    ((S.aestronglyMeasurable_universalGoodMissingMass r p d c).mul
      (S.measurable_rootChargeRow r).neg.aestronglyMeasurable) 3
  filter_upwards [S.ae_universalGoodMissingMass_le_mass r p d c] with x hx
  have ha : 0 ≤ S.universalGoodMissingMass r p d c x :=
    S.universalGoodMissingMass_nonneg r p d c x
  have ha' : S.universalGoodMissingMass r p d c x ≤ 1 :=
    hx.trans measureReal_le_one
  have hb := S.rootChargeRow_mem_Icc r x
  change ‖S.universalGoodMissingMass r p d c x *
    (-S.rootChargeRow r x)‖ ≤ 3
  rw [Real.norm_eq_abs]
  have hfa : |S.universalGoodMissingMass r p d c x| ≤ 1 :=
    abs_le.mpr ⟨by linarith, ha'⟩
  have hfb : |S.rootChargeRow r x| ≤ 3 :=
    abs_le.mpr ⟨hb.1, by linarith [hb.2]⟩
  calc
    |S.universalGoodMissingMass r p d c x * (-S.rootChargeRow r x)| =
        |S.universalGoodMissingMass r p d c x| * |S.rootChargeRow r x| := by
          rw [abs_mul, abs_neg]
    _ ≤ 1 * 3 := mul_le_mul hfa hfb (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  in
/-- The own-atom weighted allowance is paid once by the same negative
charge mass, at any actual almost-everywhere own-mass cap. -/
theorem universalWeightedOwnMoment_le
    (S : SelectedHighLowStructure W m) (r p : S.I) (z : ℝ)
    (hz : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x ≤ z) :
    S.universalWeightedOwnMoment r p ≤ z * S.universalNegativeChargeMass r p := by
  let B := S.universalNegativeRegion r p
  have hpoint : ∀ᵐ x ∂μ.restrict B,
      S.universalOwnMass x * (-S.rootChargeRow r x) ≤
        z * (-S.rootChargeRow r x) := by
    filter_upwards [hz, ae_restrict_mem (S.measurableSet_universalNegativeRegion r p)]
      with x hx hB
    exact mul_le_mul_of_nonneg_right hx (neg_nonneg.mpr hB.2.le)
  have h := integral_mono_ae
    ((S.integrable_universalWeightedOwn r).integrableOn)
    ((S.integrable_universalNegativeCharge r).integrableOn.const_mul z) hpoint
  change S.universalWeightedOwnMoment r p ≤
    ∫ x in B, z * (-S.rootChargeRow r x) ∂μ at h
  rw [integral_const_mul] at h
  exact h

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The own atom and good common missing sections spend one weighted
allowance; neither is counted again in a second inventory. -/
theorem universalWeightedHoleInventory_le
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c R : ℝ)
    (hcap : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤ R) :
    S.universalWeightedOwnMoment r p +
      S.universalWeightedGoodMissingMoment r p d c ≤
        R * S.universalNegativeChargeMass r p := by
  let B := S.universalNegativeRegion r p
  have hown := (S.integrable_universalWeightedOwn r).integrableOn (s := B)
  have hgood := (S.integrable_universalWeightedGoodMissing r p d c).integrableOn (s := B)
  have hneg := (S.integrable_universalNegativeCharge r).integrableOn (s := B)
  have hpoint : ∀ᵐ x ∂μ.restrict B,
      S.universalOwnMass x * (-S.rootChargeRow r x) +
        S.universalGoodMissingMass r p d c x * (-S.rootChargeRow r x) ≤
          R * (-S.rootChargeRow r x) := by
    filter_upwards [hcap, ae_restrict_mem (S.measurableSet_universalNegativeRegion r p)]
      with x hx hB
    calc
      _ = (S.universalOwnMass x + S.universalGoodMissingMass r p d c x) *
          (-S.rootChargeRow r x) := by ring
      _ ≤ R * (-S.rootChargeRow r x) :=
        mul_le_mul_of_nonneg_right hx (neg_nonneg.mpr hB.2.le)
  have h := integral_mono_ae (hown.add hgood) (hneg.const_mul R) hpoint
  change (∫ x in B, S.universalOwnMass x * (-S.rootChargeRow r x) +
    S.universalGoodMissingMass r p d c x * (-S.rootChargeRow r x) ∂μ) ≤
      ∫ x in B, R * (-S.rootChargeRow r x) ∂μ at h
  rw [integral_add hown hgood, integral_const_mul] at h
  exact h

/-- The original missing row pays both its own whole atom and its
good-common missing section, with no double counting. -/
theorem UniversalPhysicalPrimal.ae_negative_own_add_good_le_missing
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤
        ∫ z, 1 - adjacencyKernel W x z ∂μ := by
  let B := S.universalNegativeRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hGood : MeasurableSet Good := S.measurableSet_universalGoodCommonRegion r p d c
  have hδ : 0 ≤ 1 + m := by linarith [hell.2]
  have hsubset := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (by linarith : 0 < S.originalAtomMass r) hmargin hδ
  have hdis : Disjoint B Good := by
    apply Set.disjoint_left.mpr
    intro z hz hg
    exact hg.2 (hsubset hz)
  have hwhole := P.ae_negative_whole_fiber S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hzero : ∀ᵐ q ∂μ.prod μ,
      q ∈ S.sameAtomRelation → adjacencyKernel W q.1 q.2 = 0 := by
    filter_upwards [S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
      (hW.strict_gap_structure hd hgap).strict_support] with q hiff hs hsame
    have hm := hiff.mpr (Or.inl hsame)
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedKernel W m q.1 q.2 then 1 else 0) at hs
    rw [hm] at hs
    simpa only [lt_irrefl, ↓reduceIte] using hs
  have hsections := Measure.ae_ae_of_ae_prod hzero
  apply (ae_restrict_iff' hB).mpr
  filter_upwards [hsections, (ae_restrict_iff' hB).mp hwhole] with x hx hwhole hxB
  let f : Ω → ℝ := fun z => 1 - adjacencyKernel W x z
  have hfi : Integrable f μ := by
    have hstrong : StronglyMeasurable (adjacencyKernel W x) :=
      (W.stronglyMeasurable_moment
        CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
          (measurable_const.prodMk measurable_id)
    apply Integrable.of_bound (stronglyMeasurable_const.sub hstrong).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      have hz := adjacency_moment_mem W (x, z)
      change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at hz
      change ‖f z‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hz.2)]
      linarith [hz.1])
  have hfnonneg : 0 ≤ᵐ[μ] f := Eventually.of_forall (fun z => by
    dsimp [f]
    exact sub_nonneg.mpr (adjacency_moment_mem W (x, z)).2)
  by_cases hown : 0 < S.universalOwnMass x
  · obtain ⟨i, hxi, hfiber⟩ := hwhole hxB hown
    let I : Set Ω := {z | S.ρ z = i.val}
    let J := I ∩ B
    have hI : MeasurableSet I := (S.hfibers i.val i.property).1
    have hJ : MeasurableSet J := hI.inter hB
    have hJGood : Disjoint J Good :=
      Set.disjoint_of_subset_left (by intro z hz; exact hz.2) hdis
    have hownEq : S.universalOwnMass x = μ.real J := by
      have hmass : S.universalOwnMass x = μ.real I := by
        rw [S.universalOwnMass_eq_sameAtom_section x]
        congr 1
        ext z
        change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔ S.ρ z = i.val
        exact ⟨fun hz => hz.1.symm.trans hxi,
          fun hz => ⟨hxi.trans hz.symm, hxi ▸ i.property⟩⟩
      rw [hmass]
      apply measureReal_congr
      filter_upwards [(ae_restrict_iff' hI).mp (hfiber.mono (fun _ hz => hz.1))]
        with z hz
      exact propext ⟨fun h => ⟨h, hz h⟩, fun h => h.1⟩
    have hfJ : (∫ z in J, f z ∂μ) = μ.real J := by
      have hzeroJ : ∀ᵐ z ∂μ.restrict J, f z = 1 := by
        filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem hJ] with z hz hzJ
        have hsame : (x, z) ∈ S.sameAtomRelation :=
          ⟨hxi.trans hzJ.1.symm, hxi ▸ i.property⟩
        dsimp [f]
        rw [hz hsame]
        ring
      rw [integral_congr_ae hzeroJ, setIntegral_const]
      simp
    have hle : (∫ z in J ∪ Good, f z ∂μ) ≤ ∫ z, f z ∂μ :=
      setIntegral_le_integral hfi hfnonneg
    rw [setIntegral_union hJGood hGood hfi.integrableOn hfi.integrableOn,
      hfJ] at hle
    simpa only [universalGoodMissingMass, Good, hownEq, f] using hle
  · have hz : S.universalOwnMass x = 0 :=
      le_antisymm (le_of_not_gt hown) (S.universalOwnMass_mem_Icc x).1
    have hle : (∫ z in Good, f z ∂μ) ≤ ∫ z, f z ∂μ :=
      setIntegral_le_integral hfi hfnonneg
    simpa only [universalGoodMissingMass, Good, hz, zero_add, f] using hle

/-- The actual missing row inside `universalNegativeRegion` has mass exactly equal
to the original whole atom of its source; diffuse dust contributes zero. -/
theorem UniversalPhysicalPrimal.ae_negative_missing_row_eq_own
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      (∫ z in S.universalNegativeRegion r p,
        1 - adjacencyKernel W x z ∂μ) = S.universalOwnMass x := by
  let B := S.universalNegativeRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hsubset := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (by linarith : 0 < S.originalAtomMass r) hmargin (by linarith [hell.2] : 0 ≤ 1 + m)
  have hzero := P.ae_universalUpperE2Bad_missing_iff_sameAtom S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hsec := Measure.ae_ae_of_ae_prod hzero
  have hs := Measure.ae_ae_of_ae_prod
    (hW.strict_gap_structure hd hgap).strict_support
  have hwhole := P.ae_negative_whole_fiber S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  apply (ae_restrict_iff' hB).mpr
  filter_upwards [hsec, hs, (ae_restrict_iff' hB).mp hwhole]
    with x hx hsx hwhole hxB
  let Same : Set Ω := {z | (x, z) ∈ S.sameAtomRelation}
  have hSame : MeasurableSet Same :=
    S.measurableSet_sameAtomRelation.preimage (measurable_const.prodMk measurable_id)
  have hrow : ∀ᵐ z ∂μ.restrict B,
      1 - adjacencyKernel W x z = Same.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_of_ae hsx, ae_restrict_mem hB]
      with z hz hsupport hzB
    have heq := hz (hsubset hxB) (hsubset hzB)
    by_cases hsame : z ∈ Same
    · have hG : adjacencyKernel W x z = 0 := heq.mpr hsame
      simp [indicator_of_mem hsame, hG]
    · have hG : adjacencyKernel W x z = 1 := by
        have hn : adjacencyKernel W x z ≠ 0 := fun h => hsame (heq.mp h)
        change adjacencyKernel W x z =
          if 0 < shiftedKernel W m x z then 1 else 0 at hsupport
        by_cases hk : 0 < shiftedKernel W m x z
        · simpa only [ite_eq_left hk] using hsupport
        · have hz : adjacencyKernel W x z = 0 := by
            simpa only [ite_eq_right hk] using hsupport
          exact False.elim (hn hz)
      simp [indicator_of_notMem hsame, hG]
  have hmass : μ.real (B ∩ Same) = S.universalOwnMass x := by
    by_cases hpos : 0 < S.universalOwnMass x
    · obtain ⟨i, hxi, hfiber⟩ := hwhole hxB hpos
      have hSameEq : Same = {z | S.ρ z = i.val} := by
        ext z
        change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔ S.ρ z = i.val
        exact ⟨fun h => h.1.symm.trans hxi,
          fun h => ⟨hxi.trans h.symm, hxi ▸ i.property⟩⟩
      rw [hSameEq]
      have hI := (S.hfibers i.val i.property).1
      have heq : μ.real (B ∩ {z | S.ρ z = i.val}) =
          μ.real {z | S.ρ z = i.val} := by
        apply measureReal_congr
        filter_upwards [(ae_restrict_iff' hI).mp (hfiber.mono (fun _ h => h.1))]
          with z hz
        exact propext ⟨fun h => h.2, fun h => ⟨hz h, h⟩⟩
      rw [heq, ← hSameEq]
      exact (S.universalOwnMass_eq_sameAtom_section x).symm
    · have hzero : S.universalOwnMass x = 0 :=
        le_antisymm (le_of_not_gt hpos) (S.universalOwnMass_mem_Icc x).1
      have hle : μ.real (B ∩ Same) ≤ μ.real Same :=
        measureReal_mono (inter_subset_right)
      rw [← S.universalOwnMass_eq_sameAtom_section x, hzero] at hle
      exact le_antisymm hle measureReal_nonneg |>.trans hzero.symm
  calc
    (∫ z in B, 1 - adjacencyKernel W x z ∂μ) =
        ∫ z in B, Same.indicator (fun _ => (1 : ℝ)) z ∂μ :=
          integral_congr_ae hrow
    _ = μ.real (B ∩ Same) := by
      rw [setIntegral_indicator hSame, setIntegral_const]
      simp
    _ = S.universalOwnMass x := hmass

/-- The original negative-region atom budget is exactly its actual
missing-pair integral, including zero-mass diffuse dust. -/
theorem UniversalPhysicalPrimal.negative_square_eq_badSquareMoment
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    (∫ q, 1 - adjacencyKernel W q.1 q.2
      ∂(μ.restrict (S.universalNegativeRegion r p)).prod
        (μ.restrict (S.universalNegativeRegion r p))) =
          S.universalBadSquareMoment r p := by
  let B := S.universalNegativeRegion r p
  let f : Ω × Ω → ℝ := fun q => 1 - adjacencyKernel W q.1 q.2
  have hprod : (μ.restrict B).prod (μ.restrict B) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hfi : Integrable f ((μ.restrict B).prod (μ.restrict B)) := by
    apply Integrable.of_bound
      ((aestronglyMeasurable_const.sub (adjacencyKernel_measurable W)).mono_measure
        hprod) 1
    exact Eventually.of_forall (fun q => by
      have h := adjacency_moment_mem W q
      change adjacencyKernel W q.1 q.2 ∈ Icc (0 : ℝ) 1 at h
      change ‖f q‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]
      linarith [h.1])
  rw [integral_prod f hfi]
  have hrow := P.ae_negative_missing_row_eq_own S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  exact integral_congr_ae hrow

/-- The original H and negative-common atom budgets occupy disjoint
rectangles in one outside-head missing-density inventory. -/
theorem UniversalPhysicalPrimal.hole_add_bad_square_le_original_missing
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    S.universalHoleSquareMoment r p + S.universalBadSquareMoment r p ≤
      1 - 2 * d - (S.originalAtomMass r) ^ 2 - (S.originalAtomMass p) ^ 2 -
        2 * S.originalAtomMass p * μ.real (S.universalPartnerHoleRegion r p) := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalNegativeRegion r p
  let O := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ
  let f : Ω × Ω → ℝ := fun q => 1 - adjacencyKernel W q.1 q.2
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hO : MeasurableSet O :=
    ((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl
  have hHO : H ⊆ O := by
    intro x hx hhead
    exact hx (Or.inl hhead)
  have hBO : B ⊆ O := by
    intro x hx hhead
    exact hx.1 (Or.inl hhead)
  have hdis : Disjoint H B := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.1 (Or.inr hx)
  have hfull : Integrable f (μ.prod μ) := by
    apply Integrable.of_bound (aestronglyMeasurable_const.sub
      (adjacencyKernel_measurable W)) 1
    exact Eventually.of_forall (fun q => by
      have ha := adjacency_moment_mem W q
      change adjacencyKernel W q.1 q.2 ∈ Icc (0 : ℝ) 1 at ha
      change ‖f q‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha.2)]
      linarith [ha.1])
  have hfnonneg : 0 ≤ᵐ[μ.prod μ] f := Eventually.of_forall (fun q =>
    sub_nonneg.mpr (adjacency_moment_mem W q).2)
  have hrest : Integrable f ((μ.restrict O).prod (μ.restrict O)) :=
    hfull.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have hrestnonneg : 0 ≤ᵐ[(μ.restrict O).prod (μ.restrict O)] f :=
    ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hfnonneg
  have hsplit := disjoint_square_integral_le H B O hB hdis hHO hBO f hrest hrestnonneg
  have hHsq : (∫ q, f q ∂(μ.restrict H).prod (μ.restrict H)) =
      S.universalHoleSquareMoment r p := by
    have hi := hfull.mono_measure
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self :
        (μ.restrict H).prod (μ.restrict H) ≤ μ.prod μ)
    rw [integral_prod f hi]
    rfl
  have hBsq : (∫ q, f q ∂(μ.restrict B).prod (μ.restrict B)) =
      S.universalBadSquareMoment r p :=
    P.negative_square_eq_badSquareMoment S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin
  have hOphys := (S.empty_sat_deleted_partner_inventory r p hpair hW hd hgap hN).2.2.1
  have hOsq : (∫ q, f q ∂(μ.restrict O).prod (μ.restrict O)) =
      1 - 2 * d - (S.originalAtomMass r) ^ 2 - (S.originalAtomMass p) ^ 2 -
        2 * S.originalAtomMass p * μ.real H := by
    have hprod : (μ.restrict O).prod (μ.restrict O) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    have heq := ae_mono hprod
      (PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support)
    have hint : (∫ q, f q ∂(μ.restrict O).prod (μ.restrict O)) =
        ∫ q, (1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true
          then (1 : ℝ) else 0) ∂(μ.restrict O).prod (μ.restrict O) := by
      apply integral_congr_ae
      filter_upwards [heq] with q hq
      change adjacencyKernel W q.1 q.2 = _ at hq
      simp only [f, hq]
    rw [hint]
    simpa only [O, H, originalAtomMass] using hOphys
  rw [hHsq, hBsq, hOsq] at hsplit
  exact hsplit

/-- Integrating the genuine H-row missing-capacity estimate gives
the same H×H square budget used by the reciprocal price. -/
theorem hole_square_le_capacity_mul_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    S.universalHoleSquareMoment r p ≤
      (1 - 2 * S.originalAtomMass r - S.originalAtomMass p) *
        μ.real (S.universalPartnerHoleRegion r p) := by
  let H := S.universalPartnerHoleRegion r p
  have hcap := S.ae_hole_missing_mass_le_capacity r p hpair hW hd hgap hell hN
  have hi := (S.integrable_universalPartnerHoleMissingMass r p).integrableOn (s := H)
  have h := integral_mono_ae hi
    (integrable_const (μ := μ.restrict H)
      (1 - 2 * S.originalAtomMass r - S.originalAtomMass p)) hcap
  rw [setIntegral_const, smul_eq_mul] at h
  simpa only [universalHoleSquareMoment, mul_comm] using h

/-- The actual signed bad-row degree cap pays the same own-atom and
good-common missing allowance that appears in the copy price. -/
theorem UniversalPhysicalPrimal.ae_negative_shared_hole_cap
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hu : μ.real (S.universalPartnerCommonRegion r p) <
      1 - 2 * S.originalAtomMass r) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤
        min (1 - 3 * S.originalAtomMass r + S.originalAtomMass p)
          ((1 - μ.real (S.universalPartnerCommonRegion r p) +
              2 * m * S.originalAtomMass r - 3 * (2 * (c - m * d) + m)) / (-m)) := by
  filter_upwards [P.ae_negative_own_add_good_le_missing S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin,
    P.ae_universal_upperE2_negative_missing_le S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin hu] with x hx hcap
  rw [integral_one_sub_adjacency_eq] at hx
  exact hx.trans hcap

theorem UniversalPhysicalPrimal.weighted_hole_inventory_le_actual
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hu : μ.real (S.universalPartnerCommonRegion r p) <
      1 - 2 * S.originalAtomMass r) :
    S.universalWeightedOwnMoment r p +
      S.universalWeightedGoodMissingMoment r p d c ≤
        (min (1 - 3 * S.originalAtomMass r + S.originalAtomMass p)
          ((1 - μ.real (S.universalPartnerCommonRegion r p) +
              2 * m * S.originalAtomMass r - 3 * (2 * (c - m * d) + m)) / (-m))) *
          S.universalNegativeChargeMass r p :=
  S.universalWeightedHoleInventory_le r p d c _
    (P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN hA hAhalf
      hell hmargin hu)

/-- The negative square has at most the square of its original mass;
this uses the actual missing-pair representation, including dust. -/
theorem UniversalPhysicalPrimal.badSquareMoment_le_negative_mass_sq
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    S.universalBadSquareMoment r p ≤
      (μ.real (S.universalNegativeRegion r p)) ^ 2 := by
  let B := S.universalNegativeRegion r p
  let f : Ω × Ω → ℝ := fun q => 1 - adjacencyKernel W q.1 q.2
  have hprod : (μ.restrict B).prod (μ.restrict B) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hfi : Integrable f ((μ.restrict B).prod (μ.restrict B)) := by
    apply Integrable.of_bound
      ((aestronglyMeasurable_const.sub (adjacencyKernel_measurable W)).mono_measure
        hprod) 1
    exact Eventually.of_forall (fun q => by
      have h := adjacency_moment_mem W q
      change adjacencyKernel W q.1 q.2 ∈ Icc (0 : ℝ) 1 at h
      change ‖f q‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]
      linarith [h.1])
  have hbound : ∀ᵐ q ∂(μ.restrict B).prod (μ.restrict B), f q ≤ 1 :=
    Eventually.of_forall (fun q => by
      have hG : 0 ≤ adjacencyKernel W q.1 q.2 :=
        (adjacency_moment_mem W q).1
      change 1 - adjacencyKernel W q.1 q.2 ≤ 1
      linarith only [hG])
  have h := integral_mono_ae hfi (integrable_const (1 : ℝ)) hbound
  rw [P.negative_square_eq_badSquareMoment S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin, integral_const, smul_eq_mul,
    ← Set.univ_prod_univ, measureReal_prod_prod] at h
  rw [measureReal_restrict_apply_univ] at h
  simpa only [mul_one, pow_two, B] using h

/-- The square-root atom radius is no larger than the actual negative
region, hence no larger than its containing common region. -/
theorem UniversalPhysicalPrimal.sqrt_badSquareMoment_le_common_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    Real.sqrt (S.universalBadSquareMoment r p) ≤
      μ.real (S.universalPartnerCommonRegion r p) := by
  let B := S.universalNegativeRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hn : 0 ≤ μ.real B := measureReal_nonneg
  have hq : 0 ≤ S.universalBadSquareMoment r p :=
    integral_nonneg (fun x => (S.universalOwnMass_mem_Icc x).1)
  have hsq := P.badSquareMoment_le_negative_mass_sq S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin
  have hsqrt : Real.sqrt (S.universalBadSquareMoment r p) ≤ μ.real B := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg (S.universalBadSquareMoment r p)]
  have hsub : B ⊆ U := fun x hx => hx.1
  exact hsqrt.trans (measureReal_mono hsub)

/-- The shared price radius spends the smaller of the actual bad-row
capacity and the original missing-square radius. -/
def universalSharedHoleRadius (S : SelectedHighLowStructure W m)
    (r p : S.I) (R : ℝ) : ℝ :=
  min R (Real.sqrt (S.universalBadSquareMoment r p))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalSharedHoleRadius_le_capacity
    (S : SelectedHighLowStructure W m) (r p : S.I) (R : ℝ) :
    S.universalSharedHoleRadius r p R ≤ R := min_le_left _ _

theorem UniversalPhysicalPrimal.universalSharedHoleRadius_le_common_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (R : ℝ) :
    S.universalSharedHoleRadius r p R ≤
      μ.real (S.universalPartnerCommonRegion r p) :=
  (min_le_right _ _).trans
    (P.sqrt_badSquareMoment_le_common_mass S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A genuine positive negative region and its actual nonnegative
own/good allowance force any shared row cap to be nonnegative. -/
theorem universalSharedHoleCapacity_nonneg
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c R : ℝ)
    (hBpos : 0 < μ (S.universalNegativeRegion r p))
    (hcap : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤ R) :
    0 ≤ R := by
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hBpos.ne' hcap
  have hown := (S.universalOwnMass_mem_Icc x).1
  have hgood := S.universalGoodMissingMass_nonneg r p d c x
  linarith only [hx, hown, hgood]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalSharedHoleRadius_nonneg
    (S : SelectedHighLowStructure W m) (r p : S.I) (R : ℝ)
    (hR : 0 ≤ R) : 0 ≤ S.universalSharedHoleRadius r p R := by
  unfold universalSharedHoleRadius
  exact le_min hR (Real.sqrt_nonneg _)

/-- The same radius bounds every original own atom on the actual
negative region, with no independent replacement law. -/
theorem UniversalPhysicalPrimal.ae_negative_own_le_shared_radius
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (R : ℝ)
    (hcap : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤ R) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x ≤ S.universalSharedHoleRadius r p R := by
  filter_upwards [hcap, P.ae_negative_own_mass_le_sqrt_badSquareMoment
    S r p hpair hW hd hgap hN hA hAhalf hell hmargin] with x hx hsqrt
  apply le_min
  · linarith only [hx, S.universalGoodMissingMass_nonneg r p d c x]
  · exact hsqrt

/-- The weighted own-atom debit uses the shared radius and the same
negative charge mass as the combined allowance. -/
theorem UniversalPhysicalPrimal.weighted_own_le_shared_radius
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (R : ℝ)
    (hcap : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalOwnMass x + S.universalGoodMissingMass r p d c x ≤ R) :
    S.universalWeightedOwnMoment r p ≤
      S.universalSharedHoleRadius r p R * S.universalNegativeChargeMass r p :=
  S.universalWeightedOwnMoment_le r p _
    (P.ae_negative_own_le_shared_radius S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin R hcap)

/-- The single H and bad-region missing inventory pays the square of
the shared price radius, with the original partner cross debit retained. -/
theorem UniversalPhysicalPrimal.hole_add_shared_radius_sq_le_original_missing
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (R : ℝ) (hR : 0 ≤ R) :
    S.universalHoleSquareMoment r p +
      (S.universalSharedHoleRadius r p R) ^ 2 ≤
        1 - 2 * d - (S.originalAtomMass r) ^ 2 -
          (S.originalAtomMass p) ^ 2 -
            2 * S.originalAtomMass p *
              μ.real (S.universalPartnerHoleRegion r p) := by
  let z := S.universalSharedHoleRadius r p R
  have hz0 : 0 ≤ z := S.universalSharedHoleRadius_nonneg r p R hR
  have hzle : z ≤ Real.sqrt (S.universalBadSquareMoment r p) :=
    min_le_right _ _
  have hq0 : 0 ≤ S.universalBadSquareMoment r p :=
    integral_nonneg (fun x => (S.universalOwnMass_mem_Icc x).1)
  have hzsq : z ^ 2 ≤ S.universalBadSquareMoment r p := by
    nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg (S.universalBadSquareMoment r p)]
  have hpack := P.hole_add_bad_square_le_original_missing S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  nlinarith only [hzsq, hpack]

/-- The good-common missing mass is exactly the actual physical
missing-section mass on almost every original source row. -/
theorem ae_good_missing_section_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ,
      μ.real (IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x ∩
          S.universalGoodCommonRegion r p d c) =
        S.universalGoodMissingMass r p d c x := by
  let G := PhysicalRepresentative.adjacency W m
  let Good := S.universalGoodCommonRegion r p d c
  have hGood : MeasurableSet Good := S.measurableSet_universalGoodCommonRegion r p d c
  have hphys := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [hphys] with x hx
  have hrow : ∀ᵐ z ∂μ.restrict Good,
      1 - adjacencyKernel W x z =
        (IndependentAtomCopy.missingSection G x).indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [ae_restrict_of_ae hx] with z hz
    change adjacencyKernel W x z =
      (if G x z = true then (1 : ℝ) else 0) at hz
    by_cases hG : G x z = true
    · simp [hG, hz, IndependentAtomCopy.missingSection]
    · have hfalse : G x z = false := Bool.eq_false_iff.mpr hG
      simp [hfalse, hz, IndependentAtomCopy.missingSection]
  unfold universalGoodMissingMass
  rw [integral_congr_ae hrow]
  have hM : MeasurableSet (IndependentAtomCopy.missingSection G x) :=
    IndependentAtomCopy.measurableSet_missingSection G
      (PhysicalRepresentative.measurable_adjacency W m) x
  rw [setIntegral_indicator hM]
  rw [setIntegral_const]
  simp only [smul_eq_mul, mul_one, Set.inter_comm]
  rfl

/-- The copied original H charge row agrees almost everywhere with
the physical representative on the unchanged original measure. -/
theorem ae_universalHoleChargeRow_eq_physical
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, S.universalHoleChargeRow r p x =
      ∫ h in S.universalPartnerHoleRegion r p,
        PhysicalRepresentative.charge W m x h ∂μ := by
  have hsec := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.charge_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [hsec] with x hx
  unfold universalHoleChargeRow
  apply integral_congr_ae
  exact ae_restrict_of_ae (hx.mono (fun _ he => he.symm))

/-- Almost every negative source's original whole atom has no overlap
with the good common region; the statement includes zero-mass dust. -/
theorem UniversalPhysicalPrimal.ae_negative_sameAtom_good_null
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      μ.real ({z | (x, z) ∈ S.sameAtomRelation} ∩
        S.universalGoodCommonRegion r p d c) = 0 := by
  let B := S.universalNegativeRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hwhole := P.ae_negative_whole_fiber S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  filter_upwards [hwhole] with x hx
  let Same : Set Ω := {z | (x, z) ∈ S.sameAtomRelation}
  have hSame : MeasurableSet Same :=
    S.measurableSet_sameAtomRelation.preimage (measurable_const.prodMk measurable_id)
  have hdis : Disjoint B Good := by
    apply Set.disjoint_left.mpr
    intro z hzB hzGood
    exact hzGood.2 (S.universalNegativeRegion_subset_upperE2Bad r p d c
      (by linarith : 0 < S.originalAtomMass r) hmargin
      (by linarith [hell.2] : 0 ≤ 1 + m) hzB)
  by_cases hpos : 0 < S.universalOwnMass x
  · obtain ⟨i, hxi, hfiber⟩ := hx hpos
    have hSameEq : Same = {z | S.ρ z = i.val} := by
      ext z
      change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔ S.ρ z = i.val
      exact ⟨fun h => h.1.symm.trans hxi,
        fun h => ⟨hxi.trans h.symm, hxi ▸ i.property⟩⟩
    have hnot : ∀ᵐ z ∂μ, z ∈ Same → z ∉ Good := by
      have hI := (S.hfibers i.val i.property).1
      have hb := (ae_restrict_iff' hI).mp (hfiber.mono (fun _ h => h.1))
      filter_upwards [hb] with z hz hzSame hzGood
      have hzi : S.ρ z = i.val := by simpa [hSameEq] using hzSame
      exact (Set.disjoint_left.mp hdis) (hz hzi) hzGood
    have heq : μ.real (Same ∩ Good) = μ.real (∅ : Set Ω) := by
      apply measureReal_congr
      filter_upwards [hnot] with z hz
      exact propext ⟨fun h => False.elim (hz h.1 h.2), fun h => False.elim h⟩
    simpa only [Same, Good, measureReal_empty] using heq
  · have hzero : S.universalOwnMass x = 0 :=
      le_antisymm (le_of_not_gt hpos) (S.universalOwnMass_mem_Icc x).1
    have hle : μ.real (Same ∩ Good) ≤ μ.real Same :=
      measureReal_mono inter_subset_left
    rw [← S.universalOwnMass_eq_sameAtom_section x, hzero] at hle
    exact le_antisymm hle measureReal_nonneg

/-- The actual bad outside-own holes lie in the HIGH good region, so the H-row
copy keeps the signed deficit coefficient on every such recipient. -/
theorem UniversalPhysicalPrimal.ae_bad_missing_row_le_signed
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalNegativeRegion r p)),
      (∫ z in IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) q.2,
          PhysicalRepresentative.charge W m q.1 z ∂μ) ≤
        S.universalOwnMass q.2 * PhysicalRepresentative.charge W m q.1 q.2 +
          (S.universalRootDeficit r q.1 -
            (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) *
              S.universalGoodMissingMass r p d c q.2 := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalNegativeRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  let HighGood := S.universalHighGoodRegion r p d c
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hGood : MeasurableSet Good := S.measurableSet_universalGoodCommonRegion r p d c
  have hHighGood : MeasurableSet HighGood := S.measurableSet_universalHighGoodRegion r p d c
  have hsubset : B ⊆ S.universalUpperE2BadRegion r p d c :=
    S.universalNegativeRegion_subset_upperE2Bad r p d c
      (by linarith : 0 < S.originalAtomMass r) hmargin
      (by linarith [hell.2] : 0 ≤ 1 + m)
  have hcover := Measure.ae_ae_of_ae_prod
    (P.ae_bad_outside_own_missing_high_good S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hsame := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_physical_charge_eq_on_sameAtom hW hd hgap)
  have hmassSame := S.ae_missing_sameAtom_section_mass hW hd hgap
  have hmassGood := S.ae_good_missing_section_mass r p hW hd hgap
  have hnull := (ae_restrict_iff' hB).mp
    (P.ae_negative_sameAtom_good_null S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hrest : (μ.restrict H).prod (μ.restrict HighGood) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hsigned := S.ae_hole_high_good_charge_le_signed r p hpair hW hd hgap hN hell.2
  have hcharge := ae_mono hrest (PhysicalRepresentative.charge_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support)
  have hgoodprod : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict HighGood),
      Y q.1 q.2 ≤ S.universalRootDeficit r q.1 - θ := by
    filter_upwards [hsigned, hcharge] with q hs hc
    change Y q.1 q.2 = chargeKernel W q.1 q.2 at hc
    rw [hc]
    exact hs
  have hgoodrow : ∀ᵐ h ∂μ.restrict H,
      ∀ᵐ z ∂μ.restrict HighGood,
        Y h z ≤ S.universalRootDeficit r h - θ :=
    Measure.ae_ae_of_ae_prod hgoodprod
  have hprod : (μ.restrict H).prod (μ.restrict B) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hprod hsame,
    Measure.quasiMeasurePreserving_fst.ae hgoodrow,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae hcover),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae hmassSame),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae hmassGood),
    Measure.quasiMeasurePreserving_snd.ae ((ae_restrict_iff' hB).mpr hnull),
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hH),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hB)]
    with q hsameQ hgoodQ hcoverQ hmassSameQ hmassGoodQ hnullQ hqH hqB
  let M := IndependentAtomCopy.missingSection G q.2
  let Same : Set Ω := {z | (q.2, z) ∈ S.sameAtomRelation}
  let J := HighGood \ Same
  have hM : MeasurableSet M := IndependentAtomCopy.measurableSet_missingSection G
    (PhysicalRepresentative.measurable_adjacency W m) q.2
  have hSame : MeasurableSet Same :=
    S.measurableSet_sameAtomRelation.preimage (measurable_const.prodMk measurable_id)
  have hJ : MeasurableSet J := hHighGood.diff hSame
  have hdis : Disjoint Same J := disjoint_sdiff_self_right
  have hfi : Integrable (Y q.1) μ := by
    apply Integrable.of_bound
      ((PhysicalRepresentative.measurable_charge W m).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    exact Eventually.of_forall (fun z => by
      change ‖Y q.1 z‖ ≤ 3
      exact (PhysicalRepresentative.charge_bound W m q.1 z))
  have hset : M =ᵐ[μ] (M ∩ Same) ∪ (M ∩ J) := by
    filter_upwards [hcoverQ] with z hz
    exact propext ⟨fun hm => by
      by_cases hs : z ∈ Same
      · exact Or.inl ⟨hm, hs⟩
      · exact Or.inr ⟨hm, ⟨(hz (hsubset hqB) hm hs), hs⟩⟩,
      fun h => h.elim (fun h => h.1) (fun h => h.1)⟩
  have hrowSame : ∀ᵐ z ∂μ.restrict (M ∩ Same), Y q.1 z ≤ Y q.1 q.2 := by
    filter_upwards [ae_restrict_of_ae hsameQ, ae_restrict_mem (hM.inter hSame)]
      with z hz hzMS
    exact (hz hzMS.2).le
  have hrowJ : ∀ᵐ z ∂μ.restrict (M ∩ J),
      Y q.1 z ≤ S.universalRootDeficit r q.1 - θ := by
    have hg := hgoodQ
    have hg' := (ae_restrict_iff' hHighGood).mp hg
    filter_upwards [ae_restrict_of_ae hg', ae_restrict_mem (hM.inter hJ)]
      with z hz hzMJ
    exact hz hzMJ.2.1
  have hmassJ : μ.real (M ∩ J) = S.universalGoodMissingMass r p d c q.2 := by
    have hnot : ∀ᵐ z ∂μ, z ∉ Same ∩ Good := by
      have hnull : μ (Same ∩ Good) = 0 :=
        (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hnullQ
      exact measure_eq_zero_iff_ae_notMem.mp hnull
    have heq : μ.real (M ∩ J) = μ.real (M ∩ Good) := by
      apply measureReal_congr
      filter_upwards [hnot, hcoverQ] with z hz hc
      exact propext ⟨fun h => ⟨h.1, h.2.1.1⟩,
        fun h => by
          have hnotSame : z ∉ Same := fun hs => hz ⟨hs, h.2⟩
          have hhigh : z ∈ HighGood := hc (hsubset hqB) h.1 hnotSame
          exact ⟨h.1, ⟨hhigh, hnotSame⟩⟩⟩
    exact heq.trans hmassGoodQ
  have hrow := missing_row_le_two_sections M Same J hM hSame hJ hdis
    hset (Y q.1) hfi (Y q.1 q.2)
      (S.universalRootDeficit r q.1 - θ) hrowSame hrowJ
  rw [hmassSameQ, hmassJ] at hrow
  nlinarith only [hrow]

/-- The two actual copied missing rows yield the signed numerator.
The error row is a local intermediate paid separately by its physical
LOW good-region recipient classification. -/
private theorem UniversalPhysicalPrimal.ae_hole_negative_copy_numerator_of_rows
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) (e : Ω → ℝ)
    (hrowH : ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalNegativeRegion r p)),
      (∫ z in IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) q.1,
          PhysicalRepresentative.charge W m q.2 z ∂μ) +
          m * μ.real (IndependentAtomCopy.missingSection
            (PhysicalRepresentative.adjacency W m) q.1 ∩
              IndependentAtomCopy.missingSection
                (PhysicalRepresentative.adjacency W m) q.2) ≤
        S.universalPartnerHoleMissingMass r p q.1 *
          PhysicalRepresentative.charge W m q.1 q.2 +
          S.originalAtomMass p * (-S.rootChargeRow r q.2) + e q.1) :
    ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalNegativeRegion r p)),
      0 < PhysicalRepresentative.charge W m q.1 q.2 →
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p q.1 -
          S.universalOwnMass q.2) * PhysicalRepresentative.charge W m q.1 q.2 ≤
            S.originalAtomMass p * (-S.rootChargeRow r q.2) -
              (2 * (c - m * d) + m) +
              (S.universalRootDeficit r q.1 -
                (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) *
                S.universalGoodMissingMass r p d c q.2 + e q.1 := by
  filter_upwards [S.ae_hole_negative_raw_copy r p hW hd hgap hN,
    P.ae_bad_missing_row_le_signed S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin, hrowH] with q hcopy hrowB hrowH hpos
  have hcopy' := hcopy hpos
  nlinarith only [hcopy', hrowB, hrowH]

/-- The actual H-row capacity and negative-row cap keep every copied
denominator above `6A-2`; the signed numerator then bounds the charge. -/
private theorem UniversalPhysicalPrimal.ae_hole_negative_charge_le_price_of_rows
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hu : μ.real (S.universalPartnerCommonRegion r p) <
      1 - 2 * S.originalAtomMass r)
    (e : Ω → ℝ) (he : ∀ h, 0 ≤ e h)
    (hrowH : ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalNegativeRegion r p)),
      (∫ z in IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) q.1,
          PhysicalRepresentative.charge W m q.2 z ∂μ) +
          m * μ.real (IndependentAtomCopy.missingSection
            (PhysicalRepresentative.adjacency W m) q.1 ∩
              IndependentAtomCopy.missingSection
                (PhysicalRepresentative.adjacency W m) q.2) ≤
        S.universalPartnerHoleMissingMass r p q.1 *
          PhysicalRepresentative.charge W m q.1 q.2 +
          S.originalAtomMass p * (-S.rootChargeRow r q.2) + e q.1) :
    ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalNegativeRegion r p)),
      PhysicalRepresentative.charge W m q.1 q.2 ≤
        max (S.originalAtomMass p * (-S.rootChargeRow r q.2) -
          (2 * (c - m * d) + m) +
          (S.universalRootDeficit r q.1 -
            (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) *
            S.universalGoodMissingMass r p d c q.2) 0 /
              (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p q.1 -
                S.universalOwnMass q.2) +
          e q.1 / (S.originalAtomMass r -
            S.universalPartnerHoleMissingMass r p q.1 - S.universalOwnMass q.2) := by
  have hhole := S.ae_hole_missing_mass_le_capacity r p hpair hW hd hgap
    hell.2 hN
  have hbad := P.ae_negative_shared_hole_cap S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin hu
  have hcopy := P.ae_hole_negative_copy_numerator_of_rows S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin e hrowH
  filter_upwards [hcopy,
    Measure.quasiMeasurePreserving_fst.ae hhole,
    Measure.quasiMeasurePreserving_snd.ae hbad]
    with q hcopy hhole hbad
  have hax : S.universalOwnMass q.2 ≤
      1 - 3 * S.originalAtomMass r + S.originalAtomMass p := by
    have hgood := S.universalGoodMissingMass_nonneg r p d c q.2
    have hmin := (min_le_left
      (1 - 3 * S.originalAtomMass r + S.originalAtomMass p)
      ((1 - μ.real (S.universalPartnerCommonRegion r p) +
        2 * m * S.originalAtomMass r - 3 * (2 * (c - m * d) + m)) / (-m)))
    linarith only [hbad, hgood, hmin]
  have hden : 0 < S.originalAtomMass r -
      S.universalPartnerHoleMissingMass r p q.1 - S.universalOwnMass q.2 := by
    linarith only [hhole, hax, hA]
  exact UniversalSignedPrice.copied_charge_le_price_integrand
    (S.originalAtomMass r) (S.universalPartnerHoleMissingMass r p q.1)
    (S.universalOwnMass q.2) (PhysicalRepresentative.charge W m q.1 q.2)
    (S.originalAtomMass p * (-S.rootChargeRow r q.2) -
      (2 * (c - m * d) + m) +
      (S.universalRootDeficit r q.1 -
        (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) *
        S.universalGoodMissingMass r p d c q.2) (e q.1) hden (he q.1) hcopy

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The original reciprocal and positive-deficit bounds make every
signed copy price integrable on the actual partner hole. -/
theorem integrable_universalSignedPrice
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (θ ax α j v b γ : ℝ) (hθ : 0 ≤ θ) (hj : 0 ≤ j)
    (hα : α < S.originalAtomMass r - ax)
    (ha : ∀ᵐ h ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p h ≤ α) :
    IntegrableOn (fun h =>
      max (b * v - γ + (S.universalRootDeficit r h - θ) * j) 0 /
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h - ax))
      (S.universalPartnerHoleRegion r p) μ := by
  apply UniversalSignedPrice.integrable_priceFunction μ
    (S.universalPartnerHoleRegion r p)
    (S.universalPartnerHoleMissingMass r p) (S.universalRootDeficit r)
    (S.originalAtomMass r) b γ θ ax j v
  · exact (S.aestronglyMeasurable_universalPartnerHoleMissingMass r p).mono_measure
      Measure.restrict_le_self
  · exact (S.measurable_universalRootDeficit r).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  · exact hj
  · filter_upwards [ha] with h hh
    linarith
  · exact S.integrable_hole_reciprocal r p ax α hα ha
  · exact S.integrable_hole_positive_deficit_ratio r p θ ax α hθ hα ha

/-- A single original H deficit budget controls the positive signed
endpoint coefficient at every negative vertex, using one shared radius. -/
theorem hole_positive_deficit_ratio_le_shared
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (θ z ax α : ℝ) (hθ : 0 ≤ θ) (hθhalf : θ < 1 / 2)
    (hk : 0 < S.originalAtomMass r - z)
    (hDHk : (∫ h in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r h ∂μ) < θ * (S.originalAtomMass r - z))
    (hax : ax ≤ z) (hα : α < S.originalAtomMass r - z)
    (ha : ∀ᵐ h ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p h ≤ α)
    (hDmax : ∀ᵐ h ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalRootDeficit r h ≤ 1 - θ) :
    (∫ h in S.universalPartnerHoleRegion r p,
      max (S.universalRootDeficit r h - θ) 0 /
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h - ax) ∂μ) ≤
      (∫ h in S.universalPartnerHoleRegion r p,
        S.universalRootDeficit r h ∂μ) * (1 - 2 * θ) /
        ((S.originalAtomMass r - z) * (1 - θ) -
          ∫ h in S.universalPartnerHoleRegion r p,
            S.universalRootDeficit r h ∂μ) := by
  let H := S.universalPartnerHoleRegion r p
  let a := S.universalPartnerHoleMissingMass r p
  let D := S.universalRootDeficit r
  let DH := ∫ h in H, D h ∂μ
  have hDH0 : 0 ≤ DH := integral_nonneg (fun h => (S.universalRootDeficit_mem_Icc r h).1)
  have hpoint : ∀ᵐ h ∂μ.restrict H,
      a h < S.originalAtomMass r - z ∧ 0 ≤ D h ∧ D h ≤ 1 - θ ∧
        a h * D h ≤ DH := by
    filter_upwards [ha, hDmax,
      S.ae_hole_own_mass_mul_deficit_le_total r p hpair hW hd hgap hell]
      with h hh hDhi hbudget
    exact ⟨by linarith, (S.universalRootDeficit_mem_Icc r h).1,
      hDhi, hbudget⟩
  have hratioZInt : IntegrableOn (fun h => max (D h - θ) 0 /
      (S.originalAtomMass r - z - a h)) H μ := by
    simpa only [sub_sub, add_comm] using
      S.integrable_hole_positive_deficit_ratio r p θ z α hθ hα ha
  have hratioZ := UniversalSignedPrice.positive_deficit_integral_le H a D θ
    (S.originalAtomMass r - z) DH hθ hθhalf hk hDH0 hDHk
    ((S.integrable_universalRootDeficit r).integrableOn)
    hratioZInt
    rfl hpoint
  have hratioAx := S.integrable_hole_positive_deficit_ratio r p θ ax α hθ
    (by linarith) ha
  have hmono : (∫ h in H, max (D h - θ) 0 /
      (S.originalAtomMass r - a h - ax) ∂μ) ≤
      ∫ h in H, max (D h - θ) 0 /
        (S.originalAtomMass r - z - a h) ∂μ := by
    apply integral_mono_ae hratioAx
      hratioZInt
    filter_upwards [ha] with h hh
    have hnum : 0 ≤ max (D h - θ) 0 := le_max_right _ _
    have hdenZ : 0 < S.originalAtomMass r - z - a h := by linarith
    have hdenAx : 0 < S.originalAtomMass r - a h - ax := by linarith
    apply (div_le_div_iff₀ hdenAx hdenZ).2
    exact mul_le_mul_of_nonneg_left (by linarith) hnum
  exact hmono.trans hratioZ

/-- The actual copied charge row is bounded by the signed H price and
the separate physical LOW good-region error integral. -/
theorem UniversalPhysicalPrimal.ae_hole_negative_charge_row_le_price_of_rows
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hu : μ.real (S.universalPartnerCommonRegion r p) <
      1 - 2 * S.originalAtomMass r)
    (e : Ω → ℝ) (he : ∀ h, 0 ≤ e h)
    (hrowH : ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalNegativeRegion r p)),
      (∫ z in IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) q.1,
          PhysicalRepresentative.charge W m q.2 z ∂μ) +
          m * μ.real (IndependentAtomCopy.missingSection
            (PhysicalRepresentative.adjacency W m) q.1 ∩
              IndependentAtomCopy.missingSection
                (PhysicalRepresentative.adjacency W m) q.2) ≤
        S.universalPartnerHoleMissingMass r p q.1 *
          PhysicalRepresentative.charge W m q.1 q.2 +
          S.originalAtomMass p * (-S.rootChargeRow r q.2) + e q.1)
    (θ α : ℝ) (hθ : 0 ≤ θ)
    (hθeq : θ = 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (ha : ∀ᵐ h ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p h ≤ α)
    (hα : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      α < S.originalAtomMass r - S.universalOwnMass x)
    (hErr : ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      IntegrableOn (fun h => e h /
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
          S.universalOwnMass x)) (S.universalPartnerHoleRegion r p) μ) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.universalHoleChargeRow r p x ≤
        UniversalSignedPrice.priceFunction μ
          (S.universalPartnerHoleRegion r p)
          (S.universalPartnerHoleMissingMass r p) (S.universalRootDeficit r)
          (S.originalAtomMass r) (S.originalAtomMass p)
          (2 * (c - m * d) + m) θ (S.universalOwnMass x)
          (S.universalGoodMissingMass r p d c x) (-S.rootChargeRow r x) +
        ∫ h in S.universalPartnerHoleRegion r p,
          e h / (S.originalAtomMass r -
            S.universalPartnerHoleMissingMass r p h - S.universalOwnMass x) ∂μ := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalNegativeRegion r p
  have hpoint := P.ae_hole_negative_charge_le_price_of_rows S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin hu e he hrowH
  rw [← hθeq] at hpoint
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict B) (ν := μ.restrict H)).quasiMeasurePreserving.ae hpoint
  have hsections := Measure.ae_ae_of_ae_prod hswap
  have hJ : ∀ᵐ x ∂μ.restrict B,
      S.universalHoleChargeRow r p x =
        ∫ h in H, PhysicalRepresentative.charge W m x h ∂μ :=
    ae_restrict_of_ae (S.ae_universalHoleChargeRow_eq_physical r p hW hd hgap)
  filter_upwards [hsections, hJ, hα, hErr] with x hx hJx hαx hErrx
  have hY : IntegrableOn (fun h => PhysicalRepresentative.charge W m h x) H μ := by
    apply Integrable.of_bound
      ((PhysicalRepresentative.measurable_charge W m).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable 3
    exact Eventually.of_forall (fun h => by
      rw [Real.norm_eq_abs]
      exact PhysicalRepresentative.charge_bound W m h x)
  have hprice := S.integrable_universalSignedPrice r p θ
    (S.universalOwnMass x) α (S.universalGoodMissingMass r p d c x)
    (-S.rootChargeRow r x) (S.originalAtomMass p)
    (2 * (c - m * d) + m) hθ
    (S.universalGoodMissingMass_nonneg r p d c x) hαx ha
  have hbound := integral_mono_ae hY (hprice.add hErrx) hx
  change (∫ h in H, PhysicalRepresentative.charge W m h x ∂μ) ≤
    ∫ h in H,
      max (S.originalAtomMass p * (-S.rootChargeRow r x) -
        (2 * (c - m * d) + m) +
          (S.universalRootDeficit r h - θ) *
            S.universalGoodMissingMass r p d c x) 0 /
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p h -
          S.universalOwnMass x) +
      e h / (S.originalAtomMass r -
        S.universalPartnerHoleMissingMass r p h - S.universalOwnMass x) ∂μ at hbound
  rw [integral_add hprice hErrx] at hbound
  have hYeq : (∫ h in H, PhysicalRepresentative.charge W m h x ∂μ) =
      S.universalHoleChargeRow r p x := by
    rw [hJx]
    apply integral_congr_ae
    exact Eventually.of_forall (fun h => PhysicalRepresentative.charge_symm W m h x)
  rw [hYeq] at hbound
  exact hbound

/-- Every actual signed H price lies below the same chord endpoint,
with its reciprocal and positive-deficit moments paid once. -/
theorem universalSignedPrice_le_endpoint
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell' : -m < 1)
    (θ z ax α j v b γ ell R : ℝ)
    (hθ : 0 ≤ θ) (hk : 0 < S.originalAtomMass r - z)
    (hDHk : (∫ h in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r h ∂μ) < θ * (S.originalAtomMass r - z))
    (hax : ax ≤ z) (hα : α < S.originalAtomMass r - z)
    (ha : ∀ᵐ h ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p h ≤ α)
    (hDmax : ∀ᵐ h ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalRootDeficit r h ≤ 1 - θ)
    (hell : 0 < ell) (hv : v ∈ Icc (0 : ℝ) ell)
    (hj : 0 ≤ j) (hjR : j ≤ R)
    (hmargin : max (1 - 2 * θ) 0 * R < γ) :
    let DH := ∫ h in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r h ∂μ
    let chi := if θ < 1 / 2 then
      DH * (1 - 2 * θ) / ((S.originalAtomMass r - z) * (1 - θ) - DH) else 0
    UniversalSignedPrice.priceFunction μ (S.universalPartnerHoleRegion r p)
      (S.universalPartnerHoleMissingMass r p) (S.universalRootDeficit r)
      (S.originalAtomMass r) b γ θ ax j v ≤ v / ell *
        (max (b * ell - γ) 0 *
          (μ.real (S.universalPartnerHoleRegion r p) /
            (S.originalAtomMass r - z) +
            S.universalHoleSquareMoment r p /
              ((S.originalAtomMass r - z) *
                (S.originalAtomMass r - z - α))) + j * chi) := by
  let H := S.universalPartnerHoleRegion r p
  let a := S.universalPartnerHoleMissingMass r p
  let D := S.universalRootDeficit r
  let A := S.originalAtomMass r
  let DH := ∫ h in H, D h ∂μ
  let chi := if θ < 1 / 2 then
    DH * (1 - 2 * θ) / ((A - z) * (1 - θ) - DH) else 0
  have hαx : α < A - ax := by dsimp only [A] at *; linarith
  have hden : ∀ᵐ h ∂μ.restrict H, 0 < A - a h - ax := by
    filter_upwards [ha] with h hh
    dsimp only [A, a] at *
    linarith
  have hpoint : ∀ᵐ h ∂μ.restrict H, D h ≤ 1 - θ ∧ 0 < A - a h - ax :=
    hDmax.and hden
  have hrec := S.integrable_hole_reciprocal r p ax α hαx ha
  have hdef := S.integrable_hole_positive_deficit_ratio r p θ ax α hθ hαx ha
  have hpriceV := S.integrable_universalSignedPrice r p θ ax α j v b γ hθ hj hαx ha
  have hpriceEll := S.integrable_universalSignedPrice r p θ ax α j ell b γ hθ hj hαx ha
  have hrecBound := S.hole_reciprocal_le r p z α ax hk hα hax ha
  have hdefBound : (∫ h in H, max (D h - θ) 0 /
      (A - a h - ax) ∂μ) ≤ chi := by
    by_cases hθhalf : θ < 1 / 2
    · simp only [chi, ite_eq_left hθhalf]
      exact S.hole_positive_deficit_ratio_le_shared r p hpair hW hd hgap
        hell' θ z ax α hθ hθhalf hk hDHk hax hα ha hDmax
    · have hzero := UniversalSignedPrice.nonpositive_deficit_integral_eq_zero
        μ H a D θ (A - ax) (le_of_not_gt hθhalf) hDmax
      have hzero' : (∫ h in H, max (D h - θ) 0 /
          (A - a h - ax) ∂μ) = 0 := by
        convert hzero using 1
        congr 1
        funext h
        ring
      simp only [chi, ite_eq_right hθhalf]
      exact hzero'.le
  have hchord := UniversalSignedPrice.priceFunction_chord μ H a D A b γ θ ax j R
    v ell hell hv hj hjR hmargin hpoint hpriceV hpriceEll
  have hendpoint := UniversalSignedPrice.priceFunction_endpoint_le μ H a D A b γ θ
    ax j ell
    (μ.real H / (A - z) + S.universalHoleSquareMoment r p /
      ((A - z) * (A - z - α))) chi hj hden hpriceEll hrec hdef
      hrecBound hdefBound
  dsimp only [H, a, D, A, DH, chi] at *
  exact hchord.trans (mul_le_mul_of_nonneg_left hendpoint (div_nonneg hv.1 hell.le))

end Erdos1017.CappedModel.SelectedHighLowStructure

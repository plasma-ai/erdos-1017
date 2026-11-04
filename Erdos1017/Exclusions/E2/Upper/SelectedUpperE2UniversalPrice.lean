module

public import Erdos1017.Exclusions.Common.Universal.UniversalSignedPrice
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitAtoms
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalGeometry
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTwoHeadClique
public import Erdos1017.SelectedModel.Structure.SelectedMultipartiteHalves
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Hole prices for the universal negative region

`universalNegativeRegion` collects the common-neighbor vertices with negative
universal-root charge and `universalGoodCommonRegion` the common outside region
above the rooted-triangle star threshold; the `H`-row missing mass has the
strict two-head capacity `1-2A-b`, and the exact `H×H` square moment is spent
once in the reciprocal correction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original common-neighbor vertices with negative universal-root
charge. Its own weighted hole inventory is never replaced by a new law. -/
def universalNegativeRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) : Set Ω :=
  S.universalPartnerCommonRegion r p ∩ {x | S.rootChargeRow r x < 0}

/-- The common outside region above the actual rooted-triangle star
threshold. It retains the original carrier and original law. -/
def universalGoodCommonRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) : Set Ω :=
  S.universalPartnerCommonRegion r p \ S.universalUpperE2BadRegion r p d c

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_universalGoodCommonRegion
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    MeasurableSet (S.universalGoodCommonRegion r p d c) :=
  (S.measurableSet_universalPartnerCommonRegion r p).diff
    (S.measurableSet_universalUpperE2BadRegion r p d c)

/-- The LOW good recipients are the only possible signed error source
for an H-to-negative-common copied pair. -/
def universalLowGoodRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) : Set Ω :=
  S.universalGoodCommonRegion r p d c ∩ S.L

/-- The HIGH good recipients carry the outside-own missing allowance
for a negative common vertex. -/
def universalHighGoodRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) : Set Ω :=
  S.universalGoodCommonRegion r p d c ∩ S.H

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem common_region_mem_rootNeighborhood
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {x : Ω} (hx : x ∈ S.universalPartnerCommonRegion r p) :
    x ∈ S.rootNeighborhood p := by
  by_contra hn
  have hnotr : S.ρ x ≠ r.val := by
    intro h
    exact hx (Or.inl (Or.inl h))
  have hnotp : S.ρ x ≠ p.val := by
    intro h
    exact hx (Or.inl (Or.inr h))
  have hhole : x ∈ S.universalPartnerHoleRegion r p := by
    intro h
    rcases h with (hr | hp) | hN
    · exact hnotr hr
    · exact hnotp hp
    · exact hn hN
  exact hx (Or.inr hhole)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_universalLowGoodRegion
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    MeasurableSet (S.universalLowGoodRegion r p d c) :=
  (S.measurableSet_universalGoodCommonRegion r p d c).inter S.hpartition.2.1

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_universalHighGoodRegion
    (S : SelectedHighLowStructure W m) (r p : S.I) (d c : ℝ) :
    MeasurableSet (S.universalHighGoodRegion r p d c) :=
  (S.measurableSet_universalGoodCommonRegion r p d c).inter S.hpartition.1

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_universalNegativeRegion
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    MeasurableSet (S.universalNegativeRegion r p) :=
  (S.measurableSet_universalPartnerCommonRegion r p).inter
    (measurableSet_lt (S.measurable_rootChargeRow r) measurable_const)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A negative universal charge is below the positive insertion
threshold on the same original common region. -/
theorem universalNegativeRegion_subset_upperE2Bad
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (d c : ℝ)
    (hA : 0 < S.originalAtomMass r)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hδ : 0 ≤ 1 + m) :
    S.universalNegativeRegion r p ⊆ S.universalUpperE2BadRegion r p d c := by
  intro x hx
  have hθ : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) := by
    have hmargin' : (2 * (1 + m)) * S.originalAtomMass r <
        3 * (2 * (c - m * d) + m) := by nlinarith [hmargin]
    have hmul := (lt_div_iff₀ hA).2 hmargin'
    nlinarith
  have houtside : x ∈ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ := by
    intro hhead
    exact hx.1 (Or.inl hhead)
  exact ⟨houtside, hx.2.trans hθ⟩

/-- On the actual negative common region the saturated partner's
charge is the positive opposite of the universal charge. -/
theorem UniversalPhysicalPrimal.ae_universalNegative_partner_charge
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
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      S.rootChargeRow p x = -S.rootChargeRow r x := by
  have hApos : 0 < S.originalAtomMass r := by linarith
  have hδ : 0 ≤ 1 + m := by linarith [hell.2]
  have hsubset := S.universalNegativeRegion_subset_upperE2Bad r p d c
    hApos hmargin hδ
  have hBad := (ae_restrict_iff'
    (S.measurableSet_universalUpperE2BadRegion r p d c)).mp
      (P.ae_universalUpperE2Bad_partner_charge S r p hpair hW hd hgap
        hN hA hAhalf hell hmargin)
  apply (ae_restrict_iff' (S.measurableSet_universalNegativeRegion r p)).mpr
  filter_upwards [hBad] with x hx hxNeg
  exact hx (hsubset hxNeg)

/-- The actual tight rooted triangles make the signed two-head score
vanish on the bad region, without discarding either signed root charge. -/
theorem UniversalPhysicalPrimal.ae_universalUpperE2Bad_score_eq_zero
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
    ∀ᵐ x ∂μ.restrict (S.universalUpperE2BadRegion r p d c),
      S.rootChargeRow r x + S.rootChargeRow p x = 0 := by
  filter_upwards [P.ae_universalUpperE2Bad_partner_charge S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin] with x hx
  linarith

/-- A bad-to-bad original charge cannot be positive: the actual two
head scores vanish and the original four-clique inequality remains. -/
theorem UniversalPhysicalPrimal.ae_bad_bad_charge_nonpos
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
    ∀ᵐ q ∂(μ.restrict (S.universalUpperE2BadRegion r p d c)).prod
      (μ.restrict (S.universalUpperE2BadRegion r p d c)),
        chargeKernel W q.1 q.2 ≤ 0 := by
  let B := S.universalUpperE2BadRegion r p d c
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hU := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin
  have hscore := P.ae_universalUpperE2Bad_score_eq_zero S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hproperty : ∀ᵐ x ∂μ.restrict B,
      S.ρ x ≠ r.val ∧ x ∈ S.rootNeighborhood p ∧
        S.rootChargeRow r x + S.rootChargeRow p x = 0 := by
    filter_upwards [ae_restrict_of_ae hU, ae_restrict_mem hB, hscore]
      with x hUx hxB hs
    have hxU := hUx hxB
    have hxr : S.ρ x ≠ r.val := by
      intro h
      exact hxU (Or.inl (Or.inl h))
    exact ⟨hxr, S.common_region_mem_rootNeighborhood r p hxU, hs⟩
  have hprod : (μ.restrict B).prod (μ.restrict B) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hprod
    (S.ae_universal_saturated_common_charge_le r p hpair hW hd hgap hN),
    Measure.quasiMeasurePreserving_fst.ae hproperty,
    Measure.quasiMeasurePreserving_snd.ae hproperty]
    with q hcharge hx hy
  have h := hcharge hx.1 hy.1 hx.2.1 hy.2.1
  rw [hx.2.2, hy.2.2] at h
  linarith

/-- A bad source pays at most the remaining signed two-head deficit
of a good common recipient. -/
theorem UniversalPhysicalPrimal.ae_bad_good_charge_le_score_deficit
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
    ∀ᵐ q ∂(μ.restrict (S.universalUpperE2BadRegion r p d c)).prod
      (μ.restrict (S.universalGoodCommonRegion r p d c)),
        chargeKernel W q.1 q.2 ≤
          -(S.rootChargeRow r q.2 + S.rootChargeRow p q.2) := by
  let B := S.universalUpperE2BadRegion r p d c
  let G := S.universalGoodCommonRegion r p d c
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hG : MeasurableSet G := S.measurableSet_universalGoodCommonRegion r p d c
  have hU := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin
  have hscore := P.ae_universalUpperE2Bad_score_eq_zero S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hbad : ∀ᵐ x ∂μ.restrict B,
      S.ρ x ≠ r.val ∧ x ∈ S.rootNeighborhood p ∧
        S.rootChargeRow r x + S.rootChargeRow p x = 0 := by
    filter_upwards [ae_restrict_of_ae hU, ae_restrict_mem hB, hscore]
      with x hUx hxB hs
    have hxU := hUx hxB
    have hxr : S.ρ x ≠ r.val := by
      intro h
      exact hxU (Or.inl (Or.inl h))
    exact ⟨hxr, S.common_region_mem_rootNeighborhood r p hxU, hs⟩
  have hgood : ∀ᵐ x ∂μ.restrict G,
      S.ρ x ≠ r.val ∧ x ∈ S.rootNeighborhood p := by
    filter_upwards [ae_restrict_mem hG] with x hx
    have hxU := hx.1
    have hxr : S.ρ x ≠ r.val := by
      intro h
      exact hxU (Or.inl (Or.inl h))
    exact ⟨hxr, S.common_region_mem_rootNeighborhood r p hxU⟩
  have hprod : (μ.restrict B).prod (μ.restrict G) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hprod
    (S.ae_universal_saturated_common_charge_le r p hpair hW hd hgap hN),
    Measure.quasiMeasurePreserving_fst.ae hbad,
    Measure.quasiMeasurePreserving_snd.ae hgood]
    with q hcharge hx hy
  have h := hcharge hx.1 hy.1 hx.2.1 hy.2
  rw [hx.2.2] at h
  linarith

/-- The good-common two-head deficit is at most the actual endpoint
charge allowance `(-m-θ)_+`. -/
theorem ae_good_common_score_deficit_le_endpoint
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict (S.universalGoodCommonRegion r p d c),
      -(S.rootChargeRow r x + S.rootChargeRow p x) ≤
        max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
          (1 + m))) 0 := by
  let G := S.universalGoodCommonRegion r p d c
  have hG : MeasurableSet G := S.measurableSet_universalGoodCommonRegion r p d c
  have hUpos := (ae_restrict_iff'
    (S.measurableSet_universalPartnerCommonRegion r p)).mp
      (S.ae_partner_row_pos_on_universalCommon r p)
  have hβp := S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap
  filter_upwards [ae_restrict_mem hG, ae_restrict_of_ae hUpos,
    ae_restrict_of_ae hβp] with x hx hpos hrow
  have hxU := hx.1
  have hppos := hpos hxU
  have hθ : 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) ≤
      S.rootChargeRow r x := by
    by_contra h
    exact hx.2 ⟨by
      intro hhead
      exact hxU (Or.inl hhead), lt_of_not_ge h⟩
  change 1 - S.rootChargeRow p x =
    1 - p.val x - m * (if 0 < p.val x then 1 else 0) at hrow
  rw [ite_eq_left hppos] at hrow
  have hm : m ≤ S.rootChargeRow p x := by linarith
  exact (by linarith : -(S.rootChargeRow r x + S.rootChargeRow p x) ≤
    -m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))).trans
      (le_max_left _ _)

/-- The actual bad-to-good original charge is bounded by the single
endpoint allowance used in the positive signed copy error. -/
theorem UniversalPhysicalPrimal.ae_bad_good_charge_le_endpoint
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
    ∀ᵐ q ∂(μ.restrict (S.universalUpperE2BadRegion r p d c)).prod
      (μ.restrict (S.universalGoodCommonRegion r p d c)),
        chargeKernel W q.1 q.2 ≤
          max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
            (1 + m))) 0 := by
  filter_upwards [P.ae_bad_good_charge_le_score_deficit S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin,
    Measure.quasiMeasurePreserving_snd.ae
      (S.ae_good_common_score_deficit_le_endpoint r p hW hd hgap)]
    with q hcharge hscore
  exact hcharge.trans hscore

/-- The actual physical threshold supplies the deficit range used in
the signed positive-part moment bound. -/
theorem UniversalPhysicalPrimal.ae_hole_deficit_le_one_sub_threshold
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
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalRootDeficit r x ≤
        1 - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) := by
  filter_upwards [P.ae_universal_upperE2_hole_star_threshold S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin] with x hx
  dsimp [universalRootDeficit]
  linarith

/-- Every negative common vertex remains originally adjacent to the
entire partner hole; this is inherited from the actual join of H with the bad region. -/
theorem UniversalPhysicalPrimal.ae_hole_negative_join
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
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
        q.2 ∈ S.universalNegativeRegion r p →
          adjacencyKernel W q.1 q.2 = 1 := by
  have hApos : 0 < S.originalAtomMass r := by linarith
  have hδ : 0 ≤ 1 + m := by linarith [hell.2]
  have hsubset := S.universalNegativeRegion_subset_upperE2Bad r p d c
    hApos hmargin hδ
  filter_upwards [P.ae_universalUpperE2_hole_bad_join S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin] with q hq hH hN'
  exact hq hH (hsubset hN')

/-- The same original whole-atom mass at an atomic vertex; genuine
clique dust has own mass zero. -/
def universalOwnMass (S : SelectedHighLowStructure W m) (x : Ω) : ℝ :=
  (S.collapsedPartLabel x).elim 0 S.originalAtomMass

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
theorem measurable_universalOwnMass (S : SelectedHighLowStructure W m) :
    Measurable S.universalOwnMass := by
  let : MeasurableSpace (Option S.I) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (measurable_of_countable
    (fun o : Option S.I => o.elim 0 S.originalAtomMass)).comp
    S.measurable_collapsedPartLabel

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalOwnMass_mem_Icc (S : SelectedHighLowStructure W m) (x : Ω) :
    S.universalOwnMass x ∈ Icc (0 : ℝ) 1 := by
  unfold universalOwnMass
  cases h : S.collapsedPartLabel x with
  | none => simp
  | some i =>
      simp only [Option.elim_some]
      exact ⟨measureReal_nonneg, measureReal_le_one⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  in
theorem integrable_universalOwnMass (S : SelectedHighLowStructure W m) :
    Integrable S.universalOwnMass μ := by
  apply Integrable.of_bound (S.measurable_universalOwnMass.aestronglyMeasurable) 1
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (S.universalOwnMass_mem_Icc x).1]
    exact (S.universalOwnMass_mem_Icc x).2)

/-- The negative common region's original whole-atom square budget. -/
def universalBadSquareMoment (S : SelectedHighLowStructure W m)
    (r p : S.I) : ℝ :=
  ∫ x in S.universalNegativeRegion r p, S.universalOwnMass x ∂μ

/-- Original signed mass of the negative universal charge. -/
def universalNegativeChargeMass (S : SelectedHighLowStructure W m)
    (r p : S.I) : ℝ :=
  ∫ x in S.universalNegativeRegion r p, -S.rootChargeRow r x ∂μ

/-- The signed old charge row sent from one common vertex into the
original partner hole. -/
def universalHoleChargeRow (S : SelectedHighLowStructure W m)
    (r p : S.I) (x : Ω) : ℝ :=
  ∫ h in S.universalPartnerHoleRegion r p, chargeKernel W x h ∂μ

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem integrable_universalHoleChargeRow (S : SelectedHighLowStructure W m)
    (r p : S.I) (x : Ω) :
    IntegrableOn (chargeKernel W x) (S.universalPartnerHoleRegion r p) μ := by
  have hmeas : StronglyMeasurable (chargeKernel W x) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_charge.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound hmeas.aestronglyMeasurable 3
  exact Eventually.of_forall (fun h => by
    change ‖W.moment CappedColor.charge (x, h)‖ ≤ 3
    rw [Real.norm_eq_abs]
    have ha := adjacency_moment_mem W (x, h)
    have hlo := neg_three_adjacency_moment_le_charge W (x, h)
    have hhi := charge_moment_le_adjacency W (x, h)
    exact abs_le.mpr ⟨by linarith [ha.2, hlo], by linarith [ha.2, hhi]⟩)

/-- The original copied-row inequality is licensed for an H point and
a negative common point on their actual restricted product law. -/
theorem ae_hole_negative_raw_copy
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalNegativeRegion r p)),
      0 < PhysicalRepresentative.charge W m q.1 q.2 →
        S.originalAtomMass r * PhysicalRepresentative.charge W m q.1 q.2 +
          (2 * (c - m * d) + m) - m * μ.real
            (IndependentAtomCopy.missingSection
              (PhysicalRepresentative.adjacency W m) q.1 ∩
              IndependentAtomCopy.missingSection
                (PhysicalRepresentative.adjacency W m) q.2) ≤
          (∫ z in IndependentAtomCopy.missingSection
            (PhysicalRepresentative.adjacency W m) q.1,
            PhysicalRepresentative.charge W m q.2 z ∂μ) +
          (∫ z in IndependentAtomCopy.missingSection
            (PhysicalRepresentative.adjacency W m) q.2,
            PhysicalRepresentative.charge W m q.1 z ∂μ) := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalNegativeRegion r p
  have hprod : (μ.restrict H).prod (μ.restrict B) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hprod (S.ae_universal_copy_inequality r hW hd hgap hN),
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)),
    Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (S.measurableSet_universalNegativeRegion r p))]
    with q hcopy hH hB hq
  have hnotr : S.ρ q.1 ≠ r.val := by
    intro h
    exact hH (Or.inl (Or.inl h))
  have hnotr' : S.ρ q.2 ≠ r.val := by
    intro h
    exact hB.1 (Or.inl (Or.inl h))
  exact hcopy hnotr hnotr' hq

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem integrable_universalNegativeCharge (S : SelectedHighLowStructure W m)
    (r : S.I) : Integrable (fun x => -S.rootChargeRow r x) μ := by
  apply Integrable.of_bound (S.measurable_rootChargeRow r).neg.aestronglyMeasurable 3
  exact Eventually.of_forall (fun x => by
    have h := S.rootChargeRow_mem_Icc r x
    change ‖-S.rootChargeRow r x‖ ≤ 3
    rw [Real.norm_eq_abs, abs_neg]
    exact abs_le.mpr ⟨h.1, by linarith [h.2]⟩)

/-- Every negative universal charge on the actual common region lies
strictly between zero and the original multiplier magnitude. -/
theorem ae_universalNegativeCharge_mem_Ioo
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalNegativeRegion r p),
      -S.rootChargeRow r x ∈ Ioo (0 : ℝ) (-m) := by
  let B := S.universalNegativeRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hrpos := S.ae_universal_row_pos_on_outside r hW hd hgap hN
  have hrow := S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap
  filter_upwards [ae_restrict_mem hB, ae_restrict_of_ae hrpos,
    ae_restrict_of_ae hrow] with x hx hpos hrowx
  have hxr : S.ρ x ≠ r.val := by
    intro h
    exact hx.1 (Or.inl (Or.inl h))
  have hr := hpos hxr
  change 1 - S.rootChargeRow r x =
    1 - r.val x - m * (if 0 < r.val x then 1 else 0) at hrowx
  rw [ite_eq_left hr] at hrowx
  constructor
  · exact neg_pos.mpr hx.2
  · linarith

theorem universalNegativeChargeMass_pos
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hBpos : 0 < μ (S.universalNegativeRegion r p)) :
    0 < S.universalNegativeChargeMass r p := by
  unfold universalNegativeChargeMass
  exact UniversalSignedPrice.setIntegral_pos_of_ae_pos
    (S.universalNegativeRegion r p)
    (S.measurableSet_universalNegativeRegion r p) hBpos
    (fun x => -S.rootChargeRow r x)
    ((S.integrable_universalNegativeCharge r).integrableOn)
    ((S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN).mono
      (fun _ hx => hx.1))

theorem universalNegativeChargeMass_lt_multiplier_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hBpos : 0 < μ (S.universalNegativeRegion r p)) :
    S.universalNegativeChargeMass r p <
      (-m) * μ.real (S.universalNegativeRegion r p) := by
  let B := S.universalNegativeRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hpos : ∀ᵐ x ∂μ.restrict B, 0 < -m - (-S.rootChargeRow r x) :=
    (S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN).mono
      (fun _ hx => by linarith [hx.2])
  have hfi : IntegrableOn (fun x => -m - (-S.rootChargeRow r x)) B μ :=
    ((integrable_const (-m)).sub (S.integrable_universalNegativeCharge r)).integrableOn
  have hstrict := UniversalSignedPrice.setIntegral_pos_of_ae_pos B hB hBpos
    (fun x => -m - (-S.rootChargeRow r x)) hfi hpos
  rw [integral_sub (μ := μ.restrict B) (integrable_const _)
    ((S.integrable_universalNegativeCharge r).integrableOn),
    setIntegral_const, smul_eq_mul] at hstrict
  change 0 < μ.real B * (-m) - S.universalNegativeChargeMass r p at hstrict
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalBadSquareMoment_nonneg
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    0 ≤ S.universalBadSquareMoment r p := by
  unfold universalBadSquareMoment
  exact integral_nonneg (fun x => (S.universalOwnMass_mem_Icc x).1)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The original H-row missing mass is measurable on the original law
up to the exceptional representatives of the graphon kernel. -/
theorem aestronglyMeasurable_universalPartnerHoleMissingMass
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    AEStronglyMeasurable (S.universalPartnerHoleMissingMass r p) μ := by
  let H := S.universalPartnerHoleRegion r p
  have hf : AEStronglyMeasurable (fun z : Ω × Ω =>
      (1 : ℝ) - adjacencyKernel W z.1 z.2) (μ.prod μ) :=
    (aestronglyMeasurable_const.sub (adjacencyKernel_measurable W))
  have hprod : μ.prod (μ.restrict H) ≤ μ.prod μ :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hm := (hf.mono_measure hprod).integral_prod_right'
  change AEStronglyMeasurable (S.universalPartnerHoleMissingMass r p) μ at hm
  exact hm

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The same original H-row missing mass is bounded by the mass of H,
including the zero-mass and diffuse cases. -/
theorem ae_universalPartnerHoleMissingMass_le_mass
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    ∀ᵐ x ∂μ, S.universalPartnerHoleMissingMass r p x ≤
      μ.real (S.universalPartnerHoleRegion r p) := by
  let H := S.universalPartnerHoleRegion r p
  have hprod : μ.prod (μ.restrict H) ≤ μ.prod μ :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hmeas := (adjacencyKernel_measurable W).mono_measure hprod
  filter_upwards [hmeas.prodMk_left] with x hx
  have hint : IntegrableOn (fun z => 1 - adjacencyKernel W x z) H μ := by
    apply Integrable.of_bound (aestronglyMeasurable_const.sub hx) 1
    exact Eventually.of_forall (fun z => by
      have hz := adjacency_moment_mem W (x, z)
      change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at hz
      change ‖(1 : ℝ) - adjacencyKernel W x z‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hz.2])]
      linarith [hz.1])
  have hle : (fun z : Ω => 1 - adjacencyKernel W x z) ≤ᵐ[μ.restrict H]
      (fun _ => (1 : ℝ)) :=
    Eventually.of_forall (fun z => by
      have hz := adjacency_moment_mem W (x, z)
      change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at hz
      linarith [hz.1])
  have h := integral_mono_ae hint (integrable_const 1) hle
  simpa only [universalPartnerHoleMissingMass, H, setIntegral_const, smul_eq_mul,
    mul_one] using h

/-- The original H×H missing-square moment is the integral of the
unchanged H-row missing mass. -/
def universalHoleSquareMoment (S : SelectedHighLowStructure W m)
    (r p : S.I) : ℝ :=
  ∫ x in S.universalPartnerHoleRegion r p,
    S.universalPartnerHoleMissingMass r p x ∂μ

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem integrable_universalPartnerHoleMissingMass
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    Integrable (S.universalPartnerHoleMissingMass r p) μ := by
  apply Integrable.of_bound
    (S.aestronglyMeasurable_universalPartnerHoleMissingMass r p) 1
  filter_upwards [S.ae_universalPartnerHoleMissingMass_le_mass r p] with x hx
  have hnonneg := S.universalPartnerHoleMissingMass_nonneg r p x
  have hmass : μ.real (S.universalPartnerHoleRegion r p) ≤ 1 := measureReal_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalHoleSquareMoment_nonneg
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    0 ≤ S.universalHoleSquareMoment r p := by
  unfold universalHoleSquareMoment
  exact integral_nonneg (fun x => S.universalPartnerHoleMissingMass_nonneg r p x)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem universalHoleSquareMoment_le_mass_sq
    (S : SelectedHighLowStructure W m) (r p : S.I) :
    S.universalHoleSquareMoment r p ≤
      μ.real (S.universalPartnerHoleRegion r p) ^ 2 := by
  let H := S.universalPartnerHoleRegion r p
  have hbound := integral_mono_ae
    ((S.integrable_universalPartnerHoleMissingMass r p).integrableOn)
    (integrable_const (μ := μ.restrict H) (μ.real H))
    (ae_restrict_of_ae (S.ae_universalPartnerHoleMissingMass_le_mass r p))
  change S.universalHoleSquareMoment r p ≤ _ at hbound
  rw [setIntegral_const, smul_eq_mul] at hbound
  simpa only [pow_two] using hbound

/-- On the original H law, each whole-row atom spends no more than the
single total deficit moment. This also covers diffuse vertices. -/
theorem ae_hole_own_mass_mul_deficit_le_total
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x * S.universalRootDeficit r x ≤
        ∫ h in S.universalPartnerHoleRegion r p, S.universalRootDeficit r h ∂μ := by
  let H := S.universalPartnerHoleRegion r p
  have hgeom := S.ae_universalPartnerHole_missing_deficit_eq_mass_mul
    r p hpair hW hd hgap hell
  have hprod : μ.prod (μ.restrict H) ≤ μ.prod μ :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hmeas := ((adjacencyKernel_measurable W).mono_measure hprod).prodMk_left
  filter_upwards [hgeom, ae_restrict_of_ae hmeas] with x hx hmx
  have hD : Integrable (S.universalRootDeficit r) (μ.restrict H) :=
    (S.integrable_universalRootDeficit r).integrableOn
  have hproduct : Integrable (fun z =>
      (1 - adjacencyKernel W x z) * S.universalRootDeficit r z) (μ.restrict H) := by
    apply Integrable.of_bound
      ((aestronglyMeasurable_const.sub hmx).mul
        ((S.measurable_universalRootDeficit r).aestronglyMeasurable.mono_measure
          Measure.restrict_le_self)) 4
    exact Eventually.of_forall (fun z => by
      have ha := adjacency_moment_mem W (x, z)
      change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at ha
      have hD := S.universalRootDeficit_mem_Icc r z
      have hDhi : S.universalRootDeficit r z ≤ 4 := hD.2
      change ‖(1 - adjacencyKernel W x z) * S.universalRootDeficit r z‖ ≤ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [ha.2]) hD.1)]
      nlinarith [mul_nonneg ha.1 hD.1])
  have hle : (fun z => (1 - adjacencyKernel W x z) *
      S.universalRootDeficit r z) ≤ᵐ[μ.restrict H]
      S.universalRootDeficit r := Eventually.of_forall (fun z => by
        have ha := adjacency_moment_mem W (x, z)
        change adjacencyKernel W x z ∈ Icc (0 : ℝ) 1 at ha
        have hD := S.universalRootDeficit_mem_Icc r z
        nlinarith [mul_nonneg ha.1 hD.1])
  have h := integral_mono_ae hproduct hD hle
  rw [hx] at h
  exact h

/-- On a whole original atom of the partner hole, the hole's missing
row mass is exactly the original atom mass. -/
theorem ae_hole_missing_mass_eq_originalAtomMass_on_whole_fiber
    (S : SelectedHighLowStructure W m) (r p i : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hwhole : ∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val},
      z ∈ S.universalPartnerHoleRegion r p) :
    ∀ᵐ x ∂μ.restrict {z | S.ρ z = i.val},
      S.universalPartnerHoleMissingMass r p x = S.originalAtomMass i := by
  let H := S.universalPartnerHoleRegion r p
  let I : Set Ω := {z | S.ρ z = i.val}
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hmissing := Measure.ae_ae_of_ae_prod
    (S.ae_universalPartnerHole_missing_iff_sameAtom r p hpair hW hd hgap hell)
  have hs := Measure.ae_ae_of_ae_prod
    (hW.strict_gap_structure hd hgap).strict_support
  apply (ae_restrict_iff' hI).mpr
  filter_upwards [hmissing, hs, (ae_restrict_iff' hI).mp hwhole]
    with x hx hsx hHx hxI
  let A : Set Ω := {z | (x, z) ∈ S.sameAtomRelation}
  have hA : MeasurableSet A :=
    S.measurableSet_sameAtomRelation.preimage (measurable_const.prodMk measurable_id)
  have hrow : ∀ᵐ z ∂μ.restrict H,
      1 - adjacencyKernel W x z = A.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_of_ae hsx,
      ae_restrict_mem hH] with z hzero hsupport hz
    have heq := hzero (hHx hxI) hz
    by_cases ha : z ∈ A
    · have hG : adjacencyKernel W x z = 0 := heq.mpr ha
      simp [indicator_of_mem ha, hG]
    · have hG : adjacencyKernel W x z = 1 := by
        have hn : adjacencyKernel W x z ≠ 0 := fun h => ha (heq.mp h)
        change adjacencyKernel W x z =
          if 0 < shiftedKernel W m x z then 1 else 0 at hsupport
        by_cases hk : 0 < shiftedKernel W m x z
        · simpa only [ite_eq_left hk] using hsupport
        · have hz : adjacencyKernel W x z = 0 := by
            simpa only [ite_eq_right hk] using hsupport
          exact False.elim (hn hz)
      simp [indicator_of_notMem ha, hG]
  have hAeq : A = I := by
    ext z
    change (S.ρ x = S.ρ z ∧ S.ρ x ∈ S.I) ↔ S.ρ z = i.val
    constructor
    · exact fun h => h.1.symm.trans hxI
    · exact fun h => ⟨hxI.trans h.symm, hxI ▸ i.property⟩
  have hmass : S.universalPartnerHoleMissingMass r p x = μ.real (H ∩ I) := by
    change (∫ z in H, 1 - adjacencyKernel W x z ∂μ) = _
    rw [integral_congr_ae hrow, hAeq, setIntegral_indicator hI,
      setIntegral_const, smul_eq_mul, mul_one]
  have hfull : μ.real (H ∩ I) = S.originalAtomMass i := by
    change μ.real (H ∩ I) = μ.real I
    apply measureReal_congr
    filter_upwards [(ae_restrict_iff' hI).mp hwhole] with z hz
    exact propext ⟨fun h => h.2, fun h => ⟨hz h, h⟩⟩
  exact hmass.trans hfull

/-- The hole missing mass at almost every vertex spends at least its
square in the original H×H missing-pair inventory. -/
theorem ae_hole_missing_mass_sq_le_square_moment
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      (S.universalPartnerHoleMissingMass r p x) ^ 2 ≤
        S.universalHoleSquareMoment r p := by
  let H := S.universalPartnerHoleRegion r p
  have hatom := S.ae_universalPartnerHole_atom_of_missing_mass_pos
    r p hpair hW hd hgap hell
  filter_upwards [hatom] with x hx
  by_cases hpos : 0 < S.universalPartnerHoleMissingMass r p x
  · obtain ⟨i, _, hwhole, hmass, _⟩ := hx hpos
    let I : Set Ω := {z | S.ρ z = i.val}
    have hI : MeasurableSet I := (S.hfibers i.val i.property).1
    have hIH : I ≤ᵐ[μ] H := (ae_restrict_iff' hI).mp hwhole
    have hconst : ∀ᵐ z ∂μ.restrict I,
        S.universalPartnerHoleMissingMass r p z = μ.real I := by
      simpa only [I, originalAtomMass] using
        S.ae_hole_missing_mass_eq_originalAtomMass_on_whole_fiber
          r p i hpair hW hd hgap hell hwhole
    have hbound := UniversalSignedPrice.atom_square_le_total μ H I
      (S.universalPartnerHoleMissingMass r p)
      ((S.integrable_universalPartnerHoleMissingMass r p).integrableOn)
      (Eventually.of_forall (fun z => S.universalPartnerHoleMissingMass_nonneg r p z))
      hIH hconst
    rw [hmass]
    exact hbound
  · have hzero : S.universalPartnerHoleMissingMass r p x = 0 :=
      le_antisymm (le_of_not_gt hpos)
        (S.universalPartnerHoleMissingMass_nonneg r p x)
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)]
    exact S.universalHoleSquareMoment_nonneg r p

theorem ae_hole_missing_mass_le_sqrt_square_moment
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤
        Real.sqrt (S.universalHoleSquareMoment r p) := by
  filter_upwards [S.ae_hole_missing_mass_sq_le_square_moment
    r p hpair hW hd hgap hell] with x hx
  exact (Real.le_sqrt (S.universalPartnerHoleMissingMass_nonneg r p x)
    (S.universalHoleSquareMoment_nonneg r p)).mpr hx

/-- A hole row loses both the entire partner atom and its own missing
mass before its original adjacency degree is counted. -/
theorem ae_hole_degree_add_missing_le_one_sub_partner
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      (∫ z, adjacencyKernel W x z ∂μ) +
        S.universalPartnerHoleMissingMass r p x ≤
          1 - μ.real {z | S.ρ z = p.val} := by
  let H := S.universalPartnerHoleRegion r p
  let P : Set Ω := {z | S.ρ z = p.val}
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hle : (μ.restrict P).prod (μ.restrict H) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hzero : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict H),
      shiftedKernel W m q.1 q.2 = 0 := by
    filter_upwards [ae_mono hle (S.ae_kernel_eq_fiber_row p.val p.property),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_partner_row_zero_on_universalHole r p hW)] with q hrow hp hz
    exact (hrow hp).trans hz
  have hAdjPH : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict H),
      adjacencyKernel W q.1 q.2 = 0 := by
    filter_upwards [hzero,
      ae_mono hle (hW.strict_gap_structure hd hgap).strict_support]
      with q hz hs
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedKernel W m q.1 q.2 then 1 else 0) at hs
    rw [hz] at hs
    simpa only [lt_irrefl, ↓reduceIte] using hs
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict H) (ν := μ.restrict P)).quasiMeasurePreserving
  have hAdjHP : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict P),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle' : (μ.restrict H).prod (μ.restrict P) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [hswap.ae hAdjPH, ae_mono hle' (adjacencyKernel_symm W)]
      with q hz hs
    change adjacencyKernel W q.2 q.1 = 0 at hz
    exact hs.trans hz
  have hsec := Measure.ae_ae_of_ae_prod hAdjHP
  filter_upwards [hsec] with x hx
  have hzeroP := (ae_restrict_iff' hP).mp hx
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  have hm : Integrable (fun z => 1 - adjacencyKernel W x z) μ :=
    (integrable_const 1).sub hi
  have hiP : Integrable (P.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hP
  have hiH : Integrable (H.indicator (fun z => 1 - adjacencyKernel W x z)) μ :=
    hm.indicator hH
  have hpoint : ∀ᵐ z ∂μ,
      P.indicator (fun _ => (1 : ℝ)) z +
        H.indicator (fun z => 1 - adjacencyKernel W x z) z ≤
          1 - adjacencyKernel W x z := by
    filter_upwards [hzeroP] with z hz
    by_cases hp : z ∈ P
    · have hnotH : z ∉ H := by
        intro hzh
        exact hzh (Or.inl (Or.inr hp))
      rw [hz hp, indicator_of_mem hp, indicator_of_notMem hnotH]
      norm_num
    · rw [indicator_of_notMem hp]
      by_cases hh : z ∈ H
      · rw [indicator_of_mem hh]
        simp
      · rw [indicator_of_notMem hh]
        have hA := (adjacency_moment_mem W (x, z)).2
        change adjacencyKernel W x z ≤ 1 at hA
        linarith
  have hbound := integral_mono_ae (hiP.add hiH) hm hpoint
  change (∫ z, P.indicator (fun _ => (1 : ℝ)) z +
      H.indicator (fun z => 1 - adjacencyKernel W x z) z ∂μ) ≤
        ∫ z, 1 - adjacencyKernel W x z ∂μ at hbound
  rw [integral_add hiP hiH, integral_indicator hP, setIntegral_const,
    smul_eq_mul, mul_one, integral_indicator hH,
    integral_sub (integrable_const 1) hi,
    integral_const, probReal_univ, one_smul] at hbound
  change μ.real P + S.universalPartnerHoleMissingMass r p x ≤
    1 - ∫ z, adjacencyKernel W x z ∂μ at hbound
  linarith

/-- The original H-row missing mass has the strict two-head capacity
`1-2A-b`; no density bound is substituted for this row statement. -/
theorem ae_hole_missing_mass_le_capacity
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤
        1 - 2 * S.originalAtomMass r - S.originalAtomMass p := by
  filter_upwards [S.ae_hole_degree_add_missing_le_one_sub_partner r p hW hd hgap,
    S.ae_universalPartnerHole_degree_ge_twice_mass r p hpair hW hd hgap hell hN]
    with x hupper hlower
  change (∫ z, adjacencyKernel W x z ∂μ) +
      S.universalPartnerHoleMissingMass r p x ≤
        1 - S.originalAtomMass p at hupper
  change 2 * S.originalAtomMass r ≤ ∫ z, adjacencyKernel W x z ∂μ at hlower
  linarith

/-- Both physical constraints on a single H-atom are spent together.
The square inventory is the exact original H×H moment. -/
theorem ae_hole_missing_mass_le_min_capacity_sqrt
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤
        min (1 - 2 * S.originalAtomMass r - S.originalAtomMass p)
          (Real.sqrt (S.universalHoleSquareMoment r p)) := by
  filter_upwards [S.ae_hole_missing_mass_le_capacity r p hpair hW hd hgap hell hN,
    S.ae_hole_missing_mass_le_sqrt_square_moment r p hpair hW hd hgap hell]
    with x hcap hsqrt
  exact le_min hcap hsqrt

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem integrable_hole_reciprocal
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (ax α : ℝ)
    (hα : α < S.originalAtomMass r - ax)
    (ha : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤ α) :
    IntegrableOn (fun x => 1 /
      (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p x - ax))
      (S.universalPartnerHoleRegion r p) μ := by
  let H := S.universalPartnerHoleRegion r p
  let a := S.universalPartnerHoleMissingMass r p
  have haesm : AEStronglyMeasurable a (μ.restrict H) :=
    (S.aestronglyMeasurable_universalPartnerHoleMissingMass r p).mono_measure
      Measure.restrict_le_self
  have hsm : AEStronglyMeasurable
      (fun x => 1 / (S.originalAtomMass r - a x - ax)) (μ.restrict H) :=
    (aestronglyMeasurable_const.div₀
      ((aestronglyMeasurable_const.sub haesm).sub aestronglyMeasurable_const))
  apply Integrable.of_bound hsm (1 / (S.originalAtomMass r - ax - α))
  filter_upwards [ha] with x hx
  have hden : 0 < S.originalAtomMass r - a x - ax := by linarith
  have hfloor : 0 < S.originalAtomMass r - ax - α := by linarith
  have hle : S.originalAtomMass r - ax - α ≤
      S.originalAtomMass r - a x - ax := by linarith
  change ‖1 / (S.originalAtomMass r - a x - ax)‖ ≤
    1 / (S.originalAtomMass r - ax - α)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by norm_num) hden.le)]
  exact one_div_le_one_div_of_le hfloor hle

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The exact original H×H square moment is spent once in the
reciprocal correction, with a uniform positive pole. -/
theorem hole_reciprocal_le
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (z α ax : ℝ)
    (hk : 0 < S.originalAtomMass r - z)
    (hα : α < S.originalAtomMass r - z)
    (hax : ax ≤ z)
    (ha : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤ α) :
    (∫ x in S.universalPartnerHoleRegion r p,
      1 / (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p x - ax) ∂μ) ≤
      μ.real (S.universalPartnerHoleRegion r p) / (S.originalAtomMass r - z) +
        S.universalHoleSquareMoment r p /
          ((S.originalAtomMass r - z) * (S.originalAtomMass r - z - α)) := by
  apply UniversalSignedPrice.reciprocal_integral_le
    (S.universalPartnerHoleRegion r p) (S.universalPartnerHoleMissingMass r p)
    (S.originalAtomMass r) z α ax (S.universalHoleSquareMoment r p)
    hk hα hax
    ((S.integrable_universalPartnerHoleMissingMass r p).integrableOn)
    (S.integrable_hole_reciprocal r p ax α (by linarith) ha)
  · filter_upwards [ha] with x hx
    exact ⟨S.universalPartnerHoleMissingMass_nonneg r p x, hx⟩
  · rfl

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem integrable_hole_positive_deficit_ratio
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (θ ax α : ℝ) (hθ : 0 ≤ θ)
    (hα : α < S.originalAtomMass r - ax)
    (ha : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤ α) :
    IntegrableOn (fun x =>
      max (S.universalRootDeficit r x - θ) 0 /
        (S.originalAtomMass r - S.universalPartnerHoleMissingMass r p x - ax))
      (S.universalPartnerHoleRegion r p) μ := by
  let H := S.universalPartnerHoleRegion r p
  let a := S.universalPartnerHoleMissingMass r p
  let D := S.universalRootDeficit r
  have haesm : AEStronglyMeasurable a (μ.restrict H) :=
    (S.aestronglyMeasurable_universalPartnerHoleMissingMass r p).mono_measure
      Measure.restrict_le_self
  have hDesm : AEStronglyMeasurable D (μ.restrict H) :=
    (S.measurable_universalRootDeficit r).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hsm : AEStronglyMeasurable
      (fun x => max (D x - θ) 0 / (S.originalAtomMass r - a x - ax))
      (μ.restrict H) :=
    (continuous_max.comp_aestronglyMeasurable₂
      (hDesm.sub aestronglyMeasurable_const) aestronglyMeasurable_const).div₀
      ((aestronglyMeasurable_const.sub haesm).sub aestronglyMeasurable_const)
  apply Integrable.of_bound hsm (4 / (S.originalAtomMass r - ax - α))
  filter_upwards [ha] with x hx
  have hden : 0 < S.originalAtomMass r - a x - ax := by linarith
  have hfloor : 0 < S.originalAtomMass r - ax - α := by linarith
  have hdenle : S.originalAtomMass r - ax - α ≤
      S.originalAtomMass r - a x - ax := by linarith
  have hD := S.universalRootDeficit_mem_Icc r x
  have hnum : 0 ≤ max (D x - θ) 0 := le_max_right _ _
  have hnum4 : max (D x - θ) 0 ≤ 4 :=
    max_le (by dsimp [D] at *; linarith [hD.2]) (by norm_num)
  change ‖max (D x - θ) 0 / (S.originalAtomMass r - a x - ax)‖ ≤
    4 / (S.originalAtomMass r - ax - α)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden.le)]
  apply (div_le_div_iff₀ hden hfloor).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hnum4) hfloor.le,
    mul_nonneg hnum (sub_nonneg.mpr hdenle)]


end Erdos1017.CappedModel.SelectedHighLowStructure

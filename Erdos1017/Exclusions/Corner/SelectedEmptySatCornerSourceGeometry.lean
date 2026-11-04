module

public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerContext
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerBadRegion
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitRows

/-!
# Source geometry of the empty-source saturated corner

The private source in the null-source recovery supplies the nonexceptional
hard-moment data, with no new source law or numeric moment bound introduced.
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

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem integrable_source_marks (S : SelectedHighLowStructure W m) (r : S.I) :
    Integrable S.ownIndependentMass μ ∧
      Integrable (fun x => S.ownIndependentMass x * S.universalRootDeficit r x) μ := by
  have ha : Integrable S.ownIndependentMass μ := Integrable.of_bound
    S.measurable_ownIndependentMass.aestronglyMeasurable 1
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (show 0 ≤ S.ownIndependentMass x from measureReal_nonneg)]
      exact measureReal_le_one))
  refine ⟨ha, Integrable.of_bound
    (S.measurable_ownIndependentMass.mul
      (S.measurable_universalRootDeficit r)).aestronglyMeasurable 4 ?_⟩
  exact Eventually.of_forall (fun x => by
    have hax : 0 ≤ S.ownIndependentMass x := measureReal_nonneg
    have hax1 : S.ownIndependentMass x ≤ 1 := measureReal_le_one
    have hdx := S.universalRootDeficit_mem_Icc r x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hax hdx.1)]
    exact (mul_le_mul_of_nonneg_left hdx.2 hax).trans (by linarith only [hax1]))

private theorem private_source_deficit_budget
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let H := S.universalPartnerHoleRegion r p
    let U := S.universalPartnerCommonRegion r p
    let J := S.reverseCompulsorySource {p}
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real H + μ.real U - D
    let Sigma := ∫ x in U, -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ
    0 ≤ Sigma ∧ (∫ x in J, S.universalRootDeficit r x ∂μ) ≤
      (1 + m) * (μ.real J - L) - Sigma := by
  dsimp only
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let J := S.reverseCompulsorySource {p}
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  let L := μ.real H + μ.real U - D
  let Sigma := ∫ x in U, -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hsubset := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  have hinter : H ∩ J =ᵐ[μ] J := hsubset.mono (fun _ hx =>
    propext ⟨And.right, fun h => ⟨hx h, h⟩⟩)
  have hSigma : 0 ≤ Sigma := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae
      (S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN)]
      with x hx hs
    have hxr : S.ρ x ≠ r.val := fun h => hx (Or.inl (Or.inl h))
    exact neg_nonneg.mpr (hs hxr (S.common_region_mem_rootNeighborhood r p hx))
  have hparts := integral_inter_add_sdiff (s := H) hJ
    (S.integrable_universalRootDeficit r).integrableOn
  rw [setIntegral_congr_set hinter] at hparts
  have hmass := measureReal_inter_add_sdiff (μ := μ) (s := H) hJ
  rw [measureReal_congr hinter] at hmass
  have hmass' := congrArg (fun z : ℝ => (1 + m) * z) hmass
  have hfloor := integral_mono_ae (integrable_const (μ := μ.restrict (H \ J)) (1 + m))
    (S.integrable_universalRootDeficit r).integrableOn
    ((S.ae_universalRootDeficit_gt_floor_on_hole_compl_source r p hpair hW hd hgap hell hN).mono
      (fun _ hx => hx.le))
  rw [setIntegral_const, smul_eq_mul] at hfloor
  have hshared := S.empty_sat_corner_shared_budget r p hpair hW hd hgap hN
  have hdelta : 0 < 1 + m := by linarith only [hell]
  have hratio : (1 + m) * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hdelta.ne'
  change (∫ x in H, S.universalRootDeficit r x ∂μ) + Sigma =
    1 - m - 4 * (c - m * d) - (1 + m) * μ.real U at hshared
  change 0 ≤ Sigma ∧ (∫ x in J, S.universalRootDeficit r x ∂μ) ≤
    (1 + m) * (μ.real J - L) - Sigma
  refine ⟨hSigma, ?_⟩
  dsimp only [L]
  nlinarith only [hparts, hmass', hfloor, hshared, hratio]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integrable_original_missing_row (x : Ω) :
    Integrable (fun y => 1 - adjacencyKernel W x y) μ := by
  have hmeas : StronglyMeasurable (adjacencyKernel W x) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound (stronglyMeasurable_const.sub hmeas).aestronglyMeasurable 1
  exact Eventually.of_forall (fun y => by
    have hy := adjacency_moment_mem W (x, y)
    change adjacencyKernel W x y ∈ Icc (0 : ℝ) 1 at hy
    change ‖(1 : ℝ) - adjacencyKernel W x y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy.2)]
    linarith only [hy.1])

private theorem private_source_own_mass_le_hole_missing
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
      S.ownIndependentMass x ≤ S.universalPartnerHoleMissingMass r p x := by
  let J := S.reverseCompulsorySource {p}
  let H := S.universalPartnerHoleRegion r p
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  have hsubset := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  have hraw := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [ReverseRecovery.ae_private_source_graph_marginal r p hpair hW hd hgap hell,
    ae_restrict_of_ae hraw] with x hx hrow
  have hgeq : (∫ y in J, G (x, y) ∂μ) = ∫ y in J, adjacencyKernel W x y ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hrow] with y hy
    exact hy.symm
  have hmissing : (∫ y in J, 1 - adjacencyKernel W x y ∂μ) = S.ownIndependentMass x := by
    have ha : Integrable (adjacencyKernel W x) μ := by
      have heq : adjacencyKernel W x = fun y => 1 - (1 - adjacencyKernel W x y) := by
        funext y
        ring
      rw [heq]
      exact (integrable_const 1).sub (integrable_original_missing_row x)
    rw [integral_sub (integrable_const (1 : ℝ)) ha.integrableOn,
      setIntegral_const, smul_eq_mul, mul_one, ← hgeq, hx]
    ring
  have hbound := setIntegral_mono_set
    (integrable_original_missing_row (W := W) x).integrableOn
    (Eventually.of_forall (fun y => sub_nonneg.mpr (adjacency_moment_mem W (x, y)).2))
    hsubset
  rw [hmissing] at hbound
  exact hbound

private theorem private_source_row_data
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let H := S.universalPartnerHoleRegion r p
    let U := S.universalPartnerCommonRegion r p
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real H + μ.real U - D
    let E := D - S.originalAtomMass r
    0 < L → E < L →
      (∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L) →
      ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
        0 ≤ S.ownIndependentMass x ∧ 2 * S.ownIndependentMass x < L + E ∧
          (1 + m) * (L - S.ownIndependentMass x) ≤
            (L + E - 2 * S.ownIndependentMass x) * S.universalRootDeficit r x := by
  dsimp only
  intro hL hEL hsmall
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let J := S.reverseCompulsorySource {p}
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  let L := μ.real H + μ.real U - D
  let E := D - S.originalAtomMass r
  have hdelta : 0 < 1 + m := by linarith only [hell]
  have hratio : (1 + m) * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hdelta.ne'
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hrow := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_deficit_row r p hpair hW hd hgap hell hN)
  have hsmall' := (ae_restrict_iff' hH).mp hsmall
  have hsubset := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  filter_upwards [private_source_own_mass_le_hole_missing S r p hpair hW hd hgap hell,
    ae_restrict_of_ae hrow, ae_restrict_of_ae hsmall', ae_restrict_of_ae hsubset,
    ae_restrict_mem (S.measurableSet_reverseCompulsorySource {p})]
    with x hown hxrow hxsmall hxH hxJ
  have hx := hxrow (hxH hxJ)
  have hax : S.universalPartnerHoleMissingMass r p x < L := hxsmall (hxH hxJ)
  have hk := S.universalPartnerCommonMissingMass_nonneg r p x
  have hd0 := (S.universalRootDeficit_mem_Icc r x).1
  have hBx := S.universalPartnerCommonMissingDeficit_ge_floor r p hpair hW hd hgap hell hN x
  have hbase : (1 + m) * (L - S.universalPartnerHoleMissingMass r p x) ≤
      (L + E - 2 * S.universalPartnerHoleMissingMass r p x -
        S.universalPartnerCommonMissingMass r p x) * S.universalRootDeficit r x := by
    dsimp only [L, E, H, U]
    nlinarith only [hx, hBx, hratio]
  have hpositive : 0 < (1 + m) * (L - S.universalPartnerHoleMissingMass r p x) :=
    mul_pos hdelta (sub_pos.mpr hax)
  have hcoef : 0 < L + E - 2 * S.universalPartnerHoleMissingMass r p x -
      S.universalPartnerCommonMissingMass r p x := by
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hd0
    linarith only [hpositive, hbase, hp]
  have hcoef' : 0 < L + E - 2 * S.universalPartnerHoleMissingMass r p x := by
    linarith only [hcoef, hk]
  have hkd := mul_nonneg hk hd0
  have htwod : 1 + m < 2 * S.universalRootDeficit r x := by
    by_contra hn
    have hp := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hcoef'.le
    have hgap := mul_pos hdelta (sub_pos.mpr hEL)
    nlinarith only [hbase, hp, hgap, hkd]
  have hlift := mul_nonneg (sub_nonneg.mpr hown) (sub_nonneg.mpr htwod.le)
  refine ⟨measureReal_nonneg, ?_, ?_⟩
  · linarith only [hown, hcoef']
  · change (1 + m) * (L - S.ownIndependentMass x) ≤
      (L + E - 2 * S.ownIndependentMass x) * S.universalRootDeficit r x
    nlinarith only [hbase, hlift, hkd]

private theorem private_source_triangle
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let J := S.reverseCompulsorySource {p}
    let G := PhysicalCliqueRepresentative.edgeIndicator
      (Function.uncurry (PhysicalRepresentative.adjacency W m))
    ∀ᵐ q ∂(μ.restrict J).prod (μ.restrict J),
      shiftedKernel W m q.1 q.2 + (1 + m) * G q ≤
        (S.universalRootDeficit r q.1 + S.universalRootDeficit r q.2) * G q := by
  dsimp only
  let J := S.reverseCompulsorySource {p}
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  have hle : (μ.restrict J).prod (μ.restrict J) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hout : ∀ᵐ x ∂μ.restrict J, S.ρ x ≠ r.val := by
    filter_upwards [ae_restrict_of_ae
      (S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell),
      ae_restrict_mem (S.measurableSet_reverseCompulsorySource {p})] with x hx hxJ hxr
    exact hx hxJ (Or.inl (Or.inl hxr))
  filter_upwards [ae_mono hle (S.ae_universal_root_triangle r hW hd hgap hN),
    ae_mono hle (PhysicalRepresentative.charge_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support),
    ae_mono hle (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support),
    Measure.quasiMeasurePreserving_fst.ae hout,
    Measure.quasiMeasurePreserving_snd.ae hout] with q ht hY hA hx hy
  change shiftedKernel W m q.1 q.2 + (1 + m) * G q ≤
    (S.universalRootDeficit r q.1 + S.universalRootDeficit r q.2) * G q
  have hM := shiftedMoment_eq W m q
  change shiftedKernel W m q.1 q.2 = chargeKernel W q.1 q.2 -
    m * adjacencyKernel W q.1 q.2 at hM
  change adjacencyKernel W q.1 q.2 = G q at hA
  rw [← hY, hA] at hM
  cases he : PhysicalRepresentative.adjacency W m q.1 q.2 with
  | false =>
    have hG : G q = 0 := by
      simp [G, PhysicalCliqueRepresentative.edgeIndicator, Function.uncurry, he]
    have hzero := PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2 he
    rw [hzero, hG] at hM
    simp [hM, hG]
  | true =>
    have hG : G q = 1 := by
      simp [G, PhysicalCliqueRepresentative.edgeIndicator, Function.uncurry, he]
    have htriangle := ht hx hy he
    rw [hG] at hM ⊢
    dsimp only [universalRootDeficit]
    linarith only [htriangle, hM]

namespace ReverseRecovery

variable {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery)

/-- The entire private source in the same null-source recovery supplies
the actual nonexceptional hard-moment data. No new source law, numeric
moment bound or conditional parent section is an input. -/
theorem empty_sat_corner_source_geometry (r p : S.I) (hr : R.plateau = {r})
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    let H := S.universalPartnerHoleRegion r p
    let U := S.universalPartnerCommonRegion r p
    let J := S.reverseCompulsorySource {p}
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real H + μ.real U - D
    let E := D - S.originalAtomMass r
    let a := S.ownIndependentMass
    let deficit := S.universalRootDeficit r
    let Sigma := ∫ x in U, -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ
    let G := PhysicalCliqueRepresentative.edgeIndicator
      (Function.uncurry (PhysicalRepresentative.adjacency W m))
    0 < L → E < L →
      (∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L) →
      MeasurableSet J ∧ 0 < μ.real J ∧ S.originalAtomMass p + μ.real J < S.originalAtomMass r ∧
        0 ≤ Sigma ∧ Measurable a ∧ Integrable a (μ.restrict J) ∧
        Integrable deficit (μ.restrict J) ∧
        Integrable (fun x => a x * deficit x) (μ.restrict J) ∧
        (∀ᵐ x ∂μ.restrict J, 0 ≤ a x ∧ 2 * a x < L + E ∧
          (1 + m) * (L - a x) ≤ (L + E - 2 * a x) * deficit x) ∧
        (∫ x in J, deficit x ∂μ) ≤ (1 + m) * (μ.real J - L) - Sigma ∧
        (∀ᵐ x ∂μ.restrict J, (∫ y in J, G (x, y) ∂μ) = μ.real J - a x) ∧
        (∀ᵐ q ∂(μ.restrict J).prod (μ.restrict J),
          shiftedKernel W m q.1 q.2 + (1 + m) * G q ≤
            (deficit q.1 + deficit q.2) * G q) := by
  dsimp only
  intro hL hEL hsmall
  let J := S.reverseCompulsorySource {p}
  let U := S.universalPartnerCommonRegion r p
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  let L := μ.real (S.universalPartnerHoleRegion r p) + μ.real U - D
  let Sigma := ∫ x in U, -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨hJ, hmass⟩ := R.saturated_empty_source_private_mass r p hpair hr hW hd hgap hell hnull
  obtain ⟨hSigma, hbudget⟩ := private_source_deficit_budget S r p hpair hW hd hgap hell hN
  change 0 < L at hL
  change (∫ x in J, S.universalRootDeficit r x ∂μ) ≤
    (1 + m) * (μ.real J - L) - Sigma at hbudget
  have hnonnegative : 0 ≤ ∫ x in J, S.universalRootDeficit r x ∂μ :=
    integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  have hdelta : 0 < 1 + m := by linarith only [hell]
  have hj : 0 < μ.real J := by
    have hge : L ≤ μ.real J := by
      by_contra hn
      have hp := mul_neg_of_pos_of_neg hdelta (sub_neg.mpr (lt_of_not_ge hn))
      linarith only [hbudget, hSigma, hnonnegative, hp]
    exact hL.trans_le hge
  obtain ⟨ha, had⟩ := integrable_source_marks S r
  refine ⟨hJ, hj, hmass, hSigma, S.measurable_ownIndependentMass, ha.integrableOn,
    (S.integrable_universalRootDeficit r).integrableOn, had.integrableOn, ?_, hbudget,
    ae_private_source_graph_marginal r p hpair hW hd hgap hell,
    private_source_triangle S r p hpair hW hd hgap hell hN⟩
  exact private_source_row_data S r p hpair hW hd hgap hell hN hL hEL hsmall

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure

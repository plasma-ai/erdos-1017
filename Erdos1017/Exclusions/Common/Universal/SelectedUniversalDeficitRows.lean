module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitBudget
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalSATGeometry

/-!
# Deficit rows on the partner hole

The stationary row and the universal-root triangle give the strong missing-pair
deficit inequality at almost every partner-hole vertex, and every such vertex
has enough original neighbors to pay for all missing pairs in the two outside
regions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Every fixed original shifted-kernel row is integrable on the original
probability law, without selecting an almost-everywhere representative. -/
private theorem integrable_universal_shifted_row (x : Ω) :
    Integrable (shiftedKernel W m x) μ := by
  have hmeas : StronglyMeasurable (shiftedKernel W m x) := by
    exact (W.stronglyMeasurable_moment
      (continuous_shiftedColor m).measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (3 + ‖m‖)
  exact Eventually.of_forall (fun z => by
    have h := norm_integral_le_of_norm_le_const (μ := W.kernel (x, z))
      (Filter.Eventually.of_forall (shiftedColor_norm_le m))
    simpa only [shiftedKernel, shiftedMoment, DecoratedKernel.moment,
      probReal_univ, mul_one] using h)

/-- The original adjacency row and its weighted missing-deficit section
are integrable for every fixed vertex. -/
private theorem integrable_universal_adjacency_row (x : Ω) :
    Integrable (adjacencyKernel W x) μ := by
  have hmeas : StronglyMeasurable (adjacencyKernel W x) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  exact Eventually.of_forall (fun z => by
    change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
    exact (adjacency_moment_mem W (x, z)).2)

private theorem integrable_universal_missing_deficit_row
    (S : SelectedHighLowStructure W m) (r : S.I) (x : Ω) :
    Integrable (fun z => (1 - adjacencyKernel W x z) * S.universalRootDeficit r z) μ := by
  have hG : Measurable (adjacencyKernel W x) := by
    exact (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable.comp
        (measurable_const.prodMk measurable_id)
  have hmeas : Measurable (fun z => (1 - adjacencyKernel W x z) *
      S.universalRootDeficit r z) :=
    (measurable_const.sub hG).mul (S.measurable_universalRootDeficit r)
  apply Integrable.of_bound hmeas.aestronglyMeasurable 4
  exact Eventually.of_forall (fun z => by
    have hG0 := (adjacency_moment_mem W (x, z)).1
    have hG1 := (adjacency_moment_mem W (x, z)).2
    change 0 ≤ adjacencyKernel W x z at hG0
    change adjacencyKernel W x z ≤ 1 at hG1
    have hD := S.universalRootDeficit_mem_Icc r z
    have hD0 := hD.1
    have hD4 := hD.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hD.1)]
    nlinarith [mul_nonneg (show 0 ≤ 1 - adjacencyKernel W x z by linarith)
      (show 0 ≤ 4 - S.universalRootDeficit r z by linarith)])

private theorem integrable_universal_present_deficit_row
    (S : SelectedHighLowStructure W m) (r : S.I) (x : Ω) :
    Integrable (fun z => S.universalRootDeficit r z * adjacencyKernel W x z) μ := by
  have hG : Measurable (adjacencyKernel W x) := by
    exact (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable.comp
        (measurable_const.prodMk measurable_id)
  have hmeas : Measurable (fun z => S.universalRootDeficit r z * adjacencyKernel W x z) :=
    (S.measurable_universalRootDeficit r).mul hG
  apply Integrable.of_bound hmeas.aestronglyMeasurable 4
  exact Eventually.of_forall (fun z => by
    have hG0 := (adjacency_moment_mem W (x, z)).1
    have hG1 := (adjacency_moment_mem W (x, z)).2
    change 0 ≤ adjacencyKernel W x z at hG0
    change adjacencyKernel W x z ≤ 1 at hG1
    have hD := S.universalRootDeficit_mem_Icc r z
    have hD0 := hD.1
    have hD4 := hD.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD0 hG0)]
    nlinarith [mul_nonneg hG0 (show 0 ≤ 4 - S.universalRootDeficit r z by linarith)])

/-- Integrate the actual universal-root triangle over any measurable
outside region. The missing and present factors retain the same edge law. -/
private theorem universal_triangle_set_integral
    (S : SelectedHighLowStructure W m) (r : S.I) (x : Ω)
    (E : Set Ω) (hE : MeasurableSet E)
    (hEout : E ⊆ {z | S.ρ z ≠ r.val})
    (htri : ∀ᵐ z ∂μ, S.ρ z ≠ r.val →
      chargeKernel W x z + adjacencyKernel W x z ≤
        (S.universalRootDeficit r x + S.universalRootDeficit r z) *
          adjacencyKernel W x z) :
    (∫ z in E, shiftedKernel W m x z ∂μ) +
        (1 + m) * (∫ z in E, adjacencyKernel W x z ∂μ) ≤
      S.universalRootDeficit r x * (∫ z in E, adjacencyKernel W x z ∂μ) +
        ∫ z in E, S.universalRootDeficit r z * adjacencyKernel W x z ∂μ := by
  have hK := integrable_universal_shifted_row (W := W) (m := m) x
  have hG := integrable_universal_adjacency_row (W := W) x
  have hDG := S.integrable_universal_present_deficit_row r x
  have hleft : Integrable (fun z => shiftedKernel W m x z +
      (1 + m) * adjacencyKernel W x z) (μ.restrict E) :=
    (hK.add (hG.const_mul _)).integrableOn
  have hright : Integrable (fun z => S.universalRootDeficit r x *
      adjacencyKernel W x z + S.universalRootDeficit r z * adjacencyKernel W x z)
      (μ.restrict E) :=
    ((hG.const_mul _).add hDG).integrableOn
  have hmono : (∫ z in E, shiftedKernel W m x z +
      (1 + m) * adjacencyKernel W x z ∂μ) ≤
      ∫ z in E, S.universalRootDeficit r x * adjacencyKernel W x z +
        S.universalRootDeficit r z * adjacencyKernel W x z ∂μ := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_of_ae htri, ae_restrict_mem hE] with z hz hEz
    have h := hz (hEout hEz)
    have hshift := shiftedMoment_eq W m (x, z)
    change shiftedKernel W m x z = chargeKernel W x z -
      m * adjacencyKernel W x z at hshift
    rw [hshift]
    nlinarith
  rw [integral_add hK.integrableOn (hG.const_mul _).integrableOn,
    integral_const_mul,
    integral_add (hG.const_mul _).integrableOn hDG.integrableOn,
    integral_const_mul] at hmono
  exact hmono

/-- Four literal original regions give an exact integral partition,
including all exceptional points, before any kernel AE rewrites. -/
private theorem integral_universal_four_regions
    (S : SelectedHighLowStructure W m) (r p : S.I) (hrp : r ≠ p)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ x, f x ∂μ) =
      (∫ x in {x | S.ρ x = r.val}, f x ∂μ) +
      (∫ x in {x | S.ρ x = p.val}, f x ∂μ) +
      (∫ x in S.universalPartnerHoleRegion r p, f x ∂μ) +
      (∫ x in S.universalPartnerCommonRegion r p, f x ∂μ) := by
  let I : Set Ω := {x | S.ρ x = r.val}
  let P : Set Ω := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hIP : Disjoint I P := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hrp (Subtype.ext (hx.symm.trans hy))
  have hIPH : Disjoint (I ∪ P) H := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hy (Or.inl hx)
  have hIPHU : Disjoint (I ∪ P ∪ H) U := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hy hx
  have hwhole : I ∪ P ∪ H ∪ U = univ := S.universalPartner_regions_partition r p
  calc
    (∫ x, f x ∂μ) = ∫ x in I ∪ P ∪ H ∪ U, f x ∂μ := by rw [hwhole]; simp
    _ = (∫ x in I ∪ P ∪ H, f x ∂μ) + (∫ x in U, f x ∂μ) :=
      setIntegral_union hIPHU hU hf.integrableOn hf.integrableOn
    _ = (∫ x in I ∪ P, f x ∂μ) + (∫ x in H, f x ∂μ) +
        (∫ x in U, f x ∂μ) := by
      rw [setIntegral_union hIPH hH hf.integrableOn hf.integrableOn]
    _ = (∫ x in I, f x ∂μ) + (∫ x in P, f x ∂μ) +
        (∫ x in H, f x ∂μ) + (∫ x in U, f x ∂μ) := by
      rw [setIntegral_union hIP hP hf.integrableOn hf.integrableOn]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The original homogeneous whole-row identity also holds with its
whole-fiber vertex in the second coordinate. -/
private theorem ae_universal_shifted_column
    (S : SelectedHighLowStructure W m) (q : S.I) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.2 = q.val →
      shiftedKernel W m p.1 p.2 = q.val p.1 := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_kernel_eq_fiber_row q.val q.property)
  filter_upwards [hswap, shiftedMoment_symm W m] with p hs hh hq
  exact hh.symm.trans (hs hq)

/-- The original stationary shifted row splits exactly into the four
physical regions. On H the partner contributes zero and the universal
head contributes its actual root deficit. -/
private theorem ae_universal_hole_shifted_row
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      (∫ z in S.universalPartnerHoleRegion r p, shiftedKernel W m x z ∂μ) +
        (∫ z in S.universalPartnerCommonRegion r p, shiftedKernel W m x z ∂μ) =
          2 * (c - m * d) - S.originalAtomMass r *
            (1 - m - S.universalRootDeficit r x) := by
  let I : Set Ω := {x | S.ρ x = r.val}
  let P : Set Ω := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hcolumns := (S.ae_universal_shifted_column r).and
    (S.ae_universal_shifted_column p)
  have hsection := Measure.ae_ae_of_ae_prod hcolumns
  have hD := (ae_restrict_iff' hH).mp
    (S.ae_universalRootDeficit_eq_score_on_hole r p hW hd hgap hN)
  have hpzero := (ae_restrict_iff' hH).mp
    (S.ae_partner_row_zero_on_universalHole r p hW)
  filter_upwards [ae_restrict_of_ae hW.stationary, ae_restrict_of_ae hsection,
    ae_restrict_of_ae hD, ae_restrict_of_ae hpzero,
    ae_restrict_mem hH] with x hflat hcol hdef hpzero hxH
  have hK := integrable_universal_shifted_row (W := W) (m := m) x
  have hpart := S.integral_universal_four_regions r p hpair.1
    (shiftedKernel W m x) hK
  have hIrow : (∫ z in I, shiftedKernel W m x z ∂μ) =
      S.originalAtomMass r * r.val x := by
    have heq : ∀ᵐ z ∂μ.restrict I, shiftedKernel W m x z = r.val x := by
      filter_upwards [ae_restrict_of_ae hcol, ae_restrict_mem hI] with z hz hIz
      exact (hz.1 hIz)
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul]
    rfl
  have hProw : (∫ z in P, shiftedKernel W m x z ∂μ) = 0 := by
    have heq : ∀ᵐ z ∂μ.restrict P, shiftedKernel W m x z = 0 := by
      filter_upwards [ae_restrict_of_ae hcol, ae_restrict_mem hP] with z hz hPz
      exact (hz.2 hPz).trans (hpzero hxH)
    rw [integral_congr_ae heq]
    simp
  rw [hIrow, hProw] at hpart
  change (∫ z, shiftedKernel W m x z ∂μ) = 2 * (c - m * d) at hflat
  rw [hflat] at hpart
  have hdef' : S.universalRootDeficit r x = 1 - m - r.val x := by
    linarith [hdef hxH, hpzero hxH]
  have hrval : r.val x = 1 - m - S.universalRootDeficit r x := by linarith
  rw [hrval] at hpart
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integral_universal_adjacency_eq_mass_sub_missing
    (x : Ω) (E : Set Ω) :
    (∫ z in E, adjacencyKernel W x z ∂μ) =
      μ.real E - ∫ z in E, 1 - adjacencyKernel W x z ∂μ := by
  have hG := integrable_universal_adjacency_row (W := W) x
  have hsub := integral_sub (μ := μ.restrict E)
    (integrable_const (1 : ℝ)) hG.integrableOn
  change (∫ z in E, 1 - adjacencyKernel W x z ∂μ) = _ at hsub
  rw [setIntegral_const, smul_eq_mul] at hsub
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integral_universal_present_eq_total_sub_missing
    (S : SelectedHighLowStructure W m) (r : S.I)
    (x : Ω) (E : Set Ω) :
    (∫ z in E, S.universalRootDeficit r z * adjacencyKernel W x z ∂μ) =
      (∫ z in E, S.universalRootDeficit r z ∂μ) -
        ∫ z in E, (1 - adjacencyKernel W x z) * S.universalRootDeficit r z ∂μ := by
  have hD := S.integrable_universalRootDeficit r
  have hM := S.integrable_universal_missing_deficit_row r x
  have heq : (fun z => S.universalRootDeficit r z * adjacencyKernel W x z) =
      fun z => S.universalRootDeficit r z -
        (1 - adjacencyKernel W x z) * S.universalRootDeficit r z := by
    funext z
    ring
  rw [heq, integral_sub hD.integrableOn hM.integrableOn]

/-- The original stationary row and the actual universal-root triangle
give the strong missing-pair deficit inequality on almost every partner-hole
vertex. Every missing factor uses the original adjacency of that pair. -/
theorem ae_universalPartnerHole_deficit_row
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      (μ.real (S.universalPartnerHoleRegion r p) +
          μ.real (S.universalPartnerCommonRegion r p) - S.originalAtomMass r -
          2 * S.universalPartnerHoleMissingMass r p x -
          S.universalPartnerCommonMissingMass r p x) *
          S.universalRootDeficit r x ≥
        (1 + m) *
          (μ.real (S.universalPartnerHoleRegion r p) +
            μ.real (S.universalPartnerCommonRegion r p) -
            S.universalPartnerHoleMissingMass r p x -
            S.universalPartnerCommonMissingMass r p x) +
          S.universalPartnerCommonMissingDeficit r p x -
          (1 - m - 4 * (c - m * d)) := by
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let D := S.universalRootDeficit r
  let a := S.universalPartnerHoleMissingMass r p
  let k := S.universalPartnerCommonMissingMass r p
  let B := S.universalPartnerCommonMissingDeficit r p
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hHout : H ⊆ {z | S.ρ z ≠ r.val} := by
    intro z hz hr
    exact hz (Or.inl (Or.inl hr))
  have hUout : U ⊆ {z | S.ρ z ≠ r.val} := by
    intro z hz hr
    exact hz (Or.inl (Or.inl hr))
  have htri := S.ae_universal_deficit_triangle r hW hd hgap
    (S.neutral_atom_adjacency r hW hd hgap hN)
  have htriSec := Measure.ae_ae_of_ae_prod htri
  have hrow := S.ae_universal_hole_shifted_row r p hpair hW hd hgap hN
  have hHH := S.ae_universalPartnerHole_missing_deficit_eq_mass_mul
    r p hpair hW hd hgap hell
  have htotal := S.universalPartner_regions_deficit_integral
    r p hpair hW hd hgap hN
  filter_upwards [ae_restrict_of_ae htriSec, hrow, hHH, ae_restrict_mem hH]
    with x hxtri hxrow hxHH hxH
  have htriH := S.universal_triangle_set_integral r x H hH hHout
    (hxtri.mono fun z hz => hz (hHout hxH))
  have htriU := S.universal_triangle_set_integral r x U hU hUout
    (hxtri.mono fun z hz => hz (hHout hxH))
  have hGH := integral_universal_adjacency_eq_mass_sub_missing (W := W) x H
  have hGU := integral_universal_adjacency_eq_mass_sub_missing (W := W) x U
  have hDGH := S.integral_universal_present_eq_total_sub_missing r x H
  have hDGU := S.integral_universal_present_eq_total_sub_missing r x U
  change (∫ z in H, (1 - adjacencyKernel W x z) * D z ∂μ) = a x * D x at hxHH
  change (∫ z in H, adjacencyKernel W x z ∂μ) =
    μ.real H - a x at hGH
  change (∫ z in U, adjacencyKernel W x z ∂μ) =
    μ.real U - k x at hGU
  change (∫ z in H, D z * adjacencyKernel W x z ∂μ) =
    (∫ z in H, D z ∂μ) -
      (∫ z in H, (1 - adjacencyKernel W x z) * D z ∂μ) at hDGH
  change (∫ z in U, D z * adjacencyKernel W x z ∂μ) =
    (∫ z in U, D z ∂μ) - B x at hDGU
  change (∫ z in H, shiftedKernel W m x z ∂μ) +
    (∫ z in U, shiftedKernel W m x z ∂μ) =
      2 * (c - m * d) - S.originalAtomMass r * (1 - m - D x) at hxrow
  change (∫ z in H, D z ∂μ) + (∫ z in U, D z ∂μ) =
    (1 - m) * (1 - S.originalAtomMass r) - 2 * (c - m * d) at htotal
  change (μ.real H + μ.real U - S.originalAtomMass r - 2 * a x - k x) * D x ≥
    (1 + m) * (μ.real H + μ.real U - a x - k x) + B x -
      (1 - m - 4 * (c - m * d))
  have hsum := add_le_add htriH htriU
  dsimp only [D] at hDGH hDGU hxrow hxHH htotal ⊢
  rw [hGH, hGU, hDGH, hDGU, hxHH] at hsum
  nlinarith only [hsum, hxrow, htotal]

/-- Every partner-hole vertex has enough original neighbors to pay for
all missing pairs in the two outside regions. -/
theorem ae_universalPartnerHole_missing_capacity
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x +
          S.universalPartnerCommonMissingMass r p x ≤
        μ.real (S.universalPartnerHoleRegion r p) +
          μ.real (S.universalPartnerCommonRegion r p) - S.originalAtomMass r := by
  classical
  let I : Set Ω := {x | S.ρ x = r.val}
  let P : Set Ω := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hsym := adjacencyKernel_symm W
  have hroot := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_adjacency r hW hd hgap hN)
  have hpartner := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency p hW hd hgap)
  have hphysical := PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have hsection := Measure.ae_ae_of_ae_prod
    (hroot.and (hpartner.and (hphysical.and hsym)))
  have hpzero := S.ae_partner_row_zero_on_universalHole r p hW
  have hdegree := S.ae_universalPartnerHole_degree_ge_twice_mass
    r p hpair hW hd hgap hell hN
  filter_upwards [ae_restrict_of_ae hsection, hpzero, hdegree,
    ae_restrict_mem hH] with x hcol hpzero hdeg hxH
  have hxI : S.ρ x ≠ r.val := by
    intro he
    exact hxH (Or.inl (Or.inl he))
  have hxP : S.ρ x ≠ p.val := by
    intro he
    exact hxH (Or.inl (Or.inr he))
  have hnotN : x ∉ S.rootNeighborhood p := by
    intro he
    exact hxH (Or.inr he)
  have hi := integrable_universal_adjacency_row (W := W) x
  have hpart := S.integral_universal_four_regions r p hpair.1
    (adjacencyKernel W x) hi
  have hIrow : (∫ z in I, adjacencyKernel W x z ∂μ) = μ.real I := by
    have heq : ∀ᵐ z ∂μ.restrict I, adjacencyKernel W x z = 1 := by
      filter_upwards [ae_restrict_of_ae hcol, ae_restrict_mem hI] with z hz hIz
      have h := hz.1 hIz
      change adjacencyKernel W z x = (if S.ρ x = r.val then 0 else 1) at h
      exact hz.2.2.2.trans (h.trans (by simp [hxI]))
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_one]
  have hProw : (∫ z in P, adjacencyKernel W x z ∂μ) = 0 := by
    have heq : ∀ᵐ z ∂μ.restrict P, adjacencyKernel W x z = 0 := by
      filter_upwards [ae_restrict_of_ae hcol, ae_restrict_mem hP] with z hz hPz
      have h := hz.2.1 hPz
      change PhysicalRepresentative.adjacency W m z x = true ↔
        x ∈ S.rootNeighborhood p at h
      have hfalse : PhysicalRepresentative.adjacency W m z x = false := by
        cases hb : PhysicalRepresentative.adjacency W m z x <;> simp_all
      have hm := hz.2.2.1
      change adjacencyKernel W x z =
        (if PhysicalRepresentative.adjacency W m x z = true then 1 else 0) at hm
      rw [PhysicalRepresentative.adjacency_symm W m x z, hfalse] at hm
      simpa using hm
    rw [integral_congr_ae heq]
    simp
  rw [hIrow, hProw] at hpart
  have hGH := integral_universal_adjacency_eq_mass_sub_missing (W := W) x H
  have hGU := integral_universal_adjacency_eq_mass_sub_missing (W := W) x U
  change (∫ z in H, adjacencyKernel W x z ∂μ) =
    μ.real H - S.universalPartnerHoleMissingMass r p x at hGH
  change (∫ z in U, adjacencyKernel W x z ∂μ) =
    μ.real U - S.universalPartnerCommonMissingMass r p x at hGU
  rw [hGH, hGU] at hpart
  change S.universalPartnerHoleMissingMass r p x +
    S.universalPartnerCommonMissingMass r p x ≤ μ.real H + μ.real U - μ.real I
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure

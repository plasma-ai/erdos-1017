module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalSATGeometry
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTriangle
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral

/-!
# Deficit budget of the universal root

The averaged root charge gives a bounded nonnegative deficit, equal to one on
the universal head and zero on its saturated partner; the head rows and
common-neighbor triangle bound cap the partner-hole deficit, and the two-source
score budget specializes to the partner source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The actual averaged root charge gives a nonnegative bounded deficit,
including at exceptional representatives. -/
theorem universalRootDeficit_mem_Icc (S : SelectedHighLowStructure W m)
    (r : S.I) (x : Ω) : S.universalRootDeficit r x ∈ Icc (0 : ℝ) 4 := by
  have h := S.rootChargeRow_mem_Icc r x
  constructor <;> unfold universalRootDeficit <;> linarith [h.1, h.2]

theorem measurable_universalRootDeficit (S : SelectedHighLowStructure W m) (r : S.I) :
    Measurable (S.universalRootDeficit r) :=
  measurable_const.sub (S.measurable_rootChargeRow r)

theorem integrable_universalRootDeficit (S : SelectedHighLowStructure W m) (r : S.I) :
    Integrable (S.universalRootDeficit r) μ := by
  apply Integrable.of_bound (S.measurable_universalRootDeficit r).aestronglyMeasurable 4
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using abs_le.mpr
      ⟨by linarith [(S.universalRootDeficit_mem_Icc r x).1],
        (S.universalRootDeficit_mem_Icc r x).2⟩)

/-- The original missing mass within the partner's entire hole region.
The whole-part identity is proved from its original row geometry. -/
def universalPartnerHoleMissingMass (S : SelectedHighLowStructure W m)
    (r p : S.I) (x : Ω) : ℝ :=
  ∫ z in S.universalPartnerHoleRegion r p, 1 - adjacencyKernel W x z ∂μ

/-- The same original vertex's missing mass in the common region. -/
def universalPartnerCommonMissingMass (S : SelectedHighLowStructure W m)
    (r p : S.I) (x : Ω) : ℝ :=
  ∫ z in S.universalPartnerCommonRegion r p, 1 - adjacencyKernel W x z ∂μ

/-- The actual common-region missing deficit uses the same original holes
as the missing-mass inventory. -/
def universalPartnerCommonMissingDeficit (S : SelectedHighLowStructure W m)
    (r p : S.I) (x : Ω) : ℝ :=
  ∫ z in S.universalPartnerCommonRegion r p,
    (1 - adjacencyKernel W x z) * S.universalRootDeficit r z ∂μ

theorem universalPartnerHoleMissingMass_nonneg (S : SelectedHighLowStructure W m)
    (r p : S.I) (x : Ω) : 0 ≤ S.universalPartnerHoleMissingMass r p x := by
  exact integral_nonneg (fun z => sub_nonneg.mpr (adjacency_moment_mem W (x, z)).2)

theorem universalPartnerCommonMissingMass_nonneg (S : SelectedHighLowStructure W m)
    (r p : S.I) (x : Ω) : 0 ≤ S.universalPartnerCommonMissingMass r p x := by
  exact integral_nonneg (fun z => sub_nonneg.mpr (adjacency_moment_mem W (x, z)).2)

private theorem integral_partner_regions (S : SelectedHighLowStructure W m) (r p : S.I)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hheads : ∀ᵐ x ∂μ, S.ρ x = r.val ∨ S.ρ x = p.val → f x = 0) :
    (∫ x, f x ∂μ) = (∫ x in S.universalPartnerHoleRegion r p, f x ∂μ) +
      ∫ x in S.universalPartnerCommonRegion r p, f x ∂μ := by
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  calc
    _ = ∫ x, H.indicator f x + U.indicator f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hheads] with x hx
      by_cases hHmem : x ∈ H
      · have hUnot : x ∉ U := fun hu =>
          Set.disjoint_left.mp (S.universalPartner_regions_disjoint r p) hHmem hu
        simp only [indicator_of_mem hHmem, indicator_of_notMem hUnot, add_zero]
      · by_cases hUmem : x ∈ U
        · simp only [indicator_of_notMem hHmem, indicator_of_mem hUmem, zero_add]
        · have hhead : S.ρ x = r.val ∨ S.ρ x = p.val := by
            by_contra hn
            apply hUmem
            change x ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪ H
            intro h
            rcases h with (h | h) | h
            · exact hn (Or.inl h)
            · exact hn (Or.inr h)
            · exact hHmem h
          simp only [indicator_of_notMem hHmem, indicator_of_notMem hUmem, add_zero,
            hx hhead]
    _ = _ := by
      rw [integral_add (hf.indicator hH) (hf.indicator hU),
        integral_indicator hH, integral_indicator hU]

/-- The two original heads and the same entire H/U regions use all the
original probability mass once. -/
theorem universalPartner_regions_mass (S : SelectedHighLowStructure W m) (r p : S.I)
    (hrp : r ≠ p) :
    S.originalAtomMass r + S.originalAtomMass p +
      μ.real (S.universalPartnerHoleRegion r p) +
        μ.real (S.universalPartnerCommonRegion r p) = 1 := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Ip : Set Ω := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIp : MeasurableSet Ip := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hheads : Disjoint Ir Ip := disjoint_left.mpr
    (fun _ hx hy => hrp (Subtype.ext (hx.symm.trans hy)))
  have hhole : Disjoint (Ir ∪ Ip) H := disjoint_left.mpr
    (fun _ hx hy => hy (Or.inl hx))
  have hU : μ.real (S.universalPartnerCommonRegion r p) =
      1 - (S.originalAtomMass r + S.originalAtomMass p + μ.real H) := by
    change μ.real (Ir ∪ Ip ∪ H)ᶜ = _
    rw [measureReal_compl ((hIr.union hIp).union hH), probReal_univ,
      measureReal_union hhole hH, measureReal_union hheads hIp]
    rfl
  linarith

/-- Both original flat head rows determine one global score deficit. -/
theorem integral_universal_pair_score (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    (∫ x, 1 - m - r.val x - p.val x ∂μ) =
      1 - m - 2 * (2 * (c - m * d)) := by
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hp : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hfirst := integral_sub ((integrable_const (1 - m)).sub hr) hp
  have hsecond := integral_sub (integrable_const (1 - m)) hr
  simp only [Pi.sub_apply] at hfirst hsecond
  rw [hfirst, hsecond,
    S.row_integral_of_stationary r hW, S.row_integral_of_stationary p hW]
  simp
  ring

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The original universal-root triangle retains the same adjacency in
its missing-pair inventory. No triangle or physical representative is
supplied as a premise. -/
theorem ae_universal_deficit_triangle (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (huniv : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val then 0 else 1) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 + adjacencyKernel W p.1 p.2 ≤
        (S.universalRootDeficit r p.1 + S.universalRootDeficit r p.2) *
          adjacencyKernel W p.1 p.2 := by
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [S.ae_universal_root_triangle r hW hd hgap hN,
    PhysicalRepresentative.charge_ae_eq W m hs,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs]
    with p ht hy ha h1 h2
  by_cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 = true
  · have h := ht h1 h2 hA
    rw [hA] at ha
    simp only [ite_true] at ha
    change adjacencyKernel W p.1 p.2 = 1 at ha
    rw [ha]
    unfold universalRootDeficit
    nlinarith [hy]
  · have hA' : PhysicalRepresentative.adjacency W m p.1 p.2 = false :=
      Bool.eq_false_iff.mpr hA
    have hz := PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 hA'
    rw [hA'] at ha
    simp only [Bool.false_eq_true, ite_false] at ha
    change adjacencyKernel W p.1 p.2 = 0 at ha
    rw [ha, ← hy, hz]
    simp

/-- The actual original head rows and common-neighbor triangle bound give
the partner-hole deficit cap, including null hole and common regions. -/
theorem universalPartnerHole_deficit_cap (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    (∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ) ≤
      1 - m - 4 * (c - m * d) -
        (1 + m) * μ.real (S.universalPartnerCommonRegion r p) := by
  let f : Ω → ℝ := fun x => 1 - m - r.val x - p.val x
  let U := S.universalPartnerCommonRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hp : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hf : Integrable f μ := ((integrable_const (1 - m)).sub hr).sub hp
  have hheads : ∀ᵐ x ∂μ, S.ρ x = r.val ∨ S.ρ x = p.val → f x = 0 := by
    have hfirst := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp
      ((S.root_row_zero_on_fiber r).and hpair.symm.row_on_other)
    have hsecond := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp
      ((S.root_row_zero_on_fiber p).and hpair.row_on_other)
    filter_upwards [hfirst, hsecond] with x hx hy hhead
    rcases hhead with h | h
    · have hh := hx h
      dsimp only [f]
      linarith [hh.1, hh.2]
    · have hh := hy h
      dsimp only [f]
      linarith [hh.1, hh.2]
  have hfloor : ∀ᵐ x ∂μ.restrict U, 1 + m ≤ f x := by
    filter_upwards [ae_restrict_of_ae (S.ae_universal_row_pos_on_outside r hW hd hgap hN),
      S.ae_partner_row_pos_on_universalCommon r p,
      ae_restrict_of_ae (hpair.ae_common_neighbor_score_le hW hd hgap),
      ae_restrict_mem hU] with x hrpos hppos hscore hx
    have hnotr : S.ρ x ≠ r.val := fun h => hx (Or.inl (Or.inl h))
    have hh := hscore (hrpos hnotr) hppos
    dsimp only [f]
    linarith
  have hbound : (1 + m) * μ.real U ≤ ∫ x in U, f x ∂μ := by
    have h := integral_mono_ae (integrable_const (1 + m)) hf.integrableOn hfloor
    rw [setIntegral_const, smul_eq_mul] at h
    simpa only [mul_comm] using h
  have hpart := S.integral_partner_regions r p f hf hheads
  have hhole : (∫ x in S.universalPartnerHoleRegion r p, f x ∂μ) =
      ∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ := by
    apply integral_congr_ae
    filter_upwards [S.ae_universalRootDeficit_eq_score_on_hole r p hW hd hgap hN]
      with x hx
    exact hx.symm
  have hwhole := S.integral_universal_pair_score r p hW
  change (∫ x, f x ∂μ) = _ at hwhole
  rw [hwhole, hhole] at hpart
  change (1 + m) * μ.real (S.universalPartnerCommonRegion r p) ≤ _ at hbound
  linarith

/-- The universal original head has deficit one on itself and zero on
its actual saturated partner, on the original product-law representatives. -/
theorem ae_universalRootDeficit_on_heads (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, (S.ρ x = r.val → S.universalRootDeficit r x = 1) ∧
      (S.ρ x = p.val → S.universalRootDeficit r x = 0) := by
  have hrow := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp
    (S.root_row_zero_on_fiber r)
  have hpartner := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp hpair.row_on_other
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  filter_upwards [S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap, hrow, hpartner]
    with x hx hr hp
  constructor
  · intro h
    rw [hx, hr h]
    simp
  · intro h
    rw [hx, hp h]
    simp only [ite_eq_left (show 0 < 1 - m by linarith)]
    ring

/-- One original root row identifies the combined H/U deficit. This is
the same inventory later retained in the missing-pair row inequality. -/
theorem universalPartner_regions_deficit_integral
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    (∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ) +
      (∫ x in S.universalPartnerCommonRegion r p, S.universalRootDeficit r x ∂μ) =
        (1 - m) * (1 - S.originalAtomMass r) - 2 * (c - m * d) := by
  let I : Set Ω := {x | S.ρ x = r.val}
  let D := S.universalRootDeficit r
  let f : Ω → ℝ := D - I.indicator (fun _ => 1)
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hD : Integrable D μ := S.integrable_universalRootDeficit r
  have hind : Integrable (I.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hI
  have hf : Integrable f μ := hD.sub hind
  have hrow := (ae_restrict_iff' hI).mp (S.root_row_zero_on_fiber r)
  have hpoint : D =ᵐ[μ] fun x => 1 - r.val x - m * Iᶜ.indicator (fun _ => 1) x := by
    filter_upwards [S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap, hrow,
      S.ae_universal_row_pos_on_outside r hW hd hgap hN] with x hx hz hp
    change S.universalRootDeficit r x = _
    rw [hx]
    by_cases hi : x ∈ I
    · have hnot : x ∉ Iᶜ := notMem_compl_iff.mpr hi
      rw [hz hi]
      simp [indicator_of_notMem hnot]
    · have hc : x ∈ Iᶜ := hi
      simp only [indicator_of_mem hc, ite_eq_left (hp hi)]
  have hroot : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hDc : (∫ x, D x ∂μ) =
      1 - 2 * (c - m * d) - m * (1 - S.originalAtomMass r) := by
    have hfirst := integral_sub ((integrable_const 1).sub hroot)
      (((integrable_const 1).indicator hI.compl).const_mul m)
    have hsecond := integral_sub (integrable_const 1) hroot
    simp only [Pi.sub_apply] at hfirst hsecond
    rw [integral_congr_ae hpoint, hfirst, hsecond, integral_const,
      integral_const_mul, integral_indicator hI.compl, setIntegral_const,
      S.row_integral_of_stationary r hW, smul_eq_mul,
      measureReal_compl hI, probReal_univ]
    change _ = 1 - 2 * (c - m * d) - m * (1 - μ.real I)
    simp
  have hheads : ∀ᵐ x ∂μ, S.ρ x = r.val ∨ S.ρ x = p.val → f x = 0 := by
    filter_upwards [S.ae_universalRootDeficit_on_heads r p hpair hW hd hgap]
      with x hx hhead
    rcases hhead with hr | hp
    · change D x - I.indicator (fun _ => 1) x = 0
      have hi : x ∈ I := hr
      have hDx : D x = 1 := hx.1 hr
      rw [indicator_of_mem hi, hDx]
      simp
    · have hnot : x ∉ I := by
        intro hi
        exact hpair.1 (Subtype.ext (hi.symm.trans hp))
      change D x - I.indicator (fun _ => 1) x = 0
      have hDx : D x = 0 := hx.2 hp
      rw [indicator_of_notMem hnot, hDx]
      simp
  have hpart := S.integral_partner_regions r p f hf hheads
  have heqH : (∫ x in S.universalPartnerHoleRegion r p, f x ∂μ) =
      ∫ x in S.universalPartnerHoleRegion r p, D x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)]
      with x hx
    have hnot : x ∉ I := fun hi => hx (Or.inl (Or.inl hi))
    simp [f, indicator_of_notMem hnot]
  have heqU : (∫ x in S.universalPartnerCommonRegion r p, f x ∂μ) =
      ∫ x in S.universalPartnerCommonRegion r p, D x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (S.measurableSet_universalPartnerCommonRegion r p)]
      with x hx
    have hnot : x ∉ I := fun hi => hx (Or.inl (Or.inl hi))
    simp [f, indicator_of_notMem hnot]
  have hfint : (∫ x, f x ∂μ) = (∫ x, D x ∂μ) - S.originalAtomMass r := by
    change (∫ x, D x - I.indicator (fun _ => 1) x ∂μ) = _
    rw [integral_sub hD hind, integral_indicator hI, setIntegral_const, smul_eq_mul]
    simp only [mul_one]
    rfl
  rw [heqH, heqU, hfint, hDc] at hpart
  linarith

/-- The original two-source score budget specializes to the entire
partner source of a universal saturated root. Null source is included. -/
theorem universalPartner_source_score_budget
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    (∫ x in S.reverseCompulsorySource {p}, S.universalRootDeficit r x ∂μ) +
      (1 + m) * (1 - S.originalAtomMass r - S.originalAtomMass p -
        μ.real (S.reverseCompulsorySource {p})) ≤ 1 - m - 4 * (c - m * d) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Ip : Set Ω := {x | S.ρ x = p.val}
  let V := Ir ∪ Ip
  let Sr := S.reverseCompulsorySource {r}
  let Sp := S.reverseCompulsorySource {p}
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIp : MeasurableSet Ip := (S.hfibers p.val p.property).1
  have hV : MeasurableSet V := hIr.union hIp
  have hSp : MeasurableSet Sp := S.measurableSet_reverseCompulsorySource {p}
  have hdisjoint : Disjoint Ir Ip := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hpair.1 (Subtype.ext (hx.symm.trans hy))
  have hVmass : μ.real V = S.originalAtomMass r + S.originalAtomMass p := by
    rw [measureReal_union hdisjoint hIp]
    rfl
  have hSrzero : μ Sr = 0 := S.universalRoot_compulsorySource_null r hW hd hgap hN
  have hSrnot : ∀ᵐ x ∂μ, x ∉ Sr := compl_mem_ae_iff.mpr hSrzero
  have hSpnot : ∀ᵐ x ∂μ, x ∈ Sp → x ∉ V := by
    filter_upwards [S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell]
      with x hx hsource hhead
    exact hx hsource (Or.inl hhead)
  have hinterzero : μ (V ∩ Sp) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hSpnot] with x hx hmem
    exact hx hmem.2 hmem.1
  have hinter : μ.real (V ∩ Sp) = 0 := by
    change (μ (V ∩ Sp)).toReal = 0
    simp [hinterzero]
  have hVM : μ.real (V ∪ Sp) = S.originalAtomMass r + S.originalAtomMass p +
      μ.real Sp := by
    have h := measureReal_union_add_inter (μ := μ) (s := V) hSp
    rw [hinter, hVmass, add_zero] at h
    exact h
  have hmass : μ.real (V ∪ Sr ∪ Sp)ᶜ =
      1 - S.originalAtomMass r - S.originalAtomMass p - μ.real Sp := by
    have heq : μ.real (V ∪ Sr ∪ Sp)ᶜ = μ.real (V ∪ Sp)ᶜ := by
      apply measureReal_congr
      filter_upwards [hSrnot] with x hx
      exact propext (by simp only [mem_compl_iff, mem_union, hx, or_false])
    rw [heq, measureReal_compl (hV.union hSp), probReal_univ, hVM]
    ring
  have hbudget := hpair.entire_source_score_budget hW hd hgap hell
  have hzero : (∫ x in Sr, 1 - S.rootChargeRow p x ∂μ) = 0 :=
    setIntegral_measure_zero _ hSrzero
  change (∫ x in Sr, 1 - S.rootChargeRow p x ∂μ) +
    (∫ x in Sp, S.universalRootDeficit r x ∂μ) +
      (1 + m) * μ.real (V ∪ Sr ∪ Sp)ᶜ ≤ _ at hbudget
  rw [hzero, zero_add, hmass] at hbudget
  linarith

/-- The common region and entire partner source are disjoint original
resources; the source is contained in the same H region almost everywhere. -/
theorem universalPartner_common_mass_le_source_residual
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    μ.real (S.universalPartnerCommonRegion r p) ≤
      1 - S.originalAtomMass r - S.originalAtomMass p -
        μ.real (S.reverseCompulsorySource {p}) := by
  have hsub : μ.real (S.reverseCompulsorySource {p}) ≤
      μ.real (S.universalPartnerHoleRegion r p) :=
    ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono_ae (S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell))
  have hmass := S.universalPartner_regions_mass r p hpair.1
  linarith

/-- The nonnegative actual source integral pays the residual mass even
when the entire compulsory source is null. -/
theorem universalPartner_source_residual_bound
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    1 - S.originalAtomMass r - S.originalAtomMass p -
      μ.real (S.reverseCompulsorySource {p}) ≤ (1 - m - 4 * (c - m * d)) / (1 + m) := by
  have hbudget := S.universalPartner_source_score_budget r p hpair hW hd hgap hell hN
  have hnonneg : 0 ≤ ∫ x in S.reverseCompulsorySource {p},
      S.universalRootDeficit r x ∂μ := by
    exact integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  apply (le_div_iff₀ (by linarith : 0 < 1 + m)).mpr
  nlinarith

/-- Each common missing deficit pays its own original missing mass.
The multiplier is applied to the same pair inventory throughout. -/
theorem universalPartnerCommonMissingDeficit_ge_floor
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) (x : Ω) :
    (1 + m) * S.universalPartnerCommonMissingMass r p x ≤
      S.universalPartnerCommonMissingDeficit r p x := by
  let U := S.universalPartnerCommonRegion r p
  let D := S.universalRootDeficit r
  have hG : Measurable (fun z => adjacencyKernel W x z) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable.comp
        (measurable_const.prodMk measurable_id)
  have hmissing : Integrable (fun z => 1 - adjacencyKernel W x z) μ := by
    apply Integrable.of_bound (measurable_const.sub hG).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      have hz := adjacency_moment_mem W (x, z)
      change 0 ≤ adjacencyKernel W x z ∧ adjacencyKernel W x z ≤ 1 at hz
      change ‖1 - adjacencyKernel W x z‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - adjacencyKernel W x z)]
      linarith)
  have hdeficit : Integrable (fun z => (1 - adjacencyKernel W x z) * D z) μ := by
    apply Integrable.of_bound
      ((measurable_const.sub hG).mul (S.measurable_universalRootDeficit r)).aestronglyMeasurable 4
    exact Eventually.of_forall (fun z => by
      have hz := adjacency_moment_mem W (x, z)
      change 0 ≤ adjacencyKernel W x z ∧ adjacencyKernel W x z ≤ 1 at hz
      have hD := S.universalRootDeficit_mem_Icc r z
      change 0 ≤ D z ∧ D z ≤ 4 at hD
      change ‖(1 - adjacencyKernel W x z) * D z‖ ≤ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hD.1)]
      nlinarith [mul_nonneg hz.1 hD.1])
  have hfloor : ∀ᵐ z ∂μ.restrict U,
      (1 + m) * (1 - adjacencyKernel W x z) ≤ (1 - adjacencyKernel W x z) * D z := by
    filter_upwards [S.ae_universalRootDeficit_gt_floor_on_common r p hpair hW hd hgap hell hN]
      with z hz
    have hGle := (adjacency_moment_mem W (x, z)).2
    change adjacencyKernel W x z ≤ 1 at hGle
    have h := mul_le_mul_of_nonneg_left hz.le (sub_nonneg.mpr hGle)
    simpa only [mul_comm] using h
  have hbound := integral_mono_ae (hmissing.const_mul (1 + m)).integrableOn
    hdeficit.integrableOn hfloor
  rw [integral_const_mul] at hbound
  exact hbound

end Erdos1017.CappedModel.SelectedHighLowStructure

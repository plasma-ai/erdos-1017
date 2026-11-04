module

public import Erdos1017.Exclusions.E2.Lower.LowerE2UniversalRatio
public import Erdos1017.Exclusions.Common.E2.SelectedEmptySatE2Inventory
public import Erdos1017.Exclusions.Common.Universal.UniversalDeficitCompleteParts
public import Erdos1017.Exclusions.Common.Universal.SelectedTwoUniversalE2

/-!
# No universal saturated peak at the lower `E₂` contact

At lower `E₂` contact a universal saturated common peak is impossible, including
a null partner-hole region: one original hole-row integration forces the
saturated ratio at least `8/25`, every whole part being controlled by the same
common peak's forward redirection.
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

private theorem hole_atom_mass_lt_peak_sub_partner (S : SelectedHighLowStructure W m)
    (r p j : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hwhole : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) :
    S.originalAtomMass j < S.originalAtomMass r - S.originalAtomMass p := by
  let Ij := {x | S.ρ x = j.val}
  let Ip := {x | S.ρ x = p.val}
  have hIj := S.hfibers j.val j.property
  obtain ⟨x, hx, hxH⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIj.2.1.ne' hwhole
  have hjr : j ≠ r := fun he => hxH (Or.inl (Or.inl
    (hx.trans (congrArg Subtype.val he))))
  have hjp : j ≠ p := fun he => hxH (Or.inl (Or.inr
    (hx.trans (congrArg Subtype.val he))))
  have hhigh : ∀ᵐ x ∂μ.restrict Ij, x ∈ S.H := by
    have hH := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
      (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell)
    filter_upwards [hwhole, ae_restrict_of_ae hH] with x hx hh
    exact hh hx
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∉ S.L :=
    hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨f, hf, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap r
  have hredirect := hf.atomRedirect_of_stationary hW j j.property hhigh
  have hne : (j : Lp ℝ 2 μ) ≠ r := fun he => hjr (Subtype.ext he)
  have hstill := S.atomRedirect_avoids j r hne f havoid
  have hmassR := hredirect.classMass_eq_original_of_avoids_nonlow r hnonlow hstill
  have hmassJ : S.forwardClassMass (S.atomRedirect j f) j =
      μ.real Ij + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
    rw [S.forwardClassMass_eq_fiber]
    exact hf.atomRedirect_endpoint_mass hW j j.property hhigh
  have hsep := (hpeak (S.atomRedirect j f) hredirect).2.2 j hjr
  rw [hmassR, hmassJ] at hsep
  have hmissing : 0 < μ (Ij ∩ {x | p.val x ≤ 0}) := by
    have hz := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
      (S.ae_partner_row_zero_on_universalHole r p hW)
    have hsub : ∀ᵐ x ∂μ, x ∈ Ij → x ∈ Ij ∩ {x | p.val x ≤ 0} := by
      have hw := (ae_restrict_iff' hIj.1).mp hwhole
      filter_upwards [hw, hz] with x hx hz hxj
      exact ⟨hxj, (hz (hx hxj)).le⟩
    exact lt_of_lt_of_le hIj.2.1 (measure_mono_ae hsub)
  have hcross := KernelOperator.whole_row_cross_block_zero_of_positive_nonpositive
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ p.val j.val
    (S.hfibers p.val p.property).2.1 hIj.2.1
    (S.hfibers p.val p.property).2.2.2 hIj.2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
    (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun _ h => h.symm)) hW.moment_mem hIj.1 hmissing
  have hbmissing : S.originalAtomMass p ≤
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
    have h := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp hcross.2.1
    have hsub : ∀ᵐ x ∂μ, x ∈ Ip →
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ j.val := by
      filter_upwards [h] with x hx hxp
      refine ⟨?_, by simp [hx hxp]⟩
      intro hsame
      exact hjp (Subtype.ext (hsame.symm.trans hxp))
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have hgapEq : forwardPeakGap d c m = 2 * c - (1 - 2 * d) := by
    simp [forwardPeakGap, ForwardPeak.peakGap, show ¬1 ≤ -m from not_le.mpr hell]
  have hgapPos : 0 < forwardPeakGap d c m := by
    rw [hgapEq]
    have hB := Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩
    linarith only [hB, hgap]
  change S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) +
    forwardPeakGap d c m ≤ S.originalAtomMass r at hsep
  linarith only [hsep, hbmissing, hgapPos]

/-- One genuine original hole-row integration forces the saturated ratio
at least 8/25. Every whole part is controlled by the same common peak's
actual forward redirection; no atomic or integrated resource is supplied. -/
theorem saturated_ratio_ge_eight_twentyFifths (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hholes : 0 < μ (S.universalPartnerHoleRegion r p)) :
    8 / 25 ≤ (1 - m - 4 * (c - m * d)) / (1 + m) := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let y := (1 - m - 4 * (c - m * d)) / (1 + m)
  let L := μ.real (S.universalPartnerHoleRegion r p) + u - y
  let E := y - A
  by_contra hn
  have hy : y < 8 / 25 := lt_of_not_ge hn
  have hAy : A ≤ y := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap hell hN hholes
  have hA : 0 < A := ENNReal.toReal_pos_iff.mpr
    ⟨(S.hfibers r.val r.property).2.1, lt_top_iff_ne_top.mpr (measure_ne_top μ _)⟩
  have hb : b < A := by
    obtain ⟨hDelta, i, _, _, hi, hlargest, _, _⟩ :=
      S.exists_original_atomic_square_reserve hW hd hgap
    have heq : i = r := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
    subst i
    exact hlargest p hpair.1.symm
  have hmass := S.universalPartner_regions_mass r p hpair.1
  have hL : L = 1 - A - b - y := by dsimp only [L, u, A, b]; linarith only [hmass]
  have hLpos : 0 < L := by rw [hL]; linarith only [hb, hAy, hy]
  have hEL : E < L := by dsimp only [E]; rw [hL]; linarith only [hb, hAy, hy]
  have hsmall : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x < L := by
    filter_upwards [S.ae_universalPartnerHole_atom_of_missing_mass_pos
      r p hpair hW hd hgap hell] with x hx
    by_cases hpos : 0 < S.universalPartnerHoleMissingMass r p x
    · obtain ⟨j, _, hj, heq, _⟩ := hx hpos
      rw [heq]
      have hbound := S.hole_atom_mass_lt_peak_sub_partner r p j hpair hW hd hgap hell hN
        hpeak hj
      change S.originalAtomMass j < A - b at hbound
      rw [hL]
      linarith only [hbound, hAy, hy]
    · have hz := S.universalPartnerHoleMissingMass_nonneg r p x
      exact (le_antisymm (le_of_not_gt hpos) hz) ▸ hLpos
  obtain ⟨hsquare, _, _⟩ := S.empty_sat_small_parts_integrated_bounds
    r p hpair hW hd hgap hell hN hholes hLpos hEL hsmall
  change L ^ 2 ≤ E * (y - u) at hsquare
  rw [hL] at hsquare
  exact UniversalDeficit.false_of_small_ratio_square hA hb hAy hy measureReal_nonneg hsquare

private theorem partner_universal_of_hole_null (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hnull : μ (S.universalPartnerHoleRegion r p) = 0) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = p.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = p.val then 0 else 1 := by
  have hnotH : ∀ᵐ x ∂μ, x ∉ S.universalPartnerHoleRegion r p :=
    compl_mem_ae_iff.mpr hnull
  have hSAT := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hpair.symm.row_on_other
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hsets : ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood p ↔ S.ρ x ≠ p.val := by
    filter_upwards [hnotH, hSAT] with x hn hs
    constructor
    · exact fun h => h.1
    · intro hxp
      by_cases hxr : S.ρ x = r.val
      · exact ⟨hxp, by rw [hs hxr]; linarith only [hmneg]⟩
      · by_contra hnot
        exact hn (by
          intro hh
          rcases hh with (hh | hh) | hh
          · exact hxr hh
          · exact hxp hh
          · exact hnot hh)
  filter_upwards [S.ae_root_adjacency p hW hd hgap,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    Measure.quasiMeasurePreserving_snd.ae hsets] with z hz ha hs hzp
  change adjacencyKernel W z.1 z.2 =
    (if PhysicalRepresentative.adjacency W m z.1 z.2 = true then 1 else 0) at ha
  by_cases hy : S.ρ z.2 = p.val
  · have hf : PhysicalRepresentative.adjacency W m z.1 z.2 = false :=
      Bool.eq_false_iff.mpr (fun he => (hs.mp ((hz hzp).mp he)) hy)
    simpa only [hf, Bool.false_eq_true, ite_false, hy, ite_true] using ha
  · have ht := (hz hzp).mpr (hs.mpr hy)
    simpa only [ht, ite_true, hy, ite_false] using ha

/-- At lower-E2 contact, an actual universal saturated common peak is
impossible, including a null partner-hole region. Its ratio and all original
resource bounds are derived internally. -/
theorem no_lowerE2_universal_saturated_peak (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (1 / 10))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨hq.1, by linarith only [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ Benchmark.e2_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq' hdq hgap hglobal
  by_cases hnull : μ (S.universalPartnerHoleRegion r p) = 0
  · exact hpair.not_both_universal_e2 hW hq' hdq hgap hglobal
      (S.neutral_atom_adjacency r hW hd hgap hN)
      (S.partner_universal_of_hole_null r p hpair hW hd hgap hnull)
  have hholes : 0 < μ (S.universalPartnerHoleRegion r p) := bot_lt_iff_ne_bot.mpr hnull
  have hratio := S.saturated_ratio_ge_eight_twentyFifths r p hpair hW hd hgap hell.2
    hN hpeak hholes
  have hδ : 0 < 1 + m := by linarith only [hell.2]
  have hdef : 1 - m - 4 * (c - m * d) <
      (1 + m) * (9 * q / (2 * LowerE2Scalar.denominator q)) := by
    have href := LowerE2Scalar.deficit_eq_gap_mul_ratio hq.1.le
    rw [show LowerE2Scalar.multiplier q = -m by linarith only [hm]] at href
    nlinarith only [href, hgamma]
  have hupper : (1 - m - 4 * (c - m * d)) / (1 + m) < 2 / 7 :=
    ((div_lt_iff₀ hδ).mpr (by nlinarith only [hdef])).trans
      (LowerE2Scalar.ratio_lt_two_sevenths ⟨hq.1.le, by linarith only [hq.2]⟩)
  linarith only [hratio, hupper]

end Erdos1017.CappedModel.SelectedHighLowStructure

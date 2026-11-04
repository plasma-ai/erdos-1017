module

public import Erdos1017.Exclusions.E2.Middle.MiddleE2OffPairScalar
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedSourceBudget
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleOffPairSourceGeometry
public import Erdos1017.Exclusions.E2.Lower.SelectedLowerE2NonuniversalQuarter
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral

/-!
# Score-ratio bounds for off-pair peaks

Every off-pair original common peak is at most the score ratio
(`middle_e2_off_pair_peak_bounds`): atoms outside both compulsory sources
receive the full score floor, and through the exact cutoff the common peak is a
universal head of a constructed saturated pair
(`middle_e2_common_peak_universal_cutoff`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical BigOperators

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The score uses the two original homogeneous rows and their own common mean. -/
theorem integral_saturated_score_deficit (S : SelectedHighLowStructure W m) (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    (∫ x, 1 - m - r.val x - u.val x ∂μ) =
      1 - m - 2 * (2 * (c - m * d)) := by
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hfirst := integral_sub ((integrable_const (1 - m)).sub hr) hu
  have hsecond := integral_sub (integrable_const (1 - m)) hr
  simp only [Pi.sub_apply] at hfirst hsecond
  rw [hfirst, hsecond, S.row_integral_of_stationary r hW,
    S.row_integral_of_stationary u hW]
  simp
  ring

/-- Any original atom outside both entire compulsory sources receives the
full score floor. Membership is decided on the whole fiber, not at a chosen point. -/
theorem IsSaturatedAtomPair.off_source_atom_mass_le_score_ratio
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (i : S.I) (hir : i ≠ r) (hiu : i ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hr : ¬S.fiberCompulsoryPredicate i {r})
    (hu : ¬S.fiberCompulsoryPredicate i {u}) :
    S.originalAtomMass i ≤ (1 - m - 2 * (2 * (c - m * d))) / (1 + m) := by
  let I := {x | S.ρ x = i.val}
  let O := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val} ∪
    S.reverseCompulsorySource {r} ∪ S.reverseCompulsorySource {u})ᶜ
  let f : Ω → ℝ := fun x => 1 - m - r.val x - u.val x
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hO : MeasurableSet O := (((S.hfibers r.val r.property).1.union
    (S.hfibers u.val u.property).1).union
      (S.measurableSet_reverseCompulsorySource {r}) |>.union
        (S.measurableSet_reverseCompulsorySource {u})).compl
  have hIO : ∀ᵐ x ∂μ.restrict I, x ∈ O := by
    filter_upwards [S.ae_compulsorySource_iff_fiberPredicate i {r} hW,
      S.ae_compulsorySource_iff_fiberPredicate i {u} hW, ae_restrict_mem hI]
      with x hxr hxu hxi
    have hnr : S.ρ x ≠ r.val := fun h => hir (Subtype.ext (hxi.symm.trans h))
    have hnu : S.ρ x ≠ u.val := fun h => hiu (Subtype.ext (hxi.symm.trans h))
    exact fun h => h.elim (fun h => h.elim (fun h => h.elim hnr hnu)
      (fun h => hr (hxr.mp h))) (fun h => hu (hxu.mp h))
  have hfloor := (ae_restrict_iff' hO).mp
    (hpair.ae_entire_source_score_floor hW hd hgap hell)
  have hIraw := (ae_restrict_iff' hI).mp hIO
  have hnonneg := S.ae_saturated_head_score_le hW hd hgap hell r u hpair.1 hpair.2
  have hpoint : ∀ᵐ x ∂μ, I.indicator (fun _ => 1 + m) x ≤ f x := by
    filter_upwards [hIraw, hfloor, hnonneg] with x hx hf hn
    by_cases hi : x ∈ I
    · simpa only [indicator_of_mem hi] using hf (hx hi)
    · simp only [indicator_of_notMem hi]
      dsimp only [f]
      linarith
  have hrint : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have huint : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hfint : Integrable f μ := ((integrable_const (1 - m)).sub hrint).sub huint
  have hb := integral_mono_ae ((integrable_const (1 + m)).indicator hI) hfint hpoint
  rw [integral_indicator hI, setIntegral_const, smul_eq_mul] at hb
  change S.originalAtomMass i * (1 + m) ≤ ∫ x, 1 - m - r.val x - u.val x ∂μ at hb
  rw [S.integral_saturated_score_deficit r u hW] at hb
  exact (le_div_iff₀ (by linarith)).mpr hb

/-- The actual own contact multiplier and strict objective gap give the
strict score-ratio bound, with no peak-location assumption. -/
theorem IsSaturatedAtomPair.middle_e2_score_ratio_bounds
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < (1 - m - 2 * (2 * (c - m * d))) / (1 + m) ∧
      (1 - m - 2 * (2 * (c - m * d))) / (1 + m) < MiddleE2OffPair.ratioCap q ∧
      MiddleE2OffPair.ratioCap q < 1 / 2 := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_general_contact_parameters
    hq' hdq hvalue hderiv hgap hglobal
  have hdelta : 0 < 1 + m := by linarith [hell.2]
  have hR := LowerE2Scalar.denominator_pos hq'.1.le
  have hq2 : 0 < 2 + q := by linarith [hq.1]
  have hid : (1 - LowerE2Scalar.multiplier q) * MiddleE2OffPair.ratioCap q =
      1 - LowerE2Scalar.multiplier q - 2 * LowerE2Scalar.gapFloor q := by
    unfold MiddleE2OffPair.ratioCap LowerE2Scalar.multiplier LowerE2Scalar.gapFloor
    field_simp
    unfold LowerE2Scalar.denominator
    ring
  have hratio : (1 - m - 2 * (2 * (c - m * d))) / (1 + m) <
      MiddleE2OffPair.ratioCap q := by
    apply (div_lt_iff₀ hdelta).mpr
    rw [← neg_eq_iff_eq_neg.mpr hm] at hid
    nlinarith only [hid, hgamma]
  refine ⟨div_pos (hpair.gap_pos hW hd hgap hell.2) hdelta, hratio, ?_⟩
  unfold MiddleE2OffPair.ratioCap
  apply (div_lt_iff₀ (by positivity)).mpr
  unfold LowerE2Scalar.denominator
  have hsq : 0 < (1 - q) ^ 2 := sq_pos_of_pos (by linarith [hq.2])
  nlinarith

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual common peak, if HIGH, satisfies the quarter floor on both
parameter subintervals. The smaller-parameter theorem constructs its own
peak; separation identifies that peak with the one supplied here. -/
theorem middle_e2_high_common_peak_quarter (S : SelectedHighLowStructure W m) (i : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) :
    1 / 4 < S.originalAtomMass i := by
  by_cases hlow : q < 2 / 15
  · obtain ⟨hDelta, j, _, _, hj, _, _, _, halt⟩ :=
      S.exists_original_e2_peak_quarter_or_universal hW ⟨by linarith [hq.1], hlow⟩
        hdq hgap hglobal
    have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
    subst j
    rcases halt with huniv | hquarter
    · exfalso
      have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
        ⟨by linarith [hq.1], by linarith [hq.2]⟩
      have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
      have hmoment : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
          adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1 := by
        filter_upwards [huniv, PhysicalRepresentative.adjacency_moment_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support] with p hu hp hi
        change adjacencyKernel W p.1 p.2 = _ at hp
        rw [hp]
        by_cases he : S.ρ p.2 = i.val
        · simp [he, not_iff_not.mpr (hu hi)]
        · simp [he, (hu hi).mpr he]
      have hN := S.universal_atom_neutral i hW hd hgap hmoment
      obtain ⟨x, _, hxH, hxN⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (S.hfibers i.val i.property).2.1.ne' (hhigh.and hN)
      exact disjoint_left.mp S.hpartition.2.2.2.2.2.1 hxH hxN
    · exact hquarter
  · obtain ⟨hDelta, j, hquarter, _, hj, _, _, _, _⟩ :=
      S.exists_original_forward_quarter_peak hW ⟨le_of_not_gt hlow, hq.2⟩ hdq hgap hglobal
    have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
    simpa only [hji] using hquarter

/-- The actual entire compulsory source has mass below twice its original
common peak. The quarter, selector, saturated product and flat-row bounds
are all derived on the same original selected model. -/
theorem middle_e2_compulsory_source_mass_lt_twice_peak
    (S : SelectedHighLowStructure W m) (i r u : S.I) (hir : i ≠ r) (hiu : i ≠ u)
    (hpair : S.IsSaturatedAtomPair r u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.reverseCompulsorySource {r}) :
    μ.real (S.reverseCompulsorySource {r}) < 2 * S.originalAtomMass i := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_general_contact_parameters
    hq' hdq hvalue hderiv hgap hglobal
  obtain ⟨hDelta, j, _, _, hj, hlargest, _, _, hselector⟩ :=
    S.exists_original_forward_selector_envelope hW hd hgap hell.2
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have hquarter := S.middle_e2_high_common_peak_quarter i hW hq hdq hgap hglobal hpeak
    (hsource.mono (fun _ hx => hx.1))
  have hhalf := S.compulsory_source_atom_lt_half i r u hir hpair hW hd hgap hell.2 hsource
  have hrpos : 0 < S.originalAtomMass r :=
    ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top μ _)
  have hprod := hpair.capacity_lower_bound hW hd hgap hell.2
  have hpairEq := LowerE2Scalar.pairFloor_eq_twoHeadValue hq'.1.le
  rw [← hvalue, ← hdq] at hpairEq
  have hproduct : LowerE2Scalar.pairFloor q < S.originalAtomMass r * S.originalAtomMass u := by
    change (3 * c - d) / 2 ≤ S.originalAtomMass r * S.originalAtomMass u at hprod
    linarith
  have hhead := S.compulsory_source_head_mass_bound r hW hd hgap
  have hR := LowerE2Scalar.denominator_pos hq'.1.le
  have hq2 : 0 < 2 + q := by linarith [hq.1]
  have hid : (1 + LowerE2Scalar.multiplier q) * MiddleE2OffPair.headCap q =
      1 - LowerE2Scalar.gapFloor q := by
    unfold MiddleE2OffPair.headCap LowerE2Scalar.multiplier LowerE2Scalar.gapFloor
    field_simp
    unfold LowerE2Scalar.denominator
    ring
  have hhead' : S.originalAtomMass r + μ.real (S.reverseCompulsorySource {r}) <
      MiddleE2OffPair.headCap q := by
    rw [← neg_eq_iff_eq_neg.mpr hm] at hid
    have hpos : 0 < 1 - m := by linarith [hell.1]
    apply (mul_lt_mul_iff_right₀ hpos).mp
    nlinarith only [hhead, hid, hgamma]
  have hme : -m = LowerE2Scalar.multiplier q := by linarith
  rw [hme] at hselector
  exact MiddleE2OffPair.private_source_mass_lt_twice_peak hq hquarter hhalf hrpos
    (hlargest u hiu.symm) hproduct hhead' hgamma hselector

/-- In either entire compulsory source the original common peak is
strictly below the score ratio. All source-mass and deficit inputs are paid. -/
theorem middle_e2_compulsory_peak_lt_score_ratio
    (S : SelectedHighLowStructure W m) (i r u : S.I) (hir : i ≠ r) (hiu : i ≠ u)
    (hpair : S.IsSaturatedAtomPair r u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.reverseCompulsorySource {r}) :
    S.originalAtomMass i < (1 - m - 2 * (2 * (c - m * d))) / (1 + m) := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hell := (hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal).2.1.2
  exact S.compulsory_source_atom_lt_score_ratio i r u hir hiu hpair hW hd hgap hell hsource
    (S.middle_e2_compulsory_source_mass_lt_twice_peak i r u hir hiu hpair
      hW hq hdq hvalue hderiv hgap hglobal hpeak hsource)

/-- Every off-pair original common peak is at most the actual score ratio.
Both entire compulsory sources and their complement are treated internally. -/
theorem middle_e2_off_pair_peak_bounds (S : SelectedHighLowStructure W m)
    (i r u : S.I) (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i) :
    S.originalAtomMass i ≤ (1 - m - 2 * (2 * (c - m * d))) / (1 + m) ∧
      (1 - m - 2 * (2 * (c - m * d))) / (1 + m) < MiddleE2OffPair.ratioCap q := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hell := (hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal).2.1.2
  refine ⟨?_, (hpair.middle_e2_score_ratio_bounds hW hq hdq hvalue hderiv hgap hglobal).2.1⟩
  by_cases hr : S.fiberCompulsoryPredicate i {r}
  · have hsource := (S.ae_compulsorySource_iff_fiberPredicate i {r} hW).mono
      (fun _ hx => hx.mpr hr)
    have hmass := S.middle_e2_compulsory_source_mass_lt_twice_peak i r u hir hiu hpair
      hW hq hdq hvalue hderiv hgap hglobal hpeak hsource
    exact (S.compulsory_source_atom_lt_score_ratio i r u hir hiu hpair hW hd hgap
      hell hsource hmass).le
  · by_cases hu : S.fiberCompulsoryPredicate i {u}
    · have hsource := (S.ae_compulsorySource_iff_fiberPredicate i {u} hW).mono
        (fun _ hx => hx.mpr hu)
      have hmass := S.middle_e2_compulsory_source_mass_lt_twice_peak i u r hiu hir hpair.symm
        hW hq hdq hvalue hderiv hgap hglobal hpeak hsource
      exact (S.compulsory_source_atom_lt_score_ratio i u r hiu hir hpair.symm hW hd hgap
        hell hsource hmass).le
    · exact hpair.off_source_atom_mass_le_score_ratio i hir hiu hW hd hgap hell hr hu

/-- The exact cutoff retains the three distinct original atom squares.
The endpoint profile is not used as the original missing-density inventory. -/
theorem middle_e2_common_peak_mem_saturated_pair (S : SelectedHighLowStructure W m)
    (i r u : S.I) (hpair : S.IsSaturatedAtomPair r u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (19 / 160))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i) : i = r ∨ i = u := by
  by_contra hn
  push Not at hn
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hqmid : q ∈ Icc (1 / 10 : ℝ) (1 / 5) := ⟨hq.1, by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_general_contact_parameters
    hq' hdq hvalue hderiv hgap hglobal
  obtain ⟨hDelta, j, _, _, hj, _, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have hcap := S.middle_e2_off_pair_peak_bounds i r u hn.1 hn.2 hpair
    hW hqmid hdq hvalue hderiv hgap hglobal hpeak
  have hAcap := lt_of_le_of_lt hcap.1 hcap.2
  let _ : Countable S.I := S.hI.to_subtype
  have hfinite := Summable.sum_le_tsum (s := {i, r, u})
    (fun k _ => sq_nonneg (S.originalAtomMass k)) S.originalAtomMass_sq_summable
  have hnot : i ∉ ({r, u} : Finset S.I) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  have hQ : (S.originalAtomMass i) ^ 2 + (S.originalAtomMass r) ^ 2 +
      (S.originalAtomMass u) ^ 2 ≤ ∑' k, (S.originalAtomMass k) ^ 2 := by
    simpa only [Finset.sum_insert hnot, Finset.sum_pair hpair.1, add_assoc] using hfinite
  have hQscaled := mul_le_mul_of_nonneg_left hQ (show 0 ≤ -m by linarith [hell.1])
  have hcapacity := hpair.capacity_lower_bound hW hd hgap hell.2
  change (3 * c - d) / 2 ≤ S.originalAtomMass r * S.originalAtomMass u at hcapacity
  have hpairEq := LowerE2Scalar.pairFloor_eq_twoHeadValue hq'.1.le
  rw [← hvalue, ← hdq] at hpairEq
  have hp : LowerE2Scalar.pairFloor q < S.originalAtomMass r * S.originalAtomMass u := by
    linarith
  have hpscaled := mul_lt_mul_of_pos_left hp (show 0 < 2 * (-m) by linarith [hell.1])
  have hsq := sq_nonneg (S.originalAtomMass r - S.originalAtomMass u)
  have hsqscaled := mul_nonneg (show 0 ≤ -m by linarith [hell.1]) hsq
  have hA0 : 0 ≤ S.originalAtomMass i := measureReal_nonneg
  have hAcap2 : (S.originalAtomMass i) ^ 2 < (MiddleE2OffPair.ratioCap q) ^ 2 := by
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hAcap2 (show 0 < 2 + m by linarith [hell.2])
  have hmargin := MiddleE2OffPair.off_pair_square_margin_pos hq
  rw [← neg_eq_iff_eq_neg.mpr hm] at hmargin
  nlinarith only [hreserve, hQscaled, hpscaled, hsqscaled, hscaled, hmargin, hgamma]

/-- Through the exact cutoff, the original common peak is a universal head
of an actually constructed saturated pair. Neither saturation nor a location
certificate is a premise. -/
theorem middle_e2_common_peak_universal_cutoff (S : SelectedHighLowStructure W m)
    (i : S.I) {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (19 / 160))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i) :
    (∃ r : S.I, S.IsSaturatedAtomPair i r) ∧
      ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
        (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ i.val) := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hell := (hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal).2.1.2
  have hpairEq := LowerE2Scalar.pairFloor_eq_twoHeadValue hq'.1.le
  rw [← hvalue, ← hdq] at hpairEq
  have hp := MiddleE2OffPair.pair_floor_pos_cutoff hq
  obtain ⟨r, u, hpair, _⟩ := S.exists_saturated_atom_pair_with_capacity hW hd hgap hell
    (by linarith)
  have hhead : ∃ j : S.I, S.IsSaturatedAtomPair i j := by
    rcases S.middle_e2_common_peak_mem_saturated_pair i r u hpair hW hq hdq hvalue hderiv
      hgap hglobal hpeak with hir | hiu
    · exact ⟨u, hir ▸ hpair⟩
    · exact ⟨r, hiu ▸ hpair.symm⟩
  obtain ⟨j, hij⟩ := hhead
  refine ⟨⟨j, hij⟩, ?_⟩
  obtain ⟨hDelta, k, _, hside, hk, _, _, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
  have hki : k = i := (hk S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst k
  rcases hside with hH | hN
  · have hnotH : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.H := by
      filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr
        (hij.high_head_null hW hd hgap hell)),
        ae_restrict_mem (S.hfibers i.val i.property).1] with x hx hi hHx
      exact hx ⟨hi, hHx⟩
    obtain ⟨x, _, hxH, hxnot⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers i.val i.property).2.1.ne' (hH.and hnotH)
    exact False.elim (hxnot hxH)
  · filter_upwards [S.neutral_atom_adjacency i hW hd hgap hN,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with p hn hp hi
    have he := hn hi
    change adjacencyKernel W p.1 p.2 = _ at hp
    rw [hp] at he
    by_cases hsame : S.ρ p.2 = i.val <;>
      cases hphys : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
      simp_all

end Erdos1017.CappedModel.SelectedHighLowStructure

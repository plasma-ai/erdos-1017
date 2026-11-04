module

public import Erdos1017.Exclusions.E2.Lower.SelectedLowerE2NonuniversalQuarter
public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateRadius
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterHeadDegree
public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateContradiction

/-!
# Universal peak at the `E₂` two-center contact

The `E₂` two-center budget forces the recovered height above three eighths, so
the original outside mass is below one quarter (`e2_height_gt_three_eighths`),
and at a selected `E₂` two-center contact the internally constructed original
common forward peak has a universal physical row
(`exists_original_universal_e2_two_center_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

private theorem e2_gapFloor_gt_three_eighths_square {q : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    (9 / 32 : ℝ) * (1 - LowerE2Scalar.multiplier q) < LowerE2Scalar.gapFloor q := by
  have hQ := LowerE2Scalar.denominator_pos hq.1.le
  have hQne := hQ.ne'
  have hq2 : 2 + q ≠ 0 := by linarith [hq.1]
  have hid : 16 * LowerE2Scalar.denominator q * (q + 2) *
      (LowerE2Scalar.gapFloor q - (9 / 32 : ℝ) * (1 - LowerE2Scalar.multiplier q)) =
      q * (7 * q ^ 2 - 23 * q + 7) := by
    unfold LowerE2Scalar.gapFloor LowerE2Scalar.multiplier
    field_simp
    unfold LowerE2Scalar.denominator
    ring
  have hpoly : 0 < 7 * q ^ 2 - 23 * q + 7 := by nlinarith [sq_nonneg q, hq.2]
  have hpos := mul_pos hq.1 hpoly
  rw [← hid] at hpos
  have hden : 0 < 16 * LowerE2Scalar.denominator q * (q + 2) := by
    exact mul_pos (mul_pos (by norm_num) hQ) (by linarith [hq.1])
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hden).mp hpos)

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- The actual E2 two-center budget forces the recovered height above
three eighths, so its original outside mass is below one quarter. -/
theorem e2_height_gt_three_eighths
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) : 3 / 8 < R.height := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq hdq hgap hglobal
  have hb := R.isFullReverseFlow.plateau_budget hW hd hgap R.plateau R.height
    (R.classMass_le hW) (fun v hv => (R.classMass_eq_iff hW v).mpr hv)
  rw [hcard] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have henergy := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hpaid : 2 * (c - m * d) + m ≤ 2 * (1 + m) * R.height ^ 2 := by
    nlinarith only [hb.1, hb.2, henergy]
  have hfloor := e2_gapFloor_gt_three_eighths_square hq
  rw [← neg_eq_iff_eq_neg.mpr hm] at hfloor
  by_contra hn
  have ht : R.height ≤ 3 / 8 := le_of_not_gt hn
  have hsq : R.height ^ 2 ≤ (3 / 8 : ℝ) ^ 2 := by nlinarith [R.height_pos]
  have hscaled := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 2 * (1 + m) by linarith [hell.2])
  nlinarith [hpaid, hgamma, hfloor, hscaled]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- A single internally constructed original peak has its full reserve,
and is either physically universal or above the original quarter floor. -/
private theorem exists_e2_peak_quarter_or_universal
    (S : SelectedHighLowStructure W m)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      0 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.N)) ∧
      S.IsCommonForwardPeak d c i ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2) ∧
      ((∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
        (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ i.val)) ∨
        1 / 4 < S.originalAtomMass i) := by
  by_cases hlow : q < 2 / 15
  · obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, _, halternative⟩ :=
      S.exists_original_e2_peak_quarter_or_universal hW ⟨hq.1, hlow⟩ hdq hgap hglobal
    exact ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, halternative⟩
  · have hqhigh : q ∈ Icc (2 / 15 : ℝ) (1 / 5) := ⟨le_of_not_gt hlow, hq.2⟩
    obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, _, _⟩ :=
      S.exists_original_forward_quarter_peak hW hqhigh hdq hgap hglobal
    exact ⟨hΔ, i, by linarith, hside, hpeak, hlargest, hreserve, Or.inr hA⟩

/-- At an actual selected E2 two-center contact, the internally constructed
original common forward peak has a universal physical row. In the quarter-
mass branch, private, shared and outside locations are excluded internally;
a peak on a recovered head is neutral and therefore universal. -/
theorem exists_original_universal_e2_two_center_peak
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      0 < S.originalAtomMass i ∧ S.IsCommonForwardPeak d c i ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2) ∧
      ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
        (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ i.val) := by
  obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, halternative⟩ :=
    exists_e2_peak_quarter_or_universal S hW hq hdq hgap hglobal
  refine ⟨hΔ, i, hA, hpeak, hlargest, hreserve, ?_⟩
  rcases halternative with huniversal | hquarter
  · exact huniversal
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  obtain ⟨r, u, hru, hp⟩ := Finset.card_eq_two.mp hcard
  have hheight := R.e2_height_gt_three_eighths hW hq hdq hgap hglobal hcard
  have hlarge : 1 - 2 * R.height < S.originalAtomMass i := by linarith
  have hmax (k : S.I) : S.originalAtomMass k ≤ S.originalAtomMass i := by
    by_cases hki : k = i
    · rw [hki]
    · exact (hlargest k hki).le
  have huniversalHead (hi : i ∈ R.plateau) :
      ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
        (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ i.val) := by
    have hneutral : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.N := by
      rcases hside with hhigh | hneutral
      · have hnotHigh := R.plateau_eligible i hi
        obtain ⟨x, _, hh, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
          (S.hfibers i.val i.property).2.1.ne' (hhigh.and hnotHigh)
        exact False.elim (hn hh)
      · exact hneutral
    exact S.neutral_atom_physical_adjacency i hW hd hgap hneutral
  rcases R.original_atom_twoCenter_location i r u hru hW hp hlarge with
    hr | hu | hprivateFirst | hprivateSecond | hshared
  · obtain ⟨x, hx, hrx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers i.val i.property).2.1.ne' hr
    have hir : i = r := Subtype.ext (hx.symm.trans hrx)
    apply huniversalHead
    rw [hir, hp]
    simp
  · obtain ⟨x, hx, hux⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers i.val i.property).2.1.ne' hu
    have hiu : i = u := Subtype.ext (hx.symm.trans hux)
    apply huniversalHead
    rw [hiu, hp]
    simp
  · exact False.elim (R.no_e2_private_largest_atom i r u hru hp hprivateFirst hmax
      hW hq hdq hgap hglobal)
  · have hp' : R.plateau = {u, r} := by simpa only [Finset.pair_comm] using hp
    exact False.elim (R.no_e2_private_largest_atom i u r hru.symm hp' hprivateSecond hmax
      hW hq hdq hgap hglobal)
  · have hintercept := hW.e2_intercept_guard hq hdq hgap hglobal
    have hm := (hW.e2_gamma_floor hq hdq hgap hglobal).1
    have hmult := E2PrivateCurvature.multiplier_ge_nine_elevenths ⟨hq.1.le, hq.2⟩
    have hslope : (1 / 2 : ℝ) < -m := by rw [hm]; linarith
    have hsharedBound := R.twoCenter_shared_mass_lt r u hru hW hd hgap hp hintercept hslope
    have hsub := (ae_restrict_iff' (S.hfibers i.val i.property).1).mp hshared
    have hmass : S.originalAtomMass i ≤ μ.real (S.twoCenterShared r u) :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    exact False.elim (by linarith [hsharedBound.1, hsharedBound.2])

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

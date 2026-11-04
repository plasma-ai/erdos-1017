module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2HeadTrace
public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateExclusion
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PeakThird
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral

/-!
# Exclusion of the two-center `E₂` recovery

Two-center recovery is impossible for `E₂` parameters `1/10 ≤ q ≤ 213/1000`,
with value and derivative contact kept explicit and the original common peak and
its head location derived (`no_e2_two_center`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private theorem universal_peak_mem_plateau (R : S.ReverseRecovery) (k : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c) (hm : m = -LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q ≤ 2 * (c - m * d) + m)
    (hcard : R.plateau.card = 2)
    (hreserve : 2 * (c - m * d) + m + (-m) * (∑' i, (S.originalAtomMass i) ^ 2) ≤
      2 * (S.originalAtomMass k) ^ 2)
    (huniv : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val →
      (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ k.val)) :
    k ∈ R.plateau := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact LowerE2Scalar.contact_density_mem hq
  have hell : 0 < -m := by
    rw [hm]
    linarith [(LowerE2Scalar.contact_multiplier_mem hq).1]
  have hsquare : (S.originalAtomMass k) ^ 2 ≤ ∑' i, (S.originalAtomMass i) ^ 2 := by
    have hh := Summable.sum_le_tsum (s := {k})
      (fun i _ => sq_nonneg (S.originalAtomMass i)) S.originalAtomMass_sq_summable
    simpa using hh
  have hforward : 2 * (c - m * d) + m ≤
      (2 - LowerE2Scalar.multiplier q) * (S.originalAtomMass k) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsquare hell.le
    have hplain : 2 * (c - m * d) + m ≤ (2 + m) * (S.originalAtomMass k) ^ 2 := by
      nlinarith only [hh, hreserve]
    have heq : 2 + m = 2 - LowerE2Scalar.multiplier q := by rw [hm]; ring
    rwa [heq] at hplain
  have hb := R.isFullReverseFlow.plateau_budget hW hd hgap R.plateau R.height
    (R.classMass_le hW) (fun i hi => (R.classMass_eq_iff hW i).mpr hi)
  rw [hcard] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hreverse : 2 * (c - m * d) + m ≤
      2 * (1 - LowerE2Scalar.multiplier q) * R.height ^ 2 := by
    have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
    have hplain : 2 * (c - m * d) + m ≤ 2 * (1 + m) * R.height ^ 2 := by
      nlinarith [hb.1, hb.2]
    have heq : 1 + m = 1 - LowerE2Scalar.multiplier q := by rw [hm]; ring
    rwa [heq] at hplain
  have hlarge := LowerE2Scalar.two_center_outside_lt_peak hq
    (measureReal_nonneg : 0 ≤ S.originalAtomMass k) R.height_pos.le hgamma hreverse hforward
  have hN := S.universal_atom_neutral k hW hd hgap (by
    filter_upwards [huniv, PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hp he hx
    change adjacencyKernel W p.1 p.2 = _ at he
    rw [he]
    by_cases hh : S.ρ p.2 = k.val <;> simp [hp hx, hh])
  have hnotHigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∉ S.H :=
    hN.mono (fun _ hx hH => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hH hx)
  obtain ⟨r, u, hru, hp⟩ := Finset.card_eq_two.mp hcard
  rcases R.original_atom_twoCenter_location k r u hru hW hp hlarge with
    hr | hu | hprivateFirst | hprivateSecond | hshared
  · obtain ⟨x, hx, hrx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' hr
    have hkr : k = r := Subtype.ext (hx.symm.trans hrx)
    rw [hkr, hp]
    simp
  · obtain ⟨x, hx, hux⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' hu
    have hku : k = u := Subtype.ext (hx.symm.trans hux)
    rw [hku, hp]
    simp
  · obtain ⟨x, _, hx, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' (hprivateFirst.and hnotHigh)
    exact (hn hx.1.1.1).elim
  · obtain ⟨x, _, hx, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' (hprivateSecond.and hnotHigh)
    exact (hn hx.1.1.1).elim
  · obtain ⟨x, _, hx, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' (hshared.and hnotHigh)
    exact (hn hx.1.1.1).elim

private theorem upper_peak_mem_plateau (R : S.ReverseRecovery) (k : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c) (hm : m = -LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q ≤ 2 * (c - m * d) + m)
    (hcard : R.plateau.card = 2) (hA : 1 / 3 < S.originalAtomMass k) :
    k ∈ R.plateau := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact LowerE2Scalar.contact_density_mem hq
  have hintercept : (1 + m) / 4 < 2 * (c - m * d) + m := by
    have hh := LowerE2Scalar.two_center_gapFloor_gt_quarter hq
    rw [hm]
    rw [hm] at hgamma
    linarith
  have ht := (R.two_center_parameters hW hd hgap hcard hintercept).2.2.1
  have hell : (1 / 2 : ℝ) < -m := by
    rw [hm]
    linarith [(LowerE2Scalar.contact_multiplier_mem hq).1]
  have hlarge : 1 - 2 * R.height < S.originalAtomMass k := by linarith
  obtain ⟨r, u, hru, hp⟩ := Finset.card_eq_two.mp hcard
  rcases R.original_atom_twoCenter_location k r u hru hW hp hlarge with
    hr | hu | hprivateFirst | hprivateSecond | hshared
  · obtain ⟨x, hx, hrx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' hr
    have hkr : k = r := Subtype.ext (hx.symm.trans hrx)
    rw [hkr, hp]
    simp
  · obtain ⟨x, hx, hux⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' hu
    have hku : k = u := Subtype.ext (hx.symm.trans hux)
    rw [hku, hp]
    simp
  · have hh := R.private_atom_mass_lt_third k r u hru hW hd hgap hp hintercept hprivateFirst
    change 1 / 3 < μ.real {x | S.ρ x = k.val} at hA
    linarith
  · have hp' : R.plateau = {u, r} := by simpa only [Finset.pair_comm] using hp
    have hh := R.private_atom_mass_lt_third k u r hru.symm hW hd hgap hp'
      hintercept hprivateSecond
    change 1 / 3 < μ.real {x | S.ρ x = k.val} at hA
    linarith
  · have hb := R.twoCenter_shared_mass_lt r u hru hW hd hgap hp hintercept hell
    have hsub := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hshared
    have hh : S.originalAtomMass k ≤ μ.real (S.twoCenterShared r u) :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    linarith [hb.1, hb.2]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Actual two-center recovery is impossible on the stated closed E2
parameter interval. Value and derivative contact remain explicit; the
original common peak, its head location and positive body are all derived. -/
theorem no_e2_two_center (R : S.ReverseRecovery)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨hm, _, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hhead (k : S.I) (hpeak : S.IsCommonForwardPeak d c k) (hk : k ∈ R.plateau) :
      False := R.no_e2_common_peak_head k hW ⟨hq.1, hq'.2⟩ hdq hvalue hderiv hgap
        hglobal hcard hk hpeak
  by_cases hlow : q ≤ 1 / 5
  · obtain ⟨_, k, _, hpeak, _, hreserve, huniv⟩ :=
      R.exists_original_universal_e2_two_center_peak hW ⟨hq'.1, hlow⟩ hdq hgap hglobal hcard
    exact hhead k hpeak (universal_peak_mem_plateau R k hW hq' hdq hgap hm hgamma.le
      hcard hreserve huniv)
  · have hqupper : q ∈ Icc (1 / 5 : ℝ) (213 / 1000) := ⟨le_of_not_ge hlow, hq.2⟩
    obtain ⟨_, k, hA, _, hpeak, _, _, _⟩ :=
      S.exists_original_upper_e2_peak_gt_third hW hqupper hdq hvalue hderiv hgap hglobal
    exact hhead k hpeak (upper_peak_mem_plateau R k hW hq' hdq hgap hm hgamma.le hcard hA)

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

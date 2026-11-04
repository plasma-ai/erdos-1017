module

public import Erdos1017.Exclusions.Corner.FullSharpCornerPeak
public import Erdos1017.Exclusions.Corner.SelectedCornerZeroBody
public import Erdos1017.SelectedModel.SelectedBodyEnergy
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterAtomLocation
public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePeakBound

/-!
# Exclusion of the two-center corner recovery

A two-center corner recovery is impossible; the common peak, head location, own
slope and positive original body are derived.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- At a genuine corner global excess contact, the common original
forward peak belongs to the actual recovered two-center plateau. The own corner
intercept and the outside, private and shared-source exclusions are derived internally. -/
private theorem corner_common_peak_mem_plateau
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) (k : S.I) (hpeak : S.IsCommonForwardPeak d c k) :
    k ∈ R.plateau := by
  obtain ⟨hΔ, i, hA, hi, _, _⟩ :=
    S.exists_sharp_corner_peak hW hd hgap he heq hglobal
  have heq : i = k := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst i
  obtain ⟨hell, _, _, hgamma⟩ :=
    hW.corner_contact_parameters hd hgap he heq hglobal
  obtain ⟨r, u, hru, hp⟩ := Finset.card_eq_two.mp hcard
  have hintercept : (1 + m) / 4 < 2 * (c - m * d) + m := by linarith [hell.1]
  have ht := (R.two_center_parameters hW hd hgap hcard hintercept).2.2.1
  change 1 / 3 < μ.real {x | S.ρ x = k.val} at hA
  have hlarge : 1 - 2 * R.height < μ.real {x | S.ρ x = k.val} := by linarith
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
  · have hb := R.private_atom_mass_lt_third k r u hru hW hd hgap hp hintercept hprivateFirst
    linarith
  · have hp' : R.plateau = {u, r} := by simpa only [Finset.pair_comm] using hp
    have hb := R.private_atom_mass_lt_third k u r hru.symm hW hd hgap hp'
      hintercept hprivateSecond
    linarith
  · have hb := R.twoCenter_shared_mass_lt r u hru hW hd hgap hp hintercept (by linarith [hell.1])
    have hsub := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hshared
    have hm : S.originalAtomMass k ≤ μ.real (S.twoCenterShared r u) :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    change μ.real {x | S.ρ x = k.val} ≤ μ.real (S.twoCenterShared r u) at hm
    linarith

private theorem not_corner_head_trace {A ell gamma h : ℝ}
    (hA : 0 ≤ A) (hell : ell ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hgamma : 2 * (138261458236451 / 1116960975000000 : ℝ) -
      ell * (23243417 / 10 ^ 8) < gamma)
    (hh : h < (23243417 / 10 ^ 8 : ℝ))
    (hbudget : gamma ≤ 2 * (1 - ell) * A ^ 2)
    (htrace : 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 2 * h) : False := by
  have hdelta : 0 < 1 - ell := by linarith [hell.2]
  by_cases hhigh : (1 / 4 : ℝ) ≤ 1 - ell
  · have hsmall : (46 / 125 : ℝ) < A := by
      by_contra hn
      have hsq : A ^ 2 ≤ (46 / 125 : ℝ) ^ 2 := by
        nlinarith only [hA, le_of_not_gt hn]
      have hp := mul_nonneg hdelta.le (sub_nonneg.mpr hsq)
      have hq := mul_nonneg
        (show 0 ≤ 226 / 589 - (1 - ell) by linarith [hell.1])
        (show 0 ≤ 2 * (46 / 125 : ℝ) ^ 2 - 23243417 / 10 ^ 8 by norm_num)
      nlinarith only [hgamma, hbudget, hp, hq]
    have hg : (73 / 1000 : ℝ) < gamma := by linarith only [hgamma, hhigh]
    have hp := mul_pos (sub_pos.mpr hsmall) (sub_pos.mpr hg)
    nlinarith [sq_nonneg (A - 46 / 125), sq_nonneg (gamma - 73 / 1000)]
  · have hsmall : (191 / 500 : ℝ) < A := by
      by_contra hn
      have hsq : A ^ 2 ≤ (191 / 500 : ℝ) ^ 2 := by
        nlinarith only [hA, le_of_not_gt hn]
      have hp := mul_nonneg hdelta.le (sub_nonneg.mpr hsq)
      have hq := mul_nonneg
        (show 0 ≤ 1 / 4 - (1 - ell) by linarith only [hhigh])
        (show 0 ≤ 2 * (191 / 500 : ℝ) ^ 2 - 23243417 / 10 ^ 8 by norm_num)
      nlinarith only [hgamma, hbudget, hp, hq]
    have hg : (57 / 1000 : ℝ) < gamma := by linarith only [hgamma, hell.2]
    have hp := mul_pos (sub_pos.mpr hsmall) (sub_pos.mpr hg)
    nlinarith [sq_nonneg (A - 191 / 500), sq_nonneg (gamma - 57 / 1000)]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual two-center corner recovery is impossible. The common
peak, head location, own slope and positive original body are derived. -/
theorem no_corner_two_center
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) : False := by
  obtain ⟨_, k, _, hpeak, _, _⟩ := S.exists_sharp_corner_peak hW hd hgap he heq hglobal
  change S.IsCommonForwardPeak d c k at hpeak
  have hk := R.corner_common_peak_mem_plateau hW hd hgap he heq hglobal hcard k hpeak
  let I := {x | S.ρ x = k.val}
  have hzero : PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) I ≠ 0 :=
    fun hz => S.no_corner_zero_body k hW hd hgap he heq hglobal hz
  have hpositive := lt_of_le_of_ne (bodyPositiveEnergy_nonnegative W I) (Ne.symm hzero)
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap I (S.hfibers k.val k.property).1]
    at hpositive
  have htrace := R.common_peak_head_positive_body_trace k hk hW hd hgap hpeak hpositive
  have hbudget := R.common_peak_head_square_budget k hk hW hd hgap hpeak hcard
  obtain ⟨hell, _, hh, hgamma⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  apply not_corner_head_trace (A := μ.real I) measureReal_nonneg hell hgamma hh ?_ htrace
  simpa only [sub_neg_eq_add] using hbudget

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

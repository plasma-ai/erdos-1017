module

public import Erdos1017.Benchmark.BenchmarkHeadCountGuards
public import Erdos1017.ContactLocation.BenchmarkSplitSideExtensions
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Derivatives of the benchmark at the mixed/split junction

At the mixed/split junction the benchmark has the mixed branch's left
derivative, agrees on the right with the index-two split extension, and since
that extension has the same slope there, its right derivative equals its left
derivative (`benchmark_mixed_split_right_hasDerivWithinAt`).
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Erdos1017.Benchmark

private theorem junction_sqrt_mem :
    Real.sqrt (2 * epsilonStar) ∈ Ioo (1 / 3 : ℝ) (1 / 2) := by
  rw [sqrt_two_epsilonStar]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  constructor <;> nlinarith

private theorem junction_eventually :
    ∀ᶠ d : ℝ in nhds (1 / 2 - epsilonStar),
      d ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧
        1 / 2 - d < epsilonC ∧ 1 / 2 - d < epsilonD ∧
        Real.sqrt (2 * (1 / 2 - d)) ∈ Ioo (1 / 3 : ℝ) (1 / 2) := by
  have hd : (1 / 2 - epsilonStar : ℝ) ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    constructor <;> linarith [epsilonStar_pos, epsilonStar_lt_tenth]
  have hc : ContinuousAt (fun d : ℝ => 1 / 2 - d) (1 / 2 - epsilonStar) := by
    fun_prop
  have heC : 1 / 2 - (1 / 2 - epsilonStar) < epsilonC := by
    linarith [epsilonStar_lt_tenth, tenth_lt_epsilonC]
  have heD : 1 / 2 - (1 / 2 - epsilonStar) < epsilonD := by
    linarith [epsilonStar_lt_epsilonD]
  have hr : ContinuousAt (fun d : ℝ => Real.sqrt (2 * (1 / 2 - d)))
      (1 / 2 - epsilonStar) := by fun_prop
  have hr0 : Real.sqrt (2 * (1 / 2 - (1 / 2 - epsilonStar))) ∈
      Ioo (1 / 3 : ℝ) (1 / 2) := by
    simpa only [sub_sub_cancel] using junction_sqrt_mem
  filter_upwards [Ioo_mem_nhds hd.1 hd.2,
    hc.eventually (eventually_lt_nhds heC), hc.eventually (eventually_lt_nhds heD),
    hr.eventually (Ioo_mem_nhds hr0.1 hr0.2)] with d hd heC heD hr
  exact ⟨hd, heC, heD, hr⟩

private theorem mixedStationary_junction_hasDerivWithinAt :
    HasDerivWithinAt (fun e => mixedValue (mixedInverse e))
      ((sigmaZero + 1) / (3 * sigmaZero)) (Ici epsilonStar) epsilonStar := by
  let D := -sigmaZero *
    (2 + 24 * sigmaZero + 93 * sigmaZero ^ 2 + 120 * sigmaZero ^ 3) /
    mixedDenominator sigmaZero ^ 3
  have hs0 : 0 < sigmaZero := by linarith [sigmaZero_bounds.1]
  have hD : D < 0 := by
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs0) (by positivity)
    · exact pow_pos (mixedDenominator_pos hs0.le) 3
  have hf : HasDerivAt mixedDensity D (mixedInverse epsilonStar) := by
    rw [mixedInverse_epsilonStar]
    exact mixedDensity_hasDerivAt hs0.le
  have hc : ContinuousWithinAt mixedInverse (Icc epsilonStar epsilonD) epsilonStar :=
    mixedInverse_continuousOn epsilonStar ⟨le_rfl, epsilonStar_lt_epsilonD.le⟩
  have hfg : ∀ᶠ e in nhdsWithin epsilonStar (Icc epsilonStar epsilonD),
      mixedDensity (mixedInverse e) = e := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact (mixedInverse_spec he).2
  have hinv : HasDerivWithinAt mixedInverse D⁻¹ (Icc epsilonStar epsilonD) epsilonStar :=
    HasFDerivWithinAt.of_local_left_inverse (t := univ)
      (by simpa only [nhdsWithin_univ] using hc.tendsto)
      (hf.hasFDerivAt_equiv hD.ne).hasFDerivWithinAt
      ⟨le_rfl, epsilonStar_lt_epsilonD.le⟩ hfg
  have hvalue : HasDerivAt mixedValue
      (((sigmaZero + 1) / (3 * sigmaZero)) * D) (mixedInverse epsilonStar) := by
    rw [mixedInverse_epsilonStar]
    exact mixedValue_hasDerivAt hs0
  have hcomp := hvalue.comp_hasDerivWithinAt epsilonStar hinv
  have hcomp' : HasDerivWithinAt (fun e => mixedValue (mixedInverse e))
      ((sigmaZero + 1) / (3 * sigmaZero)) (Icc epsilonStar epsilonD) epsilonStar := by
    convert hcomp using 1
    · rfl
    · rw [mul_assoc, mul_inv_cancel₀ hD.ne, mul_one]
  exact hcomp'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE epsilonStar_lt_epsilonD)

private theorem benchmark_mixed_junction_left_eventually :
    benchmark =ᶠ[nhdsWithin (1 / 2 - epsilonStar) (Iic (1 / 2 - epsilonStar))]
      (fun d => mixedValue (mixedInverse (1 / 2 - d))) := by
  filter_upwards [junction_eventually.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with d hd hside
  have he : epsilonStar ≤ 1 / 2 - d := by
    change d ≤ 1 / 2 - epsilonStar at hside
    linarith
  have he0 : 1 / 2 - d ≠ 0 := by linarith [hd.1.2]
  have ht : twoHeadCurve (1 / 2 - d) = splitValue (Real.sqrt (2 * (1 / 2 - d))) := by
    simp only [twoHeadCurve, he0, ite_false, hd.2.1.le, ite_true]
  have hm : mixedCurve (1 / 2 - d) = mixedValue (mixedInverse (1 / 2 - d)) := by
    rcases eq_or_lt_of_le he with heq | hlt
    · rw [← heq, mixedInverse_epsilonStar]
      simp only [mixedCurve, le_refl, ite_true]
      exact mixedValue_sigmaZero.symm
    · simp only [mixedCurve, not_le.mpr hlt, ite_false, hd.2.2.1.le, ite_true]
  have hle : splitValue (Real.sqrt (2 * (1 / 2 - d))) ≤ mixedCurve (1 / 2 - d) := by
    rcases eq_or_lt_of_le he with heq | hlt
    · rw [← heq]
      simp only [mixedCurve, le_refl, ite_true]
    · exact (split_lt_mixedCurve ⟨hlt, hd.2.2.1.le⟩
        ⟨hd.2.2.2.1.le, hd.2.2.2.2.le⟩).le
  simp only [benchmark, not_le.mpr hd.1.1, ite_false, hd.1.2, ite_true, ht]
  rw [max_eq_left hle, hm]

/-- At the mixed/split junction, the actual benchmark has the mixed
stationary branch's left derivative, including the endpoint. -/
theorem benchmark_mixed_split_left_hasDerivWithinAt :
    HasDerivWithinAt benchmark (-(Real.sqrt 21 - 1) / 6)
      (Iic (1 / 2 - epsilonStar)) (1 / 2 - epsilonStar) := by
  have hmaps : MapsTo (fun d : ℝ => 1 / 2 - d)
      (Iic (1 / 2 - epsilonStar)) (Ici epsilonStar) := by
    intro d hd
    change d ≤ 1 / 2 - epsilonStar at hd
    change epsilonStar ≤ 1 / 2 - d
    linarith
  have h := mixedStationary_junction_hasDerivWithinAt.comp_of_eq
    (1 / 2 - epsilonStar)
    (((hasDerivAt_const (1 / 2 - epsilonStar) (1 / 2 : ℝ)).sub
      (hasDerivAt_id (1 / 2 - epsilonStar))).hasDerivWithinAt)
    hmaps (by dsimp; ring)
  have h' : HasDerivWithinAt (fun d => mixedValue (mixedInverse (1 / 2 - d)))
      (-(Real.sqrt 21 - 1) / 6)
      (Iic (1 / 2 - epsilonStar)) (1 / 2 - epsilonStar) := by
    convert h using 1
    · rfl
    · rw [mixed_own_slope_sigmaZero]
      ring
  exact h'.congr_of_eventuallyEq benchmark_mixed_junction_left_eventually
    (benchmark_mixed_junction_left_eventually.self_of_nhdsWithin (by simp))

/-- On the right of the mixed/split junction, the actual benchmark
agrees with the ordinary index-two split extension, including the junction. -/
theorem benchmark_mixed_split_right_eventually :
    benchmark =ᶠ[nhdsWithin (1 / 2 - epsilonStar) (Ici (1 / 2 - epsilonStar))]
      splitDensityExtension 2 := by
  filter_upwards [junction_eventually.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with d hd hside
  have he : 1 / 2 - d ≤ epsilonStar := by
    change 1 / 2 - epsilonStar ≤ d at hside
    linarith
  have he0 : 1 / 2 - d ≠ 0 := by linarith [hd.1.2]
  have ht : twoHeadCurve (1 / 2 - d) = splitValue (Real.sqrt (2 * (1 / 2 - d))) := by
    simp only [twoHeadCurve, he0, ite_false, hd.2.1.le, ite_true]
  have hm : mixedCurve (1 / 2 - d) = splitValue (Real.sqrt (2 * (1 / 2 - d))) := by
    simp only [mixedCurve, he, ite_true]
  simp only [benchmark, not_le.mpr hd.1.1, ite_false, hd.1.2, ite_true, hm, ht, max_self]
  rw [splitValue_index_two hd.2.2.2.1.le hd.2.2.2.2]
  rw [show 2 * (1 / 2 - d) = 1 - 2 * d by ring]
  norm_num [splitDensityExtension, splitPolynomial]

/-- The ordinary index-two split extension has the same slope as the
mixed branch at their common junction. -/
theorem splitDensityExtension_two_junction_hasDerivAt :
    HasDerivAt (splitDensityExtension 2) (-(Real.sqrt 21 - 1) / 6)
      (1 / 2 - epsilonStar) := by
  have hd : (1 / 2 - epsilonStar : ℝ) < 1 / 2 := by linarith [epsilonStar_pos]
  have h := splitPolynomial_density_hasDerivAt 2 (by norm_num) hd
  change HasDerivAt (splitDensityExtension 2) _ _ at h
  convert h using 1
  rw [show 1 - 2 * (1 / 2 - epsilonStar) = 2 * epsilonStar by ring]
  have hs := split_own_slope_epsilonStar
  linarith

/-- The actual benchmark has the same right derivative at the
mixed/split junction as its mixed left derivative. -/
theorem benchmark_mixed_split_right_hasDerivWithinAt :
    HasDerivWithinAt benchmark (-(Real.sqrt 21 - 1) / 6)
      (Ici (1 / 2 - epsilonStar)) (1 / 2 - epsilonStar) := by
  exact splitDensityExtension_two_junction_hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq
    benchmark_mixed_split_right_eventually
    (benchmark_mixed_split_right_eventually.self_of_nhdsWithin (by simp))

end Erdos1017.Benchmark

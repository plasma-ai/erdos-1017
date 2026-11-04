module

public import Erdos1017.Benchmark.BenchmarkCrossingBounds
public import Erdos1017.Benchmark.BenchmarkPhiBounds
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Right derivatives of the benchmark on the head-count interval

The branch comparisons include both benchmark junctions in this interval.
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- For `ε* < e < ε_D`, `x ↦ mixedValue (mixedInverse x)` has derivative
`(s + 1)/(3s)` at `e`, where `s = mixedInverse e`. -/
theorem mixedStationary_hasDerivAt {e : ℝ} (he : e ∈ Set.Ioo epsilonStar epsilonD) :
    HasDerivAt (fun x => mixedValue (mixedInverse x))
      ((mixedInverse e + 1) / (3 * mixedInverse e)) e := by
  have hi := mixedInverse_spec ⟨he.1.le, he.2.le⟩
  have hs0 : 0 < mixedInverse e := by linarith [sigmaD_spec.1.1, hi.1.1]
  have hd : -mixedInverse e *
      (2 + 24 * mixedInverse e + 93 * mixedInverse e ^ 2 + 120 * mixedInverse e ^ 3) /
      mixedDenominator (mixedInverse e) ^ 3 < 0 := by
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs0) (by positivity)
    · exact pow_pos (mixedDenominator_pos hs0.le) 3
  have hc : ContinuousAt mixedInverse e :=
    (mixedInverse_continuousOn e ⟨he.1.le, he.2.le⟩).continuousAt (Icc_mem_nhds he.1 he.2)
  have hinv := HasDerivAt.of_local_left_inverse hc (mixedDensity_hasDerivAt hs0.le) hd.ne
    (show ∀ᶠ x in nhds e, mixedDensity (mixedInverse x) = x from by
      filter_upwards [Ioo_mem_nhds he.1 he.2] with x hx
      exact (mixedInverse_spec ⟨hx.1.le, hx.2.le⟩).2)
  convert (mixedValue_hasDerivAt hs0).comp e hinv using 1
  · rfl
  · rw [mul_assoc, mul_inv_cancel₀ hd.ne, mul_one]

/-- For `z ∈ [2/3, z_C]`, the derivative
`z(21z³ - 39z² + 24z - 5) / (8(z² + z - 1)³)` of `twoHeadDensity` is
negative. -/
private theorem twoHeadDensity_derivative_neg {z : ℝ}
    (hz : z ∈ Set.Icc (2 / 3) zC) :
    z * (21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5) /
      (8 * twoHeadDenominator z ^ 3) < 0 := by
  have hzhi : z ≤ 4 / 5 := hz.2.trans zC_spec.1.2
  have hz0 : 0 < z := by linarith [hz.1]
  have ht : 0 ≤ z - 2 / 3 := sub_nonneg.mpr hz.1
  have ht' : z - 2 / 3 ≤ 2 / 15 := by linarith
  have h2 : (z - 2 / 3) ^ 2 ≤ (2 / 15 : ℝ) ^ 2 := by gcongr
  have h3 : (z - 2 / 3) ^ 3 ≤ (2 / 15 : ℝ) ^ 3 := by gcongr
  have hp : 21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5 < 0 := by nlinarith
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hz0 hp)
    (mul_pos (by norm_num) (pow_pos (twoHeadDenominator_pos hz.1) 3))

/-- For `ε_C < e < 1/4`, `x ↦ twoHeadValue (twoHeadInverse x)` has derivative
`(4 - 3z)/(3z)` at `e`, where `z = twoHeadInverse e`. -/
theorem twoHeadStationary_hasDerivAt {e : ℝ} (he : e ∈ Set.Ioo epsilonC (1 / 4)) :
    HasDerivAt (fun x => twoHeadValue (twoHeadInverse x))
      ((4 - 3 * twoHeadInverse e) / (3 * twoHeadInverse e)) e := by
  have hi := twoHeadInverse_spec ⟨he.1.le, he.2.le⟩
  have hd := twoHeadDensity_derivative_neg hi.1
  have hc : ContinuousAt twoHeadInverse e :=
    (twoHeadInverse_continuousOn e ⟨he.1.le, he.2.le⟩).continuousAt (Icc_mem_nhds he.1 he.2)
  have hinv := HasDerivAt.of_local_left_inverse hc (twoHeadDensity_hasDerivAt hi.1.1) hd.ne
    (show ∀ᶠ x in nhds e, twoHeadDensity (twoHeadInverse x) = x from by
      filter_upwards [Ioo_mem_nhds he.1 he.2] with x hx
      exact (twoHeadInverse_spec ⟨hx.1.le, hx.2.le⟩).2)
  convert (twoHeadValue_hasDerivAt hi.1.1).comp e hinv using 1
  · rfl
  · rw [mul_assoc, mul_inv_cancel₀ hd.ne, mul_one]

/-- For `ε* < e < ε_D`, `W` has derivative `(s + 1)/(3s)` at `e`, where `s = mixedInverse e`. -/
theorem mixedCurve_hasDerivAt {e : ℝ} (he : e ∈ Set.Ioo epsilonStar epsilonD) :
    HasDerivAt mixedCurve ((mixedInverse e + 1) / (3 * mixedInverse e)) e := by
  apply (mixedStationary_hasDerivAt he).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds he.1 he.2] with x hx
  simp only [mixedCurve, not_le.mpr hx.1, ite_false, hx.2.le, ite_true]

/-- For `ε_C < e < 1/4`, `E₂` has derivative `(4 - 3z)/(3z)` at `e`, where
`z = twoHeadInverse e`. -/
theorem twoHeadCurve_hasDerivAt {e : ℝ} (he : e ∈ Set.Ioo epsilonC (1 / 4)) :
    HasDerivAt twoHeadCurve ((4 - 3 * twoHeadInverse e) / (3 * twoHeadInverse e)) e := by
  apply (twoHeadStationary_hasDerivAt he).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds he.1 he.2] with x hx
  have hx0 : x ≠ 0 := by linarith [hx.1, tenth_lt_epsilonC]
  simp only [twoHeadCurve, hx0, ite_false, not_le.mpr hx.1]

/-- For every `r`, the mixed tangent at `σ₀` evaluated at `r²/2` exceeds the
index-two split polynomial at `r` by `(r - √(2ε*))²/(2√(2ε*))`. -/
theorem mixedTangent_sigmaZero_sub_split {r : ℝ} :
    mixedTangent sigmaZero (r ^ 2 / 2) - splitPolynomial 2 r =
      (r - Real.sqrt (2 * epsilonStar)) ^ 2 / (2 * Real.sqrt (2 * epsilonStar)) := by
  have hr0 : 0 < Real.sqrt (2 * epsilonStar) := Real.sqrt_pos.mpr (by linarith [epsilonStar_pos])
  have hs0 : sigmaZero ≠ 0 := ne_of_gt (lt_trans (by norm_num) sigmaZero_bounds.1)
  have hslope := mixed_own_slope_sigmaZero
  have hsplit := split_own_slope_epsilonStar
  have hvalue := mixedValue_sigmaZero
  rw [splitValue_index_two (by
    rw [sqrt_two_epsilonStar]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
    have hn := Real.sqrt_nonneg (21 : ℝ)
    nlinarith) (by
    rw [sqrt_two_epsilonStar]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
    have hn := Real.sqrt_nonneg (21 : ℝ)
    nlinarith)] at hvalue
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * epsilonStar by linarith [epsilonStar_pos])
  unfold mixedTangent
  rw [mixedDensity_sigmaZero, hvalue, hslope, ← hsplit]
  unfold splitPolynomial
  norm_num only [Nat.cast_ofNat]
  field_simp
  nlinarith

/-- For `ε* < e ≤ ε_D` with `1/3 ≤ √(2e) ≤ 1/2`, the split value lies strictly
below `W`: `H(√(2e)) < W(e)`. -/
theorem split_lt_mixedCurve {e : ℝ} (he : e ∈ Set.Ioc epsilonStar epsilonD)
    (hr : Real.sqrt (2 * e) ∈ Set.Icc (1 / 3) (1 / 2)) :
    splitValue (Real.sqrt (2 * e)) < mixedCurve e := by
  have he0 : 0 < e := epsilonStar_pos.trans he.1
  have hr0 : 0 < Real.sqrt (2 * epsilonStar) := Real.sqrt_pos.mpr (by linarith [epsilonStar_pos])
  have hne : Real.sqrt (2 * e) ≠ Real.sqrt (2 * epsilonStar) := by
    intro h
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * e by positivity)
    have hsq' := Real.sq_sqrt (show 0 ≤ 2 * epsilonStar by linarith [epsilonStar_pos])
    rw [h] at hsq
    linarith [he.1]
  have hg := mixedTangent_sigmaZero_sub_split (r := Real.sqrt (2 * e))
  rw [Real.sq_sqrt (show 0 ≤ 2 * e by positivity)] at hg
  rw [show 2 * e / 2 = e by ring] at hg
  have hp : 0 < (Real.sqrt (2 * e) - Real.sqrt (2 * epsilonStar)) ^ 2 /
      (2 * Real.sqrt (2 * epsilonStar)) := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) (by positivity)
  have ht := mixedTangent_le_mixedCurve (a := sigmaZero)
    (lt_trans (by norm_num) sigmaZero_bounds.1) ⟨he.1.le, he.2⟩
  have hcell := splitValue_on_cell 1 (r := Real.sqrt (2 * e)) (by
    norm_num only [Nat.cast_one]
    exact hr)
  norm_num only [Nat.cast_one, Nat.reduceAdd] at hcell
  rw [hcell]
  linarith

/-- If `f` has derivative `a` at `1/2 - d`, then `x ↦ f(1/2 - x)` has derivative `-a` at `d`. -/
private theorem half_sub_hasDerivAt {f : ℝ → ℝ} {a d : ℝ}
    (h : HasDerivAt f a (1 / 2 - d)) :
    HasDerivAt (fun x : ℝ => f (1 / 2 - x)) (-a) d := by
  convert h.comp d ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)) using 1
  · rfl
  · ring

/-- For `1/4 < d < 1/2`, `B(d) = max(W(1/2 - d), E₂(1/2 - d))`. -/
private theorem benchmark_eq_max {d : ℝ} (hd : d ∈ Set.Ioo (1 / 4) (1 / 2)) :
    benchmark d = max (mixedCurve (1 / 2 - d)) (twoHeadCurve (1 / 2 - d)) := by
  simp only [benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true]

/-- For `1/4 < d < 1/2`, `x ↦ W(1/2 - x)` and `x ↦ E₂(1/2 - x)` are continuous at `d`. -/
private theorem family_density_continuousAt {d : ℝ} (hd : d ∈ Set.Ioo (1 / 4) (1 / 2)) :
    ContinuousAt (fun x : ℝ => mixedCurve (1 / 2 - x)) d ∧
      ContinuousAt (fun x : ℝ => twoHeadCurve (1 / 2 - x)) d := by
  have he : 1 / 2 - d ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor <;> linarith [hd.1, hd.2]
  have hm := (mixedCurve_continuousOn (1 / 2 - d) ⟨he.1.le, he.2.le⟩).continuousAt
    (Icc_mem_nhds he.1 he.2)
  have ht := (twoHeadCurve_continuousOn (1 / 2 - d) ⟨he.1.le, he.2.le⟩).continuousAt
    (Icc_mem_nhds he.1 he.2)
  exact ⟨hm.comp (by fun_prop), ht.comp (by fun_prop)⟩

/-- For `1/4 < d < 1/2` with `ε = 1/2 - d > ε_C` and `W(ε) < E₂(ε)`, `B` has
derivative `-(4 - 3z)/(3z)` at `d`, where `z = twoHeadInverse ε`. -/
private theorem benchmark_twoHead_hasDerivAt {d : ℝ}
    (hd : d ∈ Set.Ioo (1 / 4) (1 / 2)) (he : epsilonC < 1 / 2 - d)
    (hactive : mixedCurve (1 / 2 - d) < twoHeadCurve (1 / 2 - d)) :
    HasDerivAt benchmark
      (-((4 - 3 * twoHeadInverse (1 / 2 - d)) / (3 * twoHeadInverse (1 / 2 - d)))) d := by
  have hc := family_density_continuousAt hd
  have hnear := hc.1.eventually_lt hc.2 hactive
  have hder := half_sub_hasDerivAt
    (twoHeadCurve_hasDerivAt (e := 1 / 2 - d) ⟨he, by linarith [hd.1]⟩)
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hd.1 hd.2, hnear] with x hx hact
  rw [benchmark_eq_max hx, max_eq_right hact.le]

/-- For `1/4 < d < 1/2` with `ε = 1/2 - d ∈ (ε*, ε_D)` and `E₂(ε) < W(ε)`, `B`
has derivative `-(s + 1)/(3s)` at `d`, where `s = mixedInverse ε`. -/
private theorem benchmark_mixed_hasDerivAt_of_strict {d : ℝ}
    (hd : d ∈ Set.Ioo (1 / 4) (1 / 2))
    (he : 1 / 2 - d ∈ Set.Ioo epsilonStar epsilonD)
    (hactive : twoHeadCurve (1 / 2 - d) < mixedCurve (1 / 2 - d)) :
    HasDerivAt benchmark
      (-((mixedInverse (1 / 2 - d) + 1) / (3 * mixedInverse (1 / 2 - d)))) d := by
  have hc := family_density_continuousAt hd
  have hnear := hc.2.eventually_lt hc.1 hactive
  have hder := half_sub_hasDerivAt (mixedCurve_hasDerivAt he)
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hd.1 hd.2, hnear] with x hx hact
  rw [benchmark_eq_max hx, max_eq_left hact.le]

/-- For `1/4 < d < 1/2` with `ε = 1/2 - d ∈ (ε_C, ε_D)` and `E₂(ε) ≤ W(ε)`,
`B` has right derivative `-(s + 1)/(3s)` at `d` (within `[d, ∞)`), where
`s = mixedInverse ε`. -/
private theorem benchmark_mixed_hasDerivWithinAt_of_overlap {d : ℝ}
    (hd : d ∈ Set.Ioo (1 / 4) (1 / 2))
    (he : 1 / 2 - d ∈ Set.Ioo epsilonC epsilonD)
    (hactive : twoHeadCurve (1 / 2 - d) ≤ mixedCurve (1 / 2 - d)) :
    HasDerivWithinAt benchmark
      (-((mixedInverse (1 / 2 - d) + 1) / (3 * mixedInverse (1 / 2 - d)))) (Set.Ici d) d := by
  have hstar : epsilonStar < 1 / 2 - d := by
    linarith [he.1, epsilonStar_lt_tenth, tenth_lt_epsilonC]
  have hder := (half_sub_hasDerivAt (mixedCurve_hasDerivAt ⟨hstar, he.2⟩)).hasDerivWithinAt
    (s := Set.Ici d)
  have hnear : ∀ᶠ x in nhds d, 1 / 2 - x ∈ Set.Ioo epsilonC epsilonD :=
    (show ContinuousAt (fun x : ℝ => 1 / 2 - x) d by fun_prop).eventually
      (isOpen_Ioo.mem_nhds he)
  have hdom : ∀ᶠ x in nhds d, x ∈ Set.Ioo (1 / 4) (1 / 2) := Ioo_mem_nhds hd.1 hd.2
  apply hder.congr_of_eventuallyEq _ (by rw [benchmark_eq_max hd, max_eq_left hactive])
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
    hdom.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hx hxd hright
  have hdle : d ≤ x := hright
  have hm := family_difference_strictMonoOn.monotoneOn
    ⟨hx.1.le, hx.2.le⟩ ⟨he.1.le, he.2.le⟩ (by linarith)
  have hact : twoHeadCurve (1 / 2 - x) ≤ mixedCurve (1 / 2 - x) := by
    linarith
  rw [benchmark_eq_max hxd, max_eq_left hact]

/-- For `3/8 < d < 21/50` there is `L` such that `B` has right derivative `-L`
at `d` (within `[d, ∞)`), `1/2 < L < 1`, `B(d) > 1/2 - d`, and the head-count
ratio satisfies `√(1 - 2d)(1 - L)/(2(B(d) - L(1/2 - d))) < 2`. -/
theorem benchmark_head_count_guards {d : ℝ} (hd : d ∈ Set.Ioo (3 / 8 : ℝ) (21 / 50)) :
    ∃ L : ℝ, HasDerivWithinAt benchmark (-L) (Set.Ici d) d ∧
      1 / 2 < L ∧ L < 1 ∧ benchmark d > 1 / 2 - d ∧
      Real.sqrt (1 - 2 * d) * (1 - L) /
        (2 * (benchmark d - L * (1 / 2 - d))) < 2 := by
  have hdom : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
    constructor <;> linarith [hd.1, hd.2]
  have he : 1 / 2 - d ∈ Set.Ioo (2 / 25 : ℝ) (1 / 8) := by
    constructor <;> linarith [hd.1, hd.2]
  have hr0 := Real.sqrt_nonneg (1 - 2 * d)
  have hrsq := Real.sq_sqrt (show 0 ≤ 1 - 2 * d by linarith [hd.2])
  have hr : Real.sqrt (1 - 2 * d) ∈ Set.Ioo (2 / 5 : ℝ) (1 / 2) := by
    constructor <;> nlinarith [hd.1, hd.2]
  have heD : 1 / 2 - d < epsilonD := he.2.trans eighth_lt_epsilonD
  have hsqrt : Real.sqrt (2 * (1 / 2 - d)) = Real.sqrt (1 - 2 * d) := by
    congr 1
    ring
  by_cases heS : 1 / 2 - d ≤ epsilonStar
  · have heC : 1 / 2 - d ≤ epsilonC :=
      heS.trans (epsilonStar_lt_tenth.trans tenth_lt_epsilonC).le
    have hphi := split_phi_bounds (r := Real.sqrt (1 - 2 * d))
      (show Real.sqrt (1 - 2 * d) ∈ Set.Ioo (2 / 5 : ℝ) (9 / 20) from by
        refine ⟨hr.1, ?_⟩
        have hstar : epsilonStar < 81 / 800 := by
          have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
          have hn := Real.sqrt_nonneg (21 : ℝ)
          unfold epsilonStar
          nlinarith
        nlinarith)
    have hcell : Real.sqrt (1 - 2 * d) ∈
        Set.Ioo (1 / (((1 : ℕ) : ℝ) + 2)) (1 / (((1 : ℕ) : ℝ) + 1)) := by
      norm_num only [Nat.cast_one]
      constructor <;> linarith [hr.1, hr.2]
    have hval : benchmark d = splitPolynomial 2 (Real.sqrt (1 - 2 * d)) := by
      rw [benchmark_eq_max hdom]
      have he0 : 1 / 2 - d ≠ 0 := by linarith [he.1]
      simp only [mixedCurve, heS, ite_true, twoHeadCurve, he0, ite_false, heC, max_self]
      rw [hsqrt]
      exact splitValue_on_cell 1 ⟨hcell.1.le, hcell.2.le⟩
    have hder : HasDerivAt (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x)))
        (-(1 / Real.sqrt (1 - 2 * d) - 5 / 3)) d := by
      convert splitValue_density_hasDerivAt 1 hcell using 1
      norm_num only [Nat.cast_ofNat]
      ring
    have hnear : ∀ᶠ x in nhds d, x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) :=
      Ioo_mem_nhds hdom.1 hdom.2
    have heq : benchmark =ᶠ[nhdsWithin d (Set.Ici d)]
        (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x))) := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hright
      have hdle : d ≤ x := hright
      have hxS : 1 / 2 - x ≤ epsilonStar := by linarith
      have hxC : 1 / 2 - x ≤ epsilonC := by linarith
      have hx0 : 1 / 2 - x ≠ 0 := by linarith [hx.2]
      rw [benchmark_eq_max hx]
      simp only [mixedCurve, hxS, ite_true, twoHeadCurve, hx0, ite_false, hxC, max_self]
      congr 2
      ring
    refine ⟨1 / Real.sqrt (1 - 2 * d) - 5 / 3,
      hder.hasDerivWithinAt.congr_of_eventuallyEq heq (by
        rw [hval]
        exact (splitValue_on_cell 1 ⟨hcell.1.le, hcell.2.le⟩).symm),
      hphi.1, hphi.2.1, ?_, ?_⟩
    · rw [hval]
      nlinarith [hphi.2.2.1]
    · rw [hval, show 1 / 2 - d = Real.sqrt (1 - 2 * d) ^ 2 / 2 by nlinarith]
      exact hphi.2.2.2
  · have heS' : epsilonStar < 1 / 2 - d := lt_of_not_ge heS
    have hsplit : splitValue (Real.sqrt (2 * (1 / 2 - d))) < mixedCurve (1 / 2 - d) :=
      split_lt_mixedCurve ⟨heS', heD.le⟩ (by rw [hsqrt]; constructor <;> linarith [hr.1, hr.2])
    by_cases hactive : twoHeadCurve (1 / 2 - d) ≤ mixedCurve (1 / 2 - d)
    · have hi := mixedInverse_spec ⟨heS'.le, heD.le⟩
      have hs : sigmaD < mixedInverse (1 / 2 - d) := by
        by_contra h
        have hseq : mixedInverse (1 / 2 - d) = sigmaD := le_antisymm (le_of_not_gt h) hi.1.1
        have heq := hi.2
        rw [hseq] at heq
        change epsilonD = 1 / 2 - d at heq
        linarith
      have hval : benchmark d = mixedValue (mixedInverse (1 / 2 - d)) := by
        rw [benchmark_eq_max hdom, max_eq_left hactive]
        simp only [mixedCurve, not_le.mpr heS', ite_false, heD.le, ite_true]
      have hphi := mixed_phi_bounds hs hi.1.2 (by rw [hi.2]; linarith [he.1])
      have hder : HasDerivWithinAt benchmark
          (-((mixedInverse (1 / 2 - d) + 1) / (3 * mixedInverse (1 / 2 - d)))) (Set.Ici d) d := by
        by_cases heC : 1 / 2 - d ≤ epsilonC
        · have hE : twoHeadCurve (1 / 2 - d) = splitValue (Real.sqrt (2 * (1 / 2 - d))) := by
            have he0 : 1 / 2 - d ≠ 0 := by linarith [he.1]
            simp only [twoHeadCurve, he0, ite_false, heC, ite_true]
          exact (benchmark_mixed_hasDerivAt_of_strict hdom ⟨heS', heD⟩
            (by rw [hE]; exact hsplit)).hasDerivWithinAt
        · exact benchmark_mixed_hasDerivWithinAt_of_overlap hdom
            ⟨lt_of_not_ge heC, heD⟩ hactive
      refine ⟨(mixedInverse (1 / 2 - d) + 1) / (3 * mixedInverse (1 / 2 - d)),
        hder, hphi.1, hphi.2.1, ?_, ?_⟩
      · have hv := hphi.2.2.1
        rw [hi.2] at hv
        rw [hval]
        exact hv
      · have hp := hphi.2.2.2
        rw [hi.2, hsqrt] at hp
        rw [hval]
        exact hp
    · have hactive' := lt_of_not_ge hactive
      have heC : epsilonC < 1 / 2 - d := by
        by_contra h
        have heC := le_of_not_gt h
        have hE : twoHeadCurve (1 / 2 - d) = splitValue (Real.sqrt (2 * (1 / 2 - d))) := by
          have he0 : 1 / 2 - d ≠ 0 := by linarith [he.1]
          simp only [twoHeadCurve, he0, ite_false, heC, ite_true]
        rw [hE] at hactive'
        linarith
      have hi := twoHeadInverse_spec ⟨heC.le, by linarith [he.2]⟩
      have hz : twoHeadInverse (1 / 2 - d) ∈ Set.Ioo (2 / 3 : ℝ) (4 / 5) := by
        refine ⟨?_, hi.1.2.trans_lt zC_lt_four_fifths⟩
        by_contra h
        have hzeq : twoHeadInverse (1 / 2 - d) = 2 / 3 := le_antisymm (le_of_not_gt h) hi.1.1
        have heq := hi.2
        rw [hzeq, twoHeadDensity_two_thirds] at heq
        linarith [he.2]
      have hphi := twoHead_phi_bounds hz (by rw [hi.2]; linarith [he.1])
      have hval : benchmark d = twoHeadValue (twoHeadInverse (1 / 2 - d)) := by
        rw [benchmark_eq_max hdom, max_eq_right hactive'.le]
        have he0 : 1 / 2 - d ≠ 0 := by linarith [he.1]
        simp only [twoHeadCurve, he0, ite_false, not_le.mpr heC]
      refine ⟨(4 - 3 * twoHeadInverse (1 / 2 - d)) / (3 * twoHeadInverse (1 / 2 - d)),
        (benchmark_twoHead_hasDerivAt hdom heC hactive').hasDerivWithinAt,
        hphi.1, hphi.2.1, ?_, ?_⟩
      · have hv := hphi.2.2.1
        rw [hi.2] at hv
        rw [hval]
        exact hv
      · have hp := hphi.2.2.2
        rw [hi.2, hsqrt] at hp
        rw [hval]
        exact hp

end Erdos1017.Benchmark

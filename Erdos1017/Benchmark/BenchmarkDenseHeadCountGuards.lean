module

public import Erdos1017.Benchmark.BenchmarkHeadCountGuards
public import Erdos1017.Benchmark.BenchmarkHeadRatio

/-!
# Right slope and head-count ratio on the dense bridge

At the reciprocal cusp the right density derivative uses the index-three split
branch. No multipartite maximizer or variational multiplier is assumed.
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- The split junction of `W` satisfies `2/25 < ε*`. -/
theorem two_twenty_fifths_lt_epsilonStar : (2 / 25 : ℝ) < epsilonStar := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  unfold epsilonStar
  nlinarith

/-- For `21/50 ≤ d ≤ 1/2`, the benchmark is the split value: `B(d) = H(√(1 - 2d))`. -/
theorem benchmark_eq_split_of_dense {d : ℝ} (hd : d ∈ Set.Icc (21 / 50 : ℝ) (1 / 2)) :
    benchmark d = splitValue (Real.sqrt (1 - 2 * d)) := by
  by_cases heq : d = 1 / 2
  · subst d
    norm_num [splitValue]
  have hhalf : d < 1 / 2 := lt_of_le_of_ne hd.2 heq
  have hquarter : 1 / 4 < d := by linarith [hd.1]
  have heS : 1 / 2 - d ≤ epsilonStar := by linarith [hd.1, two_twenty_fifths_lt_epsilonStar]
  have heC : 1 / 2 - d ≤ epsilonC := by linarith [hd.1, tenth_lt_epsilonC]
  have he0 : 1 / 2 - d ≠ 0 := by linarith
  simp only [benchmark, not_le.mpr hquarter, ite_false, hhalf, ite_true,
    mixedCurve, heS, twoHeadCurve, he0, heC, max_self]
  congr 2
  ring

/-- If `1/(n + 2) < √(1 - 2d) ≤ 1/(n + 1)`, then `x ↦ H(√(1 - 2x))` has right
derivative `2(2j + 1)/(j(j + 1)) - 2/(j√(1 - 2d))` at `d` (within `[d, ∞)`),
where `j = n + 1`. -/
theorem splitValue_density_hasDerivWithinAt_right_cell (n : ℕ) {d : ℝ}
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Set.Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    HasDerivWithinAt (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x)))
      (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) /
        (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) -
          2 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (1 - 2 * d))) (Set.Ici d) d := by
  have hr : 0 < Real.sqrt (1 - 2 * d) := lt_trans (by positivity) hcell.1
  have hd : d < 1 / 2 := by
    have := Real.sqrt_pos.mp hr
    linarith
  have hder := (splitPolynomial_density_hasDerivAt (n + 1) (by omega) hd).hasDerivWithinAt
    (s := Set.Ici d)
  have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 - 2 * x)) d := by fun_prop
  have hnear : ∀ᶠ x in nhds d, 1 / ((n : ℝ) + 2) < Real.sqrt (1 - 2 * x) :=
    hc.eventually_const_lt hcell.1
  apply hder.congr_of_eventuallyEq _ (splitValue_on_cell n ⟨hcell.1.le, hcell.2⟩)
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hright
  have hdle : d ≤ x := hright
  have hhi : Real.sqrt (1 - 2 * x) ≤ Real.sqrt (1 - 2 * d) :=
    Real.sqrt_le_sqrt (by linarith)
  exact splitValue_on_cell n ⟨hx.le, hhi.trans hcell.2⟩

/-- For `1/3 < r ≤ 2/5`, put `L = 1/r - 5/3`, `e = r²/2` and
`b = splitPolynomial 2 r`; then `L ≥ 5/6`, `e < b`, and if `L < 1` the
head-count ratio satisfies `r(1 - L)/(2(b - Le)) ≤ 1`. -/
theorem split_two_dense_phi_bounds {r : ℝ} (hr : r ∈ Set.Ioc (1 / 3 : ℝ) (2 / 5)) :
    5 / 6 ≤ 1 / r - 5 / 3 ∧ r ^ 2 / 2 < splitPolynomial 2 r ∧
      (1 / r - 5 / 3 < 1 →
        r * (1 - (1 / r - 5 / 3)) /
          (2 * (splitPolynomial 2 r - (1 / r - 5 / 3) * (r ^ 2 / 2))) ≤ 1) := by
  have hr0 : 0 < r := by linarith [hr.1]
  have hL : 5 / 6 ≤ 1 / r - 5 / 3 := by
    have h : 5 / 2 ≤ 1 / r := (le_div_iff₀ hr0).mpr (by linarith [hr.2])
    linarith
  have hv : r ^ 2 / 2 < splitPolynomial 2 r := by
    have hp := mul_pos (show 0 < 1 - 2 * r by linarith [hr.2])
      (show 0 < 4 * r - 1 by linarith [hr.1])
    norm_num [splitPolynomial]
    nlinarith
  refine ⟨hL, hv, ?_⟩
  intro hLhi
  have hr' := hr0.ne'
  have hd : 3 * r - 1 ≠ 0 := by linarith [hr.1]
  have hden : 2 * (splitPolynomial 2 r - (1 / r - 5 / 3) * (r ^ 2 / 2)) =
      (3 * r - 1) / 3 := by
    norm_num [splitPolynomial]
    field_simp
    ring
  have hid : r * (1 - (1 / r - 5 / 3)) /
      (2 * (splitPolynomial 2 r - (1 / r - 5 / 3) * (r ^ 2 / 2))) =
        (8 * r - 3) / (3 * r - 1) := by
    rw [hden]
    field_simp
    ring
  rw [hid]
  apply (div_le_iff₀ (by linarith [hr.1] : 0 < 3 * r - 1)).mpr
  linarith [hr.2]

/-- For `4/13 ≤ r ≤ 1/3`, put `L = 2/(3r) - 7/6`, `e = r²/2` and
`b = splitPolynomial 3 r`; then `L ≥ 5/6`, `e < b`, and the head-count ratio
satisfies `r(1 - L)/(2(b - Le)) ≤ 1`. -/
theorem split_three_dense_phi_bounds {r : ℝ} (hr : r ∈ Set.Icc (4 / 13 : ℝ) (1 / 3)) :
    5 / 6 ≤ 2 / (3 * r) - 7 / 6 ∧ r ^ 2 / 2 < splitPolynomial 3 r ∧
      r * (1 - (2 / (3 * r) - 7 / 6)) /
        (2 * (splitPolynomial 3 r - (2 / (3 * r) - 7 / 6) * (r ^ 2 / 2))) ≤ 1 := by
  have hr0 : 0 < r := by linarith [hr.1]
  have hL : 5 / 6 ≤ 2 / (3 * r) - 7 / 6 := by
    have h : 2 ≤ 2 / (3 * r) := (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
      (by linarith [hr.2])
    linarith
  have hv : r ^ 2 / 2 < splitPolynomial 3 r := by
    have hp := mul_nonneg (show 0 ≤ 1 / 3 - r by linarith [hr.2]) hr0.le
    norm_num [splitPolynomial]
    nlinarith [hr.1]
  have hr' := hr0.ne'
  have hd : 4 * r - 1 ≠ 0 := by linarith [hr.1]
  have hden : 2 * (splitPolynomial 3 r - (2 / (3 * r) - 7 / 6) * (r ^ 2 / 2)) =
      (4 * r - 1) / 6 := by
    norm_num [splitPolynomial]
    field_simp
    ring
  have hid : r * (1 - (2 / (3 * r) - 7 / 6)) /
      (2 * (splitPolynomial 3 r - (2 / (3 * r) - 7 / 6) * (r ^ 2 / 2))) =
        (13 * r - 4) / (4 * r - 1) := by
    rw [hden]
    field_simp
    ring
  refine ⟨hL, hv, ?_⟩
  rw [hid]
  apply (div_le_iff₀ (by linarith [hr.1] : 0 < 4 * r - 1)).mpr
  linarith [hr.2]

/-- For `21/50 ≤ d ≤ 153/338` there is `L` such that `B` has right derivative
`-L` at `d` (within `[d, ∞)`), `L ≥ 5/6`, `B(d) > 1/2 - d`, and, if `L < 1`,
the head-count ratio satisfies
`√(1 - 2d)(1 - L)/(2(B(d) - L(1/2 - d))) ≤ 1`. -/
theorem benchmark_dense_head_count_guards {d : ℝ}
    (hd : d ∈ Set.Icc (21 / 50 : ℝ) (153 / 338)) :
    ∃ L : ℝ, HasDerivWithinAt benchmark (-L) (Set.Ici d) d ∧
      5 / 6 ≤ L ∧ benchmark d > 1 / 2 - d ∧
      (L < 1 → Real.sqrt (1 - 2 * d) * (1 - L) /
        (2 * (benchmark d - L * (1 / 2 - d))) ≤ 1) := by
  have hdhalf : d < 1 / 2 := by linarith [hd.2]
  have hr0 := Real.sqrt_nonneg (1 - 2 * d)
  have hrsq := Real.sq_sqrt (show 0 ≤ 1 - 2 * d by linarith)
  have hr : Real.sqrt (1 - 2 * d) ∈ Set.Icc (4 / 13 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hd.1, hd.2]
  have hsplit := benchmark_eq_split_of_dense ⟨hd.1, hdhalf.le⟩
  have hnear : ∀ᶠ x in nhds d, x < 1 / 2 := Iio_mem_nhds hdhalf
  have heq : benchmark =ᶠ[nhdsWithin d (Set.Ici d)]
      (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x))) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hright
    have hdx : d ≤ x := hright
    exact benchmark_eq_split_of_dense ⟨hd.1.trans hdx, hx.le⟩
  by_cases hcut : 1 / 3 < Real.sqrt (1 - 2 * d)
  · have hcell : Real.sqrt (1 - 2 * d) ∈
        Set.Ioo (1 / (((1 : ℕ) : ℝ) + 2)) (1 / (((1 : ℕ) : ℝ) + 1)) := by
      norm_num only [Nat.cast_one]
      constructor <;> linarith [hr.2]
    have hder : HasDerivAt (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x)))
        (-(1 / Real.sqrt (1 - 2 * d) - 5 / 3)) d := by
      convert splitValue_density_hasDerivAt 1 hcell using 1
      norm_num only [Nat.cast_ofNat]
      ring
    have hval : benchmark d = splitPolynomial 2 (Real.sqrt (1 - 2 * d)) := by
      rw [hsplit]
      exact splitValue_on_cell 1 ⟨hcell.1.le, hcell.2.le⟩
    have hphi := split_two_dense_phi_bounds ⟨hcut, hr.2⟩
    refine ⟨1 / Real.sqrt (1 - 2 * d) - 5 / 3,
      hder.hasDerivWithinAt.congr_of_eventuallyEq heq hsplit, hphi.1, ?_, ?_⟩
    · rw [hval]
      nlinarith [hphi.2.1]
    · intro hL
      rw [hval, show 1 / 2 - d = Real.sqrt (1 - 2 * d) ^ 2 / 2 by nlinarith]
      exact hphi.2.2 hL
  · have hrhi : Real.sqrt (1 - 2 * d) ≤ 1 / 3 := le_of_not_gt hcut
    have hcell : Real.sqrt (1 - 2 * d) ∈
        Set.Ioc (1 / (((2 : ℕ) : ℝ) + 2)) (1 / (((2 : ℕ) : ℝ) + 1)) := by
      norm_num only [Nat.cast_ofNat]
      constructor <;> linarith [hr.1]
    have hder : HasDerivWithinAt (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x)))
        (-(2 / (3 * Real.sqrt (1 - 2 * d)) - 7 / 6)) (Set.Ici d) d := by
      convert splitValue_density_hasDerivWithinAt_right_cell 2 hcell using 1
      norm_num only [Nat.cast_ofNat]
      ring
    have hval : benchmark d = splitPolynomial 3 (Real.sqrt (1 - 2 * d)) := by
      rw [hsplit]
      exact splitValue_on_cell 2 ⟨hcell.1.le, hcell.2⟩
    have hphi := split_three_dense_phi_bounds ⟨hr.1, hrhi⟩
    refine ⟨2 / (3 * Real.sqrt (1 - 2 * d)) - 7 / 6,
      hder.congr_of_eventuallyEq heq hsplit, hphi.1, ?_, ?_⟩
    · rw [hval]
      nlinarith [hphi.2.1]
    · intro hL
      rw [hval, show 1 / 2 - d = Real.sqrt (1 - 2 * d) ^ 2 / 2 by nlinarith]
      exact hphi.2.2

/-- For `21/50 ≤ d ≤ 153/338` there is `L` such that `B` has right derivative
`-L` at `d` (within `[d, ∞)`), `L ≥ 5/6`, `B(d) > 1/2 - d`, and every `ell`
with `L ≤ ell < 1` has head-count ratio
`√(1 - 2d)(1 - ell)/(2(B(d) - ell(1/2 - d))) ≤ 1`. -/
theorem benchmark_dense_head_count_own_multiplier_guards {d : ℝ}
    (hd : d ∈ Set.Icc (21 / 50 : ℝ) (153 / 338)) :
    ∃ L : ℝ, HasDerivWithinAt benchmark (-L) (Set.Ici d) d ∧
      5 / 6 ≤ L ∧ benchmark d > 1 / 2 - d ∧
      ∀ ell : ℝ, L ≤ ell → ell < 1 →
        Real.sqrt (1 - 2 * d) * (1 - ell) /
          (2 * (benchmark d - ell * (1 / 2 - d))) ≤ 1 := by
  obtain ⟨L, hder, hL, hb, hphi⟩ := benchmark_dense_head_count_guards hd
  refine ⟨L, hder, hL, hb, ?_⟩
  intro ell hle hell
  exact headRatio_le_of_slope (Real.sqrt_nonneg _)
    (by linarith [hd.2] : 0 ≤ 1 / 2 - d) hb hle hell (hphi (hle.trans_lt hell))

end Erdos1017.Benchmark

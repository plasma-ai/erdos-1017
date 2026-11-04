module

public import Erdos1017.ContactLocation.BenchmarkSplitCurvature
public import Erdos1017.Benchmark.BenchmarkDenseHeadCountGuards

/-!
# Benchmark comparisons for the dispersed third-cusp exit

On the density interval reached by the dispersed edit, the benchmark lies below
the right tangent of the third cusp, and the negative-density return together
with the edited-value comparison forces the strict body-to-hole ratio.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Benchmark

/-- On the full density interval reached by the dispersed edit, the
benchmark lies below the third cusp's right tangent. -/
theorem cusp_three_right_tangent_bound {d : ℝ}
    (hd : d ∈ Set.Icc (4 / 9 : ℝ) (9 / 20)) :
    benchmark d ≤ 2 / 27 - (5 / 6) * (d - 4 / 9) := by
  have hband : d ∈ Set.Ioo (1 / 2 - epsilonStar) (1 / 2) := by
    constructor <;> linarith only [hd.1, hd.2, two_twenty_fifths_lt_epsilonStar]
  have hs := Real.sq_sqrt (show 0 ≤ 1 - 2 * d by linarith only [hd.2])
  have hs0 := Real.sqrt_nonneg (1 - 2 * d)
  have hcell : Real.sqrt (1 - 2 * d) ∈
      Set.Icc (1 / (((2 : ℕ) : ℝ) + 2)) (1 / (((2 : ℕ) : ℝ) + 1)) := by
    constructor <;> norm_num <;> nlinarith only [hd.1, hd.2, hs, hs0]
  rw [(benchmark_split_eventually hband).eq_of_nhds, splitValue_on_cell 2 hcell]
  norm_num [splitPolynomial]
  nlinarith only [hs, sq_nonneg (3 * Real.sqrt (1 - 2 * d) - 1)]

/-- The original negative-density return and the actual edited-value
comparison force the strict body-to-hole ratio used in the dispersed exit. -/
theorem cusp_three_dispersed_body_ratio {A t z v L YJJ : ℝ}
    (hA : 11 / 39 < A) (ht : 0 < t) (hmass : A + t < 1 / 3)
    (hz : 0 ≤ z) (hreturn : (2 + A / t) * z < v)
    (hd : 4 / 9 + v - z ∈ Set.Icc (4 / 9 : ℝ) (9 / 20))
    (hcharge : YJJ ≤ (8 / 21) * z)
    (hvalue : 2 / 27 - YJJ / 2 - L / 2 ≤ benchmark (4 / 9 + v - z)) :
    (439 / 315) * v < L := by
  have hvt : (2 * t + A) * z < v * t := by
    have hscaled := mul_lt_mul_of_pos_right hreturn ht
    have hid : ((2 + A / t) * z) * t = (2 * t + A) * z := by
      field_simp
    rwa [hid] at hscaled
  have hmass' : 11 * t < 2 * A := by linarith only [hA, hmass]
  have hzv : 15 * z < 2 * v := by
    apply (mul_lt_mul_iff_left₀ ht).mp
    have hpositive := mul_nonneg (sub_pos.mpr hmass').le hz
    nlinarith only [hvt, hpositive]
  have hbenchmark := cusp_three_right_tangent_bound hd
  have hbody : (5 / 3) * v - (43 / 21) * z ≤ L := by
    linarith only [hvalue, hbenchmark, hcharge]
  linarith only [hzv, hbody]

end Erdos1017.Benchmark

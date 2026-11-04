module

public import Erdos1017.Benchmark.BenchmarkDenseHeadCountGuards

/-!
# Benchmark bounds at the fourth-cusp reverse cutoff

Scalar estimates on the benchmark along the reverse-density interval: a common
shifted-half cap (`benchmark_shifted_half_le`), the strict fourth-cusp reverse
cutoff (`benchmark_lt_four_cusp_line`), and the high-slope third-cusp cutoff.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.Benchmark

private theorem mixed_shifted_cap {s : ℝ} (hs : s ∈ Icc (1 : ℝ) (13 / 10)) :
    mixedValue s - mixedDensity s < 1 / 54 := by
  let t := (10 / 3 : ℝ) * (s - 1)
  have ht : 0 ≤ t := by dsimp [t]; linarith [hs.1]
  have hu : 0 ≤ 1 - t := by dsimp [t]; linarith [hs.2]
  have hp : 0 < 4 + 50 * s + 194 * s ^ 2 + 160 * s ^ 3 - 260 * s ^ 4 := by
    have he : 4 + 50 * s + 194 * s ^ 2 + 160 * s ^ 3 - 260 * s ^ 4 =
        1 + 147 * (1 - t) ^ 4 + 4 * (2757 / 20) * t * (1 - t) ^ 3 +
          6 * (11541 / 100) * t ^ 2 * (1 - t) ^ 2 +
          4 * (3687 / 50) * t ^ 3 * (1 - t) + (2397 / 500) * t ^ 4 := by
      dsimp [t]
      ring
    rw [he]
    positivity
  have hd := mixedDenominator_pos (show 0 ≤ s by linarith [hs.1])
  have he : 1 / 54 - (mixedValue s - mixedDensity s) =
      (4 + 50 * s + 194 * s ^ 2 + 160 * s ^ 3 - 260 * s ^ 4) /
        (54 * mixedDenominator s ^ 2) := by
    unfold mixedValue mixedDensity
    field_simp
    unfold mixedDenominator
    ring
  have hpos : 0 < 1 / 54 - (mixedValue s - mixedDensity s) := by
    rw [he]
    exact div_pos hp (mul_pos (by norm_num) (sq_pos_of_pos hd))
  linarith

private theorem twoHead_shifted_cap {z : ℝ} (hz : z ∈ Icc (2 / 3 : ℝ) (4 / 5)) :
    twoHeadValue z - twoHeadDensity z < 1 / 54 := by
  let t := (15 / 2 : ℝ) * (z - 2 / 3)
  have ht : 0 ≤ t := by dsimp [t]; linarith [hz.1]
  have hu : 0 ≤ 1 - t := by dsimp [t]; linarith [hz.2]
  have hp : 0 < 40 - 260 * z + 617 * z ^ 2 - 640 * z ^ 3 + 247 * z ^ 4 := by
    have he : 40 - 260 * z + 617 * z ^ 2 - 640 * z ^ 3 + 247 * z ^ 4 =
        (1 / 100 : ℝ) + (4 / 81 - 1 / 100) * (1 - t) ^ 4 +
          4 * (16 / 135 - 1 / 100) * t * (1 - t) ^ 3 +
          6 * (118 / 675 - 1 / 100) * t ^ 2 * (1 - t) ^ 2 +
          4 * (86 / 375 - 1 / 100) * t ^ 3 * (1 - t) +
          (232 / 625 - 1 / 100) * t ^ 4 := by
      dsimp [t]
      ring
    rw [he]
    positivity
  have hd := twoHeadDenominator_pos hz.1
  have he : 1 / 54 - (twoHeadValue z - twoHeadDensity z) =
      (40 - 260 * z + 617 * z ^ 2 - 640 * z ^ 3 + 247 * z ^ 4) /
        (216 * twoHeadDenominator z ^ 2) := by
    unfold twoHeadValue
    field_simp
    unfold twoHeadDenominator
    ring
  have hpos : 0 < 1 / 54 - (twoHeadValue z - twoHeadDensity z) := by
    rw [he]
    exact div_pos hp (mul_pos (by norm_num) (sq_pos_of_pos hd))
  linarith

private theorem split_shifted_cap {H0 H : ℝ}
    (h0 : H0 ∈ Icc (9 / 64 : ℝ) (25 / 144)) (hH : H ∈ Icc H0 1) :
    splitValue (Real.sqrt H) - H / 2 ≤ Real.sqrt H0 - 4 / 3 * H0 - 1 / 6 := by
  let r0 := Real.sqrt H0
  let r := Real.sqrt H
  have h0pos : 0 ≤ H0 := by linarith [h0.1]
  have hHpos : 0 ≤ H := h0pos.trans hH.1
  have hr0 := Real.sq_sqrt h0pos
  have hr := Real.sq_sqrt hHpos
  have hn0 := Real.sqrt_nonneg H0
  have hn := Real.sqrt_nonneg H
  have hlo : 3 / 8 ≤ r0 := by dsimp [r0]; nlinarith [h0.1]
  have hhi : r0 ≤ 5 / 12 := by dsimp [r0]; nlinarith [h0.2]
  have hrr : r0 ≤ r := Real.sqrt_le_sqrt hH.1
  have hcap : 1 / 54 ≤ r0 - 4 / 3 * H0 - 1 / 6 := by
    have hp := mul_nonneg (sub_nonneg.mpr hhi)
      (show 0 ≤ 4 / 3 * (5 / 12 + r0) - 1 by linarith)
    change r0 ^ 2 = H0 at hr0
    nlinarith
  by_cases hhalf : r ≤ 1 / 2
  · have hcell : r ∈ Icc (1 / (((1 : ℕ) : ℝ) + 2)) (1 / (((1 : ℕ) : ℝ) + 1)) := by
      norm_num only [Nat.cast_one]
      constructor <;> linarith
    change splitValue r - H / 2 ≤ _
    rw [splitValue_on_cell 1 hcell]
    norm_num [splitPolynomial]
    have hp := mul_nonneg (sub_nonneg.mpr hrr)
      (show 0 ≤ 4 / 3 * (r + r0) - 1 by linarith)
    change r ^ 2 = H at hr
    change r0 ^ 2 = H0 at hr0
    change _ ≤ r0 - 4 / 3 * H0 - 1 / 6 + H / 2
    nlinarith
  · have hcell : r ∈ Icc (1 / (((0 : ℕ) : ℝ) + 2)) (1 / (((0 : ℕ) : ℝ) + 1)) := by
      norm_num only [Nat.cast_zero, zero_add, div_one]
      constructor
      · linarith
      · dsimp [r]
        exact (Real.sqrt_le_one).mpr hH.2
    change splitValue r - H / 2 ≤ _
    rw [splitValue_on_cell 0 hcell]
    norm_num [splitPolynomial]
    change r ^ 2 = H at hr
    change _ ≤ r0 - 4 / 3 * H0 - 1 / 6 + H / 2
    nlinarith [sq_nonneg (r - 1 / 2)]

/-- The actual benchmark has a common shifted-half cap on the original
reverse-density interval. Both stationary families are bounded directly;
the split pieces retain their exact cells and all branch endpoints. -/
theorem benchmark_shifted_half_le {H0 H : ℝ}
    (h0 : H0 ∈ Icc (9 / 64 : ℝ) (25 / 144)) (hH : H ∈ Icc H0 1) :
    benchmark ((1 - H) / 2) - H / 2 ≤ Real.sqrt H0 - 4 / 3 * H0 - 1 / 6 := by
  have h0pos : 0 ≤ H0 := by linarith [h0.1]
  have hHpos : 0 < H := by linarith [h0.1, hH.1]
  have hsq := Real.sq_sqrt h0pos
  have hn := Real.sqrt_nonneg H0
  have hlo : 3 / 8 ≤ Real.sqrt H0 := by nlinarith [h0.1]
  have hhi : Real.sqrt H0 ≤ 5 / 12 := by nlinarith [h0.2]
  have hcap : 1 / 54 ≤ Real.sqrt H0 - 4 / 3 * H0 - 1 / 6 := by
    have hp := mul_nonneg (sub_nonneg.mpr hhi)
      (show 0 ≤ 4 / 3 * (5 / 12 + Real.sqrt H0) - 1 by linarith)
    nlinarith
  by_cases hquarter : (1 - H) / 2 ≤ 1 / 4
  · rw [benchmark_of_le_quarter hquarter]
    linarith
  · have hdhalf : (1 - H) / 2 < 1 / 2 := by linarith
    have he : H / 2 ∈ Ioo (0 : ℝ) (1 / 4) := by constructor <;> linarith
    have hsplit := split_shifted_cap h0 hH
    have hrad : Real.sqrt (2 * (H / 2)) = Real.sqrt H := by congr 1; ring
    have hm : mixedCurve (H / 2) - H / 2 ≤ Real.sqrt H0 - 4 / 3 * H0 - 1 / 6 := by
      unfold mixedCurve
      split_ifs with hS hD
      · simpa only [hrad] using hsplit
      · obtain ⟨hs, heq⟩ := mixedInverse_spec ⟨le_of_not_ge hS, hD⟩
        have hsHi : sigmaZero < 13 / 10 := by
          have hq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
          have hn := Real.sqrt_nonneg (21 : ℝ)
          unfold sigmaZero
          nlinarith
        have hbound := mixed_shifted_cap
          ⟨sigmaD_spec.1.1.trans hs.1, hs.2.trans hsHi.le⟩
        rw [heq] at hbound
        exact hbound.le.trans hcap
      · linarith
    have ht : twoHeadCurve (H / 2) - H / 2 ≤ Real.sqrt H0 - 4 / 3 * H0 - 1 / 6 := by
      unfold twoHeadCurve
      rw [ite_eq_right (ne_of_gt he.1)]
      split_ifs with hC
      · simpa only [hrad] using hsplit
      · obtain ⟨hz, heq⟩ := twoHeadInverse_spec ⟨(lt_of_not_ge hC).le, he.2.le⟩
        have hbound := twoHead_shifted_cap ⟨hz.1, hz.2.trans zC_spec.1.2⟩
        rw [heq] at hbound
        exact hbound.le.trans hcap
    simp only [benchmark, hquarter, ite_false, hdhalf, ite_true,
      show 1 / 2 - (1 - H) / 2 = H / 2 by ring]
    rcases le_total (mixedCurve (H / 2)) (twoHeadCurve (H / 2)) with h | h
    · rw [max_eq_right h]
      exact ht
    · rw [max_eq_left h]
      exact hm

/-- The fourth-cusp reverse cutoff is strict; its endpoint square gap is nine. -/
theorem benchmark_lt_four_cusp_line {H : ℝ} (hH : H ∈ Icc (5 / 32 : ℝ) 1) :
    benchmark ((1 - H) / 2) < 3 / 64 + 11 / 20 * (H - 1 / 16) := by
  have hb := benchmark_shifted_half_le (H0 := 5 / 32) (by norm_num) hH
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 32)
  have hn := Real.sqrt_nonneg (5 / 32 : ℝ)
  have hroot : Real.sqrt (5 / 32 : ℝ) < 253 / 640 := by nlinarith
  nlinarith [hH.1]

/-- The same benchmark estimate supplies the high-slope third-cusp cutoff. -/
theorem benchmark_shifted_half_le_one_fifty_fourth {H : ℝ}
    (hH : H ∈ Icc (25 / 144 : ℝ) 1) :
    benchmark ((1 - H) / 2) - H / 2 ≤ 1 / 54 := by
  have hb := benchmark_shifted_half_le (H0 := 25 / 144) (by norm_num) hH
  have hs : Real.sqrt (25 / 144 : ℝ) = 5 / 12 := by
    rw [show (25 / 144 : ℝ) = (5 / 12 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hs] at hb
  norm_num at hb ⊢
  exact hb

end Erdos1017.Benchmark

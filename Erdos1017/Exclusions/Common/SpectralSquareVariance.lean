module

public import Erdos1017.SelectedModel.Flows.ForwardPeakSeparation

/-!
# Variance bound for a square-summable spectrum

A square-summable signed spectrum has nonnegative upper and lower extremes after
adjoining zero, both extremes pay their squares in the same spectral square sum,
its cube and fourth moments are summable, and the square-weighted spectral
variance is at most half the square energy.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical

namespace Erdos1017.SpectralSquareVariance

/-- A square-summable signed spectrum has an actual nonnegative upper
extreme after adjoining zero. -/
theorem exists_upper_extreme {ι : Type*} (t : ι → ℝ) (hsq : Summable (fun i => (t i) ^ 2)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ i, t i ≤ M) ∧ (M = 0 ∨ ∃ i, t i = M) := by
  by_cases hp : ∃ i, 0 < t i
  · have hs : Summable (fun i => (max (t i) 0) ^ 2) :=
      hsq.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => by
        by_cases hi : 0 ≤ t i
        · rw [max_eq_left hi]
        · rw [max_eq_right (le_of_not_ge hi)]
          simpa only [zero_pow (by norm_num : 2 ≠ 0)] using sq_nonneg (t i))
    have hpositive : ∃ i, 0 < (max (t i) 0) ^ 2 := by
      obtain ⟨i, hi⟩ := hp
      exact ⟨i, by rw [max_eq_left hi.le]; exact sq_pos_of_pos hi⟩
    obtain ⟨j, hj, hmax⟩ := ForwardPeak.exists_positive_max_of_summable _ hs hpositive
    have hjpos : 0 < t j := by
      by_contra hn
      rw [max_eq_right (le_of_not_gt hn)] at hj
      norm_num at hj
    refine ⟨t j, hjpos.le, ?_, Or.inr ⟨j, rfl⟩⟩
    intro i
    by_cases hi : 0 ≤ t i
    · have hb := hmax i
      rw [max_eq_left hi, max_eq_left hjpos.le] at hb
      nlinarith
    · exact (le_of_not_ge hi).trans hjpos.le
  · refine ⟨0, le_rfl, ?_, Or.inl rfl⟩
    intro i
    exact le_of_not_gt (fun hi => hp ⟨i, hi⟩)

/-- Both actual signed extremes pay their squares in the same spectral
square sum, including spectra with only one sign or with no coordinates. -/
theorem exists_range_square_bound {ι : Type*} (t : ι → ℝ)
    (hsq : Summable (fun i => (t i) ^ 2)) :
    ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ (∀ i, t i ∈ Set.Icc a b) ∧
      a ^ 2 + b ^ 2 ≤ ∑' i, (t i) ^ 2 := by
  obtain ⟨b, hb, hupper, hbvalue⟩ := exists_upper_extreme t hsq
  have hneg : Summable (fun i => (-t i) ^ 2) := by simpa only [neg_sq] using hsq
  obtain ⟨c, hc, hlower, hcvalue⟩ := exists_upper_extreme (fun i => -t i) hneg
  refine ⟨-c, b, by linarith, hb, fun i => ⟨by linarith [hlower i], hupper i⟩, ?_⟩
  have hsum0 : 0 ≤ ∑' i, (t i) ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
  rcases hbvalue with hbzero | ⟨i, hi⟩ <;> rcases hcvalue with hczero | ⟨j, hj⟩
  · simp only [hbzero, hczero, neg_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    exact hsum0
  · have hsingle := hsq.le_tsum j (fun _ _ => sq_nonneg _)
    rw [hbzero]
    nlinarith
  · have hsingle := hsq.le_tsum i (fun _ _ => sq_nonneg _)
    rw [hczero]
    nlinarith
  · by_cases hij : i = j
    · subst j
      nlinarith
    · have hpair := hsq.sum_le_tsum {i, j} (fun _ _ => sq_nonneg _)
      rw [Finset.sum_pair hij] at hpair
      nlinarith

/-- Square summability and a bounded signed range pay both higher moments
needed by the Hilbert-Schmidt variance calculation. -/
theorem summable_cube_fourth {ι : Type*} (t : ι → ℝ)
    (hsq : Summable (fun i => (t i) ^ 2)) (C : ℝ)
    (hbound : ∀ i, |t i| ≤ C) :
    Summable (fun i => (t i) ^ 3) ∧ Summable (fun i => (t i) ^ 4) := by
  constructor
  · apply (hsq.mul_left C).of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_pow]
    calc
      |t i| ^ 3 = (t i) ^ 2 * |t i| := by rw [← sq_abs]; ring
      _ ≤ (t i) ^ 2 * C := mul_le_mul_of_nonneg_left (hbound i) (sq_nonneg _)
      _ = C * (t i) ^ 2 := mul_comm _ _
  · apply (hsq.mul_left (C ^ 2)).of_norm_bounded
    intro i
    have hs : (t i) ^ 2 ≤ C ^ 2 := by nlinarith [abs_le.mp (hbound i)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (t i) ^ 4)]
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (t i))]

/-- The square-weighted spectral variance is at most half the original
square energy. Both extremes and all signed sums are constructed. -/
theorem weighted_variance_le_half_square {ι : Type*} (t : ι → ℝ)
    (hsq : Summable (fun i => (t i) ^ 2)) (hZ : 0 < ∑' i, (t i) ^ 2) :
    (∑' i, (t i) ^ 4) - (∑' i, (t i) ^ 3) ^ 2 / (∑' i, (t i) ^ 2) ≤
      (∑' i, (t i) ^ 2) ^ 2 / 2 := by
  obtain ⟨a, b, ha, hb, hrange, hsqrange⟩ := exists_range_square_bound t hsq
  let C := max |a| |b|
  have hbound : ∀ i, |t i| ≤ C := fun i => abs_le_max_abs_abs (hrange i).1 (hrange i).2
  obtain ⟨h₃, h₄⟩ := summable_cube_fourth t hsq C hbound
  have hpoint (i : ι) : (t i) ^ 4 - (a + b) * (t i) ^ 3 + a * b * (t i) ^ 2 ≤ 0 := by
    have hprod := mul_nonneg (sub_nonneg.mpr (hrange i).1) (sub_nonneg.mpr (hrange i).2)
    nlinarith [mul_nonneg (sq_nonneg (t i)) hprod]
  have hs := Summable.tsum_le_tsum hpoint
    ((h₄.sub (h₃.mul_left (a + b))).add (hsq.mul_left (a * b))) summable_zero
  rw [tsum_zero, (h₄.sub (h₃.mul_left (a + b))).tsum_add (hsq.mul_left (a * b)),
    h₄.tsum_sub (h₃.mul_left (a + b)), tsum_mul_left, tsum_mul_left] at hs
  have hspread : (b - a) ^ 2 ≤ 2 * (∑' i, (t i) ^ 2) := by nlinarith [sq_nonneg (a + b)]
  apply (mul_le_mul_iff_left₀ hZ).mp
  have hweighted := mul_nonneg (sub_nonneg.mpr hspread) (sq_nonneg (∑' i, (t i) ^ 2))
  have hpop := sq_nonneg (2 * (∑' i, (t i) ^ 3) - (a + b) * (∑' i, (t i) ^ 2))
  have hsum := mul_nonpos_of_nonpos_of_nonneg hs hZ.le
  have hdiv := div_mul_cancel₀ ((∑' i, (t i) ^ 3) ^ 2) hZ.ne'
  nlinarith only [hweighted, hpop, hsum, hdiv]

end Erdos1017.SpectralSquareVariance

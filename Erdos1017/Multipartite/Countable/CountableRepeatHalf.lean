module

public import Erdos1017.Multipartite.Countable.CountableRepeatPenalty

/-!
# Two-copy tests above one half

Above the one-half threshold, no repeat count of three or more forces a larger
repeat penalty than the two-copy tests, and a full repeat penalty strictly above
one half is already forced by two copies.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

/-- Above the universal one-half threshold, no count of three or more can
force a larger repeat penalty than the actual two-copy tests. -/
theorem repeatPenalty_le_max_twoRepeat_half {D : Coefficients} (hD : D ∈ feasible) {i : ℕ}
    (hi : head D i < 1) : repeatPenalty D i ≤ max (twoRepeatPenalty D i) (1 / 2) := by
  let K := max (twoRepeatPenalty D i) (1 / 2)
  have hKhalf : (1 / 2 : ℝ) ≤ K := le_max_right _ _
  have hKtwo : twoRepeatPenalty D i ≤ K := le_max_left _ _
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hKhalf
  apply repeatPenalty_le_of_tests D i K hK
  intro S r
  have htwo : 2 * S.row D + S.charge D - K ≤ 1 := by
    have h := twoRepeatPenalty_test hD S
    linarith
  by_cases hr : r ≤ 2
  · have hsmall : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hsmall with rfl | rfl | rfl
    · simpa using S.zero_test hD
    · simpa using S.one_test hD
    · norm_num
      linarith
  · have hr' : (3 : ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
    have hrow : S.row D < 1 := (S.row_le_head hD).trans_lt hi
    have hprod := mul_nonneg hK (show 0 ≤ (r : ℝ) - 3 by linarith)
    have hnegative : S.row D - K * ((r : ℝ) + 1) / 2 ≤ 0 := by nlinarith
    have hinc := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (r : ℝ) - 2 by linarith) hnegative
    nlinarith

/-- A full repeat penalty strictly above one half is already forced by two
copies, without assuming that fact about the two-copy supremum in advance. -/
theorem repeatPenalty_eq_two_of_half_lt_repeat {D : Coefficients} (hD : D ∈ feasible) {i : ℕ}
    (hi : head D i < 1) (hhalf : 1 / 2 < repeatPenalty D i) :
    repeatPenalty D i = twoRepeatPenalty D i := by
  have hmax := repeatPenalty_le_max_twoRepeat_half hD hi
  have htwo : 1 / 2 < twoRepeatPenalty D i := by
    by_contra h
    rw [max_eq_right (le_of_not_gt h)] at hmax
    linarith
  exact repeatPenalty_eq_twoRepeatPenalty hD hi htwo

end Erdos1017.MultipartiteCountableDual

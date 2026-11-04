module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Tight counts of the seven-coefficient count polynomial

Two distinct tight natural counts must be adjacent, three cannot all be tight,
adjacent tight counts determine the slope, and an integral nonnegative slope
ratio gives exactly two adjacent maximizers.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TightCounts

/-- The count polynomial in each Boolean state of the seven-coefficient problem. -/
def value (C s p : ℝ) (n : ℕ) : ℝ :=
  C + (n : ℝ) * s - p * (n : ℝ) * ((n : ℝ) - 1) / 2

/-- Adjacent tight counts determine the slope exactly. -/
theorem slope_of_adjacent_tight (C s p : ℝ) (k : ℕ)
    (hk : value C s p k = 1) (hk₁ : value C s p (k + 1) = 1) :
    s = p * (k : ℝ) := by
  simp only [value, Nat.cast_add, Nat.cast_one] at hk hk₁
  nlinarith

/-- Feasibility at the next count bounds the slope at a tight count. -/
theorem slope_le_of_tight (C s p : ℝ) (k : ℕ)
    (h : ∀ n, value C s p n ≤ 1) (hk : value C s p k = 1) :
    s ≤ p * (k : ℝ) := by
  have hk₁ := h (k + 1)
  simp only [value, Nat.cast_add, Nat.cast_one] at hk hk₁
  nlinarith

/-- Two distinct tight natural counts must be adjacent. -/
theorem tight_counts_adjacent (C s p : ℝ) (hp : 0 < p)
    (h : ∀ n, value C s p n ≤ 1) (m n : ℕ)
    (hmn : m < n) (hm : value C s p m = 1) (hn : value C s p n = 1) :
    n = m + 1 := by
  have hs := slope_le_of_tight C s p m h hm
  by_contra hne
  have hgap : m + 2 ≤ n := by omega
  have hgap' : (m : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hgap
  have hprod := mul_nonneg (show 0 ≤ (n : ℝ) - (m : ℝ) by linarith)
    (sub_nonneg.mpr hs)
  have hpos := mul_pos hp
    (show 0 < ((n : ℝ) - (m : ℝ)) * ((n : ℝ) - (m : ℝ) - 1) by
      apply mul_pos <;> linarith)
  simp only [value] at hm hn
  nlinarith

/-- Three ordered distinct counts cannot all be tight. -/
theorem no_three_tight (C s p : ℝ) (hp : 0 < p)
    (h : ∀ n, value C s p n ≤ 1) (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    ¬ (value C s p a = 1 ∧ value C s p b = 1 ∧ value C s p c = 1) := by
  rintro ⟨ha, hb, hc⟩
  have hab' := tight_counts_adjacent C s p hp h a b hab ha hb
  have hac' := tight_counts_adjacent C s p hp h a c (hab.trans hbc) ha hc
  omega

/-- The product of consecutive integer differences is nonnegative. -/
theorem gap_nonneg (k n : ℕ) :
    0 ≤ ((n : ℝ) - (k : ℝ)) * ((n : ℝ) - (k : ℝ) - 1) := by
  rcases le_or_gt n k with h | h
  · have h' : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
  · have h' : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    apply mul_nonneg <;> linarith

/-- An integral nonnegative slope ratio gives two adjacent global maximizers. -/
theorem integer_slope_maximizers (C s p : ℝ) (hp : 0 < p) (k : ℕ)
    (hs : s = p * (k : ℝ)) :
    value C s p (k + 1) = value C s p k ∧
      ∀ n, value C s p n ≤ value C s p k := by
  constructor
  · simp only [value, hs, Nat.cast_add, Nat.cast_one]
    ring
  · intro n
    have hprod := mul_nonneg hp.le (gap_nonneg k n)
    simp only [value, hs]
    nlinarith

/-- The two adjacent counts are the only maximizers when the penalty is positive. -/
theorem integer_slope_maximum_iff (C s p : ℝ) (hp : 0 < p) (k n : ℕ)
    (hs : s = p * (k : ℝ)) :
    value C s p n = value C s p k ↔ n = k ∨ n = k + 1 := by
  constructor
  · intro h
    have hgap : ((n : ℝ) - (k : ℝ)) * ((n : ℝ) - (k : ℝ) - 1) = 0 := by
      have hzero : p * (((n : ℝ) - (k : ℝ)) * ((n : ℝ) - (k : ℝ) - 1)) = 0 := by
        simp only [value, hs] at h
        nlinarith
      exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hp)
    rcases mul_eq_zero.mp hgap with h | h
    · left
      exact_mod_cast (sub_eq_zero.mp h)
    · right
      have h' : (n : ℝ) = (k : ℝ) + 1 := by linarith
      exact_mod_cast h'
  · rintro (rfl | rfl)
    · rfl
    · exact (integer_slope_maximizers C s p hp k hs).1

/-- The slope-ratio formulation used in the tight-count classification. -/
theorem maximizers_of_integer_ratio (C s p : ℝ) (hp : 0 < p) (k : ℕ)
    (hs : s / p = (k : ℝ)) :
    value C s p (k + 1) = value C s p k ∧
      ∀ n, value C s p n ≤ value C s p k := by
  apply integer_slope_maximizers C s p hp k
  have h := (div_eq_iff (ne_of_gt hp)).mp hs
  nlinarith

/-- If an integral-slope feasible state is tight anywhere, both maximizers are tight. -/
theorem adjacent_tight_of_integer_slope (C s p : ℝ) (hp : 0 < p) (k : ℕ)
    (hs : s = p * (k : ℝ)) (h : ∀ n, value C s p n ≤ 1)
    (htight : ∃ n, value C s p n = 1) :
    value C s p k = 1 ∧ value C s p (k + 1) = 1 := by
  obtain ⟨heq, hmax⟩ := integer_slope_maximizers C s p hp k hs
  obtain ⟨n, hn⟩ := htight
  have hk : value C s p k = 1 := le_antisymm (h k) (hn ▸ hmax n)
  exact ⟨hk, heq.trans hk⟩

end Erdos1017.TightCounts

module

public import Erdos1017.Multipartite.Selector.VertexClassification
public import Erdos1017.Multipartite.ZeroPattern

/-!
# Coefficients extracted from tight states

Adjacent-tight and double-tight states determine the constant term, the six
coefficients, the cross penalty and the parallelogram relation among the four
slope indices.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.PatternExtraction

open VertexClassification Repeat

/-- The height of an adjacent-tight quadratic determines its constant term. -/
theorem constant_of_adjacent_tight (C s p : ℝ) (k : ℕ)
    (hk : TightCounts.value C s p k = 1)
    (hk₁ : TightCounts.value C s p (k + 1) = 1) :
    C = 1 - p * (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  have hs := TightCounts.slope_of_adjacent_tight C s p k hk hk₁
  unfold TightCounts.value at hk
  nlinarith

/-- Extract all six coefficients determined by the first three double-tight states.
This theorem does not assume that a vertex has these tight states. -/
theorem three_double_tight_coefficients (x : Coefficients) (j k l : ℕ)
    (hp : 0 < x 6) (hc₁ : 0 < x 4) (hc₂ : 0 < x 5)
    (h00 : test ((false, false), j) x = 1 ∧
      test ((false, false), j + 1) x = 1)
    (h10 : test ((true, false), k) x = 1 ∧
      test ((true, false), k + 1) x = 1)
    (h01 : test ((false, true), l) x = 1 ∧
      test ((false, true), l + 1) x = 1) :
    0 < j ∧ k < j ∧ l < j ∧
      x 6 = 2 / denominator j ∧
      x 2 = 2 * (j : ℝ) / denominator j ∧
      x 0 = zeroStar j k ∧ x 1 = zeroStar j l ∧
      x 4 = 2 * ((j - k : ℕ) : ℝ) / denominator j ∧
      x 5 = 2 * ((j - l : ℕ) : ℝ) / denominator j := by
  simp [test_eq_value, constant, slope] at h00 h10 h01
  have hs00 := TightCounts.slope_of_adjacent_tight _ _ _ _ h00.1 h00.2
  have hs10 := TightCounts.slope_of_adjacent_tight _ _ _ _ h10.1 h10.2
  have hs01 := TightCounts.slope_of_adjacent_tight _ _ _ _ h01.1 h01.2
  have hC00 := constant_of_adjacent_tight _ _ _ _ h00.1 h00.2
  have hC10 := constant_of_adjacent_tight _ _ _ _ h10.1 h10.2
  have hC01 := constant_of_adjacent_tight _ _ _ _ h01.1 h01.2
  have hj : 0 < j := by
    by_contra hj
    have hj₀ : j = 0 := by omega
    subst j
    norm_num at hC00
  have hkj : (k : ℝ) < (j : ℝ) := by nlinarith
  have hlj : (l : ℝ) < (j : ℝ) := by nlinarith
  have hk : k < j := by exact_mod_cast hkj
  have hl : l < j := by exact_mod_cast hlj
  have hJ := denominator_pos j hj
  have hp' : x 6 = 2 / denominator j := by
    apply (eq_div_iff (ne_of_gt hJ)).2
    unfold denominator
    nlinarith
  have hv : x 2 = 2 * (j : ℝ) / denominator j := by rw [hs00, hp']; ring
  have ht₁ : x 0 = zeroStar j k := by rw [hC10, hp']; unfold zeroStar; ring
  have ht₂ : x 1 = zeroStar j l := by rw [hC01, hp']; unfold zeroStar; ring
  have hc₁' : x 4 = 2 * ((j - k : ℕ) : ℝ) / denominator j := by
    rw [Nat.cast_sub hk.le]
    rw [hp', hv] at hs10
    ring_nf at hs10 ⊢
    linarith
  have hc₂' : x 5 = 2 * ((j - l : ℕ) : ℝ) / denominator j := by
    rw [Nat.cast_sub hl.le]
    rw [hp', hv] at hs01
    ring_nf at hs01 ⊢
    linarith
  exact ⟨hj, hk, hl, hp', hv, ht₁, ht₂, hc₁', hc₂'⟩

/-- A zero-count tight state 11 supplies the cross coefficient of the zero pattern. -/
theorem zero_tight_cross (x : Coefficients) (j k l : ℕ)
    (ht₁ : x 0 = zeroStar j k) (ht₂ : x 1 = zeroStar j l)
    (h11 : test ((true, true), 0) x = 1) : x 3 = zeroCross j k l := by
  simp [test_eq_value, TightCounts.value, constant] at h11
  unfold zeroCross
  rw [← ht₁, ← ht₂]
  linarith

/-- The four adjacent-tight slope indices satisfy the parallelogram relation. -/
theorem four_slope_indices (x : Coefficients) (j k l m : ℕ) (hp : 0 < x 6)
    (h00 : test ((false, false), j) x = 1 ∧ test ((false, false), j + 1) x = 1)
    (h10 : test ((true, false), k) x = 1 ∧ test ((true, false), k + 1) x = 1)
    (h01 : test ((false, true), l) x = 1 ∧ test ((false, true), l + 1) x = 1)
    (h11 : test ((true, true), m) x = 1 ∧ test ((true, true), m + 1) x = 1) :
    j + m = k + l := by
  simp [test_eq_value, constant, slope] at h00 h10 h01 h11
  have hs00 := TightCounts.slope_of_adjacent_tight _ _ _ _ h00.1 h00.2
  have hs10 := TightCounts.slope_of_adjacent_tight _ _ _ _ h10.1 h10.2
  have hs01 := TightCounts.slope_of_adjacent_tight _ _ _ _ h01.1 h01.2
  have hs11 := TightCounts.slope_of_adjacent_tight _ _ _ _ h11.1 h11.2
  have hmul : x 6 * ((j : ℝ) + (m : ℝ) - (k : ℝ) - (l : ℝ)) = 0 := by
    nlinarith
  have heq := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
  have heq' : (j : ℝ) + (m : ℝ) = (k : ℝ) + (l : ℝ) := by linarith
  exact_mod_cast heq'

/-- A negative fourth slope is precisely the strict index inequality of the zero pattern. -/
theorem negative_fourth_index (x : Coefficients) (j k l : ℕ) (hp : 0 < x 6)
    (h00 : test ((false, false), j) x = 1 ∧ test ((false, false), j + 1) x = 1)
    (h10 : test ((true, false), k) x = 1 ∧ test ((true, false), k + 1) x = 1)
    (h01 : test ((false, true), l) x = 1 ∧ test ((false, true), l + 1) x = 1)
    (hneg : slope (true, true) x < 0) : k + l < j := by
  simp [test_eq_value, constant, slope] at h00 h10 h01
  simp [slope] at hneg
  have hs00 := TightCounts.slope_of_adjacent_tight _ _ _ _ h00.1 h00.2
  have hs10 := TightCounts.slope_of_adjacent_tight _ _ _ _ h10.1 h10.2
  have hs01 := TightCounts.slope_of_adjacent_tight _ _ _ _ h01.1 h01.2
  have h : (k : ℝ) + (l : ℝ) < (j : ℝ) := by nlinarith
  exact_mod_cast h

/-- The fourth double-tight state determines the product cross penalty. -/
theorem double_tight_cross (x : Coefficients) (j k l m : ℕ)
    (hj : 0 < j) (hk : k ≤ j) (hl : l ≤ j) (hm : j + m = k + l)
    (hp : x 6 = 2 / denominator j)
    (ht₁ : x 0 = zeroStar j k) (ht₂ : x 1 = zeroStar j l)
    (h11 : test ((true, true), m) x = 1 ∧ test ((true, true), m + 1) x = 1) :
    x 3 = crossPenalty j (j - k) (j - l) := by
  simp [test_eq_value, constant, slope] at h11
  have hC := constant_of_adjacent_tight _ _ _ _ h11.1 h11.2
  have hm' : (m : ℝ) = (k : ℝ) + (l : ℝ) - (j : ℝ) := by
    have h : (j : ℝ) + (m : ℝ) = (k : ℝ) + (l : ℝ) := by exact_mod_cast hm
    linarith
  rw [ht₁, ht₂, hp, hm'] at hC
  unfold zeroStar at hC
  have hJ : denominator j ≠ 0 := ne_of_gt (denominator_pos j hj)
  field_simp at hC
  unfold crossPenalty
  rw [Nat.cast_sub hk, Nat.cast_sub hl]
  apply (eq_div_iff hJ).2
  unfold denominator at hC ⊢
  nlinarith

end Erdos1017.PatternExtraction

module

public import Erdos1017.ContactLocation.BenchmarkSplitCellClassification

/-!
# Reciprocal affine cap of the split curve

The split curve lies below its capped reciprocal affine bound on the whole
interval, including zero and every smaller cusp.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.Benchmark

private theorem polynomial_cap (k j : ℕ) (hk : 4 ≤ k) (hjk : k ≤ j) {x : ℝ}
    (hx : x ∈ Icc (1 / ((j : ℝ) + 1)) (1 / (j : ℝ))) :
    2 * splitPolynomial j x - (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) * x ^ 2 ≤
      2 * (((k : ℝ) - 1) / (k : ℝ) ^ 3) -
        (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) / (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hj0 : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
  have hjk' : (k : ℝ) ≤ j := by exact_mod_cast hjk
  let L := 2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)
  let a := 1 / (k : ℝ)
  let y := 1 / (j : ℝ)
  let B := 2 * (2 * (j : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) + L
  have hL : 0 ≤ L := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have h₁ := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hk1
    have h₂ := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ (k : ℝ) + 1)
    dsimp [L]
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have h₃ := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hk4
    simp only [div_eq_mul_inv, one_mul] at h₂ h₃ ⊢
    linarith
  have hLj : L ≤ 2 - 2 / (j : ℝ) - 2 / ((j : ℝ) + 1) := by
    have h₁ := one_div_le_one_div_of_le hk0 hjk'
    have h₂ := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (k : ℝ) + 1)
      (by linarith : (k : ℝ) + 1 ≤ (j : ℝ) + 1)
    dsimp [L]
    simp only [div_eq_mul_inv, one_mul] at h₁ h₂ ⊢
    linarith
  have hy : 0 ≤ y := by positivity
  have hya : y ≤ a := one_div_le_one_div_of_le hk0 hjk'
  have hxa : x ≤ y := hx.2
  have hB : 0 ≤ B := add_nonneg (by positivity) hL
  have hbracket : 0 ≤ 4 / (j : ℝ) - B * (x + y) := by
    have he : 4 / (j : ℝ) - 2 * B * y =
        2 / (j : ℝ) * (2 - 2 / (j : ℝ) - 2 / ((j : ℝ) + 1) - L) := by
      dsimp [B, y]
      field_simp
      ring
    have hp := mul_nonneg (show 0 ≤ 2 / (j : ℝ) by positivity) (sub_nonneg.mpr hLj)
    rw [← he] at hp
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hxa)]
  have hcell : 2 * splitPolynomial j x - L * x ^ 2 ≤
      2 * splitPolynomial j y - L * y ^ 2 := by
    have he : (2 * splitPolynomial j y - L * y ^ 2) -
        (2 * splitPolynomial j x - L * x ^ 2) = (y - x) * (4 / (j : ℝ) - B * (x + y)) := by
      dsimp [splitPolynomial, B]
      field_simp
      ring
    rw [← sub_nonneg, he]
    exact mul_nonneg (sub_nonneg.mpr hxa) hbracket
  have hLa : 0 ≤ 2 - L - 3 * a := by
    have he : 2 - L - 3 * a = ((k : ℝ) - 1) / ((k : ℝ) * ((k : ℝ) + 1)) := by
      dsimp [L, a]
      field_simp
      ring
    rw [he]
    apply div_nonneg _ (by positivity)
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hrecip : (2 - L) * y ^ 2 - 2 * y ^ 3 ≤ (2 - L) * a ^ 2 - 2 * a ^ 3 := by
    have hp : 0 ≤ (2 - L) * (a + y) - 2 * (a ^ 2 + a * y + y ^ 2) := by
      have h₁ := mul_nonneg hLa (show 0 ≤ a + y by positivity)
      have h₂ := mul_nonneg (sub_nonneg.mpr hya) (show 0 ≤ a + 2 * y by positivity)
      nlinarith
    have hmul := mul_nonneg (sub_nonneg.mpr hya) hp
    nlinarith
  have hjvalue : 2 * splitPolynomial j y - L * y ^ 2 = (2 - L) * y ^ 2 - 2 * y ^ 3 := by
    dsimp [splitPolynomial, y]
    field_simp
    ring
  have hkvalue : (2 - L) * a ^ 2 - 2 * a ^ 3 =
      2 * (((k : ℝ) - 1) / (k : ℝ) ^ 3) - L / (k : ℝ) ^ 2 := by
    dsimp [a]
    field_simp
    ring
  rw [hjvalue] at hcell
  exact hcell.trans (hrecip.trans_eq hkvalue)

/-- The actual split curve lies below its capped reciprocal affine
bound on the entire interval, including zero and every smaller cusp. -/
theorem splitValue_le_cusp_cap (k : ℕ) (hk : 4 ≤ k) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / (k : ℝ))) :
    splitValue x ≤ ((k : ℝ) - 1) / (k : ℝ) ^ 3 +
      (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) * (x ^ 2 - 1 / (k : ℝ) ^ 2) / 2 := by
  have hk0 : (0 : ℝ) < k := by positivity
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · have he : ((k : ℝ) - 1) / (k : ℝ) ^ 3 +
        (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) * ((0 : ℝ) ^ 2 - 1 / (k : ℝ) ^ 2) / 2 =
        1 / ((k : ℝ) ^ 2 * ((k : ℝ) + 1)) := by field_simp; ring
    rw [he]
    simpa [splitValue] using (show (0 : ℝ) ≤ 1 / ((k : ℝ) ^ 2 * ((k : ℝ) + 1)) by positivity)
  let j := ⌊1 / x⌋₊
  have hkj : k ≤ j := Nat.le_floor ((le_div_iff₀ hx0).mpr
    (by simpa only [mul_comm] using (le_div_iff₀ hk0).mp hx.2))
  have hj0 : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
  have hcell : x ∈ Icc (1 / ((j : ℝ) + 1)) (1 / (j : ℝ)) := by
    constructor
    · apply le_of_lt
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
      have h := (div_lt_iff₀ hx0).mp (Nat.lt_floor_add_one (1 / x))
      nlinarith
    · apply (le_div_iff₀ hj0).mpr
      have h := (le_div_iff₀ hx0).mp (Nat.floor_le (one_div_nonneg.mpr hx0.le))
      nlinarith
  have hvalue : splitValue x = splitPolynomial j x := by
    have hj1 : 1 ≤ j := by omega
    have hcell' : x ∈ Icc (1 / (((j - 1 : ℕ) : ℝ) + 2)) (1 / (((j - 1 : ℕ) : ℝ) + 1)) := by
      rw [Nat.cast_sub hj1, Nat.cast_one]
      simpa only [sub_add_cancel, show (j : ℝ) - 1 + 2 = (j : ℝ) + 1 by ring] using hcell
    simpa only [Nat.sub_add_cancel hj1] using splitValue_on_cell (j - 1) hcell'
  rw [hvalue]
  have h := polynomial_cap k j hk hkj hcell
  linear_combination h / 2

end Erdos1017.Benchmark

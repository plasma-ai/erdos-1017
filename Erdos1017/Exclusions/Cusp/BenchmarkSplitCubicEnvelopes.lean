module

public import Erdos1017.Benchmark.SplitCurve

/-!
# Cubic envelopes of the split curve

The split curve satisfies `splitValue r ≤ r² (1 - c r)` with `c = 7/8` on
`[0, 1]`, `c = 15/16` on `[0, 1/3]` and `c = 19/20` on `[0, 1/4]`.
-/

@[expose] public section

namespace Erdos1017.Benchmark

private theorem splitPolynomial_le_cell_cubic (j : ℕ) (hj : 1 ≤ j) {r : ℝ}
    (hr : r ∈ Set.Icc (1 / ((j : ℝ) + 1)) (1 / (j : ℝ))) :
    splitPolynomial j r ≤ r ^ 2 - r ^ 3 + r ^ 3 / (4 * ((j : ℝ) + 1)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hr1 : r ≤ 1 := hr.2.trans (by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hj1)
  have hlow : 0 ≤ ((j : ℝ) + 1) * r - 1 := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mp hr.1
    nlinarith
  have hid : 4 * (j : ℝ) * ((j : ℝ) + 1) *
      (r ^ 2 - r ^ 3 + r ^ 3 / (4 * ((j : ℝ) + 1)) - splitPolynomial j r) =
        r ^ 2 * (((j : ℝ) + 1) * r - 1) +
          (1 - r) * ((2 * (j : ℝ) + 1) * r - 2) ^ 2 := by
    unfold splitPolynomial
    have hjn : (j : ℝ) ≠ 0 := ne_of_gt hj0
    have hjn1 : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hnonneg := add_nonneg (mul_nonneg (sq_nonneg r) hlow)
    (mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg ((2 * (j : ℝ) + 1) * r - 2)))
  rw [← hid] at hnonneg
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by positivity :
    (0 : ℝ) < 4 * (j : ℝ) * ((j : ℝ) + 1))).mp hnonneg)

private theorem exists_closed_cell_above_index (k : ℕ) (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hrk : r ≤ 1 / (k : ℝ)) :
    ∃ j : ℕ, k ≤ j ∧ r ∈ Set.Icc (1 / ((j : ℝ) + 1)) (1 / (j : ℝ)) := by
  let j := ⌊1 / r⌋₊
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkr : (k : ℝ) ≤ 1 / r := by
    apply (le_div_iff₀ hr0).mpr
    have h := (le_div_iff₀ hk0).mp hrk
    nlinarith
  have hjk : k ≤ j := Nat.le_floor hkr
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  refine ⟨j, hjk, ?_, ?_⟩
  · apply le_of_lt
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    have h := (div_lt_iff₀ hr0).mp (Nat.lt_floor_add_one (1 / r))
    nlinarith
  · apply (le_div_iff₀ hj0).mpr
    have h := (le_div_iff₀ hr0).mp (Nat.floor_le (one_div_nonneg.mpr hr0.le))
    nlinarith

private theorem splitValue_le_indexed_cubic (k : ℕ) (hk : 1 ≤ k) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (1 / (k : ℝ))) :
    splitValue r ≤ r ^ 2 * (1 - (1 - 1 / (4 * ((k : ℝ) + 1))) * r) := by
  rcases eq_or_lt_of_le hr.1 with rfl | hr0
  · norm_num [splitValue]
  obtain ⟨j, hjk, hcell⟩ := exists_closed_cell_above_index k hk hr0 hr.2
  have hj : 1 ≤ j := hk.trans hjk
  have hvalue : splitValue r = splitPolynomial j r := by
    have hsub : j - 1 + 1 = j := Nat.sub_add_cancel hj
    have hcell' : r ∈ Set.Icc
        (1 / (((j - 1 : ℕ) : ℝ) + 2)) (1 / (((j - 1 : ℕ) : ℝ) + 1)) := by
      rw [Nat.cast_sub hj, Nat.cast_one]
      convert hcell using 1
      congr 1 <;> ring
    simpa only [hsub] using splitValue_on_cell (j - 1) hcell'
  have hden : 4 * ((k : ℝ) + 1) ≤ 4 * ((j : ℝ) + 1) := by
    have hcast : (k : ℝ) ≤ j := by exact_mod_cast hjk
    linarith
  have hrecip := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < 4 * ((k : ℝ) + 1)) hden
  have hcorrection := mul_le_mul_of_nonneg_left hrecip (pow_nonneg hr.1 3)
  calc
    splitValue r = splitPolynomial j r := hvalue
    _ ≤ r ^ 2 - r ^ 3 + r ^ 3 / (4 * ((j : ℝ) + 1)) :=
      splitPolynomial_le_cell_cubic j hj hcell
    _ ≤ r ^ 2 - r ^ 3 + r ^ 3 / (4 * ((k : ℝ) + 1)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        add_le_add (le_refl (r ^ 2 - r ^ 3)) hcorrection
    _ = r ^ 2 * (1 - (1 - 1 / (4 * ((k : ℝ) + 1))) * r) := by ring

/-- The actual split curve has the seven-eighths cubic bound on its full
nonnegative unit interval, including both endpoints. -/
theorem splitValue_le_seven_eighths {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    splitValue r ≤ r ^ 2 * (1 - (7 / 8) * r) := by
  have h := splitValue_le_indexed_cubic 1 (by norm_num) (r := r) (by simpa using hr)
  norm_num at h
  exact h

/-- The actual split curve has the fifteen-sixteenths cubic bound through
the reciprocal one-third endpoint, with its cell derived internally. -/
theorem splitValue_le_fifteen_sixteenths {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (1 / 3)) :
    splitValue r ≤ r ^ 2 * (1 - (15 / 16) * r) := by
  have h := splitValue_le_indexed_cubic 3 (by norm_num) hr
  norm_num at h
  exact h

/-- The actual split curve has the nineteen-twentieths cubic bound through
the reciprocal one-quarter endpoint, with its cell derived internally. -/
theorem splitValue_le_nineteen_twentieths {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    splitValue r ≤ r ^ 2 * (1 - (19 / 20) * r) := by
  have h := splitValue_le_indexed_cubic 4 (by norm_num) hr
  norm_num at h
  exact h

end Erdos1017.Benchmark

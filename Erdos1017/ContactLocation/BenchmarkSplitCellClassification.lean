module

public import Erdos1017.Benchmark.SplitCurve

/-!
# Classification of split parameters into cells

Every positive split parameter below one half lies in the half-open reciprocal
cell given by its ceiling index, and so is either in a strict cell or at a
reciprocal junction with denominator at least three
(`split_cell_or_reciprocal`).
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- The actual ceiling index places every positive split parameter below
one half in its half-open reciprocal cell. -/
theorem splitIndex_cell {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    2 ≤ splitIndex r ∧ r ∈ Set.Ico
      (1 / ((splitIndex r : ℝ) + 1)) (1 / (splitIndex r : ℝ)) := by
  have ha : (1 : ℝ) < (1 - r) / r :=
    (lt_div_iff₀ hr.1).mpr (by linarith [hr.2])
  have hk : 2 ≤ ⌈(1 - r) / r⌉₊ := by
    have h := (Nat.lt_ceil (a := (1 - r) / r) (n := 1)).mpr (by simpa using ha)
    omega
  have hj : splitIndex r = ⌈(1 - r) / r⌉₊ := max_eq_right (by omega)
  have hj2 : 2 ≤ splitIndex r := by omega
  have hc := (Nat.ceil_eq_iff (show splitIndex r ≠ 0 by omega)).mp hj.symm
  rw [Nat.cast_sub (by omega : 1 ≤ splitIndex r), Nat.cast_one] at hc
  have hj0 : (0 : ℝ) < splitIndex r := by
    exact_mod_cast (show 0 < splitIndex r by omega)
  refine ⟨hj2, ?_, ?_⟩
  · apply (div_le_iff₀ (by linarith : (0 : ℝ) < (splitIndex r : ℝ) + 1)).mpr
    have hprod := (div_le_iff₀ hr.1).mp hc.2
    nlinarith
  · apply (lt_div_iff₀ hj0).mpr
    have hprod := (lt_div_iff₀ hr.1).mp hc.1
    nlinarith

/-- Every positive split parameter below one half is in a strict cell
or is a reciprocal junction with denominator at least three. -/
theorem split_cell_or_reciprocal {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    (∃ n : ℕ, r ∈ Set.Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) ∨
      ∃ m : ℕ, 3 ≤ m ∧ r = 1 / (m : ℝ) := by
  obtain ⟨hj, hcell⟩ := splitIndex_cell hr
  rcases eq_or_lt_of_le hcell.1 with heq | hlt
  · right
    refine ⟨splitIndex r + 1, by omega, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using heq.symm
  · left
    refine ⟨splitIndex r - 1, ?_⟩
    rw [Nat.cast_sub (by omega : 1 ≤ splitIndex r), Nat.cast_one]
    convert (show r ∈ Set.Ioo
      (1 / ((splitIndex r : ℝ) + 1)) (1 / (splitIndex r : ℝ)) from ⟨hlt, hcell.2⟩)
      using 1
    congr 1 <;> ring

end Erdos1017.Benchmark

module

public import Erdos1017.Benchmark
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The split curve of the benchmark

This module defines `splitPolynomial` and proves the cell formula, bounds and
continuity of the split value, including continuity across every reciprocal
split junction and at their accumulation point zero (`splitValue_continuousOn`).
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- The split polynomial `(2(j + 1)r - (2j + 1)r² - 1) / (j(j + 1))` of index
`j`; for `r ≠ 0`, the split value `H(r)` is this polynomial with
`j = splitIndex r`. -/
noncomputable def splitPolynomial (j : ℕ) (r : ℝ) : ℝ :=
  (-(2 * (j : ℝ) + 1) * r ^ 2 + 2 * ((j : ℝ) + 1) * r - 1) /
    ((j : ℝ) * ((j : ℝ) + 1))

/-- For `j > 0`, the split polynomials of indices `j` and `j + 1` agree at the
junction `r = 1/(j + 1)`. -/
theorem splitPolynomial_adjacent (j : ℕ) (hj : 0 < j) :
    splitPolynomial j (1 / ((j : ℝ) + 1)) =
      splitPolynomial (j + 1) (1 / ((j : ℝ) + 1)) := by
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  unfold splitPolynomial
  push_cast
  field_simp
  ring

/-- At `r = 1/(n + 1)` the split index is `max 1 n`. -/
theorem splitIndex_reciprocal (n : ℕ) : splitIndex (1 / ((n : ℝ) + 1)) = max 1 n := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have heq : (1 - 1 / ((n : ℝ) + 1)) / (1 / ((n : ℝ) + 1)) = n := by
    field_simp
    ring
  simp only [splitIndex, heq, Nat.ceil_natCast]

/-- On the closed split cell `1/(n + 2) ≤ r ≤ 1/(n + 1)`, the split value
`H(r)` equals the split polynomial of index `n + 1`. -/
theorem splitValue_on_cell (n : ℕ) {r : ℝ}
    (hr : r ∈ Set.Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    splitValue r = splitPolynomial (n + 1) r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr.1
  by_cases heq : r = 1 / ((n : ℝ) + 1)
  · subst r
    unfold splitValue
    rw [ite_eq_right hr0.ne', splitIndex_reciprocal]
    cases n with
    | zero => norm_num [splitPolynomial]
    | succ n =>
      have hm : max 1 (n + 1) = n + 1 := max_eq_right (by omega)
      rw [hm]
      change splitPolynomial (n + 1) (1 / ((↑(n + 1) : ℝ) + 1)) = _
      exact splitPolynomial_adjacent (n + 1) (by omega)
  · have hhi : r < 1 / ((n : ℝ) + 1) := lt_of_le_of_ne hr.2 heq
    have hceil : ⌈(1 - r) / r⌉₊ = n + 1 := by
      apply (Nat.ceil_eq_iff (by omega : n + 1 ≠ 0)).mpr
      constructor
      · simp only [Nat.add_sub_cancel]
        apply (lt_div_iff₀ hr0).mpr
        have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mp hhi
        nlinarith
      · apply (div_le_iff₀ hr0).mpr
        have h := (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).mp hr.1
        push_cast
        nlinarith
    have hj : splitIndex r = n + 1 := by
      unfold splitIndex
      rw [hceil, max_eq_right (by omega : 1 ≤ n + 1)]
    unfold splitValue
    rw [ite_eq_right hr0.ne', hj]
    rfl

/-- The split value `H` is continuous on each closed split cell `[1/(n + 2), 1/(n + 1)]`. -/
theorem splitValue_continuousOn_cell (n : ℕ) :
    ContinuousOn splitValue (Set.Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) := by
  apply (continuousOn_congr (fun _ hr => splitValue_on_cell n hr)).mpr
  unfold splitPolynomial
  fun_prop

/-- For `0 ≤ r ≤ 1`, the split value satisfies `0 ≤ H(r) ≤ r²`. -/
theorem splitValue_bounds {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ splitValue r ∧ splitValue r ≤ r ^ 2 := by
  rcases eq_or_lt_of_le hr.1 with rfl | hr0
  · simp [splitValue]
  have hj : 1 ≤ splitIndex r := le_max_left _ _
  have hj' : (1 : ℝ) ≤ splitIndex r := by exact_mod_cast hj
  have hceil : (1 - r) / r ≤ (splitIndex r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈(1 - r) / r⌉₊)
  have hprod : 1 - r ≤ (splitIndex r : ℝ) * r := (div_le_iff₀ hr0).mp hceil
  have hd : 0 < (splitIndex r : ℝ) * ((splitIndex r : ℝ) + 1) := by positivity
  unfold splitValue
  rw [ite_eq_right hr0.ne']
  dsimp only
  constructor
  · apply div_nonneg _ hd.le
    have hp := mul_nonneg (sub_nonneg.mpr hr.2) (show 0 ≤ 2 * (splitIndex r : ℝ) * r + r - 1 by nlinarith [hr.2])
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    have hp := sq_nonneg ((splitIndex r : ℝ) * r - (1 - r))
    have hnonneg : 0 ≤ (splitIndex r : ℝ) * r ^ 2 := by positivity
    nlinarith

/-- The accumulation of reciprocal split branches at zero is controlled uniformly. -/
theorem splitValue_tendsto_zero :
    Filter.Tendsto splitValue (nhdsWithin 0 (Set.Icc (0 : ℝ) 1)) (nhds 0) := by
  have hpow : Filter.Tendsto (fun r : ℝ => r ^ 2) (nhdsWithin 0 (Set.Icc (0 : ℝ) 1)) (nhds 0) := by
    have hc : ContinuousAt (fun r : ℝ => r ^ 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := squeeze_zero' (f := splitValue) (g := fun r : ℝ => r ^ 2)
    (Filter.eventually_of_mem self_mem_nhdsWithin fun r hr => (splitValue_bounds hr).1)
    (Filter.eventually_of_mem self_mem_nhdsWithin fun r hr => (splitValue_bounds hr).2)
    hpow
  simpa using h

/-- The split value `H` is continuous on `[1/(n + 2), 1]` for every `n`. -/
theorem splitValue_continuousOn_above_reciprocal (n : ℕ) :
    ContinuousOn splitValue (Set.Icc (1 / ((n : ℝ) + 2)) 1) := by
  induction n with
  | zero => simpa using splitValue_continuousOn_cell 0
  | succ n ih =>
    have hc := (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).mpr
      ⟨splitValue_continuousOn_cell (n + 1), ih⟩
    have hlow : 1 / ((n : ℝ) + 3) ≤ 1 / ((n : ℝ) + 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have hhigh : 1 / ((n : ℝ) + 2) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    norm_num only [Nat.cast_add, Nat.cast_one] at hc ⊢
    convert hc using 1
    rw [show (n : ℝ) + 1 + 2 = n + 3 by ring,
      show (n : ℝ) + 1 + 1 = n + 2 by ring, Set.Icc_union_Icc_eq_Icc hlow hhigh]

/-- All reciprocal split junctions and their accumulation point are continuous. -/
theorem splitValue_continuousOn : ContinuousOn splitValue (Set.Icc (0 : ℝ) 1) := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with rfl | hr0
  · simpa [ContinuousWithinAt, splitValue] using splitValue_tendsto_zero
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr0
    have hlo : 1 / ((n : ℝ) + 2) < r := by
      apply lt_of_le_of_lt _ hn
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    apply ((splitValue_continuousOn_above_reciprocal n) r ⟨hlo.le, hr.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlo), self_mem_nhdsWithin] with x hx hx'
    exact ⟨hx.le, hx'.2⟩

end Erdos1017.Benchmark

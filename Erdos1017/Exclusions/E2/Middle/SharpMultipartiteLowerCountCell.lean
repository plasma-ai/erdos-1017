module

public import Erdos1017.Exclusions.E2.Middle.SharpSelectorLowerCountCell
public import Erdos1017.Exclusions.Common.SharpCounts.SharpMultipartiteCountCells

/-!
# Lower count cell for finite and countable heads

The two-fifths lower count-cell bound holds for finite heads and dust, and for
countable heads and dust on the closed total range `[3/2, 2]`, where finite
prefixes eventually exceed `10/7` (`value_le_lower_countCell`).
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos1017.MultipartiteDust

private theorem lower_target_moments {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ i, DustPaddedCells.target p s n i) = (∑ i, p i) + s ∧
      (∑ i, (DustPaddedCells.target p s n i) ^ 2) = (∑ i, (p i) ^ 2) + s ^ 2 / n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  constructor <;> rw [Fin.sum_univ_add] <;>
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul] <;> field_simp

/-- The two-fifths lower count-cell bound for actual finite heads and dust. -/
theorem value_le_lower_countCell {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : 0 ≤ s)
    (hT : ((∑ i, p i) + s) ∈ Icc (10 / 7 : ℝ) 2) :
    value p s ≤ (4 * ((∑ i, p i) + s) - ((∑ i, p i) + s) ^ 2) / 6 +
      2 / 5 * ∑ i, (p i) ^ 2 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (s ^ 2 / ε))
  have hnreal : (0 : ℝ) < n := hs.trans_lt ((le_max_left _ _).trans_lt hn)
  have hn0 : 0 < n := by exact_mod_cast hnreal
  have hsn : s ≤ n := (le_max_left _ _).trans hn.le
  have hsmall : s ^ 2 / (n : ℝ) < ε := by
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    exact (div_lt_iff₀ hnreal).mpr (by linarith)
  have herr : 0 ≤ s ^ 2 / (n : ℝ) := by positivity
  have hq := DustPaddedCells.target_cube p hp s hs n hn0 hsn
  have hm := lower_target_moments p s n hn0
  have hb := Selector.Sharp.value_le_lower_countCell (DustPaddedCells.target p s n) hq
    (by rw [hm.1]; exact hT)
  rw [hm.1, hm.2] at hb
  have hcell := (DustPaddedCells.finite_cell_value_error p hp s hs n hn0 hsn).1
  linarith

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

private theorem lower_prefix_facts (p : ℕ → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hsum : Summable p) (s : ℝ) :
    Tendsto (fun n => (∑ i : Fin n, p i.val) + s) atTop (nhds ((∑' i, p i) + s)) ∧
      ∀ n, (∑ i : Fin n, p i.val) + s ≤ (∑' i, p i) + s ∧
        (∑ i : Fin n, (p i.val) ^ 2) ≤ ∑' i, (p i) ^ 2 := by
  have hsq : Summable (fun i => (p i) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hsum
    intro i
    nlinarith [(hp i).1, (hp i).2]
  constructor
  · have hpLimit : Tendsto (fun n => ∑ i : Fin n, p i.val) atTop (nhds (∑' i, p i)) := by
      simpa only [Fin.sum_univ_eq_sum_range] using hsum.hasSum.tendsto_sum_nat
    exact hpLimit.add_const s
  · intro n
    constructor
    · have h := hsum.sum_le_tsum (Finset.range n) (fun i _ => (hp i).1)
      rw [Fin.sum_univ_eq_sum_range]
      linarith
    · rw [Fin.sum_univ_eq_sum_range (fun i => (p i) ^ 2) n]
      exact hsq.sum_le_tsum (Finset.range n) (fun i _ => sq_nonneg (p i))

/-- The two-fifths lower count-cell bound for countable heads and dust on
the closed total range `[3/2, 2]`. Finite prefixes eventually exceed
`10/7`, where the finite theorem already applies, so no boundary case is
separate. -/
theorem value_le_lower_countCell (p : ℕ → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) (hT : ((∑' i, p i) + s) ∈ Icc (3 / 2 : ℝ) 2) :
    value p s ≤ (4 * ((∑' i, p i) + s) - ((∑' i, p i) + s) ^ 2) / 6 +
      2 / 5 * ∑' i, (p i) ^ 2 := by
  have hstrict : 10 / 7 < (∑' i, p i) + s := by linarith [hT.1]
  obtain ⟨D, hD, hvalue⟩ := exists_value_eq p (fun i => (hp i).1) hsum s
  rw [hvalue]
  have hf := lower_prefix_facts p hp hsum s
  have hlimit := (((hf.1.const_mul 4).sub (hf.1.pow 2)).div_const 6).add_const
    (2 / 5 * ∑' i, (p i) ^ 2)
  apply le_of_tendsto_of_tendsto
    (objective_restrict_tendsto p (fun i => (hp i).1) hsum s hD.1) hlimit
  filter_upwards [hf.1.eventually (lt_mem_nhds hstrict)] with n hn
  have hb := MultipartiteDust.value_le_lower_countCell (fun i : Fin n => p i.val)
    (fun i => hp i.val) s hs ⟨hn.le, (hf.2 n).1.trans hT.2⟩
  have ho := MultipartiteDust.objective_le_value (fun i : Fin n => p i.val) s (restrict n D)
    (restrict_mem_feasible hD n)
  linarith [(hf.2 n).2]

end Erdos1017.MultipartiteCountableDual

module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorCountCells
public import Erdos1017.Exclusions.Common.SharpCounts.SharpMultipartiteSmallTotal

/-!
# Middle and large count-cell bounds for heads and dust

The middle (total in `[2, 3]`) and large (total at least three) count-cell
bounds hold for finitely many heads and dust and pass to summable sequences of
heads through finite prefixes; the boundary totals two and three use the
small-total and middle bounds.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos1017.MultipartiteDust

private theorem target_moments {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ i, DustPaddedCells.target p s n i) = (∑ i, p i) + s ∧
      (∑ i, (DustPaddedCells.target p s n i) ^ 2) = (∑ i, (p i) ^ 2) + s ^ 2 / n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  constructor <;> rw [Fin.sum_univ_add] <;>
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul] <;> field_simp

/-- The middle count-cell bound for actual finite heads and dust. -/
theorem value_le_middle_countCell {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : 0 ≤ s)
    (hT : ((∑ i, p i) + s) ∈ Icc (2 : ℝ) 3) :
    value p s ≤ (6 * ((∑ i, p i) + s) - ((∑ i, p i) + s) ^ 2) / 12 +
      (∑ i, (p i) ^ 2) / 3 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (s ^ 2 / (3 * ε)))
  have hnreal : (0 : ℝ) < n := hs.trans_lt ((le_max_left _ _).trans_lt hn)
  have hn0 : 0 < n := by exact_mod_cast hnreal
  have hsn : s ≤ n := (le_max_left _ _).trans hn.le
  have hsmall : s ^ 2 / (3 * (n : ℝ)) < ε := by
    have h := (div_lt_iff₀ (show 0 < 3 * ε by positivity)).mp
      ((le_max_right _ _).trans_lt hn)
    apply (div_lt_iff₀ (show (0 : ℝ) < 3 * n by positivity)).mpr
    nlinarith
  have hq := DustPaddedCells.target_cube p hp s hs n hn0 hsn
  have hm := target_moments p s n hn0
  have hb := Selector.Sharp.value_le_middle_countCell (DustPaddedCells.target p s n) hq
    (by rw [hm.1]; exact hT)
  rw [hm.1, hm.2] at hb
  have hcell := (DustPaddedCells.finite_cell_value_error p hp s hs n hn0 hsn).1
  have herr : (s ^ 2 / n) / 3 = s ^ 2 / (3 * (n : ℝ)) := by ring
  rw [add_div, herr] at hb
  linarith

/-- The large count-cell bound for actual finite heads and dust. -/
theorem value_le_large_countCell {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : 0 ≤ s)
    (hT : 3 ≤ (∑ i, p i) + s) :
    value p s ≤ ((∑ i, p i) + s) / 4 + (∑ i, (p i) ^ 2) / ((∑ i, p i) + s) := by
  let T : ℝ := (∑ i, p i) + s
  have hT0 : 0 < T := by dsimp [T]; linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (s ^ 2 / (T * ε)))
  have hnreal : (0 : ℝ) < n := hs.trans_lt ((le_max_left _ _).trans_lt hn)
  have hn0 : 0 < n := by exact_mod_cast hnreal
  have hsn : s ≤ n := (le_max_left _ _).trans hn.le
  have hsmall : s ^ 2 / ((n : ℝ) * T) < ε := by
    have h := (div_lt_iff₀ (show 0 < T * ε by positivity)).mp
      ((le_max_right _ _).trans_lt hn)
    apply (div_lt_iff₀ (show (0 : ℝ) < n * T by positivity)).mpr
    nlinarith
  have hq := DustPaddedCells.target_cube p hp s hs n hn0 hsn
  have hm := target_moments p s n hn0
  have hb := Selector.Sharp.value_le_large_countCell (DustPaddedCells.target p s n) hq
    (by rw [hm.1]; exact hT)
  rw [hm.1, hm.2] at hb
  have hcell := (DustPaddedCells.finite_cell_value_error p hp s hs n hn0 hsn).1
  have herr : (s ^ 2 / n) / T = s ^ 2 / ((n : ℝ) * T) := by field_simp
  change Selector.value (DustPaddedCells.target p s n) ≤ T / 4 +
    ((∑ i, (p i) ^ 2) + s ^ 2 / n) / T at hb
  rw [add_div (∑ i, (p i) ^ 2) (s ^ 2 / n) T, herr] at hb
  change value p s ≤ T / 4 + (∑ i, (p i) ^ 2) / T + ε
  linarith

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

private theorem prefix_facts (p : ℕ → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
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

/-- At a strict middle-cell total, actual finite prefixes eventually lie
in that same cell. The boundary total two uses the proved small-total bound. -/
theorem value_le_middle_countCell (p : ℕ → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) (hT : ((∑' i, p i) + s) ∈ Icc (2 : ℝ) 3) :
    value p s ≤ (6 * ((∑' i, p i) + s) - ((∑' i, p i) + s) ^ 2) / 12 +
      (∑' i, (p i) ^ 2) / 3 := by
  by_cases heq : (∑' i, p i) + s = 2
  · have hb := value_le_sumTwo p hp hsum s hs heq.le
    rw [heq]
    linarith
  have hstrict : 2 < (∑' i, p i) + s := lt_of_le_of_ne hT.1 (Ne.symm heq)
  obtain ⟨D, hD, hvalue⟩ := exists_value_eq p (fun i => (hp i).1) hsum s
  rw [hvalue]
  have hf := prefix_facts p hp hsum s
  have hlimit := (((hf.1.const_mul 6).sub (hf.1.pow 2)).div_const 12).add_const
    ((∑' i, (p i) ^ 2) / 3)
  apply le_of_tendsto_of_tendsto
    (objective_restrict_tendsto p (fun i => (hp i).1) hsum s hD.1) hlimit
  filter_upwards [hf.1.eventually (lt_mem_nhds hstrict)] with n hn
  have hb := MultipartiteDust.value_le_middle_countCell (fun i : Fin n => p i.val)
    (fun i => hp i.val) s hs ⟨hn.le, (hf.2 n).1.trans hT.2⟩
  have ho := MultipartiteDust.objective_le_value (fun i : Fin n => p i.val) s (restrict n D)
    (restrict_mem_feasible hD n)
  linarith [(hf.2 n).2]

/-- At a strict large-cell total, prefixes eventually stay above three;
the exact boundary three is supplied by the already proved middle cell. -/
theorem value_le_large_countCell (p : ℕ → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) (hT : 3 ≤ (∑' i, p i) + s) :
    value p s ≤ ((∑' i, p i) + s) / 4 + (∑' i, (p i) ^ 2) / ((∑' i, p i) + s) := by
  by_cases heq : (∑' i, p i) + s = 3
  · have hb := value_le_middle_countCell p hp hsum s hs ⟨by linarith, heq.le⟩
    rw [heq] at hb ⊢
    linarith
  have hstrict : 3 < (∑' i, p i) + s := lt_of_le_of_ne hT (Ne.symm heq)
  have hpos : 0 < (∑' i, p i) + s := by linarith
  obtain ⟨D, hD, hvalue⟩ := exists_value_eq p (fun i => (hp i).1) hsum s
  rw [hvalue]
  have hf := prefix_facts p hp hsum s
  have hlimit := (hf.1.div_const 4).add
    ((tendsto_const_nhds (x := (∑' i, (p i) ^ 2))).div hf.1 hpos.ne')
  apply le_of_tendsto_of_tendsto
    (objective_restrict_tendsto p (fun i => (hp i).1) hsum s hD.1) hlimit
  filter_upwards [hf.1.eventually (lt_mem_nhds hstrict)] with n hn
  have hnpos : 0 < (∑ i : Fin n, p i.val) + s := by linarith
  have hb := MultipartiteDust.value_le_large_countCell (fun i : Fin n => p i.val)
    (fun i => hp i.val) s hs hn.le
  have ho := MultipartiteDust.objective_le_value (fun i : Fin n => p i.val) s (restrict n D)
    (restrict_mem_feasible hD n)
  have hdiv := div_le_div_of_nonneg_right (hf.2 n).2 hnpos.le
  change MultipartiteDust.objective (fun i : Fin n => p i.val) s (restrict n D) ≤
    ((∑ i : Fin n, p i.val) + s) / 4 + (∑' i, (p i) ^ 2) / ((∑ i : Fin n, p i.val) + s)
  linarith

end Erdos1017.MultipartiteCountableDual

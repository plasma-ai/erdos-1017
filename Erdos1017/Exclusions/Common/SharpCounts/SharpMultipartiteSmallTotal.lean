module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorSmallTotal
public import Erdos1017.Multipartite.MultipartiteCountableRestriction

/-!
# Sharp bound for countable head families at total load at most two

An unrestricted summable countable head family with total load at most two
satisfies the sharp bound (`value_le_sumTwo`): refining the dust into equal
cells gives the finite bound up to its residual square-mass error, which
arbitrarily fine cells remove.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Refining actual dust into equal cells gives the sharp finite bound
with precisely its residual square-mass error. -/
theorem value_le_sumTwo_add_error {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : 0 ≤ s)
    (hT : (∑ i, p i) + s ≤ 2) (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) :
    value p s ≤ (2 + ∑ i, (p i) ^ 2) / 3 + s ^ 2 / (3 * n) := by
  let q := DustPaddedCells.target p s n
  have hq := DustPaddedCells.target_cube p hp s hs n hn hsn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ i, q i) = (∑ i, p i) + s := by
    dsimp [q]
    rw [Fin.sum_univ_add]
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hsquare : (∑ i, (q i) ^ 2) = (∑ i, (p i) ^ 2) + s ^ 2 / n := by
    dsimp [q]
    rw [Fin.sum_univ_add]
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hcell := (DustPaddedCells.finite_cell_value_error p hp s hs n hn hsn).1
  have hselector := Selector.Sharp.value_le_smallTotal q hq (hsum.trans_le hT)
  rw [hsquare] at hselector
  change 0 ≤ Selector.value q - value p s at hcell
  calc
    value p s ≤ Selector.value q := sub_nonneg.mp hcell
    _ ≤ _ := hselector
    _ = _ := by ring

/-- Arbitrarily fine actual dust cells remove the square-mass error. -/
theorem value_le_sumTwo {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : 0 ≤ s)
    (hT : (∑ i, p i) + s ≤ 2) :
    value p s ≤ (2 + ∑ i, (p i) ^ 2) / 3 := by
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
  linarith [value_le_sumTwo_add_error p hp s hs hT n hn0 hsn]

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

/-- An unrestricted summable countable head family has the sharp bound
at total load at most two. No sorting or extra square bound is imposed. -/
theorem value_le_sumTwo (p : ℕ → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) (hT : (∑' i, p i) + s ≤ 2) :
    value p s ≤ (2 + ∑' i, (p i) ^ 2) / 3 := by
  obtain ⟨D, hD, hvalue⟩ := exists_value_eq p (fun i => (hp i).1) hsum s
  rw [hvalue]
  have hsq : Summable (fun i => (p i) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hsum
    intro i
    nlinarith [(hp i).1, (hp i).2]
  apply le_of_tendsto (objective_restrict_tendsto p (fun i => (hp i).1) hsum s hD.1)
  apply Eventually.of_forall
  intro n
  have hprefix : (∑ i : Fin n, p i.val) ≤ ∑' i, p i := by
    simpa only [Fin.sum_univ_eq_sum_range] using
      hsum.sum_le_tsum (Finset.range n) (fun i _ => (hp i).1)
  have hprefixSq : (∑ i : Fin n, (p i.val) ^ 2) ≤ ∑' i, (p i) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (p i) ^ 2) n]
    exact hsq.sum_le_tsum (Finset.range n) (fun i _ => sq_nonneg (p i))
  have hv := MultipartiteDust.value_le_sumTwo (fun i : Fin n => p i.val)
    (fun i => hp i.val) s hs (by linarith)
  exact ((MultipartiteDust.objective_le_value (fun i : Fin n => p i.val) s (restrict n D)
    (restrict_mem_feasible hD n)).trans hv).trans (by linarith)

end Erdos1017.MultipartiteCountableDual

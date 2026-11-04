module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Replacing a clique by its uniform r-subsets

Replacing a clique by uniformly weighted `r`-subsets preserves each pair load
(`uniform_pair_load`), and the total replacement cost is the ratio of the old
and new pair counts (`uniform_cost`).
-/

@[expose] public section

namespace Erdos1017.CliqueTruncation

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Every fixed pair occurs in exactly this many uniform `r`-subsets. -/
theorem pair_subset_count (s e : Finset V) (he : e.card = 2) (hes : e ⊆ s)
    (r : ℕ) (hr : 2 ≤ r) :
    ((s.powersetCard r).filter (e ⊆ ·)).card = (s.card - 2).choose (r - 2) := by
  simpa only [he] using Finset.card_filter_powersetCard_subset e s r hes (by omega)

omit [DecidableEq V] in
/-- The uniform-subset denominator is positive whenever the truncation is possible. -/
theorem pair_subset_count_pos (s : Finset V) (r : ℕ) (hr : r ≤ s.card) :
    0 < (s.card - 2).choose (r - 2) := Nat.choose_pos (Nat.sub_le_sub_right hr 2)

/-- Replacing a clique by uniformly weighted `r`-subsets preserves each pair load. -/
theorem uniform_pair_load (s e : Finset V) (he : e.card = 2) (hes : e ⊆ s)
    (r : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s.card) :
    (∑ u ∈ s.powersetCard r,
      if e ⊆ u then ((s.card - 2).choose (r - 2) : ℝ)⁻¹ else 0) = 1 := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, pair_subset_count s e he hes r hr]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (pair_subset_count_pos s r hrs).ne')

omit [DecidableEq V] in
/-- The total replacement cost is the ratio of the old and new pair counts. -/
theorem uniform_cost (s : Finset V) (r : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s.card) :
    (∑ _u ∈ s.powersetCard r, ((s.card - 2).choose (r - 2) : ℝ)⁻¹) =
      (s.card.choose 2 : ℝ) / (r.choose 2 : ℝ) := by
  have hden : ((s.card - 2).choose (r - 2) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pair_subset_count_pos s r hrs).ne'
  have hrden : (r.choose 2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
  have hid : (s.card.choose r : ℝ) * (r.choose 2 : ℝ) =
      (s.card.choose 2 : ℝ) * ((s.card - 2).choose (r - 2) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := s.card) hr
  simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  apply (eq_div_iff hrden).mpr
  calc
    (s.card.choose r : ℝ) * ((s.card - 2).choose (r - 2) : ℝ)⁻¹ * (r.choose 2 : ℝ) =
        ((s.card.choose r : ℝ) * (r.choose 2 : ℝ)) /
          ((s.card - 2).choose (r - 2) : ℝ) := by ring
    _ = (s.card.choose 2 : ℝ) := by rw [hid]; exact mul_div_cancel_right₀ _ hden

end Erdos1017.CliqueTruncation

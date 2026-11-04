module

public import Erdos1017.IntegerTransfer.CliqueCountingEdge

/-!
# Bounded-pattern counting from rectangle discrepancy

This module counts assignments of a bounded pattern from rectangle discrepancy,
with each unordered pattern edge represented once in increasing order and an
error that is additive per edge (`pattern_discrepancy`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CliqueCounting

open scoped BigOperators

variable {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Bounded-pattern counting from rectangle discrepancy. Each unordered pattern
edge is represented once, in increasing order. The error is additive per edge. -/
theorem pattern_discrepancy (E : Finset (Fin k × Fin k))
    (K : (Fin k × Fin k) → A → A → ℝ) (d : (Fin k × Fin k) → ℝ)
    (η : ℝ) (hη : 0 ≤ η)
    (horder : ∀ e ∈ E, e.1 < e.2)
    (hK : ∀ e ∈ E, ∀ a b, 0 ≤ K e a b ∧ K e a b ≤ 1)
    (hd : ∀ e ∈ E, 0 ≤ d e ∧ d e ≤ 1)
    (hcut : ∀ e ∈ E, ∀ (X Y : A → Bool),
      |∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) * (K e a b - d e)| ≤ η) :
    (Fintype.card A : ℝ) ^ 2 *
      |(∑ X : Fin k → A, ∏ e ∈ E, K e (X e.1) (X e.2)) -
        Fintype.card (Fin k → A) * ∏ e ∈ E, d e| ≤
      E.card * Fintype.card (Fin k → A) * η := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert e E he ih =>
    have hrest : ∀ f ∈ E, f.1 < f.2 := fun f hf => horder f (Finset.mem_insert_of_mem hf)
    have hKrest := fun f hf => hK f (Finset.mem_insert_of_mem hf)
    have hdrest := fun f hf => hd f (Finset.mem_insert_of_mem hf)
    have hcutrest := fun f hf => hcut f (Finset.mem_insert_of_mem hf)
    have horde := horder e (Finset.mem_insert_self _ _)
    have hde := hd e (Finset.mem_insert_self _ _)
    have hsep : ∀ f ∈ E, ¬ ((f.1 = e.1 ∨ f.2 = e.1) ∧ (f.1 = e.2 ∨ f.2 = e.2)) := by
      intro f hf hboth
      have hford := hrest f hf
      have hfe : f ≠ e := fun h => he (h ▸ hf)
      rcases hboth with ⟨h1 | h1, h2 | h2⟩
      · omega
      · exact hfe (Prod.ext h1 h2)
      · omega
      · omega
    have hedge := edge_discrepancy E K hKrest (fun a b => K e a b - d e) η hη
      (hcut e (Finset.mem_insert_self _ _)) e.1 e.2 (ne_of_lt horde) hsep
    have hind := ih hrest hKrest hdrest hcutrest
    let u := ∑ X : Fin k → A, (K e (X e.1) (X e.2) - d e) *
      ∏ f ∈ E, K f (X f.1) (X f.2)
    let v := (∑ X : Fin k → A, ∏ f ∈ E, K f (X f.1) (X f.2)) -
      Fintype.card (Fin k → A) * ∏ f ∈ E, d f
    have heq : ((∑ X : Fin k → A, ∏ f ∈ insert e E, K f (X f.1) (X f.2)) -
        Fintype.card (Fin k → A) * ∏ f ∈ insert e E, d f) = u + d e * v := by
      simp only [Finset.prod_insert he, u, v, sub_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      ring
    rw [heq, Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one]
    have habs : |u + d e * v| ≤ |u| + d e * |v| := by
      simpa only [abs_mul, abs_of_nonneg hde.1] using abs_add_le u (d e * v)
    have hmul := mul_le_mul_of_nonneg_left habs (sq_nonneg (Fintype.card A : ℝ))
    have hv := mul_le_mul_of_nonneg_left hind hde.1
    have hc : 0 ≤ (E.card : ℝ) * Fintype.card (Fin k → A) * η := by positivity
    have hlast := mul_le_of_le_one_left hc hde.2
    change (Fintype.card A : ℝ) ^ 2 * |u| ≤ _ at hedge
    change (Fintype.card A : ℝ) ^ 2 * |v| ≤ _ at hind
    change d e * ((Fintype.card A : ℝ) ^ 2 * |v|) ≤ _ at hv
    nlinarith

end Erdos1017.CliqueCounting

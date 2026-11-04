module

public import Erdos1017.IntegerTransfer.CliqueCountingCoordinates
public import Mathlib.Tactic.Positivity

/-!
# Replacing one edge in a pattern sum

The error from replacing a single edge factor in a pattern sum is controlled on
every assignment slice by the rectangle bound, even with all other edge factors
present, and hence in the complete sum with exact scaling (`edge_discrepancy`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CliqueCounting

open scoped BigOperators

variable {ι A : Type*} [DecidableEq ι]

/-- After fixing all other coordinates, an edge product with no edge joining
the two exposed coordinates factors into one function of each coordinate. -/
theorem edge_product_factor (E : Finset (ι × ι)) (K : (ι × ι) → A → A → ℝ)
    (X : ι → A) (i j : ι) (hij : i ≠ j)
    (hE : ∀ e ∈ E, ¬ ((e.1 = i ∨ e.2 = i) ∧ (e.1 = j ∨ e.2 = j)))
    (a b : A) :
    (∏ e ∈ E, K e ((Function.update (Function.update X i a) j b) e.1)
      ((Function.update (Function.update X i a) j b) e.2)) =
      (∏ e ∈ E, if e.1 = i ∨ e.2 = i then
        K e ((Function.update X i a) e.1) ((Function.update X i a) e.2) else 1) *
      (∏ e ∈ E, if e.1 = j ∨ e.2 = j then
        K e ((Function.update X j b) e.1) ((Function.update X j b) e.2) else 1) *
      (∏ e ∈ E, if (e.1 = i ∨ e.2 = i) ∨ (e.1 = j ∨ e.2 = j) then 1
        else K e (X e.1) (X e.2)) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  have hsep := hE e he
  by_cases h1 : e.1 = i <;> by_cases h2 : e.2 = i <;>
    by_cases h3 : e.1 = j <;> by_cases h4 : e.2 = j <;>
      simp_all

/-- The error from one edge replacement is controlled on every assignment
slice by the rectangle bound, even with all other edge factors present. -/
theorem edge_slice_discrepancy [Fintype A] [DecidableEq A]
    (E : Finset (ι × ι)) (K : (ι × ι) → A → A → ℝ)
    (hK : ∀ e ∈ E, ∀ a b, 0 ≤ K e a b ∧ K e a b ≤ 1)
    (L : A → A → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hL : ∀ (X Y : A → Bool),
      |∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) * L a b| ≤ η)
    (X : ι → A) (i j : ι) (hij : i ≠ j)
    (hE : ∀ e ∈ E, ¬ ((e.1 = i ∨ e.2 = i) ∧ (e.1 = j ∨ e.2 = j))) :
    |∑ a, ∑ b, L a b * ∏ e ∈ E,
      K e ((Function.update (Function.update X i a) j b) e.1)
        ((Function.update (Function.update X i a) j b) e.2)| ≤ η := by
  let p := fun a => ∏ e ∈ E, if e.1 = i ∨ e.2 = i then
    K e ((Function.update X i a) e.1) ((Function.update X i a) e.2) else 1
  let q := fun b => ∏ e ∈ E, if e.1 = j ∨ e.2 = j then
    K e ((Function.update X j b) e.1) ((Function.update X j b) e.2) else 1
  let c := ∏ e ∈ E, if (e.1 = i ∨ e.2 = i) ∨ (e.1 = j ∨ e.2 = j) then 1
    else K e (X e.1) (X e.2)
  have hrange : ∀ (P : (ι × ι) → Prop) [DecidablePred P] (Y : ι → A),
      0 ≤ (∏ e ∈ E, if P e then K e (Y e.1) (Y e.2) else 1) ∧
        (∏ e ∈ E, if P e then K e (Y e.1) (Y e.2) else 1) ≤ 1 := by
    intro P _ Y
    have h0 : ∀ e ∈ E, 0 ≤ (if P e then K e (Y e.1) (Y e.2) else 1) := by
      intro e he
      split_ifs <;> first | exact (hK e he _ _).1 | positivity
    exact ⟨Finset.prod_nonneg h0, Finset.prod_le_one₀ h0 (by
      intro e he
      split_ifs <;> first | exact (hK e he _ _).2 | exact le_rfl)⟩
  have hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1 := fun a => hrange _ (Function.update X i a)
  have hq : ∀ b, 0 ≤ q b ∧ q b ≤ 1 := fun b => hrange _ (Function.update X j b)
  have hc : 0 ≤ c ∧ c ≤ 1 := by
    have hc := hrange (fun e => ¬ ((e.1 = i ∨ e.2 = i) ∨ (e.1 = j ∨ e.2 = j))) X
    simpa only [ite_not] using hc
  have hbound := WeightedRectangle.abs_sum_le L η hL p q hp hq
  have heq : (∑ a, ∑ b, L a b * ∏ e ∈ E,
      K e ((Function.update (Function.update X i a) j b) e.1)
        ((Function.update (Function.update X i a) j b) e.2)) =
      c * ∑ a, ∑ b, p a * q b * L a b := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [edge_product_factor E K X i j hij hE a b]
    change L a b * (p a * q b * c) = c * (p a * q b * L a b)
    ring
  rw [heq, abs_mul, abs_of_nonneg hc.1]
  exact (mul_le_mul_of_nonneg_left hbound hc.1).trans (mul_le_of_le_one_left hη hc.2)

/-- A single edge replacement in the complete pattern sum, with exact scaling. -/
theorem edge_discrepancy [Fintype ι] [Fintype A] [DecidableEq A]
    (E : Finset (ι × ι)) (K : (ι × ι) → A → A → ℝ)
    (hK : ∀ e ∈ E, ∀ a b, 0 ≤ K e a b ∧ K e a b ≤ 1)
    (L : A → A → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hL : ∀ (X Y : A → Bool),
      |∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) * L a b| ≤ η)
    (i j : ι) (hij : i ≠ j)
    (hE : ∀ e ∈ E, ¬ ((e.1 = i ∨ e.2 = i) ∧ (e.1 = j ∨ e.2 = j))) :
    (Fintype.card A : ℝ) ^ 2 *
      |∑ X : ι → A, L (X i) (X j) * ∏ e ∈ E, K e (X e.1) (X e.2)| ≤
        Fintype.card (ι → A) * η := by
  apply abs_sum_le_of_slices _ i j η
  intro X
  simpa only [Function.update_self, Function.update_of_ne hij] using
    edge_slice_discrepancy E K hK L η hη hL X i j hij hE

end Erdos1017.CliqueCounting

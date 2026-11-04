module

public import Erdos1017.Exclusions.Common.Flows.FullForwardFiniteRerouting

/-!
# Square reserve of finitely many merged sources

When several nonnegative source masses enter one recipient, the square bound
retains the countable base reserve and every assigned source square, with
collisions only strengthening it and no injective assignment required; optional
labels mark diffuse receivers.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical

namespace Erdos1017.FiniteReceiverReserve

/-- Several nonnegative source masses may enter one actual recipient.
Their collision strengthens the square bound; no receiver is split. -/
theorem square_ge_base_add_source_squares {n : ℕ} (a b : ℝ) (s : Fin n → ℝ)
    (ha : 0 ≤ a) (hs : ∀ i, 0 ≤ s i) (hb : a + ∑ i, s i ≤ b) :
    a ^ 2 + ∑ i, (s i) ^ 2 ≤ b ^ 2 := by
  have hsum : 0 ≤ ∑ i, s i := Finset.sum_nonneg (fun i _ => hs i)
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => hs i)
  nlinarith [mul_nonneg ha hsum]

/-- The finite incoming square masses have their exact total after grouping
by an arbitrary recipient assignment, even on an infinite class-label type. -/
theorem hasSum_grouped_source_squares {ι : Type*} {n : ℕ} (κ : Fin n → ι) (s : Fin n → ℝ) :
    HasSum (fun k => ∑ i, if k = κ i then (s i) ^ 2 else 0) (∑ i, (s i) ^ 2) := by
  exact hasSum_sum (fun i _ => hasSum_ite_eq (κ i) ((s i) ^ 2))

/-- Retain the entire countable base reserve and every assigned source
square. Recipient collisions require no injective assignment premise. -/
theorem tsum_square_ge_base_add_sources {ι : Type*} {n : ℕ}
    (a b : ι → ℝ) (κ : Fin n → ι) (s : Fin n → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : ∀ i, 0 ≤ s i)
    (haSum : Summable (fun k => (a k) ^ 2)) (hbSum : Summable (fun k => (b k) ^ 2))
    (hb : ∀ k, a k + (∑ i, if k = κ i then s i else 0) ≤ b k) :
    (∑' k, (a k) ^ 2) + (∑ i, (s i) ^ 2) ≤ ∑' k, (b k) ^ 2 := by
  have hgroup := hasSum_grouped_source_squares κ s
  have hle (k : ι) : (a k) ^ 2 + (∑ i, if k = κ i then (s i) ^ 2 else 0) ≤ (b k) ^ 2 := by
    have h := square_ge_base_add_source_squares (a k) (b k)
      (fun i => if k = κ i then s i else 0) (ha k)
      (fun i => by split_ifs; exact hs i; exact le_rfl) (hb k)
    simpa only [ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
  exact hasSum_le hle (haSum.hasSum.add hgroup) hbSum.hasSum

/-- Optional labels mark diffuse receivers by `none`. Only genuine original
atomic recipients contribute to this grouped atomic-square sum. -/
theorem hasSum_grouped_optional_source_squares {ι : Type*} {n : ℕ}
    (κ : Fin n → Option ι) (s : Fin n → ℝ) :
    HasSum (fun k => ∑ i, if κ i = some k then (s i) ^ 2 else 0)
      (∑ i, if κ i = none then 0 else (s i) ^ 2) := by
  apply hasSum_sum
  intro i _
  cases hi : κ i with
  | none => simp only [reduceCtorEq, ↓reduceIte]; exact hasSum_zero
  | some k =>
      simpa only [Option.some.injEq, reduceCtorEq, ↓reduceIte, eq_comm] using
        (hasSum_ite_eq k ((s i) ^ 2))

/-- Preserve every countable base square while crediting all finite source
squares assigned to actual atomic labels, allowing arbitrary collisions. -/
theorem tsum_square_ge_base_add_optional_sources {ι : Type*} {n : ℕ}
    (a b : ι → ℝ) (κ : Fin n → Option ι) (s : Fin n → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : ∀ i, 0 ≤ s i)
    (haSum : Summable (fun k => (a k) ^ 2)) (hbSum : Summable (fun k => (b k) ^ 2))
    (hb : ∀ k, a k + (∑ i, if κ i = some k then s i else 0) ≤ b k) :
    (∑' k, (a k) ^ 2) + (∑ i, if κ i = none then 0 else (s i) ^ 2) ≤
      ∑' k, (b k) ^ 2 := by
  have hgroup := hasSum_grouped_optional_source_squares κ s
  have hle (k : ι) : (a k) ^ 2 + (∑ i, if κ i = some k then (s i) ^ 2 else 0) ≤
      (b k) ^ 2 := by
    have h := square_ge_base_add_source_squares (a k) (b k)
      (fun i => if κ i = some k then s i else 0) (ha k)
      (fun i => by split_ifs; exact hs i; exact le_rfl) (hb k)
    simpa only [ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
  exact hasSum_le hle (haSum.hasSum.add hgroup) hbSum.hasSum

end Erdos1017.FiniteReceiverReserve

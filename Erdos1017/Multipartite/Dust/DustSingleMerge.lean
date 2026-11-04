module

public import Erdos1017.Multipartite.Dust.DustTwoTypeAveraging

/-!
# Merging one head into existing dust

`mergeOne` averages one completed head with existing dust using a two-type
probability vector, leaving a zero slot; the merged dual stays in the unit box
and is feasible for every new-dust count, and completing one head loses exactly
its self penalty times half its square mass.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Remove one completed head from the retained Boolean selection. -/
def eraseSelection {m : ℕ} (X : Selector.Selection m) (i : Fin m) : Selector.Selection m :=
  fun j => if j = i then false else X j

/-- Average one completed head with existing dust using an actual two-type
probability vector. The removed head slot remains as a zero slot. -/
def mergeOne {m : ℕ} (C : Coefficients m) (i : Fin m) (q : Fin 2 → ℝ) : Coefficients m
  | .inl j => if j = i then 0 else head C j
  | .inr (.inl (j, k)) => if j = i ∨ k = i then 0 else pair C j k
  | .inr (.inr (.inl j)) => if j = i then 0 else
      -(DustCellRestriction.headDual C).beta i j * q 0 + incident C j * q 1
  | .inr (.inr (.inr false)) => head C i * q 0 + linear C * q 1
  | .inr (.inr (.inr true)) =>
      head C i * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2

/-- The merged count charge is precisely the independent two-type average. -/
theorem mergeOne_charge {m : ℕ} (C : Coefficients m) (i : Fin m) (q : Fin 2 → ℝ)
    (X : Selector.Selection m) (k : ℕ) :
    charge (mergeOne C i q) X k =
      objective (fun j => Selector.bit (eraseSelection X i j)) 0 C +
      (k : ℝ) * ((head C i + ∑ j, (DustCellRestriction.headDual C).beta i j *
          Selector.bit (eraseSelection X i j)) * q 0 +
        (linear C - ∑ j, incident C j * Selector.bit (eraseSelection X i j)) * q 1) -
      (k : ℝ) * ((k : ℝ) - 1) *
        (head C i * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2) / 2 := by
  have hhead : (∑ j, head (mergeOne C i q) j * Selector.bit (X j)) =
      ∑ j, head C j * Selector.bit (eraseSelection X i j) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i <;> simp [head, mergeOne, eraseSelection, hj, Selector.bit]
  have hpair : (∑ j, ∑ l, pair (mergeOne C i q) j l * (if j < l then 1 else 0) *
      Selector.bit (X j) * Selector.bit (X l)) =
      ∑ j, ∑ l, pair C j l * (if j < l then 1 else 0) *
        Selector.bit (eraseSelection X i j) * Selector.bit (eraseSelection X i l) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hj : j = i <;> by_cases hl : l = i <;>
      simp [pair, mergeOne, eraseSelection, hj, hl, Selector.bit]
  have hinc : (∑ j, incident (mergeOne C i q) j * Selector.bit (X j)) =
      -(∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (eraseSelection X i j)) * q 0 +
        (∑ j, incident C j * Selector.bit (eraseSelection X i j)) * q 1 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · simp [incident, mergeOne, eraseSelection, hj, Selector.bit]
    · simp only [incident, mergeOne, hj, ↓reduceIte, eraseSelection]
      ring
  unfold charge
  rw [hhead, hpair, hinc]
  simp only [linear, penalty, mergeOne, objective, mul_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_div, sub_zero]
  ring

/-- All merged count constraints are derived from the actual mixed-count
extension and its independent two-type experiment. -/
theorem mergeOne_tests {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (i : Fin m) (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1) :
    ∀ X k, charge (mergeOne C i q) X k ≤ 1 := by
  intro X k
  rw [mergeOne_charge]
  exact single_head_average_test C hC (eraseSelection X i) i
    (by simp [eraseSelection]) q hq₀ hq

/-- The merged coefficients remain in the compact unit box. -/
theorem mergeOne_box {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (i : Fin m) (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1) :
    mergeOne C i q ∈ Set.Icc 0 1 := by
  have hqsum : q 0 + q 1 = 1 := by simpa [Fin.sum_univ_two] using hq
  have hcoef (j : Coordinate m) : 0 ≤ C j ∧ C j ≤ 1 := ⟨hC.1.1 j, hC.1.2 j⟩
  have hb (j : Fin m) : 0 ≤ -(DustCellRestriction.headDual C).beta i j ∧
      -(DustCellRestriction.headDual C).beta i j ≤ 1 := by
    dsimp only [DustCellRestriction.headDual]
    rw [neg_neg]
    split_ifs
    · exact hcoef (.inr (.inl (i, j)))
    · exact hcoef (.inr (.inl (j, i)))
    · norm_num
  have hmix (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
      0 ≤ x * q 0 + y * q 1 ∧ x * q 0 + y * q 1 ≤ 1 := by
    constructor
    · exact add_nonneg (mul_nonneg hx.1 (hq₀ 0)) (mul_nonneg hy.1 (hq₀ 1))
    · nlinarith [mul_le_mul_of_nonneg_right hx.2 (hq₀ 0),
        mul_le_mul_of_nonneg_right hy.2 (hq₀ 1)]
  have ht : 0 ≤ head C i ∧ head C i ≤ 1 := hcoef (.inl i)
  have hc : 0 ≤ incident C i ∧ incident C i ≤ 1 := hcoef (.inr (.inr (.inl i)))
  have hp : 0 ≤ penalty C ∧ penalty C ≤ 1 := hcoef (.inr (.inr (.inr true)))
  have hpen : 0 ≤ head C i * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2 ∧
      head C i * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2 ≤ 1 := by
    constructor
    · exact add_nonneg (add_nonneg (mul_nonneg ht.1 (sq_nonneg _))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.1) (hq₀ 0)) (hq₀ 1)))
        (mul_nonneg hp.1 (sq_nonneg _))
    · have hcross := mul_le_mul_of_nonneg_right hc.2 (mul_nonneg (hq₀ 0) (hq₀ 1))
      have hsumSquare : q 0 ^ 2 + 2 * q 0 * q 1 + q 1 ^ 2 = 1 := by nlinarith [sq_nonneg (q 0 + q 1 - 1)]
      nlinarith [mul_le_mul_of_nonneg_right ht.2 (sq_nonneg (q 0)),
        mul_le_mul_of_nonneg_right hp.2 (sq_nonneg (q 1))]
  have hall (j : Coordinate m) : 0 ≤ mergeOne C i q j ∧ mergeOne C i q j ≤ 1 := by
    rcases j with j | (⟨j, l⟩ | (j | b))
    · dsimp only [mergeOne]
      split_ifs
      · norm_num
      · exact hcoef (.inl j)
    · dsimp only [mergeOne]
      split_ifs
      · norm_num
      · exact hcoef (.inr (.inl (j, l)))
    · dsimp only [mergeOne]
      split_ifs
      · norm_num
      · exact hmix _ _ (hb j) (hcoef (.inr (.inr (.inl j))))
    · cases b
      · exact hmix _ _ ht (hcoef (.inr (.inr (.inr false))))
      · exact hpen
  exact ⟨fun j => (hall j).1, fun j => (hall j).2⟩

/-- A genuine feasible homogeneous dual after completing one old head into
pre-existing dust. Every natural new-dust count is covered. -/
theorem mergeOne_feasible {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (i : Fin m) (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1) :
    mergeOne C i q ∈ feasible m :=
  ⟨mergeOne_box C hC i q hq₀ hq, mergeOne_tests C hC i q hq₀ hq⟩

/-- Separate the head-only objective from all existing-dust interactions. -/
theorem objective_dust_split {m : ℕ} (C : Coefficients m) (p : Fin m → ℝ) (s : ℝ) :
    objective p s C = Selector.objective p (DustCellRestriction.headDual C) +
      s * (linear C - ∑ j, incident C j * p j) - penalty C * s ^ 2 / 2 := by
  rw [DustCellRestriction.headDual_objective]
  unfold objective
  rw [← Finset.sum_mul]
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_div, sub_zero]
  ring

/-- Exact averaged objective on retained masses, with the completed slot zero. -/
theorem mergeOne_objective {m : ℕ} (C : Coefficients m) (i : Fin m) (q : Fin 2 → ℝ)
    (p : Fin m → ℝ) (hpi : p i = 0) (s : ℝ) :
    objective p s (mergeOne C i q) = objective p 0 C +
      s * ((head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * p j) * q 0 +
        (linear C - ∑ j, incident C j * p j) * q 1) -
      (head C i * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2) * s ^ 2 / 2 := by
  have hh : (∑ j, head (mergeOne C i q) j * p j) = ∑ j, head C j * p j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i <;> simp [head, mergeOne, hj, hpi]
  have hp : (∑ j, ∑ l, pair (mergeOne C i q) j l * (if j < l then 1 else 0) * p j * p l) =
      ∑ j, ∑ l, pair C j l * (if j < l then 1 else 0) * p j * p l := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hj : j = i <;> by_cases hl : l = i <;> simp [pair, mergeOne, hj, hl, hpi]
  have hc : (∑ j, incident (mergeOne C i q) j * p j) =
      -(∑ j, (DustCellRestriction.headDual C).beta i j * p j) * q 0 +
        (∑ j, incident C j * p j) * q 1 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · simp [incident, mergeOne, hj, hpi]
    · simp only [incident, mergeOne, hj, ↓reduceIte]
      ring
  unfold objective
  rw [hh, hp, ← Finset.sum_mul, hc]
  simp only [linear, penalty, mergeOne, mul_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_div, sub_zero]
  ring

/-- Adding one old head isolates its row against retained heads and old dust. -/
theorem objective_add_head {m : ℕ} (C : Coefficients m) (i : Fin m)
    (p : Fin m → ℝ) (hpi : p i = 0) (x s : ℝ) :
    objective (Function.update p i x) s C = objective p 0 C +
      x * (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * p j) +
      s * (linear C - ∑ j, incident C j * p j) - incident C i * x * s - penalty C * s ^ 2 / 2 := by
  have hc : (∑ j, incident C j * Function.update p i x j) =
      (∑ j, incident C j * p j) + incident C i * x := by
    have ht (j : Fin m) : incident C j * Function.update p i x j =
        incident C j * p j + if j = i then incident C i * x else 0 := by
      by_cases hj : j = i <;> simp [hj, Function.update_of_ne, hpi]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  rw [objective_dust_split, Selector.objective_update, hc, hpi, sub_zero,
    DustCellRestriction.headDual_objective]
  simp only [show (DustCellRestriction.headDual C).alpha = head C from rfl]
  ring

/-- Completing one old head loses exactly its default self penalty times
half its square mass; the pre-existing dust contributes no extra loss. -/
theorem mergeOne_loss {m : ℕ} (C : Coefficients m) (i : Fin m) (q : Fin 2 → ℝ)
    (p : Fin m → ℝ) (hpi : p i = 0) (s : ℝ) :
    objective (Function.update p i (s * q 0)) (s * q 1) C -
      objective p s (mergeOne C i q) = head C i * (s * q 0) ^ 2 / 2 := by
  rw [objective_add_head C i p hpi, mergeOne_objective C i q p hpi]
  ring

theorem objective_le_value {m : ℕ} (p : Fin m → ℝ) (s : ℝ)
    (C : Coefficients m) (hC : C ∈ feasible m) : objective p s C ≤ value p s := by
  exact le_csSup ((feasible_isCompact m).image (objective_continuous p s)).bddAbove ⟨C, hC, rfl⟩

/-- Completing one head into existing dust loses at most half its square mass,
including the zero-total-mass boundary case. -/
theorem value_le_single_merge {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (i : Fin m)
    (hpi : 0 ≤ p i) (hs : 0 ≤ s) :
    value p s ≤ value (Function.update p i 0) (s + p i) + (p i) ^ 2 / 2 := by
  by_cases hT : s + p i = 0
  · have hi : p i = 0 := by linarith
    have hs0 : s = 0 := by linarith
    have hup : Function.update p i 0 = p := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [hi]
      · simp [hj]
    simp [hi, hs0, hup]
  · have hTpos : 0 < s + p i := lt_of_le_of_ne (add_nonneg hs hpi) (Ne.symm hT)
    let q : Fin 2 → ℝ := fun j => if j = 0 then p i / (s + p i) else s / (s + p i)
    have hq₀ (j : Fin 2) : 0 ≤ q j := by
      dsimp only [q]
      split_ifs <;> positivity
    have hq : ∑ j, q j = 1 := by
      simp only [Fin.sum_univ_two, q]
      norm_num
      field_simp
      ring
    have hx : (s + p i) * q 0 = p i := by
      dsimp only [q]
      simp only [↓reduceIte]
      field_simp
    have hy : (s + p i) * q 1 = s := by
      dsimp only [q]
      norm_num
      field_simp
    obtain ⟨C, hC, hvalue⟩ := exists_value_eq p s
    have hloss := mergeOne_loss C i q (Function.update p i 0) (by simp) (s + p i)
    rw [hx, hy] at hloss
    have hpback : Function.update (Function.update p i 0) i (p i) = p := by
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · simp [hj]
    rw [hpback] at hloss
    have hbound := objective_le_value (Function.update p i 0) (s + p i)
      (mergeOne C i q) (mergeOne_feasible C hC i q hq₀ hq)
    have ht : head C i ≤ 1 := hC.1.2 (.inl i)
    have hsquare := mul_le_mul_of_nonneg_right ht (sq_nonneg (p i))
    rw [hvalue]
    linarith

end Erdos1017.MultipartiteDust

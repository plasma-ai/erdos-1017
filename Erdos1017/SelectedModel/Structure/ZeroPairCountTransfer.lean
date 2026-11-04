module

public import Erdos1017.LowerBound.Repeat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

/-!
# Moving counts off zero pairs

This module defines the finite charge polynomial `countCharge` with strict
support and the moves of a pair's count onto one endpoint, and shows that every
finite count vector has a same-total strict-support vector with at least its
charge, so fixed-total tests on strict cross support bound every count vector.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.ZeroPairCount

variable {n : ℕ}

/-- The finite charge polynomial, with each unordered cross term counted once.
The diagonal coefficient may have either sign. -/
def countCharge (h ell : ℝ) (x δ : Fin n → ℝ) (M : Fin n → Fin n → ℝ)
    (k : Fin n → ℕ) : ℝ :=
  h + (∑ i, x i * (k i : ℝ)) +
    (∑ i, (δ i - ell) * Repeat.pairs (k i)) +
    ∑ i, ∑ j, if i < j then (M i j - ell) * (k i : ℝ) * (k j : ℝ) else 0

/-- The occupied types have strictly positive cross entries. -/
def strictSupport (M : Fin n → Fin n → ℝ) (k : Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → 0 < k i → 0 < k j → 0 < M i j

/-- Number of occupied types in a finite count vector. -/
def occupiedCount (k : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun i => 0 < k i).card

/-- Move the whole count of a pair onto its first type. -/
def moveLeft (k : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  fun a => if a = i then k i + k j else if a = j then 0 else k a

/-- Move the whole count of a pair onto its second type. -/
def moveRight (k : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  fun a => if a = i then 0 else if a = j then k i + k j else k a

private theorem moveLeft_total (k : Fin n → ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∑ a, moveLeft k i j a) = ∑ a, k a := by
  classical
  have hjmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hrest : (∑ a ∈ (Finset.univ.erase i).erase j, moveLeft k i j a) =
      ∑ a ∈ (Finset.univ.erase i).erase j, k a := by
    apply Finset.sum_congr rfl
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    have haj : a ≠ j := (Finset.mem_erase.mp ha).1
    simp [moveLeft, hai, haj]
  calc
    (∑ a, moveLeft k i j a) = moveLeft k i j i +
        (moveLeft k i j j + ∑ a ∈ (Finset.univ.erase i).erase j, moveLeft k i j a) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase (Finset.univ.erase i) _ hjmem]
    _ = k i + (k j + ∑ a ∈ (Finset.univ.erase i).erase j, k a) := by
      rw [hrest]
      simp [moveLeft, hij.symm]
      omega
    _ = ∑ a, k a := by
      rw [Finset.add_sum_erase (Finset.univ.erase i) _ hjmem,
        Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]

private theorem moveLeft_occupied (k : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hi : 0 < k i) (hj : 0 < k j) :
    occupiedCount (moveLeft k i j) < occupiedCount k := by
  classical
  have hfilter : (Finset.univ.filter fun a => 0 < moveLeft k i j a) =
      (Finset.univ.filter fun a => 0 < k a).erase j := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hai : a = i
    · subst a
      simp [moveLeft, hij, hi, hj]
    by_cases haj : a = j
    · subst a
      simp [moveLeft, hij.symm]
    · simp [moveLeft, hai, haj]
  unfold occupiedCount
  rw [hfilter]
  apply Finset.card_erase_lt_of_mem
  simp [hj]

private theorem moveRight_eq_moveLeft_swap (k : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) : moveRight k i j = moveLeft k j i := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [moveRight, moveLeft, hij]
  by_cases haj : a = j
  · subst a
    simp [moveRight, moveLeft, hij.symm, Nat.add_comm]
  · simp [moveRight, moveLeft, hai, haj]

private theorem moveRight_total (k : Fin n → ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∑ a, moveRight k i j a) = ∑ a, k a := by
  rw [moveRight_eq_moveLeft_swap k i j hij]
  exact moveLeft_total k j i hij.symm

private theorem moveRight_occupied (k : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hi : 0 < k i) (hj : 0 < k j) :
    occupiedCount (moveRight k i j) < occupiedCount k := by
  rw [moveRight_eq_moveLeft_swap k i j hij]
  exact moveLeft_occupied k j i hij.symm hj hi

private def realPairs (t : ℝ) : ℝ := t * (t - 1) / 2

private def realCharge (h ell : ℝ) (x δ : Fin n → ℝ) (M : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) : ℝ :=
  h + (∑ i, x i * v i) +
    (∑ i, (δ i - ell) * realPairs (v i)) +
    ∑ i, ∑ j, if i < j then (M i j - ell) * v i * v j else 0

private def realMoveLeft (v : Fin n → ℝ) (i j : Fin n) : Fin n → ℝ :=
  fun a => if a = i then v i + v j else if a = j then 0 else v a

private def realMoveRight (v : Fin n → ℝ) (i j : Fin n) : Fin n → ℝ :=
  fun a => if a = i then 0 else if a = j then v i + v j else v a

private theorem realCharge_nat (h ell : ℝ) (x δ : Fin n → ℝ)
    (M : Fin n → Fin n → ℝ) (k : Fin n → ℕ) :
    realCharge h ell x δ M (fun i => (k i : ℝ)) = countCharge h ell x δ M k := by
  simp only [realCharge, countCharge, Repeat.pairs, realPairs]

private theorem realMoveLeft_nat (k : Fin n → ℕ) (i j : Fin n) :
    realMoveLeft (fun a => (k a : ℝ)) i j = fun a => (moveLeft k i j a : ℝ) := by
  funext a
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [realMoveLeft, moveLeft, hai, haj]

private theorem realMoveRight_nat (k : Fin n → ℕ) (i j : Fin n) :
    realMoveRight (fun a => (k a : ℝ)) i j = fun a => (moveRight k i j a : ℝ) := by
  funext a
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [realMoveRight, moveRight, hai, haj]

private theorem linear_chord_term (x v : Fin n → ℝ) {i j u : Fin n} :
    v i * (x u * realMoveLeft v i j u) +
      v j * (x u * realMoveRight v i j u) -
      (v i + v j) * (x u * v u) = 0 := by
  by_cases hui : u = i
  · subst u
    simp [realMoveLeft, realMoveRight]
    ring
  by_cases huj : u = j
  · subst u
    simp [realMoveLeft, realMoveRight, hui]
    ring
  simp [realMoveLeft, realMoveRight, hui, huj]
  ring

private theorem diagonal_chord_term (ell : ℝ) (δ v : Fin n → ℝ)
    {i j u : Fin n} :
    v i * ((δ u - ell) * realPairs (realMoveLeft v i j u)) +
      v j * ((δ u - ell) * realPairs (realMoveRight v i j u)) -
      (v i + v j) * ((δ u - ell) * realPairs (v u)) =
        if u = i then (δ i - ell) * (v i + v j) * v i * v j / 2
        else if u = j then (δ j - ell) * (v i + v j) * v i * v j / 2 else 0 := by
  by_cases hui : u = i
  · subst u
    simp [realMoveLeft, realMoveRight, realPairs]
    ring
  by_cases huj : u = j
  · subst u
    simp [realMoveLeft, realMoveRight, hui, realPairs]
    ring
  simp [realMoveLeft, realMoveRight, hui, huj]
  ring

private theorem cross_chord_term (ell : ℝ) (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    {i j u w : Fin n} (hij : i < j) (hM : M i j = 0) :
    v i * (if u < w then (M u w - ell) * realMoveLeft v i j u * realMoveLeft v i j w else 0) +
      v j * (if u < w then (M u w - ell) * realMoveRight v i j u * realMoveRight v i j w else 0) -
      (v i + v j) * (if u < w then (M u w - ell) * v u * v w else 0) =
        if u = i ∧ w = j then ell * (v i + v j) * v i * v j else 0 := by
  by_cases huw : u < w
  · by_cases hui : u = i
    all_goals by_cases huj : u = j
    all_goals by_cases hwi : w = i
    all_goals by_cases hwj : w = j
    all_goals
      first | omega | (simp_all [realMoveLeft, realMoveRight]; ring)
  · have hnot : ¬(u = i ∧ w = j) := by
      rintro ⟨rfl, rfl⟩
      exact huw hij
    simp [huw, hnot]

private theorem realCharge_chord_identity (h ell : ℝ) (x δ : Fin n → ℝ)
    (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    {i j : Fin n} (hij : i < j) (hM : M i j = 0) :
    v i * realCharge h ell x δ M (realMoveLeft v i j) +
      v j * realCharge h ell x δ M (realMoveRight v i j) -
      (v i + v j) * realCharge h ell x δ M v =
        (v i + v j) * v i * v j * (δ i + δ j) / 2 := by
  have hlin : v i * (∑ u, x u * realMoveLeft v i j u) +
      v j * (∑ u, x u * realMoveRight v i j u) -
      (v i + v j) * (∑ u, x u * v u) = 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro u _
    exact linear_chord_term x v
  have hdiag : v i * (∑ u, (δ u - ell) * realPairs (realMoveLeft v i j u)) +
      v j * (∑ u, (δ u - ell) * realPairs (realMoveRight v i j u)) -
      (v i + v j) * (∑ u, (δ u - ell) * realPairs (v u)) =
        (δ i - ell) * (v i + v j) * v i * v j / 2 +
          (δ j - ell) * (v i + v j) * v i * v j / 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    simp_rw [diagonal_chord_term ell δ v]
    have hsplit (u : Fin n) :
        (if u = i then (δ i - ell) * (v i + v j) * v i * v j / 2
          else if u = j then (δ j - ell) * (v i + v j) * v i * v j / 2 else 0) =
        (if u = i then (δ i - ell) * (v i + v j) * v i * v j / 2 else 0) +
          (if u = j then (δ j - ell) * (v i + v j) * v i * v j / 2 else 0) := by
      by_cases hui : u = i <;> simp [hui, ne_of_lt hij]
    simp_rw [hsplit]
    simp only [Finset.sum_add_distrib]
    simp
  have hcross : v i * (∑ u, ∑ w,
      if u < w then (M u w - ell) * realMoveLeft v i j u * realMoveLeft v i j w else 0) +
      v j * (∑ u, ∑ w,
      if u < w then (M u w - ell) * realMoveRight v i j u * realMoveRight v i j w else 0) -
      (v i + v j) * (∑ u, ∑ w,
      if u < w then (M u w - ell) * v u * v w else 0) =
        ell * (v i + v j) * v i * v j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    simp_rw [cross_chord_term ell M v hij hM]
    have hnested (u w : Fin n) :
        (if u = i ∧ w = j then ell * (v i + v j) * v i * v j else 0) =
          if u = i then (if w = j then ell * (v i + v j) * v i * v j else 0) else 0 := by
      by_cases hui : u = i <;> by_cases hwj : w = j <;> simp [hui, hwj]
    simp_rw [hnested]
    simp
  unfold realCharge
  linear_combination hlin + hdiag + hcross

/-- An occupied zero pair can be moved entirely to one endpoint without
lowering the exact finite charge. Signed diagonal charge is allowed. -/
theorem countCharge_le_moveLeft_or_moveRight (h ell : ℝ) (x δ : Fin n → ℝ)
    (M : Fin n → Fin n → ℝ) (k : Fin n → ℕ) {i j : Fin n}
    (hij : i < j) (hki : 0 < k i) (hkj : 0 < k j)
    (hM : M i j = 0) (hδi : 0 ≤ δ i) (hδj : 0 ≤ δ j) :
    countCharge h ell x δ M k ≤ countCharge h ell x δ M (moveLeft k i j) ∨
      countCharge h ell x δ M k ≤ countCharge h ell x δ M (moveRight k i j) := by
  let a : ℝ := k i
  let b : ℝ := k j
  have ha : 0 < a := by dsimp [a]; exact_mod_cast hki
  have hb : 0 < b := by dsimp [b]; exact_mod_cast hkj
  have hδ : 0 ≤ δ i + δ j := add_nonneg hδi hδj
  have hchord := realCharge_chord_identity h ell x δ M (fun t => (k t : ℝ)) hij hM
  rw [realMoveLeft_nat, realMoveRight_nat, realCharge_nat, realCharge_nat,
    realCharge_nat] at hchord
  change a * countCharge h ell x δ M (moveLeft k i j) +
      b * countCharge h ell x δ M (moveRight k i j) -
      (a + b) * countCharge h ell x δ M k =
        (a + b) * a * b * (δ i + δ j) / 2 at hchord
  have hnonneg : 0 ≤ (a + b) * a * b * (δ i + δ j) / 2 := by positivity
  by_cases hleft : countCharge h ell x δ M k ≤ countCharge h ell x δ M (moveLeft k i j)
  · exact Or.inl hleft
  right
  have hleft' : countCharge h ell x δ M (moveLeft k i j) < countCharge h ell x δ M k :=
    lt_of_not_ge hleft
  by_contra hright
  have hright' : countCharge h ell x δ M (moveRight k i j) < countCharge h ell x δ M k :=
    lt_of_not_ge hright
  nlinarith

/-- Eliminate one occupied zero pair while preserving the integer total. -/
theorem exists_zero_pair_move (h ell : ℝ) (x δ : Fin n → ℝ)
    (M : Fin n → Fin n → ℝ) (k : Fin n → ℕ) {i j : Fin n}
    (hij : i < j) (hki : 0 < k i) (hkj : 0 < k j)
    (hM : M i j = 0) (hδi : 0 ≤ δ i) (hδj : 0 ≤ δ j) :
    ∃ k' : Fin n → ℕ, (∑ a, k' a) = ∑ a, k a ∧
      occupiedCount k' < occupiedCount k ∧
      countCharge h ell x δ M k ≤ countCharge h ell x δ M k' := by
  rcases countCharge_le_moveLeft_or_moveRight h ell x δ M k hij hki hkj hM hδi hδj with
    hleft | hright
  · exact ⟨moveLeft k i j, moveLeft_total k i j (ne_of_lt hij),
      moveLeft_occupied k i j (ne_of_lt hij) hki hkj, hleft⟩
  · exact ⟨moveRight k i j, moveRight_total k i j (ne_of_lt hij),
      moveRight_occupied k i j (ne_of_lt hij) hki hkj, hright⟩

/-- Failure of strict support exposes an occupied zero cross entry. -/
private theorem exists_zero_pair_of_not_strictSupport (M : Fin n → Fin n → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (hM : ∀ i j, i ≠ j → 0 ≤ M i j) (k : Fin n → ℕ)
    (hnot : ¬strictSupport M k) :
    ∃ i j : Fin n, i < j ∧ 0 < k i ∧ 0 < k j ∧ M i j = 0 := by
  unfold strictSupport at hnot
  push Not at hnot
  obtain ⟨i, j, hij, hi, hj, hnotpos⟩ := hnot
  have hz : M i j = 0 := le_antisymm hnotpos (hM i j hij)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, hi, hj, hz⟩
  · exact ⟨j, i, hgt, hj, hi, (hSym j i).trans hz⟩

/-- Every finite count vector has a same-total strict-support vector with
at least its charge. No sign restriction is placed on the diagonal charge. -/
theorem exists_strictSupport_countCharge_ge (h ell : ℝ) (x δ : Fin n → ℝ)
    (M : Fin n → Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hSym : ∀ i j, M i j = M j i)
    (hM : ∀ i j, i ≠ j → 0 ≤ M i j) (k : Fin n → ℕ) :
    ∃ k' : Fin n → ℕ, (∑ i, k' i) = ∑ i, k i ∧ strictSupport M k' ∧
      countCharge h ell x δ M k ≤ countCharge h ell x δ M k' := by
  suffices hresult : ∀ q : ℕ, ∀ k : Fin n → ℕ, occupiedCount k = q →
      ∃ k' : Fin n → ℕ, (∑ i, k' i) = ∑ i, k i ∧ strictSupport M k' ∧
        countCharge h ell x δ M k ≤ countCharge h ell x δ M k' from
    hresult (occupiedCount k) k rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro k hk
    by_cases hstrict : strictSupport M k
    · exact ⟨k, rfl, hstrict, le_rfl⟩
    obtain ⟨i, j, hij, hi, hj, hz⟩ := exists_zero_pair_of_not_strictSupport M hSym hM k hstrict
    obtain ⟨k₁, htotal, hsmaller, hcharge⟩ :=
      exists_zero_pair_move h ell x δ M k hij hi hj hz (hδ i) (hδ j)
    obtain ⟨k', htotal', hsupport', hcharge'⟩ := ih (occupiedCount k₁) (by omega) k₁ rfl
    exact ⟨k', htotal'.trans htotal, hsupport', hcharge.trans hcharge'⟩

/-- Fixed-total tests on strict-positive cross support bound every count
vector of that same total, including those with occupied zero pairs. -/
theorem countCharge_le_of_strictSupport (h ell : ℝ) (x δ : Fin n → ℝ)
    (M : Fin n → Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hSym : ∀ i j, M i j = M j i)
    (hM : ∀ i j, i ≠ j → 0 ≤ M i j) (K : ℕ)
    (hbound : ∀ k : Fin n → ℕ, (∑ i, k i) = K → strictSupport M k →
      countCharge h ell x δ M k ≤ 1)
    (k : Fin n → ℕ) (htotal : (∑ i, k i) = K) :
    countCharge h ell x δ M k ≤ 1 := by
  obtain ⟨k', htotal', hsupport, hcharge⟩ :=
    exists_strictSupport_countCharge_ge h ell x δ M hδ hSym hM k
  exact hcharge.trans (hbound k' (htotal'.trans htotal) hsupport)

end Erdos1017.ZeroPairCount

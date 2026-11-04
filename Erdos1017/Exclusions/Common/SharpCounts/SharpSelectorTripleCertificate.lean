module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Triple certificate for the centered sharp selector

This module defines the weighted sum over ordered triples of distinct labels and
shows that centered null rows turn the distinct-triple test into an explicit
nonnegative-diagonal identity, so positive occupied triples and nonnegative
centered diagonals exclude an intercept greater than one.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical

namespace Erdos1017.Selector.Sharp

variable {ι : Type*} [Fintype ι]

/-- Ordered triples of distinct labels, with their actual product weights. -/
def tripleSum (p : ι → ℝ) (F : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if i ≠ j ∧ i ≠ k ∧ j ≠ k then p i * p j * p k * F i j k else 0

private theorem sum_excluding_two (p : ι → ℝ) (hs : ∑ i, p i = 2)
    {i j : ι} (hij : i ≠ j) :
    (∑ k, if i ≠ k ∧ j ≠ k then p k else 0) = 2 - p i - p j := by
  have ht (k : ι) : (if i ≠ k ∧ j ≠ k then p k else 0) =
      p k - (if k = i then p i else 0) - (if k = j then p j else 0) := by
    by_cases hi : k = i
    · subst k
      simp [hij]
    by_cases hj : k = j
    · subst k
      simp [hij, Ne.symm hij]
    simp [hi, hj, Ne.symm hi, Ne.symm hj]
  simp_rw [ht, Finset.sum_sub_distrib]
  simp [hs]

private theorem tripleSum_first_pair (p : ι → ℝ) (hs : ∑ i, p i = 2)
    (K : ι → ι → ℝ) :
    tripleSum p (fun i j _ => K i j) =
      ∑ i, ∑ j, if i ≠ j then p i * p j * K i j * (2 - p i - p j) else 0 := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · have ht (k : ι) :
        (if i ≠ j ∧ i ≠ k ∧ j ≠ k then p i * p j * p k * K i j else 0) =
          (p i * p j * K i j) * (if i ≠ k ∧ j ≠ k then p k else 0) := by
      split_ifs <;> simp_all
      ring
    simp_rw [ht]
    rw [← Finset.mul_sum, sum_excluding_two p hs hij, ite_eq_left hij]

private theorem offDiagonal_zero_rows (p : ι → ℝ) (K : ι → ι → ℝ)
    (hsym : ∀ i j, K i j = K j i) (hrow : ∀ i, ∑ j, p j * K i j = 0) :
    (∑ i, ∑ j, if i ≠ j then p i * p j * K i j * (2 - p i - p j) else 0) =
      -2 * ∑ i, (p i) ^ 2 * (1 - p i) * K i i := by
  have hcol (j : ι) : ∑ i, p i * K i j = 0 := by
    simpa only [hsym] using hrow j
  have hfull : (∑ i, ∑ j, p i * p j * K i j * (2 - p i - p j)) = 0 := by
    have ht (i j : ι) : p i * p j * K i j * (2 - p i - p j) =
        (2 * p i - (p i) ^ 2) * (p j * K i j) - (p j) ^ 2 * (p i * K i j) := by ring
    simp_rw [ht, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, mul_zero]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_zero]
    simp
  have ht (i j : ι) : (if i ≠ j then p i * p j * K i j * (2 - p i - p j) else 0) =
      p i * p j * K i j * (2 - p i - p j) -
        (if j = i then 2 * (p i) ^ 2 * (1 - p i) * K i i else 0) := by
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij, Ne.symm hij]
  simp_rw [ht, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hfull]
  simp_rw [show ∀ i, 2 * (p i) ^ 2 * (1 - p i) * K i i =
    2 * ((p i) ^ 2 * (1 - p i) * K i i) by intro i; ring, ← Finset.mul_sum]
  ring

private theorem tripleSum_permute (p : ι → ℝ) (K : ι → ι → ℝ) :
    tripleSum p (fun i _ k => K i k) = tripleSum p (fun i j _ => K i j) ∧
      tripleSum p (fun _ j k => K j k) = tripleSum p (fun i j _ => K i j) := by
  constructor
  · unfold tripleSum
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases hij : i = j
    · subst j
      simp
    by_cases hik : i = k
    · subst k
      simp
    by_cases hjk : j = k
    · subst k
      simp
    rw [ite_eq_left ⟨hik, hij, Ne.symm hjk⟩, ite_eq_left ⟨hij, hik, hjk⟩]
    ring
  · unfold tripleSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i = j
    · subst j
      simp
    by_cases hik : i = k
    · subst k
      simp
    by_cases hjk : j = k
    · subst k
      simp
    rw [ite_eq_left ⟨hij, hik, hjk⟩, ite_eq_left ⟨hjk, Ne.symm hij, Ne.symm hik⟩]
    ring

/-- Centered null rows turn the weighted distinct-triple test into an
explicit nonnegative-diagonal certificate, an exact finite identity that
assumes no positive semidefiniteness. -/
theorem tripleSum_centered_identity (p : ι → ℝ) (hs : ∑ i, p i = 2)
    (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j, p j * K i j = 0) (L : ℝ) :
    tripleSum p (fun i j k => 3 * L - 3 - 2 * (K i j + K i k + K j k)) =
      (3 * L - 3) * tripleSum p (fun _ _ _ => 1) +
        12 * ∑ i, (p i) ^ 2 * (1 - p i) * K i i := by
  have he : tripleSum p (fun i j k => 3 * L - 3 - 2 * (K i j + K i k + K j k)) =
      (3 * L - 3) * tripleSum p (fun _ _ _ => 1) -
        2 * (tripleSum p (fun i j _ => K i j) + tripleSum p (fun i _ k => K i k) +
          tripleSum p (fun _ j k => K j k)) := by
    unfold tripleSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  rw [he, (tripleSum_permute p K).1, (tripleSum_permute p K).2,
    tripleSum_first_pair p hs K, offDiagonal_zero_rows p K hsym hrow]
  ring

/-- Positive occupied triples and nonnegative centered diagonals exclude
an intercept greater than one. Later maximization supplies these finite
certificate hypotheses from actual Boolean feasibility. -/
theorem centered_intercept_le_one (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hs : ∑ i, p i = 2)
    (K : ι → ι → ℝ) (hsym : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j, p j * K i j = 0)
    (hdiag : ∀ i, 0 < p i → 0 ≤ K i i) (L : ℝ)
    (htest : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      0 < p i → 0 < p j → 0 < p k → 3 * L - 3 - 2 * (K i j + K i k + K j k) ≤ 0)
    (htriple : ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ 0 < p i ∧ 0 < p j ∧ 0 < p k) :
    L ≤ 1 := by
  have hweight (i j k : ι) : 0 ≤ p i * p j * p k :=
    mul_nonneg (mul_nonneg (hp i).1 (hp j).1) (hp k).1
  have hnonneg (i j k : ι) :
      0 ≤ if i ≠ j ∧ i ≠ k ∧ j ≠ k then p i * p j * p k * 1 else 0 := by
    split_ifs
    · simpa only [mul_one] using hweight i j k
    · exact le_rfl
  have hmass : 0 < tripleSum p (fun _ _ _ => 1) := by
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := htriple
    have hterm : 0 < p i * p j * p k * 1 := by positivity
    apply hterm.trans_le
    unfold tripleSum
    calc
      p i * p j * p k * 1 =
          (if i ≠ j ∧ i ≠ k ∧ j ≠ k then p i * p j * p k * 1 else 0) := by simp [hij, hik, hjk]
      _ ≤ ∑ k, if i ≠ j ∧ i ≠ k ∧ j ≠ k then p i * p j * p k * 1 else 0 :=
        Finset.single_le_sum (fun k _ => hnonneg i j k) (Finset.mem_univ k)
      _ ≤ ∑ j, ∑ k, if i ≠ j ∧ i ≠ k ∧ j ≠ k then p i * p j * p k * 1 else 0 :=
        Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ => hnonneg i j k))
          (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hnonneg i j k)))
        (Finset.mem_univ i)
  have hsum : tripleSum p (fun i j k => 3 * L - 3 - 2 * (K i j + K i k + K j k)) ≤ 0 := by
    unfold tripleSum
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    apply Finset.sum_nonpos
    intro k _
    split_ifs with h
    · by_cases hi : 0 < p i
      · by_cases hj : 0 < p j
        · by_cases hk : 0 < p k
          · exact mul_nonpos_of_nonneg_of_nonpos (hweight i j k)
              (htest i j k h.1 h.2.1 h.2.2 hi hj hk)
          · have hk0 : p k = 0 := le_antisymm (le_of_not_gt hk) (hp k).1
            simp [hk0]
        · have hj0 : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j).1
          simp [hj0]
      · have hi0 : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i).1
        simp [hi0]
    · exact le_rfl
  have hdiagSum : 0 ≤ ∑ i, (p i) ^ 2 * (1 - p i) * K i i := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : 0 < p i
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hp i).2)) (hdiag i hi)
    · have hi0 : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i).1
      simp [hi0]
  rw [tripleSum_centered_identity p hs K hsym hrow] at hsum
  nlinarith

end Erdos1017.Selector.Sharp

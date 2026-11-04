module

public import Erdos1017.Exclusions.Common.Physical.PhysicalCoverCancellation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Shape of saturated tight parents

Saturated tightness forces every pair outside the two saturated endpoints to
have zero charge, and strict negativity of every outside-root edge leaves at
most one coordinate outside a tight saturated pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.PhysicalPrimal.SaturatedParent

private theorem sum_pairIndex_eq_double {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, Y i i = 0) :
    (∑ ij : PairIndex n, Y ij.val.1 ij.val.2) = ∑ i, ∑ j, Y i j := by
  classical
  have h : (∑ ab ∈ Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2), Y ab.1 ab.2) =
      ∑ ab : PairIndex n, Y ab.val.1 ab.val.2 := Finset.sum_subtype (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
    (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)) (by simp)
    (fun ij => Y ij.1 ij.2)
  rw [Finset.sum_filter] at h
  rw [← h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij, hdiag]
  · simp [hij]

/-- Saturated tightness forces every pair outside the two saturated
endpoints to have zero charge. The argument uses only actual finite
triangle inequalities and the nonpositive body. -/
theorem body_pairs_zero {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Y i j = Y j i) (i j : Fin n) (hij : i ≠ j)
    (hsat : Y i j = 1)
    (hbody : ∀ a b, a ≠ b → a ≠ i → b ≠ i → Y a b ≤ 0)
    (htriangle : ∀ k, k ≠ i → k ≠ j → Y i k + Y j k ≤ 0)
    (htight : (∑ ab : PairIndex n, Y ab.val.1 ab.val.2) = 2) :
    ∀ k l, k ≠ l → k ≠ i → k ≠ j → l ≠ i → l ≠ j → Y k l = 0 := by
  classical
  let w (k : Fin n) : ℝ := if k = i ∨ k = j then 0 else Y i k
  let Z (a b : Fin n) : ℝ :=
    (if a = i then (if b = j then 1 else 0) else 0) +
    (if a = j then (if b = i then 1 else 0) else 0) +
    (if a = i then w b else 0) + (if b = i then w a else 0) -
    (if a = j then w b else 0) - (if b = j then w a else 0)
  have hwi : w i = 0 := by simp [w]
  have hwj : w j = 0 := by simp [w]
  have hdiag (a : Fin n) : Z a a = 0 := by
    by_cases hai : a = i
    · subst a
      simp [Z, hij, hwi]
    · by_cases haj : a = j
      · subst a
        simp [Z, hij.symm, hwj]
      · simp [Z, hai, haj]
  have hZsum : (∑ ab : PairIndex n, Z ab.val.1 ab.val.2) = 2 := by
    rw [sum_pairIndex_eq_double Z hdiag]
    simp [Z, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    norm_num
  have hbound (a b : Fin n) (hab : a ≠ b) : Y a b ≤ Z a b := by
    by_cases hai : a = i
    · subst a
      by_cases hbj : b = j
      · subst b
        simp [Z, hij, hij.symm, hwi, hwj, hsat]
      · have hbi := hab.symm
        simp [Z, hij, hbi, hbj, w]
    · by_cases hbi : b = i
      · subst b
        by_cases haj : a = j
        · subst a
          simp [Z, hij, hij.symm, hwi, hwj, ← hsym i j, hsat]
        · simp [Z, hai, haj, hij, w, hsym a i]
      · by_cases haj : a = j
        · subst a
          have hbj := hab.symm
          have ht := htriangle b hbi hbj
          simp [Z, hij.symm, hbi, hbj, w]
          linarith
        · by_cases hbj : b = j
          · subst b
            have ht := htriangle a hai haj
            have hy := hsym a j
            simp [Z, hij.symm, hai, haj, w]
            linarith
          · simpa [Z, hai, hbi, haj, hbj] using hbody a b hab hai hbi
  have heq : ∀ ab : PairIndex n, Y ab.val.1 ab.val.2 = Z ab.val.1 ab.val.2 := by
    have h := (Finset.sum_eq_sum_iff_of_le
      (fun ab (_ : ab ∈ (Finset.univ : Finset (PairIndex n))) =>
        hbound ab.val.1 ab.val.2 ab.property)).mp (htight.trans hZsum.symm)
    exact fun ab => h ab (Finset.mem_univ _)
  intro k l hkl hki hkj hli hlj
  have he := heq ⟨(k, l), hkl⟩
  simpa [Z, hki, hkj, hli, hlj] using he

/-- Strict negativity of every outside-root edge leaves at most one
coordinate outside a tight saturated pair. -/
theorem outside_pair_eq {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Y i j = Y j i) (i j : Fin n) (hij : i ≠ j)
    (hsat : Y i j = 1)
    (hbody : ∀ a b, a ≠ b → a ≠ i → b ≠ i → Y a b < 0)
    (htriangle : ∀ k, k ≠ i → k ≠ j → Y i k + Y j k ≤ 0)
    (htight : (∑ ab : PairIndex n, Y ab.val.1 ab.val.2) = 2) :
    ∀ k l, k ≠ i → k ≠ j → l ≠ i → l ≠ j → k = l := by
  intro k l hki hkj hli hlj
  by_contra hkl
  have hz := body_pairs_zero Y hsym i j hij hsat
    (fun a b hab hai hbi => (hbody a b hab hai hbi).le) htriangle htight
    k l hkl hki hkj hli hlj
  exact (ne_of_lt (hbody k l hkl hki hli)) hz

end Erdos1017.PhysicalPrimal.SaturatedParent

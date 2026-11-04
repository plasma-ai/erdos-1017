module

public import Erdos1017.Exclusions.Common.Covered.CoveredRepeatWitness

/-!
# Compressing a repeat violation to two copies

A finite homogeneous completed cell has an explicit repeated-copy charge, a
violating cell contains a two-copy violating subset with the same exterior, and
a single positive root incidence bounds the exterior row sum by one.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

/-- A finite homogeneous completed cell has its actual repeated-copy
charge, with the untouched exterior charge retained literally. -/
theorem pairCharge_homogeneous_cell {α : Type*} [DecidableEq α]
    (D E : Finset α) (hdisj : Disjoint D E) (Y : α → α → ℝ)
    (hdiag : ∀ a, Y a a = 0) (hsym : ∀ a b, Y a b = Y b a)
    (ell : ℝ) (w : α → ℝ)
    (hcell : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Y a b = -ell)
    (hrow : ∀ a ∈ D, ∀ b ∈ E, Y a b = w b) :
    pairCharge (D ∪ E) Y = pairCharge E Y + D.card * (∑ b ∈ E, w b) -
      ell * D.card * ((D.card : ℝ) - 1) / 2 := by
  have hinner (a : α) (ha : a ∈ D) :
      (∑ b ∈ D, Y a b) = ((D.card : ℝ) - 1) * (-ell) := by
    calc
      _ = ∑ b ∈ D, ((-ell) - (if b = a then -ell else 0)) := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases heq : b = a
        · subst b
          simp [hdiag]
        · rw [hcell a ha b hb (Ne.symm heq)]
          simp [heq]
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp [ha]
        ring
  have hcharge : pairCharge D Y =
      -ell * D.card * ((D.card : ℝ) - 1) / 2 := by
    unfold pairCharge crossSum
    rw [Finset.sum_congr rfl (fun a ha => hinner a ha)]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hcross : crossSum D E Y = D.card * (∑ b ∈ E, w b) := by
    unfold crossSum
    have he (a : α) (ha : a ∈ D) : (∑ b ∈ E, Y a b) = ∑ b ∈ E, w b :=
      Finset.sum_congr rfl (fun b hb => hrow a ha b hb)
    rw [Finset.sum_congr rfl (fun a ha => he a ha)]
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hreverse : crossSum E D Y = crossSum D E Y := by
    unfold crossSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact hsym b a
  rw [pairCharge_union D E hdisj, hcharge, hreverse, hcross]
  ring

/-- A violating homogeneous completed cell contains an actual two-copy
violating subset with the same exterior. All one-copy subset tests are
retained, and the strict incidence threshold is derived. -/
theorem exists_two_copy_violating_subset {α : Type*} [DecidableEq α]
    (D E : Finset α) (hdisj : Disjoint D E) (Y : α → α → ℝ)
    (hdiag : ∀ a, Y a a = 0) (hsym : ∀ a b, Y a b = Y b a)
    (ell : ℝ) (w : α → ℝ) (hell : 1 / 2 < ell)
    (hcell : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Y a b = -ell)
    (hrow : ∀ a ∈ D, ∀ b ∈ E, Y a b = w b)
    (hincidence : (∑ b ∈ E, w b) ≤ 1)
    (hsmall : ∀ T ⊆ D, T.card ≤ 1 → pairCharge (T ∪ E) Y ≤ 1)
    (hbad : 1 < pairCharge (D ∪ E) Y) :
    ∃ T ⊆ D, T.card = 2 ∧ 1 < pairCharge (T ∪ E) Y ∧ ell < ∑ b ∈ E, w b := by
  have hr : 2 ≤ D.card := by
    by_contra hnot
    exact (not_lt_of_ge (hsmall D Finset.Subset.rfl (by omega))) hbad
  have hformula := pairCharge_homogeneous_cell D E hdisj Y hdiag hsym ell w hcell hrow
  rw [hformula] at hbad
  have htwo := CoveredRepeat.two_copy_violation_of_repeat hell hr hincidence hbad
  obtain ⟨T, hTD, hT⟩ := Finset.exists_subset_card_eq hr
  have hdisjT : Disjoint T E := hdisj.mono_left hTD
  have hformulaT := pairCharge_homogeneous_cell T E hdisjT Y hdiag hsym ell w
    (fun a ha b hb hab => hcell a (hTD ha) b (hTD hb) hab)
    (fun a ha b hb => hrow a (hTD ha) b hb)
  have hTbad : 1 < pairCharge (T ∪ E) Y := by
    rw [hformulaT, hT]
    norm_num
    linarith
  have hnonempty : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hnonempty
  have hsingle := hsmall {a} (by simpa using ha) (by simp)
  have hformulaOne := pairCharge_homogeneous_cell {a} E
    (hdisj.mono_left (show {a} ⊆ D by simpa using ha)) Y hdiag hsym ell w
    (fun x hx y hy hxy => by
      simp only [Finset.mem_singleton] at hx hy
      exact False.elim (hxy (hx.trans hy.symm)))
    (fun x hx b hb => by
      have hxa : x = a := Finset.mem_singleton.mp hx
      subst x
      exact hrow a ha b hb)
  rw [hformulaOne] at hsingle
  simp only [Finset.card_singleton, Nat.cast_one, one_mul, sub_self, mul_zero,
    zero_div, sub_zero] at hsingle
  exact ⟨T, hTD, hT, hTbad, CoveredRepeat.incidence_gt_of_two_copy_violation hsingle htwo⟩

/-- At most one positive root incidence bounds the entire exterior row
sum by one, while all other incidences retain their nonpositive sign. -/
theorem incidence_le_one_of_single_root {α : Type*} [DecidableEq α]
    (E : Finset α) (R : Set α) (w : α → ℝ)
    (hroot : ∀ a ∈ E, ∀ b ∈ E, a ∈ R → b ∈ R → a = b)
    (hstar : ∀ a ∈ E, a ∈ R → w a ≤ 1)
    (hbody : ∀ a ∈ E, a ∉ R → w a ≤ 0) : (∑ a ∈ E, w a) ≤ 1 := by
  classical
  by_cases hex : ∃ r ∈ E, r ∈ R
  · obtain ⟨r, hr, hrR⟩ := hex
    calc
      _ ≤ ∑ a ∈ E, (if a = r then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases heq : a = r
        · subst a
          simpa using hstar r hr hrR
        · simp only [heq, ite_false]
          exact hbody a ha (fun haR => heq (hroot a ha r hr haR hrR))
      _ = 1 := by simp [hr]
  · have hnonpos : (∑ a ∈ E, w a) ≤ 0 := Finset.sum_nonpos
      (fun a ha => hbody a ha (fun haR => hex ⟨a, ha, haR⟩))
    exact hnonpos.trans zero_le_one

end Erdos1017.FiniteArity

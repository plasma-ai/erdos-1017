module

public import Erdos1017.Exclusions.Common.Covered.CoveredRepeatCompression

/-!
# Shape of a finite repeat context

A positive witnessing incidence must contain a root when every nonroot charge is
nonpositive, and a single root with the half-delta edge penalties leaves at most
one nonroot vertex in an exterior whose incidence exceeds `ell`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

/-- A positive witnessing incidence must contain a root when every
nonroot charge has the original nonpositive sign. -/
theorem exists_root_of_incidence_pos {α : Type*} [DecidableEq α]
    (E : Finset α) (R : Set α) (w : α → ℝ)
    (hbody : ∀ a ∈ E, a ∉ R → w a ≤ 0) (hpositive : 0 < ∑ a ∈ E, w a) :
    ∃ a ∈ E, a ∈ R := by
  by_contra hnot
  have hsum : (∑ a ∈ E, w a) ≤ 0 := Finset.sum_nonpos
    (fun a ha => hbody a ha (fun haR => hnot ⟨a, ha, haR⟩))
  linarith

/-- A single root and the actual half-delta edge penalties leave at most
one nonroot vertex in an exterior whose incidence exceeds ell. -/
theorem nonroot_card_le_one_of_incidence_gt {α : Type*} [DecidableEq α]
    (E : Finset α) (R : Set α) [DecidablePred (· ∈ R)] (w : α → ℝ)
    (ell : ℝ) (hell : ell ∈ Set.Ioo (0 : ℝ) 1)
    (hroot : ∀ a ∈ E, ∀ b ∈ E, a ∈ R → b ∈ R → a = b)
    (hstar : ∀ a ∈ E, a ∈ R → w a ≤ 1)
    (hbody : ∀ a ∈ E, a ∉ R → w a ≤ -(1 - ell) / 2)
    (hincidence : ell < ∑ a ∈ E, w a) :
    (E.filter (fun a => a ∉ R)).card ≤ 1 := by
  classical
  have hnonpos (a : α) (ha : a ∈ E) (haR : a ∉ R) : w a ≤ 0 :=
    (hbody a ha haR).trans (by linarith [hell.2])
  obtain ⟨r, hr, hrR⟩ := exists_root_of_incidence_pos E R w hnonpos
    (hell.1.trans hincidence)
  by_contra hnot
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show
    1 < (E.filter (fun a => a ∉ R)).card by omega)
  obtain ⟨haE, haR⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbE, hbR⟩ := Finset.mem_filter.mp hb
  have har : a ≠ r := fun he => haR (he ▸ hrR)
  have hbr : b ≠ r := fun he => hbR (he ▸ hrR)
  have hsum : (∑ i ∈ E, w i) ≤ ∑ i ∈ E,
      ((if i = r then (1 : ℝ) else 0) +
        (if i = a then -(1 - ell) / 2 else 0) +
        (if i = b then -(1 - ell) / 2 else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hir : i = r
    · subst i
      simpa [Ne.symm har, Ne.symm hbr] using hstar r hr hrR
    · by_cases hia : i = a
      · subst i
        simpa [har, hab] using hbody a haE haR
      · by_cases hib : i = b
        · subst i
          simpa [hbr, Ne.symm hab] using hbody b hbE hbR
        · simp only [hir, hia, hib, ite_false, add_zero]
          exact hnonpos i hi (fun hiR => hir (hroot i hi r hr hiR hrR))
  simp only [Finset.sum_add_distrib] at hsum
  simp [hr, haE, hbE] at hsum
  linarith

end Erdos1017.FiniteArity

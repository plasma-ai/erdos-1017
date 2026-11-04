module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomStrictFamily

/-!
# No positive vertex at contact two with `r = h/2`

At contact two with `q > 1/3` and `r = h/2`, the full all-count feasible set has
no positive vertex; both possible double-contact cases are derived.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

private theorem not_vertex_boundary_covers (x : Coefficients) (hpos : ∀ i, 0 < x i)
    (s₀ s₁ : Finset ℕ) (hc : s₀.card + s₁.card + 2 ≤ 4)
    (h₀ : ∀ k, countTest k 0 x = 1 → k ∈ s₀)
    (h₁ : ∀ k, countTest k 1 x = 1 → k ∈ s₁)
    (hs : ∀ k l, countTest k l x = 1 →
      (k = 0 ∧ l = 2) ∨ (k = 1 ∧ l = 2) ∨ l = 0 ∨ l = 1) :
    x ∉ feasible.extremePoints ℝ := by
  let s := (s₀.image (fun k => (k, 0))) ∪ (s₁.image (fun k => (k, 1))) ∪ {(0, 2), (1, 2)}
  apply not_vertex_of_tight_cover x hpos s
  · have hA := Finset.card_union_le
      (s₀.image (fun k => (k, 0))) (s₁.image (fun k => (k, 1)))
    have hB := Finset.card_union_le
      ((s₀.image (fun k => (k, 0))) ∪ (s₁.image (fun k => (k, 1)))) {(0, 2), (1, 2)}
    have hC := Finset.card_image_le (s := s₀) (f := fun k => (k, 0))
    have hD := Finset.card_image_le (s := s₁) (f := fun k => (k, 1))
    have hE : ({(0, 2), (1, 2)} : Finset (ℕ × ℕ)).card = 2 := by norm_num
    dsimp only [s]
    omega
  · intro k l ht
    simp only [s, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    rcases hs k l ht with h | h | h | h
    · exact Or.inr (Or.inl (Prod.ext h.1 h.2))
    · exact Or.inr (Or.inr (Prod.ext h.1 h.2))
    · subst l
      exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨k, h₀ k ht, rfl⟩))
    · subst l
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨k, h₁ k ht, rfl⟩))

/-- At contact two with q>1/3 and r=h/2, the full all-count feasible set
has no positive vertex. Both possible double-contact cases are derived. -/
theorem not_vertex_contact_two_boundary_strict_q (x : Coefficients)
    (hx : x ∈ feasible) (ell : ℝ) (hg : OwnCountGuards x ell)
    (hq : 1 / 3 < x 3) (hv : x 1 = (1 + x 3) / 2)
    (hcontact : countTest 0 2 x = 1) (hr : x 0 = 2 * x 4) :
    x ∉ feasible.extremePoints ℝ := by
  have hp := hg.positive 2
  have hvlt : x 1 < 1 := by linarith [hg.q_lt_ell, hg.ell_lt_one]
  have hsupp : ∀ k l, countTest k l x = 1 →
      (k = 0 ∧ l = 2) ∨ (k = 1 ∧ l = 2) ∨ l = 0 ∨ l = 1 := by
    intro k l ht
    by_cases hk : k = 0
    · subst k
      rcases contact_two_axis_support x hx hq.le
        (hg.q_lt_ell.trans hg.ell_lt_one) hv hcontact l ht with h | ⟨_, heq⟩
      · exact Or.inl ⟨rfl, h⟩
      · linarith
    · have hl : l ≤ 2 := by
        by_contra h
        have hb := contact_two_high_rows_slack x hx ell hg hcontact k l
          (Nat.pos_of_ne_zero hk) (by omega)
        linarith only [hb, ht]
      by_cases hl2 : l = 2
      · subst l
        exact Or.inr (Or.inl ⟨(contact_two_mixed_two_tight x hx hp hcontact k
          (Nat.pos_of_ne_zero hk) ht).1, rfl⟩)
      · exact Or.inr (Or.inr (by omega))
  by_cases hdouble : ∃ k, countTest k 1 x = 1 ∧ countTest (k + 1) 1 x = 1
  · obtain ⟨k, hk, hk1⟩ := hdouble
    have hC : x 1 * (1 : ℝ) - x 3 * 1 * (1 - 1) / 2 < 1 := by linarith
    obtain ⟨hkpos, hs, hpen⟩ := adjacent_line_relations x 1 k
      (by simpa only [Nat.cast_one] using hC) hk hk1
    norm_num at hs hpen
    have hkEq : k = 1 := by
      by_contra h
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      have hprod : (6 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hprod hp.le
      nlinarith [hg.p_floor, hg.ell_lt_v]
    subst k
    norm_num at hs hpen
    have hheq : x 0 = 2 * x 2 := by linarith
    have haxis2 := hx.2.2.1 2 0
    norm_num [countTest_apply] at haxis2
    have hpless : x 2 < 1 / 3 := by
      by_contra h
      have hpEq : x 2 = 1 / 3 := by linarith
      nlinarith [hg.h_lt_ell, hg.ell_lt_v]
    have hRnone : ∀ n, countTest n 0 x ≠ 1 := by
      intro n hn
      have hgap := mul_nonneg hp.le (TightCounts.gap_nonneg 2 n)
      norm_num only [Nat.cast_ofNat] at hgap
      norm_num [countTest_apply, hheq] at hn
      nlinarith only [hgap, hn, hpless]
    obtain ⟨s₁, hc₁, hs₁⟩ := exists_line_tight_cover x hx hp 1
    exact not_vertex_boundary_covers x hg.positive ∅ s₁ (by simp; omega)
      (fun n hn => False.elim (hRnone n hn)) hs₁ hsupp
  · have hno₁ : ∀ k, ¬(countTest k 1 x = 1 ∧ countTest (k + 1) 1 x = 1) := by
      simpa only [not_exists, not_and] using hdouble
    by_cases hRdouble : ∃ j, countTest j 0 x = 1 ∧ countTest (j + 1) 0 x = 1
    · obtain ⟨j, hj, hj1⟩ := hRdouble
      obtain ⟨hjpos, hheq, hpJ⟩ := adjacent_line_relations x 0 j (by norm_num) hj hj1
      norm_num at hheq hpJ
      have h21 := hx.2.2.1 2 1
      norm_num [countTest_apply] at h21
      have hjlt : j ≤ 2 := by
        by_contra h
        have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast (show 3 ≤ j by omega)
        have hmul := mul_le_mul_of_nonneg_left hj3 hp.le
        nlinarith [hg.p_floor, hg.ell_lt_v]
      have hjEq : j = 2 := by
        have hj12 : j = 1 ∨ j = 2 := by omega
        rcases hj12 with h | h
        · subst j
          norm_num at hheq hpJ
          linarith [hg.h_lt_ell, hg.ell_lt_v, hg.v_le_one]
        · exact h
      subst j
      norm_num at hheq hpJ
      have hLnone : ∀ k, countTest k 1 x ≠ 1 := by
        intro k hk
        have hs : x 0 - x 4 = x 2 * (1 : ℝ) := by linarith
        have hc := TightCounts.adjacent_tight_of_integer_slope (x 1) (x 0 - x 4)
          (x 2) hp 1 (by simpa only [Nat.cast_one] using hs)
          (fun n => by simpa only [countTest_eq_line, Nat.cast_one, mul_one, sub_self,
            mul_zero, zero_div, sub_zero] using hx.2.2.1 n 1)
          ⟨k, by simpa only [countTest_eq_line, Nat.cast_one, mul_one, sub_self,
            mul_zero, zero_div, sub_zero] using hk⟩
        have hc1 : countTest 1 1 x = 1 := by simpa [countTest_eq_line] using hc.1
        have hc2 : countTest 2 1 x = 1 := by simpa [countTest_eq_line] using hc.2
        exact hno₁ 1 ⟨hc1, hc2⟩
      obtain ⟨s₀, hc₀, hs₀⟩ := exists_line_tight_cover x hx hp 0
      exact not_vertex_boundary_covers x hg.positive s₀ ∅ (by simp; omega)
        hs₀ (fun k hk => False.elim (hLnone k hk)) hsupp
    · have hno₀ : ∀ k, ¬(countTest k 0 x = 1 ∧ countTest (k + 1) 0 x = 1) := by
        simpa only [not_exists, not_and] using hRdouble
      obtain ⟨s₀, hc₀, hs₀⟩ := exists_single_line_tight_cover x hx hp 0 hno₀
      obtain ⟨s₁, hc₁, hs₁⟩ := exists_single_line_tight_cover x hx hp 1 hno₁
      exact not_vertex_boundary_covers x hg.positive s₀ s₁ (by omega) hs₀ hs₁ hsupp

end Erdos1017.TwoAtomCountGate

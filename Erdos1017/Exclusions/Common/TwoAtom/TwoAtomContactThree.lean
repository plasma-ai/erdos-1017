module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountLines

/-!
# No vertex at contact three

A scalar contact-three vector has strict mixed slope `r > h/3`, slack mixed rows
at `E` count three or more, a unique axis contact and no adjacent double
contacts, so its tight rows fall into at most four classes and cannot form a
five-coordinate vertex.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- A scalar contact-three vector has the strict mixed slope r>h/3;
the equality boundary contradicts the original (1,1) count. -/
theorem contact_three_r_strict (x : Coefficients) (hx : x ∈ feasible) (ell : ℝ)
    (hg : OwnCountGuards x ell) (hv : x 1 = 1 / 3 + x 3) : x 0 < 3 * x 4 := by
  have h13 := hx.2.2.1 1 3
  have h11 := hx.2.2.1 1 1
  norm_num [countTest_apply] at h13 h11
  have hle : x 0 ≤ 3 * x 4 := by linarith
  by_contra hn
  have heq : x 0 = 3 * x 4 := le_antisymm hle (le_of_not_gt hn)
  nlinarith [hg.r_floor, hg.ell_lt_v]

/-- All mixed rows at E count at least three are strictly slack. -/
theorem contact_three_high_rows_slack (x : Coefficients) (hx : x ∈ feasible) (ell : ℝ)
    (hg : OwnCountGuards x ell) (hr : x 0 < 3 * x 4) (k l : ℕ)
    (hk : 0 < k) (hl : 3 ≤ l) : countTest k l x < 1 := by
  have haxis := hx.2.2.1 0 l
  have hln : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hkn : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlr := mul_nonneg (hg.positive 4).le (sub_nonneg.mpr hln)
  have hneg : x 0 - x 4 * l < 0 := by nlinarith only [hr, hlr]
  have hstrict := mul_neg_of_pos_of_neg hkn hneg
  have hbin : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    simpa using TightCounts.gap_nonneg 0 k
  have hpen := mul_nonneg (hg.positive 2).le hbin
  rw [countTest_apply] at haxis ⊢
  norm_num only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, zero_add] at haxis
  nlinarith only [haxis, hstrict, hpen]

/-- The scalar contact-three axis has exactly its old count three contact. -/
theorem contact_three_axis_unique (x : Coefficients) (hx : x ∈ feasible)
    (hqlo : 1 / 6 < x 3) (hqhi : x 3 < 1 / 3) (hv : x 1 = 1 / 3 + x 3)
    (hcontact : countTest 0 3 x = 1) (l : ℕ) (hl : countTest 0 l x = 1) : l = 3 := by
  have hp : 0 < x 3 := by linarith
  have hline (n : ℕ) : countTest 0 n x = TightCounts.value 0 (x 1) (x 3) n := by
    rw [countTest_apply]
    unfold TightCounts.value
    ring
  have hfeas (n : ℕ) : TightCounts.value 0 (x 1) (x 3) n ≤ 1 := by
    rw [← hline]
    exact hx.2.2.1 0 n
  rcases lt_trichotomy l 3 with h | h | h
  · have hadj := TightCounts.tight_counts_adjacent 0 (x 1) (x 3) hp hfeas l 3 h
      (by rwa [← hline]) (by rwa [← hline])
    have hl2 : l = 2 := by omega
    norm_num [hl2, countTest_apply] at hl
    linarith
  · exact h
  · have hadj := TightCounts.tight_counts_adjacent 0 (x 1) (x 3) hp hfeas 3 l h
      (by rwa [← hline]) (by rwa [← hline])
    norm_num [hadj, countTest_apply] at hl
    linarith

/-- The R axis cannot have two adjacent contacts in contact three. -/
theorem contact_three_no_double_axis (x : Coefficients) (ell : ℝ)
    (hg : OwnCountGuards x ell) (hv : x 1 = 1 / 3 + x 3) (hqhi : x 3 < 1 / 3) :
    ∀ k, ¬(countTest k 0 x = 1 ∧ countTest (k + 1) 0 x = 1) := by
  intro k hk
  have hvhi : x 1 < 2 / 3 := by linarith
  have hhhi : x 0 < 2 / 3 := hg.h_lt_ell.trans (hg.ell_lt_v.trans hvhi)
  have hp16 : 1 / 6 < x 2 := by linarith [hg.p_floor, hg.ell_lt_v]
  obtain ⟨hk1, hs, hp⟩ := adjacent_line_relations x 0 k (by norm_num) hk.1 hk.2
  norm_num at hs hp
  by_cases hk3 : 3 ≤ k
  · have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    have hprod : (12 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod (hg.positive 2).le
    nlinarith only [hp16, hmul, hp]
  · have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with h | h <;> subst k <;> norm_num at hs hp <;> nlinarith

/-- The l=2 line cannot have two adjacent contacts in contact three. -/
theorem contact_three_no_double_two (x : Coefficients) (ell : ℝ)
    (hg : OwnCountGuards x ell) (hv : x 1 = 1 / 3 + x 3) (hqhi : x 3 < 1 / 3) :
    ∀ k, ¬(countTest k 2 x = 1 ∧ countTest (k + 1) 2 x = 1) := by
  intro k hk
  have hC : x 1 * (2 : ℝ) - x 3 * 2 * (2 - 1) / 2 < 1 := by linarith
  obtain ⟨hk1, _, hp⟩ := adjacent_line_relations x 2 k hC hk.1 hk.2
  norm_num at hp
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hprod : (2 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hprod (hg.positive 2).le
  nlinarith [hg.p_floor, hg.ell_lt_v, hg.positive 3]

/-- The l=1 line cannot have two adjacent contacts in contact three. -/
theorem contact_three_no_double_one (x : Coefficients) (hx : x ∈ feasible) (ell : ℝ)
    (hg : OwnCountGuards x ell) (hv : x 1 = 1 / 3 + x 3) (hqhi : x 3 < 1 / 3) :
    ∀ k, ¬(countTest k 1 x = 1 ∧ countTest (k + 1) 1 x = 1) := by
  intro k hk
  have hvhi : x 1 < 2 / 3 := by linarith
  have hhhi : x 0 < 2 / 3 := hg.h_lt_ell.trans (hg.ell_lt_v.trans hvhi)
  have hC : x 1 * (1 : ℝ) - x 3 * 1 * (1 - 1) / 2 < 1 := by linarith
  obtain ⟨hk1, hs, hp⟩ := adjacent_line_relations x 1 k
    (by simpa only [Nat.cast_one] using hC) hk.1 hk.2
  norm_num at hs hp
  have hkEq : k = 1 := by
    by_contra h
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have hprod : (6 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod (hg.positive 2).le
    nlinarith [hg.p_floor, hg.ell_lt_v]
  subst k
  norm_num at hs hp
  have h12 := hx.2.2.1 1 2
  norm_num [countTest_apply] at h12
  nlinarith

/-- The four possible contact-three row classes, before proving uniqueness. -/
def contactThreeRowClass (k l : ℕ) : Fin 4 :=
  ⟨if k = 0 then 0 else if l = 0 then 1 else if l = 1 then 2 else 3, by split_ifs <;> omega⟩

/-- Original count tests and own strict guards make the row-class map
injective on all actual tight rows, without supplying a contact list. -/
theorem contact_three_tight_row_class_injective (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hg : OwnCountGuards x ell) (hqlo : 1 / 6 < x 3)
    (hqhi : x 3 < 1 / 3) (hv : x 1 = 1 / 3 + x 3) (hcontact : countTest 0 3 x = 1)
    (k l a b : ℕ) (hkl : countTest k l x = 1) (hab : countTest a b x = 1)
    (hclass : contactThreeRowClass k l = contactThreeRowClass a b) : k = a ∧ l = b := by
  have hr := contact_three_r_strict x hx ell hg hv
  have hsmall (i j : ℕ) (hi : i ≠ 0) (hij : countTest i j x = 1) : j ≤ 2 := by
    by_contra h
    have hs := contact_three_high_rows_slack x hx ell hg hr i j
      (Nat.pos_of_ne_zero hi) (by omega)
    linarith only [hs, hij]
  have huniq (j : ℕ) (hj : j ≤ 2) :
      ∀ i n, countTest i j x = 1 → countTest n j x = 1 → i = n := by
    apply tight_line_unique_of_no_adjacent x hx (hg.positive 2) j
    interval_cases j
    · exact contact_three_no_double_axis x ell hg hv hqhi
    · exact contact_three_no_double_one x hx ell hg hv hqhi
    · exact contact_three_no_double_two x ell hg hv hqhi
  have hc := congrArg Fin.val hclass
  change (if k = 0 then 0 else if l = 0 then 1 else if l = 1 then 2 else 3) =
    (if a = 0 then 0 else if b = 0 then 1 else if b = 1 then 2 else 3) at hc
  by_cases hk : k = 0
  · have ha : a = 0 := by
      by_contra ha
      by_cases hb0 : b = 0
      · simp [hk, ha, hb0] at hc
      · by_cases hb1 : b = 1 <;> simp [hk, ha, hb0, hb1] at hc
    subst k
    subst a
    exact ⟨rfl, (contact_three_axis_unique x hx hqlo hqhi hv hcontact l hkl).trans
      (contact_three_axis_unique x hx hqlo hqhi hv hcontact b hab).symm⟩
  · have ha : a ≠ 0 := by
      intro ha
      by_cases hl0 : l = 0
      · simp [hk, ha, hl0] at hc
      · by_cases hl1 : l = 1 <;> simp [hk, ha, hl0, hl1] at hc
    have hl := hsmall k l hk hkl
    have hb := hsmall a b ha hab
    interval_cases l <;> interval_cases b <;> norm_num [hk, ha] at hc
    all_goals exact ⟨huniq _ (by omega) k a hkl hab, rfl⟩

/-- Contact three has at most four actual active count rows and therefore
cannot be a genuine five-coordinate vertex. -/
theorem not_vertex_of_scalar_contact_three (x : Coefficients)
    (hx : x ∈ feasible) (ell : ℝ) (hg : OwnCountGuards x ell)
    (hqlo : 1 / 6 < x 3) (hqhi : x 3 < 1 / 3)
    (hv : x 1 = 1 / 3 + x 3) (hcontact : countTest 0 3 x = 1) :
    x ∉ feasible.extremePoints ℝ := by
  intro hvertex
  obtain ⟨N, hN⟩ := five_active_tests x hvertex hg.positive
  let T := {i : Fin N × Fin N // countTest i.1.val i.2.val x = 1}
  let f : T → Fin 4 := fun i => contactThreeRowClass i.val.1.val i.val.2.val
  have hinj : Function.Injective f := by
    intro i j heq
    have hh := contact_three_tight_row_class_injective x hx ell hg hqlo hqhi hv hcontact
      i.val.1.val i.val.2.val j.val.1.val j.val.2.val i.property j.property heq
    apply Subtype.ext
    exact Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Nat.card_eq_fintype_card] at hN
  change 5 ≤ Fintype.card T at hN
  change Fintype.card T ≤ Fintype.card (Fin 4) at hcard
  norm_num only [Fintype.card_fin] at hcard
  omega

end Erdos1017.TwoAtomCountGate

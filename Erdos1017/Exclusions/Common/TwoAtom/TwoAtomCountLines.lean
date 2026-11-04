module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomScalarContact

/-!
# Tight counts on the lines of the two-atom system

This module defines the own-dual count guards at the active coefficient vector
and shows that every feasible positive-penalty line has a tight cover by at most
two consecutive counts, adjacent contacts determining slope and penalty without
division; four tight rows cannot define a positive five-coordinate vertex.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- Own-dual guards at the selected active coefficient vector.
They are hypotheses here; their applications derive them from the model. -/
structure OwnCountGuards (x : Coefficients) (ell : ℝ) : Prop where
  h_pos : 0 < x 0
  ell_half : 1 / 2 < ell
  h_lt_ell : x 0 < ell
  p_lt_ell : x 2 < ell
  q_lt_ell : x 3 < ell
  r_lt_ell : x 4 < ell
  ell_lt_v : ell < x 1
  v_le_one : x 1 ≤ 1
  p_floor : (1 - ell) / 2 < x 2
  q_floor : (1 - ell) / 2 < x 3
  r_floor : (1 - ell) / 2 < x 4

theorem OwnCountGuards.ell_lt_one {x : Coefficients} {ell : ℝ}
    (h : OwnCountGuards x ell) : ell < 1 := h.ell_lt_v.trans_le h.v_le_one

theorem OwnCountGuards.positive {x : Coefficients} {ell : ℝ}
    (h : OwnCountGuards x ell) : ∀ i, 0 < x i := by
  intro i
  have hd : 0 < (1 - ell) / 2 := by linarith [h.ell_lt_one]
  fin_cases i
  · exact h.h_pos
  · change 0 < x 1
    exact (show 0 < ell by linarith [h.ell_half]).trans h.ell_lt_v
  · exact hd.trans h.p_floor
  · exact hd.trans h.q_floor
  · exact hd.trans h.r_floor

/-- Each fixed E count is the original strictly concave R-count polynomial. -/
theorem countTest_eq_line (x : Coefficients) (k l : ℕ) :
    countTest k l x = TightCounts.value
      (x 1 * l - x 3 * l * ((l : ℝ) - 1) / 2) (x 0 - x 4 * l) (x 2) k := by
  rw [countTest_apply]
  unfold TightCounts.value
  ring

theorem tight_line_adjacent (x : Coefficients) (hx : x ∈ feasible) (hp : 0 < x 2)
    (l k n : ℕ) (hkn : k < n) (hk : countTest k l x = 1) (hn : countTest n l x = 1) :
    n = k + 1 := by
  exact TightCounts.tight_counts_adjacent _ _ _ hp
    (fun j => by rw [← countTest_eq_line]; exact hx.2.2.1 j l) k n hkn
    (by rwa [← countTest_eq_line]) (by rwa [← countTest_eq_line])

/-- Adjacent genuine tight counts determine the slope and penalty without
division. A strict subunit constant excludes the zero-count boundary. -/
theorem adjacent_line_relations (x : Coefficients) (l k : ℕ)
    (hC : x 1 * l - x 3 * l * ((l : ℝ) - 1) / 2 < 1)
    (hk : countTest k l x = 1) (hk1 : countTest (k + 1) l x = 1) :
    1 ≤ k ∧ x 0 - x 4 * l = x 2 * k ∧
      x 2 * k * ((k : ℝ) + 1) = 2 * (1 - (x 1 * l - x 3 * l * ((l : ℝ) - 1) / 2)) := by
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    norm_num [countTest_apply] at hk
    linarith
  have hs := TightCounts.slope_of_adjacent_tight
    (x 1 * l - x 3 * l * ((l : ℝ) - 1) / 2) (x 0 - x 4 * l) (x 2) k
    (by rwa [← countTest_eq_line]) (by rwa [← countTest_eq_line])
  refine ⟨Nat.one_le_iff_ne_zero.mpr hk0, hs, ?_⟩
  rw [countTest_eq_line] at hk
  unfold TightCounts.value at hk
  have hmul := congrArg (fun z : ℝ => z * (k : ℝ)) hs
  nlinarith only [hk, hmul]

/-- Absence of consecutive contacts on one line implies uniqueness of its
actual integer contact, using genuine global count feasibility. -/
theorem tight_line_unique_of_no_adjacent (x : Coefficients) (hx : x ∈ feasible)
    (hp : 0 < x 2) (l : ℕ)
    (hno : ∀ k, ¬(countTest k l x = 1 ∧ countTest (k + 1) l x = 1)) :
    ∀ k n, countTest k l x = 1 → countTest n l x = 1 → k = n := by
  intro k n hk hn
  rcases lt_trichotomy k n with h | h | h
  · have hadj := tight_line_adjacent x hx hp l k n h hk hn
    exact False.elim (hno k ⟨hk, hadj ▸ hn⟩)
  · exact h
  · have hadj := tight_line_adjacent x hx hp l n k h hn hk
    exact False.elim (hno n ⟨hn, hadj ▸ hk⟩)

/-- A positive tight count and the preceding original feasible test bound
the quadratic penalty, without a maximizer or adjacent-tight assumption. -/
theorem penalty_bound_of_tight (C s p : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hprev : TightCounts.value C s p (k - 1) ≤ 1)
    (htight : TightCounts.value C s p k = 1) :
    p * k * ((k : ℝ) - 1) ≤ 2 * (1 - C) := by
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  unfold TightCounts.value at hprev htight
  rw [hcast] at hprev
  have hp := mul_le_mul_of_nonneg_right hprev (Nat.cast_nonneg k)
  have ht := congrArg (fun z : ℝ => z * ((k : ℝ) - 1)) htight
  nlinarith only [hp, ht]

/-- Every genuinely feasible positive-penalty line has an actual cover by
at most two consecutive natural tight counts. -/
theorem exists_line_tight_cover (x : Coefficients) (hx : x ∈ feasible) (hp : 0 < x 2)
    (l : ℕ) : ∃ s : Finset ℕ, s.card ≤ 2 ∧ ∀ k, countTest k l x = 1 → k ∈ s := by
  by_cases ht : ∃ k, countTest k l x = 1
  · let k := Nat.find ht
    have hk : countTest k l x = 1 := Nat.find_spec ht
    refine ⟨{k, k + 1}, Finset.card_le_two, ?_⟩
    intro n hn
    have hkn : k ≤ n := Nat.find_min' ht hn
    by_cases heq : k = n
    · simp [← heq]
    · have hadj := tight_line_adjacent x hx hp l k n (lt_of_le_of_ne hkn heq) hk hn
      simp [hadj]
  · refine ⟨∅, by simp, ?_⟩
    intro k hk
    exact False.elim (ht ⟨k, hk⟩)

/-- A line without consecutive contacts has a genuine tight cover of
size at most one, including an empty line. -/
theorem exists_single_line_tight_cover (x : Coefficients) (hx : x ∈ feasible)
    (hp : 0 < x 2) (l : ℕ)
    (hno : ∀ k, ¬(countTest k l x = 1 ∧ countTest (k + 1) l x = 1)) :
    ∃ s : Finset ℕ, s.card ≤ 1 ∧ ∀ k, countTest k l x = 1 → k ∈ s := by
  by_cases ht : ∃ k, countTest k l x = 1
  · obtain ⟨k, hk⟩ := ht
    refine ⟨{k}, by simp, ?_⟩
    intro n hn
    have heq := tight_line_unique_of_no_adjacent x hx hp l hno n k hn hk
    simp [heq]
  · refine ⟨∅, by simp, ?_⟩
    intro k hk
    exact False.elim (ht ⟨k, hk⟩)

/-- Four actually derived tight rows cannot define a positive genuine
five-coordinate vertex. This generic finite-cover lemma assumes no rank. -/
theorem not_vertex_of_tight_cover (x : Coefficients) (hpos : ∀ i, 0 < x i)
    (s : Finset (ℕ × ℕ)) (hcard : s.card ≤ 4)
    (hsupport : ∀ k l, countTest k l x = 1 → (k, l) ∈ s) :
    x ∉ feasible.extremePoints ℝ := by
  intro hvertex
  obtain ⟨N, hN⟩ := five_active_tests x hvertex hpos
  let T := {i : Fin N × Fin N // countTest i.1.val i.2.val x = 1}
  let f : T → {p : ℕ × ℕ // p ∈ s} := fun i =>
    ⟨(i.val.1.val, i.val.2.val), hsupport _ _ i.property⟩
  have hinj : Function.Injective f := by
    intro i j heq
    have hp := congrArg Subtype.val heq
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst hp)) (Fin.ext (congrArg Prod.snd hp))
  have hc := Fintype.card_le_of_injective f hinj
  rw [Nat.card_eq_fintype_card] at hN
  change 5 ≤ Fintype.card T at hN
  have hc' : Fintype.card T ≤ s.card := by simpa only [Fintype.card_coe] using hc
  omega

/-- An adjacent double contact gives the exact entire tight support on
its genuine positive-penalty line, with no other integer counts omitted. -/
theorem tight_line_iff_of_adjacent (x : Coefficients) (hp : 0 < x 2) (l j : ℕ)
    (hj : countTest j l x = 1) (hj1 : countTest (j + 1) l x = 1) (n : ℕ) :
    countTest n l x = 1 ↔ n = j ∨ n = j + 1 := by
  let C := x 1 * l - x 3 * l * ((l : ℝ) - 1) / 2
  let s := x 0 - x 4 * l
  have hs := TightCounts.slope_of_adjacent_tight C s (x 2) j
    (by rwa [← countTest_eq_line]) (by rwa [← countTest_eq_line])
  have hv : TightCounts.value C s (x 2) j = 1 := by rwa [← countTest_eq_line]
  rw [countTest_eq_line]
  change (TightCounts.value C s (x 2) n = 1 ↔ n = j ∨ n = j + 1)
  conv_lhs => rhs; rw [← hv]
  exact TightCounts.integer_slope_maximum_iff C s (x 2) hp j n hs

end Erdos1017.TwoAtomCountGate

module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomTwoLineVertex

/-!
# Integer family at strict contact two

In strict contact two with `q > 1/3`, every tight row lies on one of the two
surviving `R` lines or is the scalar `E₂` row, and the vertex together with the
strict bonus forces `k = 1` in the two-line integer equations, producing the
unbounded `j`-family.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- In strict contact two with q>1/3, every old tight row lies on one of
the two surviving R lines or is the actual scalar E2 row. -/
theorem strict_contact_two_support (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hg : OwnCountGuards x ell) (hq : 1 / 3 < x 3)
    (hv : x 1 = (1 + x 3) / 2) (hcontact : countTest 0 2 x = 1)
    (hr : x 0 < 2 * x 4) :
    ∀ k l, countTest k l x = 1 → (k = 0 ∧ l = 2) ∨ l = 0 ∨ l = 1 := by
  intro k l ht
  by_cases hk : k = 0
  · subst k
    have hs := contact_two_axis_support x hx hq.le
      (hg.q_lt_ell.trans hg.ell_lt_one) hv hcontact l ht
    rcases hs with hs | ⟨_, heq⟩
    · exact Or.inl ⟨rfl, hs⟩
    · linarith
  · have hl : l ≤ 2 := by
      by_contra h
      have hs := contact_two_high_rows_slack x hx ell hg hcontact k l
        (Nat.pos_of_ne_zero hk) (by omega)
      linarith only [hs, ht]
    have hl2 : l ≠ 2 := by
      intro hl2
      subst l
      have hs := contact_two_mixed_two_tight x hx (hg.positive 2) hcontact k
        (Nat.pos_of_ne_zero hk) ht
      linarith [hs.2]
    exact Or.inr (by omega)

/-- The genuine vertex and strict bonus force k=1 in the two-line
integer equations, yielding the actual unbounded j-family internally. -/
theorem strict_contact_two_integer_family (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (ell : ℝ) (hg : OwnCountGuards x ell)
    (hq : 1 / 3 < x 3) (hv : x 1 = (1 + x 3) / 2)
    (hcontact : countTest 0 2 x = 1) (hr : x 0 < 2 * x 4) :
    ∃ j : ℕ, 3 ≤ j ∧
      x 0 = 2 * (j : ℝ) / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      x 2 = 2 / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      x 4 = 2 * ((j : ℝ) - 1) / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      x 1 = 1 - 2 / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      x 3 = 1 - 4 / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      ∀ k l, countTest k l x = 1 ↔
        (k = j ∧ l = 0) ∨ (k = j + 1 ∧ l = 0) ∨
          (k = 1 ∧ l = 1) ∨ (k = 2 ∧ l = 1) ∨ (k = 0 ∧ l = 2) := by
  have hx := hvertex.1
  have hsupp := strict_contact_two_support x hx ell hg hq hv hcontact hr
  obtain ⟨⟨j, hj, hj1⟩, ⟨k, hk, hk1⟩⟩ := two_double_lines_of_vertex x hvertex hg.positive hsupp
  obtain ⟨hjpos, hheq, hpJ⟩ := adjacent_line_relations x 0 j (by norm_num) hj hj1
  norm_num at hheq hpJ
  have hvlt : x 1 < 1 := by linarith [hg.q_lt_ell, hg.ell_lt_one]
  have hC : x 1 * (1 : ℝ) - x 3 * 1 * (1 - 1) / 2 < 1 := by linarith
  obtain ⟨hkpos, hrk, hpK⟩ := adjacent_line_relations x 1 k
    (by simpa only [Nat.cast_one] using hC) hk hk1
  norm_num at hrk hpK
  have hkEq : k = 1 := by
    by_contra h
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have hprod : (6 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod (hg.positive 2).le
    nlinarith [hg.p_floor, hg.ell_lt_v]
  subst k
  norm_num at hrk hpK
  have hj3 : 3 ≤ j := by
    by_contra h
    have hjr : (j : ℝ) ≤ 2 := by exact_mod_cast (show j ≤ 2 by omega)
    have hmul := mul_le_mul_of_nonneg_left hjr (hg.positive 2).le
    nlinarith only [hheq, hrk, hr, hmul]
  have hJpos : 0 < (j : ℝ) * ((j : ℝ) + 1) := by
    have hjr : (3 : ℝ) ≤ j := by exact_mod_cast hj3
    positivity
  have hpform : x 2 = 2 / ((j : ℝ) * ((j : ℝ) + 1)) := by
    apply (eq_div_iff (ne_of_gt hJpos)).mpr
    nlinarith only [hpJ]
  have hhform : x 0 = 2 * (j : ℝ) / ((j : ℝ) * ((j : ℝ) + 1)) := by
    rw [hheq, hpform]
    ring
  have hrform : x 4 = 2 * ((j : ℝ) - 1) / ((j : ℝ) * ((j : ℝ) + 1)) := by
    apply (eq_div_iff (ne_of_gt hJpos)).mpr
    have hhJ := (eq_div_iff (ne_of_gt hJpos)).mp hhform
    have hpJ' := (eq_div_iff (ne_of_gt hJpos)).mp hpform
    have hrJ := congrArg (fun z : ℝ => z * ((j : ℝ) * ((j : ℝ) + 1))) hrk
    nlinarith only [hhJ, hpJ', hrJ]
  have hvform : x 1 = 1 - 2 / ((j : ℝ) * ((j : ℝ) + 1)) := by
    rw [hpform] at hpK
    linarith only [hpK]
  have hqform : x 3 = 1 - 4 / ((j : ℝ) * ((j : ℝ) + 1)) := by
    calc
      x 3 = 1 - 2 * x 2 := by linarith only [hv, hpK]
      _ = _ := by rw [hpform]; ring
  refine ⟨j, hj3, hhform, hpform, hrform, hvform, hqform, ?_⟩
  intro k l
  constructor
  · intro ht
    rcases hsupp k l ht with hE | hl | hl
    · exact Or.inr (Or.inr (Or.inr (Or.inr hE)))
    · subst l
      have hc := (tight_line_iff_of_adjacent x (hg.positive 2) 0 j hj hj1 k).mp ht
      rcases hc with hc | hc
      · exact Or.inl ⟨hc, rfl⟩
      · exact Or.inr (Or.inl ⟨hc, rfl⟩)
    · subst l
      have hc := (tight_line_iff_of_adjacent x (hg.positive 2) 1 1 hk hk1 k).mp ht
      rcases hc with hc | hc
      · exact Or.inr (Or.inr (Or.inl ⟨hc, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, rfl⟩)))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hj
    · exact hj1
    · exact hk
    · exact hk1
    · exact hcontact

end Erdos1017.TwoAtomCountGate

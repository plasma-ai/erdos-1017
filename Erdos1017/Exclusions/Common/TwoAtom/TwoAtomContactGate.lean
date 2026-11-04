module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountMoments
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomMomentContradiction

/-!
# Contact gate of the two-atom system

The generic five-coordinate gate constructs an optimal vertex, classifies all
active integer counts, derives the factorial-moment inequality and reaches a
contradiction, so the unscaled cost moments and the active dual's own rows rule
out the derived integer family.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- Original unscaled cost moments and the same active dual's own rows
contradict the derived integer family. E normalization is proved internally. -/
theorem IntegerFamily.contradiction_of_own_rows_moments {x : Coefficients}
    (F : IntegerFamily x) {a b u e ell : ℝ} (he : 0 < e)
    (hg : OwnCountGuards x ell) (hrows : OwnCountRows x a b u e ell)
    (D : TightMomentData x a b u e) : False := by
  let j := F.index
  let J := (j : ℝ) * ((j : ℝ) + 1)
  have hj : 3 ≤ j := F.index_ge_three
  have hJ : 0 < J := by
    have hjr : (3 : ℝ) ≤ j := by exact_mod_cast hj
    dsimp only [J]
    positivity
  have he0 := ne_of_gt he
  have hJ0 := ne_of_gt hJ
  have hhr : x 0 - x 4 = 2 / J := by
    rw [F.h_eq, F.r_eq]
    dsimp only [J, j]
    ring
  have hhp : x 0 - x 2 = 2 * ((j : ℝ) - 1) / J := by
    rw [F.h_eq, F.p_eq]
    dsimp only [J, j]
    ring
  have hBE : (1 - x 1) * (b / e) = (ell - x 3) + (x 0 - x 4) * (u / e) := by
    apply (mul_left_inj' he0).mp
    field_simp [he0]
    nlinarith only [hrows.BE]
  have hBA : (1 + ell) * (b / e - a / e) = 2 * x 0 * (u / e) + ell + x 1 := by
    apply (mul_left_inj' he0).mp
    field_simp [he0]
    nlinarith only [hrows.BA]
  have hAR : (ell - x 0) * (a / e) + (x 0 - 1) * (b / e) +
      (x 0 - x 2) * (u / e) + (ell - x 4) = 0 := by
    apply (mul_left_inj' he0).mp
    field_simp [he0]
    nlinarith only [hrows.AR]
  have hW : b / e - u / e = (ell - x 3) * J / 2 := by
    rw [hhr, F.v_eq] at hBE
    change (1 - (1 - 2 / J)) * (b / e) = ell - x 3 + (2 / J) * (u / e) at hBE
    field_simp [hJ0] at hBE
    apply (mul_left_inj' he0).mp
    field_simp [he0]
    nlinarith only [hBE]
  have hres := F.factorial_moment_nonnegative D
  have hnorm : 0 ≤ (u / e) ^ 2 - 2 * (u / e - b / e + 1) -
      ((j : ℝ) - 1) * (u / e) * (b / e - a / e - 1) := by
    have hd := div_nonneg hres (sq_nonneg e)
    have heq : (u ^ 2 - 2 * (u * e - b * e + e ^ 2) -
        ((j : ℝ) - 1) * ((b - a) * u - u * e)) / e ^ 2 =
        (u / e) ^ 2 - 2 * (u / e - b / e + 1) -
          ((j : ℝ) - 1) * (u / e) * (b / e - a / e - 1) := by
      field_simp [he0]
    rwa [heq] at hd
  have hmoment : 0 ≤ (u / e) ^ 2 - 2 * (1 - (ell - x 3) * J / 2) -
      ((j : ℝ) - 1) * (u / e) * (b / e - a / e - 1) := by
    have hid : u / e - b / e + 1 = 1 - (ell - x 3) * J / 2 := by linarith only [hW]
    rwa [hid] at hnorm
  apply stationary_integer_family_contradiction hj
    (a := a / e) (b := b / e) (u := u / e) (ell := ell)
  · exact ⟨F.q_eq ▸ hg.q_lt_ell, F.v_eq ▸ hg.ell_lt_v⟩
  · rw [hhr, F.v_eq, F.q_eq] at hBE
    change (2 / J) * (b / e) = ell - (1 - 4 / J) + (2 / J) * (u / e)
    convert hBE using 1
    ring
  · rw [F.h_eq, F.v_eq] at hBA
    change (1 + ell) * (b / e - a / e) =
      (4 * (j : ℝ) / J) * (u / e) + ell + 1 - 2 / J
    convert hBA using 1
    ring
  · rw [hhp, F.h_eq, F.r_eq] at hAR
    exact hAR
  · rw [F.q_eq] at hmoment
    exact hmoment

/-- The generic five-coordinate gate constructs its actual optimal vertex,
classifies all active integer counts, derives the factorial-moment inequality
and reaches contradiction. Physical own-data extraction remains explicit. -/
theorem no_optimal_face_with_own_rows_moments {a b u e V : ℝ}
    (hab : a < b) (hb : 0 < b) (hu : 0 < u) (he : 0 < e) (hbu : u < b)
    (hentry : ∃ x ∈ optimalFace a b u e V, 0 < x 0)
    (hmax : ∀ x ∈ feasible, objective a b u e x ≤ V)
    (hown : ∀ x ∈ optimalFace a b u e V, 0 < x 0 →
      ∃ ell, OwnCountGuards x ell ∧ OwnCountRows x a b u e ell ∧
        Nonempty (TightMomentData x a b u e)) : False := by
  obtain ⟨x, hx, hobj, hH, _, _, hfamily⟩ := exists_h_maximizing_integer_family
    hab hb hu he hbu hentry hmax (fun x hx hh => by
      obtain ⟨ell, hg, _, _⟩ := hown x hx hh
      exact ⟨ell, hg⟩)
  obtain ⟨x₀, hx₀, hh₀⟩ := hentry
  have hh : 0 < x 0 := hh₀.trans_le (hH x₀ hx₀)
  obtain ⟨ell, hg, hrows, ⟨D⟩⟩ := hown x ⟨hx.1, hobj⟩ hh
  obtain ⟨F⟩ := hfamily
  exact F.contradiction_of_own_rows_moments he hg hrows D

end Erdos1017.TwoAtomCountGate

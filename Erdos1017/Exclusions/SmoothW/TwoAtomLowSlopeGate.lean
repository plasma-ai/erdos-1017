module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomVertexClassification

/-!
# Low own-slope gate for the two-atom smooth-W case

An active dual whose own slope is at most two thirds is incompatible with its
derived integer family, whose `EE` penalty is at least two thirds, so the
all-count optimal-face gate closes at low own slopes
(`no_optimal_face_with_own_ell_le_two_thirds`).
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- The actual remaining integer family's EE penalty is at least two thirds. -/
theorem IntegerFamily.q_ge_two_thirds {x : Coefficients} (F : IntegerFamily x) :
    2 / 3 ≤ x 3 := by
  have hj : (3 : ℝ) ≤ F.index := by exact_mod_cast F.index_ge_three
  have hJ : (12 : ℝ) ≤ (F.index : ℝ) * ((F.index : ℝ) + 1) := by nlinarith
  have hJ0 : 0 < (F.index : ℝ) * ((F.index : ℝ) + 1) := by linarith
  have hfrac : 4 / ((F.index : ℝ) * ((F.index : ℝ) + 1)) ≤ (1 / 3 : ℝ) :=
    (div_le_iff₀ hJ0).mpr (by nlinarith)
  rw [F.q_eq]
  linarith

/-- The same active dual's own slope at most two thirds is incompatible
with its derived integer family and strict EE present floor. -/
theorem IntegerFamily.not_own_ell_le_two_thirds {x : Coefficients} (F : IntegerFamily x)
    {ell : ℝ} (hg : OwnCountGuards x ell) (hell : ell ≤ 2 / 3) : False := by
  have hq := F.q_ge_two_thirds
  linarith [hg.q_lt_ell]

/-- The full all-count optimal-face gate already closes at low own slopes.
It constructs its actual vertex/family, and needs no physical count moments. -/
theorem no_optimal_face_with_own_ell_le_two_thirds {a b u e V : ℝ}
    (hab : a < b) (hb : 0 < b) (hu : 0 < u) (he : 0 < e) (hbu : u < b)
    (hentry : ∃ x ∈ optimalFace a b u e V, 0 < x 0)
    (hmax : ∀ x ∈ feasible, objective a b u e x ≤ V)
    (hown : ∀ x ∈ optimalFace a b u e V, 0 < x 0 →
      ∃ ell, OwnCountGuards x ell ∧ ell ≤ 2 / 3) : False := by
  obtain ⟨x, hx, hobj, hH, _, _, hfamily⟩ := exists_h_maximizing_integer_family
    hab hb hu he hbu hentry hmax (fun x hx hh => by
      obtain ⟨ell, hg, _⟩ := hown x hx hh
      exact ⟨ell, hg⟩)
  obtain ⟨x₀, hx₀, hh₀⟩ := hentry
  have hh : 0 < x 0 := hh₀.trans_le (hH x₀ hx₀)
  obtain ⟨ell, hg, hell⟩ := hown x ⟨hx.1, hobj⟩ hh
  obtain ⟨F⟩ := hfamily
  exact F.not_own_ell_le_two_thirds hg hell

end Erdos1017.TwoAtomCountGate

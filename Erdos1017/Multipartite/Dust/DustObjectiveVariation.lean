module

public import Erdos1017.Multipartite.Dust.DustTwoHeadChord

/-!
# Affine dependence on one head mass

Every head mass enters the objective affinely, with its exterior row as slope
(`objective_update`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- Every head mass enters affinely, with its actual exterior row as slope. -/
theorem objective_update {m : ℕ} (C : Coefficients m) (p : Fin m → ℝ) (s : ℝ)
    (i : Fin m) (y : ℝ) :
    objective (Function.update p i y) s C = objective p s C +
      (y - p i) * (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * p j - s * incident C i) := by
  have hinc : (∑ j, incident C j * Function.update p i y j) =
      (∑ j, incident C j * p j) + incident C i * (y - p i) := by
    simp_rw [Selector.update_expansion, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp
  simp only [objective_dust_split]
  rw [Selector.objective_update, hinc]
  change _ = _ + (y - p i) *
    ((DustCellRestriction.headDual C).alpha i + _ - s * incident C i)
  ring

end Erdos1017.MultipartiteDust

module

public import Erdos1017.Multipartite.Dust.DustTypeCompletion

/-!
# Convexity of the two-head objective

When two empty head slots receive arbitrary masses, the objective is convex
along any fixed-total line, with exact chord gap equal to the pair penalty times
the product of the two masses.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- The exact objective when two empty head slots receive arbitrary masses. -/
theorem objective_two_heads {m : ℕ} (C : Coefficients m) (i j : Fin m) (hij : i ≠ j)
    (p : Fin m → ℝ) (hpi : p i = 0) (hpj : p j = 0) (u v s : ℝ) :
    objective (Function.update (Function.update p i u) j v) s C = objective p s C +
      u * (head C i + ∑ k, (DustCellRestriction.headDual C).beta i k * p k - s * incident C i) +
      v * (head C j + ∑ k, (DustCellRestriction.headDual C).beta j k * p k - s * incident C j) +
      (DustCellRestriction.headDual C).beta i j * u * v := by
  have hpj' : Function.update p i u j = 0 := by simp [Ne.symm hij, hpj]
  have hrow : (∑ k, (DustCellRestriction.headDual C).beta j k * Function.update p i u k) =
      (∑ k, (DustCellRestriction.headDual C).beta j k * p k) +
        (DustCellRestriction.headDual C).beta j i * u := by
    have ht (k : Fin m) : (DustCellRestriction.headDual C).beta j k * Function.update p i u k =
        (DustCellRestriction.headDual C).beta j k * p k +
          if k = i then (DustCellRestriction.headDual C).beta j i * u else 0 := by
      by_cases hk : k = i <;> simp [hk, Function.update_of_ne, hpi]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  have hinc : (∑ k, incident C k * Function.update p i u k) =
      (∑ k, incident C k * p k) + incident C i * u := by
    have ht (k : Fin m) : incident C k * Function.update p i u k =
        incident C k * p k + if k = i then incident C i * u else 0 := by
      by_cases hk : k = i <;> simp [hk, Function.update_of_ne, hpi]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  rw [objective_add_head C j _ hpj', objective_add_head C i p hpi,
    hrow, hinc,
    objective_dust_split C p s, objective_dust_split C p 0,
    (DustCellRestriction.headDual C).beta_symm j i]
  ring

/-- The two-head objective is convex along a fixed-total line. Its exact
chord gap is the pair penalty times the product of the two masses. -/
theorem two_head_chord {m : ℕ} (C : Coefficients m) (i j : Fin m) (hij : i ≠ j)
    (p : Fin m → ℝ) (hpi : p i = 0) (hpj : p j = 0) (x r s : ℝ) :
    (x - r) * objective (Function.update (Function.update p i x) j 0) s C +
      r * objective (Function.update (Function.update p i 0) j x) s C -
      x * objective (Function.update (Function.update p i (x - r)) j r) s C =
        -(DustCellRestriction.headDual C).beta i j * x * r * (x - r) := by
  rw [objective_two_heads C i j hij p hpi hpj,
    objective_two_heads C i j hij p hpi hpj,
    objective_two_heads C i j hij p hpi hpj]
  ring

end Erdos1017.MultipartiteDust

module

public import Erdos1017.Multipartite.Dust.DustUnboundedDual

/-!
# Adding a dust point to a head's exterior row

`addDustRow` adds one original dust point to the exterior row of an independent
head, with gain the head mass times the original dust row; each changed anchored
clique is an original clique with one more dust point, so the count tests hold
outside the unit box.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- Add one old dust point to the exterior row of a chosen independent head.
The resulting bounded dual is not required to stay in the coefficient box. -/
def addDustRow {m : ℕ} (C : Coefficients m) (i : Fin m) : Coefficients m
  | .inl j => if j = i then head C j + linear C - incident C i else head C j
  | .inr (.inl (j, k)) => pair C j k + if j = i then incident C k else if k = i then incident C j else 0
  | .inr (.inr (.inl j)) => if j = i then incident C j + penalty C else incident C j
  | .inr (.inr (.inr b)) => C (.inr (.inr (.inr b)))

theorem headDual_addDustRow_beta {m : ℕ} (C : Coefficients m) (i j k : Fin m) :
    (DustCellRestriction.headDual (addDustRow C i)).beta j k =
      (DustCellRestriction.headDual C).beta j k - (if j = i then incident C k else 0) -
        (if k = i then incident C j else 0) + (if j = i ∧ k = i then 2 * incident C i else 0) := by
  rcases lt_trichotomy j k with h | rfl | h
  · by_cases hj : j = i <;> by_cases hk : k = i <;>
      simp_all [DustCellRestriction.headDual, pair, addDustRow] <;> ring
  · by_cases hj : j = i
    · subst j
      simp [DustCellRestriction.headDual]
      ring
    · simp [DustCellRestriction.headDual, hj]
  · by_cases hj : j = i <;> by_cases hk : k = i <;>
      simp_all [DustCellRestriction.headDual, pair, addDustRow] <;> (try split_ifs) <;> ring

/-- The surgery gain is the new head mass times the old dust row, with the
missing independent-head diagonal restored explicitly. -/
theorem addDustRow_objective {m : ℕ} (C : Coefficients m) (i : Fin m)
    (p : Fin m → ℝ) (s : ℝ) :
    objective p s (addDustRow C i) = objective p s C + p i *
      (linear C - (∑ j, incident C j * p j) - penalty C * s - incident C i * (1 - p i)) := by
  have hh : (∑ j, head (addDustRow C i) j * p j) =
      (∑ j, head C j * p j) + (linear C - incident C i) * p i := by
    have ht (j : Fin m) : head (addDustRow C i) j * p j = head C j * p j +
        if j = i then (linear C - incident C i) * p i else 0 := by
      by_cases hj : j = i
      · subst j
        simp only [head, addDustRow, ↓reduceIte]
        ring
      · simp [head, addDustRow, hj]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  have hi : (∑ j, incident (addDustRow C i) j * p j) =
      (∑ j, incident C j * p j) + penalty C * p i := by
    have ht (j : Fin m) : incident (addDustRow C i) j * p j = incident C j * p j +
        if j = i then penalty C * p i else 0 := by
      by_cases hj : j = i
      · subst j
        simp only [incident, addDustRow, ↓reduceIte]
        ring
      · simp [incident, addDustRow, hj]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  have hpair : (∑ j, ∑ k, (DustCellRestriction.headDual (addDustRow C i)).beta j k * (p j * p k)) =
      (∑ j, ∑ k, (DustCellRestriction.headDual C).beta j k * (p j * p k)) -
        2 * p i * (∑ j, incident C j * p j) + 2 * incident C i * (p i) ^ 2 := by
    have ht (j k : Fin m) : (DustCellRestriction.headDual (addDustRow C i)).beta j k * (p j * p k) =
        (DustCellRestriction.headDual C).beta j k * (p j * p k) -
          (if j = i then p i * (incident C k * p k) else 0) -
          (if k = i then p i * (incident C j * p j) else 0) +
          (if j = i then if k = i then 2 * incident C i * (p i) ^ 2 else 0 else 0) := by
      rw [headDual_addDustRow_beta]
      by_cases hj : j = i <;> by_cases hk : k = i <;> simp [hj, hk] <;> ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_irrel,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
    rw [← Finset.mul_sum]
    ring
  simp only [objective_headDual, Selector.objective, ← Finset.sum_mul,
    show (DustCellRestriction.headDual (addDustRow C i)).alpha = head (addDustRow C i) from rfl,
    show (DustCellRestriction.headDual C).alpha = head C from rfl]
  rw [hh, hpair, hi]
  simp only [linear, penalty, addDustRow]
  ring

/-- Every changed anchored clique is literally an old clique with one
additional dust point. All old dust counts are retained. -/
theorem addDustRow_charge {m : ℕ} (C : Coefficients m) (i : Fin m)
    (X : Selector.Selection m) (k : ℕ) :
    charge (addDustRow C i) X k = charge C X (k + if X i then 1 else 0) := by
  rw [DustCellBridge.charge_eq_objective, addDustRow_objective, DustCellBridge.charge_eq_objective]
  simp only [penalty, addDustRow]
  cases hXi : X i
  · simp [Selector.bit]
  · simp only [↓reduceIte, Selector.bit]
    rw [objective_dust_split, objective_dust_split]
    push_cast
    unfold penalty
    ring

/-- The full literal count tests hold even when the new coefficients leave
the compact unit box. -/
theorem addDustRow_tests {m : ℕ} (C : Coefficients m)
    (hC : ∀ X k, charge C X k ≤ 1) (i : Fin m) : ∀ X k, charge (addDustRow C i) X k ≤ 1 := by
  intro X k
  rw [addDustRow_charge]
  exact hC _ _

end Erdos1017.MultipartiteDust

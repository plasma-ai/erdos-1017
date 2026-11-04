module

public import Erdos1017.Multipartite.Dust.DustRowSurgery

/-!
# Turning a dust cell into an independent head

`prependDustHead` turns one original dust cell into an independent head carrying
twice the original dust exterior row, possibly with negative anchor charge; its
exact objective gain counts the deleted internal dust pairs, and cliques using
it are original anchored cliques with two more dust points.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- Turn one old dust cell into an independent head carrying twice the old
dust exterior row. Its anchor charge can be negative. -/
def prependDustHead {m : ℕ} (C : Coefficients m) : Coefficients (m + 1)
  | .inl j => Fin.cases (2 * linear C - penalty C) (head C) j
  | .inr (.inl (j, k)) => Fin.cases (Fin.cases 0 (fun k => 2 * incident C k) k)
      (fun j => Fin.cases (2 * incident C j) (fun k => pair C j k) k) j
  | .inr (.inr (.inl j)) => Fin.cases (2 * penalty C) (incident C) j
  | .inr (.inr (.inr b)) => C (.inr (.inr (.inr b)))

/-- The new independent head has no internal charge; all exterior
interactions are the literal twice-dust row. -/
theorem prependDustHead_objective {m : ℕ} (C : Coefficients m) (p : Fin m → ℝ) (z s : ℝ) :
    objective (Fin.cons z p) s (prependDustHead C) = objective p s C +
      z * (2 * linear C - penalty C - 2 * (∑ j, incident C j * p j) - 2 * penalty C * s) := by
  simp only [objective, head, pair, incident, linear, penalty, prependDustHead,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ,
    Fin.succ_pos, Fin.succ_lt_succ_iff, Fin.not_lt_zero, ↓reduceIte,
    zero_mul, mul_zero, zero_add, mul_one]
  have hrow : (∑ j, 2 * C (.inr (.inr (.inl j))) * z * p j) =
      2 * z * ∑ j, C (.inr (.inr (.inl j))) * p j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrow]
  ring

/-- Removing the new independent cell from old dust gives its exact
objective gain, including the deleted internal dust pairs. -/
theorem prependDustHead_gain {m : ℕ} (C : Coefficients m) (p : Fin m → ℝ) (z s : ℝ) :
    objective (Fin.cons z p) (s - z) (prependDustHead C) = objective p s C +
      z * (linear C - (∑ j, incident C j * p j) - penalty C * s - penalty C) +
        3 * penalty C * z ^ 2 / 2 := by
  rw [prependDustHead_objective, objective_dust_split, objective_dust_split]
  ring

/-- A clique using the new independent cell is exactly an old anchored
clique with two more dust points for the purpose of its charge. -/
theorem prependDustHead_charge {m : ℕ} (C : Coefficients m)
    (X : Selector.Selection (m + 1)) (k : ℕ) :
    charge (prependDustHead C) X k = charge C (fun j => X j.succ) (k + if X 0 then 2 else 0) := by
  have hbits : (fun j => Selector.bit (X j)) =
      Fin.cons (Selector.bit (X 0)) (fun j => Selector.bit (X j.succ)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  rw [DustCellBridge.charge_eq_objective, hbits, prependDustHead_objective,
    DustCellBridge.charge_eq_objective]
  simp only [penalty, prependDustHead]
  cases hX : X 0
  · simp [Selector.bit]
  · simp only [↓reduceIte, Selector.bit]
    rw [objective_dust_split, objective_dust_split]
    push_cast
    unfold penalty
    ring

theorem prependDustHead_tests {m : ℕ} (C : Coefficients m)
    (hC : ∀ X k, charge C X k ≤ 1) : ∀ X k, charge (prependDustHead C) X k ≤ 1 := by
  intro X k
  rw [prependDustHead_charge]
  exact hC _ _

end Erdos1017.MultipartiteDust

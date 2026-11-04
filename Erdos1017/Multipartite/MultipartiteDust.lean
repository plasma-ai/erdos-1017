module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.FunProp

/-!
# Finite-head bounded homogeneous duals

Coordinates are linear head charges, head-pair and head-dust penalties, and the
linear and quadratic dust coefficients; the feasible set with all natural dust
counts is compact, and the optimum `value` is attained and depends continuously
on all mass parameters, with no physical primal attainment asserted.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators
open Set

/-- Linear head charges, head-pair penalties, head-dust penalties, and the
linear and quadratic dust coefficients. Unused diagonal pair slots are harmless. -/
abbrev Coordinate (m : ℕ) := Fin m ⊕ ((Fin m × Fin m) ⊕ (Fin m ⊕ Bool))

abbrev Coefficients (m : ℕ) := Coordinate m → ℝ

def head {m : ℕ} (D : Coefficients m) (i : Fin m) : ℝ := D (.inl i)
def pair {m : ℕ} (D : Coefficients m) (i j : Fin m) : ℝ := D (.inr (.inl (i, j)))
def incident {m : ℕ} (D : Coefficients m) (i : Fin m) : ℝ := D (.inr (.inr (.inl i)))
def linear {m : ℕ} (D : Coefficients m) : ℝ := D (.inr (.inr (.inr false)))
def penalty {m : ℕ} (D : Coefficients m) : ℝ := D (.inr (.inr (.inr true)))

/-- Rooted all-count charge. Each head is Boolean and dust has any natural count. -/
def charge {m : ℕ} (D : Coefficients m) (X : Selector.Selection m) (k : ℕ) : ℝ :=
  (∑ i, head D i * Selector.bit (X i)) -
    (∑ i, ∑ j, pair D i j * (if i < j then 1 else 0) * Selector.bit (X i) * Selector.bit (X j)) +
    (k : ℝ) * (linear D - ∑ i, incident D i * Selector.bit (X i)) -
    penalty D * (k : ℝ) * ((k : ℝ) - 1) / 2

/-- The compact coefficient box together with every finite count constraint. -/
def feasible (m : ℕ) : Set (Coefficients m) :=
  Icc 0 1 ∩ {D | ∀ X k, charge D X k ≤ 1}

/-- The bounded homogeneous dual objective in anchor-normalized masses.
This definition does not identify its maximum with a physical partition infimum. -/
def objective {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (D : Coefficients m) : ℝ :=
  (∑ i, head D i * p i) + linear D * s -
    (∑ i, ∑ j, pair D i j * (if i < j then 1 else 0) * p i * p j) -
    (∑ i, incident D i * p i * s) - penalty D * s ^ 2 / 2

theorem charge_continuous {m : ℕ} (X : Selector.Selection m) (k : ℕ) :
    Continuous (fun D : Coefficients m => charge D X k) := by
  unfold charge head pair incident linear penalty
  fun_prop

theorem objective_continuous {m : ℕ} (p : Fin m → ℝ) (s : ℝ) :
    Continuous (objective p s) := by
  unfold objective head pair incident linear penalty
  fun_prop

/-- Infinitely many count inequalities remain closed in the finite coefficient space. -/
theorem feasible_isCompact (m : ℕ) : IsCompact (feasible m) := by
  apply isCompact_Icc.inter_right
  simp only [ofPred_forall]
  exact isClosed_iInter (fun X => isClosed_iInter (fun k =>
    isClosed_le (charge_continuous X k) continuous_const))

theorem zero_mem_feasible (m : ℕ) : (0 : Coefficients m) ∈ feasible m := by
  constructor
  · constructor
    · exact le_rfl
    · intro i
      norm_num
  · intro X k
    simp [charge, head, pair, incident, linear, penalty]

/-- Finite-head bounded homogeneous duals attain their optimum, even with
all natural dust counts. No physical primal attainment is asserted. -/
theorem exists_optimal {m : ℕ} (p : Fin m → ℝ) (s : ℝ) :
    ∃ D ∈ feasible m, ∀ E ∈ feasible m, objective p s E ≤ objective p s D := by
  exact (feasible_isCompact m).exists_isMaxOn ⟨0, zero_mem_feasible m⟩
    (objective_continuous p s).continuousOn

/-- The maximum of the bounded homogeneous coefficient problem. -/
def value {m : ℕ} (p : Fin m → ℝ) (s : ℝ) : ℝ :=
  sSup (objective p s '' feasible m)

/-- Finite-head coefficient values depend continuously on all mass parameters. -/
theorem value_continuous (m : ℕ) :
    Continuous (fun z : (Fin m → ℝ) × ℝ => value z.1 z.2) := by
  apply (feasible_isCompact m).continuous_sSup
  unfold objective head pair incident linear penalty
  fun_prop

/-- The supremum defining the coefficient value is achieved by a feasible dual. -/
theorem exists_value_eq {m : ℕ} (p : Fin m → ℝ) (s : ℝ) :
    ∃ D ∈ feasible m, value p s = objective p s D := by
  obtain ⟨D, hD, heq, _⟩ := (feasible_isCompact m).exists_sSup_image_eq_and_ge
    ⟨0, zero_mem_feasible m⟩ (objective_continuous p s).continuousOn
  exact ⟨D, hD, heq⟩

end Erdos1017.MultipartiteDust

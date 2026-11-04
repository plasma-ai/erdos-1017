module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Fractional clique partitions of multipartite graphs

Selections pick at most one vertex from each independent part, `PrimalFeasible`
gives exact edge loads for a fractional partition of a weighted complete
multipartite graph, and adjoining an anchor turns an exact selector into an
exact normalized multipartite partition with a matching anchor dual.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Multipartite

open scoped BigOperators
open Selector (bit)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A clique selects at most one vertex from each independent part. -/
abbrev Selection (ι : Type*) := ι → Bool

/-- Empty and singleton selections carry no edges. -/
def Nontrivial (X : Selection ι) : Prop := ∃ i j, i ≠ j ∧ X i = true ∧ X j = true

/-- Exact edge loads for a fractional partition of a weighted complete multipartite graph. -/
def PrimalFeasible (a : ι → ℝ) (w : Selection ι → ℝ) : Prop :=
  (∀ X, 0 ≤ w X) ∧ (∀ X, ¬Nontrivial X → w X = 0) ∧
    ∀ i j, i ≠ j → ∑ X, w X * (bit (X i) * bit (X j)) = a i * a j

def cost (w : Selection ι → ℝ) : ℝ := ∑ X, w X

/-- The fractional clique-partition value; later lemmas exhibit feasible minimizers. -/
def value (a : ι → ℝ) : ℝ := sInf {c | ∃ w, PrimalFeasible a w ∧ cost w = c}

theorem cost_nonneg (a : ι → ℝ) (w : Selection ι → ℝ) (hw : PrimalFeasible a w) :
    0 ≤ cost w := Finset.sum_nonneg (fun X _ => hw.1 X)

theorem value_le_cost (a : ι → ℝ) (w : Selection ι → ℝ) (hw : PrimalFeasible a w) :
    value a ≤ cost w := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨v, hv, rfl⟩
    exact cost_nonneg a v hv
  · exact ⟨w, hw, rfl⟩

theorem value_eq_of_optimal (a : ι → ℝ) (w : Selection ι → ℝ)
    (hw : PrimalFeasible a w) (hmin : ∀ v, PrimalFeasible a v → cost w ≤ cost v) :
    value a = cost w := by
  apply le_antisymm (value_le_cost a w hw)
  refine le_csInf (s := {c | ∃ v, PrimalFeasible a v ∧ cost v = c}) ⟨cost w, w, hw, rfl⟩ ?_
  rintro c ⟨v, hv, rfl⟩
  exact hmin v hv

/-- Scaling all part masses by `t` scales every edge demand and cost by `t²`. -/
theorem scale_feasible (a : ι → ℝ) (w : Selection ι → ℝ)
    (hw : PrimalFeasible a w) (t : ℝ) :
    PrimalFeasible (fun i => t * a i) (fun X => t ^ 2 * w X) := by
  refine ⟨fun X => mul_nonneg (sq_nonneg t) (hw.1 X), ?_, ?_⟩
  · intro X hX
    simp only [hw.2.1 X hX, mul_zero]
  · intro i j hij
    simp_rw [mul_assoc, ← Finset.mul_sum, hw.2.2 i j hij]
    ring

theorem scale_cost (w : Selection ι → ℝ) (t : ℝ) :
    cost (fun X => t ^ 2 * w X) = t ^ 2 * cost w := by
  simp [cost, Finset.mul_sum]

/-- Signed edge charges, with each unordered edge represented twice. -/
structure Dual (ι : Type*) where
  beta : ι → ι → ℝ
  beta_symm : ∀ i j, beta i j = beta j i
  beta_diag : ∀ i, beta i i = 0

def objective (a : ι → ℝ) (D : Dual ι) : ℝ :=
  (∑ i, ∑ j, D.beta i j * (a i * a j)) / 2

def charge (D : Dual ι) (X : Selection ι) : ℝ := objective (fun i => bit (X i)) D

def DualFeasible (D : Dual ι) : Prop := ∀ X, charge D X ≤ 1

theorem primal_dual_identity (a : ι → ℝ) (w : Selection ι → ℝ)
    (hw : PrimalFeasible a w) (D : Dual ι) :
    (∑ X, w X * charge D X) = objective a D := by
  have hpair (i j : ι) :
      (∑ X, w X * (D.beta i j * (bit (X i) * bit (X j)))) = D.beta i j * (a i * a j) := by
    by_cases hij : i = j
    · subst j
      simp [D.beta_diag]
    · simp_rw [mul_left_comm (w _) (D.beta i j), ← Finset.mul_sum]
      rw [hw.2.2 i j hij]
  unfold charge objective
  simp only [mul_div, Finset.mul_sum, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => hpair i j)

theorem weak_duality (a : ι → ℝ) (w : Selection ι → ℝ) (D : Dual ι)
    (hw : PrimalFeasible a w) (hD : DualFeasible D) : objective a D ≤ cost w := by
  rw [← primal_dual_identity a w hw D]
  apply Finset.sum_le_sum
  intro X _
  simpa using mul_le_mul_of_nonneg_left (hD X) (hw.1 X)

theorem objective_le_value (a : ι → ℝ) (D : Dual ι) (hD : DualFeasible D)
    (hfeasible : ∃ w, PrimalFeasible a w) : objective a D ≤ value a := by
  obtain ⟨w, hw⟩ := hfeasible
  refine le_csInf (s := {c | ∃ v, PrimalFeasible a v ∧ cost v = c}) ⟨cost w, w, hw, rfl⟩ ?_
  rintro c ⟨v, hv, rfl⟩
  exact weak_duality a v D hv hD

omit [DecidableEq ι] in
theorem scale_objective (a : ι → ℝ) (D : Dual ι) (t : ℝ) :
    objective (fun i => t * a i) D = t ^ 2 * objective a D := by
  unfold objective
  have hterm (i j : ι) : D.beta i j * (t * a i * (t * a j)) =
      t ^ 2 * (D.beta i j * (a i * a j)) := by ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

/-- The normalized largest part is indexed by `none`. -/
def anchorMasses {m : ℕ} (p : Fin m → ℝ) : Option (Fin m) → ℝ := Option.elim' 1 p

/-- Adjoin the anchor to every nonempty selector outcome. -/
def anchorWeight {m : ℕ} (w : Selector.Selection m → ℝ)
    (X : Selection (Option (Fin m))) : ℝ :=
  if X none then w (fun i => X (some i)) else 0

theorem anchor_sum {m : ℕ} (w : Selector.Selection m → ℝ)
    (h : Selection (Option (Fin m)) → ℝ) :
    (∑ X, anchorWeight w X * h X) =
      ∑ X, w X * h (Option.elim' true X) := by
  rw [← (Equiv.piOptionEquivProd (β := fun _ : Option (Fin m) => Bool)).symm.sum_comp]
  simp [Fintype.sum_prod_type, anchorWeight, Equiv.piOptionEquivProd_symm_apply]
  apply Finset.sum_congr rfl
  intro X _
  have heq : Equiv.piOptionEquivProd.symm (true, X) = Option.elim' true X := by
    funext i
    cases i <;> rfl
  rw [heq]

theorem anchor_cost {m : ℕ} (w : Selector.Selection m → ℝ) :
    cost (anchorWeight w) = Selector.cost w := by
  simpa [cost, Selector.cost] using anchor_sum w (fun _ => 1)

/-- An exact selector produces an exact normalized multipartite partition. -/
theorem anchor_feasible {m : ℕ} (p : Fin m → ℝ) (w : Selector.Selection m → ℝ)
    (hw : Selector.PrimalFeasible p w) : PrimalFeasible (anchorMasses p) (anchorWeight w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    unfold anchorWeight
    split_ifs
    · exact hw.1 _
    · exact le_rfl
  · intro X hX
    unfold anchorWeight
    split_ifs with h
    · have hempty : (fun i => X (some i)) = (fun _ => false) := by
        funext i
        cases hi : X (some i)
        · rfl
        · exact False.elim (hX ⟨none, some i, by simp, h, hi⟩)
      rw [hempty]
      exact hw.2.1
    · rfl
  · intro i j hij
    rw [anchor_sum]
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        change (∑ X, w X * (1 * bit (X j))) = 1 * p j
        simpa only [one_mul] using hw.2.2.1 j
    | some i =>
      cases j with
      | none =>
        change (∑ X, w X * (bit (X i) * 1)) = p i * 1
        simpa only [mul_one] using hw.2.2.1 i
      | some j =>
        simpa [anchorMasses, Option.elim'] using hw.2.2.2 i j (fun h => hij (congrArg some h))

/-- Selector first charges become anchor-edge charges. -/
def anchorDual {m : ℕ} (D : Selector.Dual m) : Dual (Option (Fin m)) where
  beta i j := match i, j with
    | none, none => 0
    | none, some j => D.alpha j
    | some i, none => D.alpha i
    | some i, some j => D.beta i j
  beta_symm i j := by cases i <;> cases j <;> simp [D.beta_symm]
  beta_diag i := by cases i <;> simp [D.beta_diag]

theorem anchor_objective {m : ℕ} (p : Fin m → ℝ) (D : Selector.Dual m) :
    objective (anchorMasses p) (anchorDual D) = Selector.objective p D := by
  simp [objective, anchorMasses, anchorDual, Selector.objective, Option.elim',
    Fintype.sum_option, Finset.sum_add_distrib]
  ring

theorem anchor_charge {m : ℕ} (D : Selector.Dual m)
    (X : Selection (Option (Fin m))) :
    charge (anchorDual D) X =
      bit (X none) * (∑ i, D.alpha i * bit (X (some i))) +
        (∑ i, ∑ j, D.beta i j * (bit (X (some i)) * bit (X (some j)))) / 2 := by
  simp only [charge, objective, anchorDual, Fintype.sum_option, zero_mul, zero_add,
    Finset.sum_add_distrib]
  have hleft : (∑ i, D.alpha i * (bit (X none) * bit (X (some i)))) =
      bit (X none) * ∑ i, D.alpha i * bit (X (some i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i, D.alpha i * (bit (X (some i)) * bit (X none))) =
      bit (X none) * ∑ i, D.alpha i * bit (X (some i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, hright]
  ring

/-- Nonpositive pair charges ensure that cliques avoiding the anchor pass their tests. -/
theorem anchor_dual_feasible {m : ℕ} (D : Selector.Dual m)
    (hD : Selector.DualFeasible D) (hbeta : ∀ i j, D.beta i j ≤ 0) :
    DualFeasible (anchorDual D) := by
  intro X
  rw [anchor_charge]
  cases h : X none
  · simp only [show bit false = 0 from rfl, zero_mul, zero_add]
    have hpair : (∑ i, ∑ j, D.beta i j * (bit (X (some i)) * bit (X (some j)))) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      apply Finset.sum_nonpos
      intro j _
      apply mul_nonpos_of_nonpos_of_nonneg (hbeta i j)
      exact mul_nonneg (by cases X (some i) <;> norm_num [bit])
        (by cases X (some j) <;> norm_num [bit])
    linarith
  · simpa [bit, h, Selector.quadratic, Selector.objective] using hD (fun i => X (some i))

end Erdos1017.Multipartite

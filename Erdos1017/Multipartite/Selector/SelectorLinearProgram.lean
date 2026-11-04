module

public import Erdos1017.FractionalLimit.Selector
public import Erdos1017.Models.FiniteLinearProgram
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The finite selector linear program

The finite selector LP has one coordinate for each first moment and each
unordered pair moment. Its nonempty Boolean columns span this space. Strictly
positive Bernoulli weights therefore allow the finite LP duality theorem to
produce an attained selector dual in the symmetric coefficient convention.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.SelectorLinearProgram

open scoped BigOperators
open Selector

abbrev Pair (m : ℕ) := {ij : Fin m × Fin m // ij.1 < ij.2}
abbrev Coordinate (m : ℕ) := Fin m ⊕ Pair m
abbrev Moments (m : ℕ) := Coordinate m → ℝ
abbrev NonemptySelection (m : ℕ) := {X : Selection m // X ≠ (fun _ => false)}

/-- First and unordered pair moments, without redundant coordinates. -/
def target {m : ℕ} (p : Fin m → ℝ) : Moments m
  | .inl i => p i
  | .inr ij => p ij.val.1 * p ij.val.2

def column {m : ℕ} (X : Selection m) : Moments m := target (fun i => bit (X i))

def singleton {m : ℕ} (i : Fin m) : Selection m := fun k => decide (k = i)
def pairSelection {m : ℕ} (i j : Fin m) : Selection m := fun k => decide (k = i ∨ k = j)

theorem singleton_nonempty {m : ℕ} (i : Fin m) : singleton i ≠ (fun _ => false) := by
  intro h
  have := congrFun h i
  simp [singleton] at this

theorem pairSelection_nonempty {m : ℕ} (i j : Fin m) : pairSelection i j ≠ (fun _ => false) := by
  intro h
  have := congrFun h i
  simp [pairSelection] at this

theorem singleton_column {m : ℕ} (i : Fin m) :
    column (singleton i) = Pi.single (.inl i : Coordinate m) 1 := by
  funext c
  rcases c with k | ⟨⟨a, b⟩, hab⟩
  · simp [column, target, singleton, bit, Pi.single_apply]
  · have hne : a ≠ b := ne_of_lt hab
    by_cases ha : a = i <;> by_cases hb : b = i <;>
      simp_all [column, target, singleton, bit]

theorem pair_column {m : ℕ} (ij : Pair m) :
    column (pairSelection ij.val.1 ij.val.2) =
      Pi.single (.inl ij.val.1 : Coordinate m) 1 + Pi.single (.inl ij.val.2 : Coordinate m) 1 +
        Pi.single (.inr ij : Coordinate m) 1 := by
  rcases ij with ⟨⟨i, j⟩, hij⟩
  funext c
  rcases c with k | ⟨⟨a, b⟩, hab⟩
  · have hne : i ≠ j := ne_of_lt hij
    by_cases hk : k = i <;> by_cases hk' : k = j <;>
      simp_all [column, target, pairSelection, bit]
  · have horder : (a = i ∨ a = j) ∧ (b = i ∨ b = j) ↔ a = i ∧ b = j := by
      constructor
      · rintro ⟨ha | ha, hb | hb⟩ <;> subst_vars <;> simp_all [lt_asymm]
      · tauto
    simp only [column, target, pairSelection, bit, Pi.add_apply, Pi.single_apply,
      Sum.inr.injEq, decide_eq_true_eq]
    by_cases heq : a = i ∧ b = j
    · rcases heq with ⟨rfl, rfl⟩
      simp
    · have hn := mt horder.mp heq
      by_cases ha : a = i ∨ a = j <;> by_cases hb : b = i ∨ b = j <;>
        simp_all [Subtype.ext_iff, Prod.ext_iff]

/-- Singleton columns and pair columns span all first and unordered pair coordinates. -/
theorem columns_span (m : ℕ) :
    Submodule.span ℝ (Set.range (fun X : NonemptySelection m => column X.val)) = ⊤ := by
  apply top_unique
  intro v _
  have hbasis : ∀ c : Coordinate m,
      Pi.single c (1 : ℝ) ∈ Submodule.span ℝ (Set.range (fun X : NonemptySelection m => column X.val)) := by
    intro c
    rcases c with i | ij
    · rw [← singleton_column]
      exact Submodule.subset_span ⟨⟨singleton i, singleton_nonempty i⟩, rfl⟩
    · let S := Submodule.span ℝ (Set.range (fun X : NonemptySelection m => column X.val))
      have hpair : column (pairSelection ij.val.1 ij.val.2) ∈ S :=
        Submodule.subset_span ⟨⟨pairSelection ij.val.1 ij.val.2, pairSelection_nonempty _ _⟩, rfl⟩
      have hi : column (singleton ij.val.1) ∈ S :=
        Submodule.subset_span ⟨⟨singleton ij.val.1, singleton_nonempty _⟩, rfl⟩
      have hj : column (singleton ij.val.2) ∈ S :=
        Submodule.subset_span ⟨⟨singleton ij.val.2, singleton_nonempty _⟩, rfl⟩
      rw [singleton_column] at hi hj
      rw [pair_column] at hpair
      simpa only [add_sub_cancel_left] using
        Submodule.sub_mem _ hpair (Submodule.add_mem _ hi hj)
  have hv := (Pi.basisFun ℝ (Coordinate m)).sum_repr v
  rw [← hv]
  apply Submodule.sum_mem
  intro c _
  apply Submodule.smul_mem
  simpa only [Pi.basisFun_apply] using hbasis c

/-- Omitting the empty assignment preserves a sum whose empty summand vanishes. -/
theorem sum_nonempty {m : ℕ} {V : Type*} [AddCommMonoid V]
    (f : Selection m → V) (hf : f (fun _ => false) = 0) :
    (∑ X : NonemptySelection m, f X.val) = ∑ X : Selection m, f X := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun X : Selection m => X ≠ (fun _ => false))
    (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro X _
  by_cases hX : X = (fun _ => false)
  · simp [hX, hf]
  · simp [hX]

/-- The Bernoulli selector realizes the target vector in the nonredundant coordinate space. -/
theorem bernoulli_vector_moment {m : ℕ} (p : Fin m → ℝ) :
    FinitePrimal.moment (fun X : NonemptySelection m => column X.val)
      (fun X => selectorWeight p X.val) = target p := by
  rw [FinitePrimal.moment, sum_nonempty (fun X => selectorWeight p X • column X)
    (by simp [selectorWeight])]
  funext c
  rcases c with i | ij
  · simpa [column, target, Finset.sum_apply] using selector_first_moment p i
  · simpa [column, target, Finset.sum_apply] using
      selector_pair_moment p ij.val.1 ij.val.2 (ne_of_lt ij.property)

/-- Every interior selector has an attained primal and a supporting linear dual. -/
theorem exists_linear_primal_dual {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) :
    ∃ w : NonemptySelection m → ℝ,
      FinitePrimal.Feasible (fun X : NonemptySelection m => column X.val) (target p) w ∧
      ∃ y : Moments m →L[ℝ] ℝ,
        (∀ X : NonemptySelection m, y (column X.val) ≤ 1) ∧
        y (target p) = FinitePrimal.cost w ∧
        ∀ v, FinitePrimal.Feasible (fun X : NonemptySelection m => column X.val) (target p) v →
          FinitePrimal.cost w ≤ FinitePrimal.cost v := by
  exact FiniteLinearProgram.exists_primal_dual _ _ (fun X => selectorWeight p X.val)
    (fun X => selectorWeight_pos p hp X.val X.property) (bernoulli_vector_moment p) (columns_span m)

/-- A symmetric coefficient array made from coefficients on unordered pairs. -/
def coordinateDual {m : ℕ} (c : Coordinate m → ℝ) : Dual m where
  alpha i := c (.inl i)
  beta i j := if hij : i < j then c (.inr ⟨(i, j), hij⟩)
    else if hji : j < i then c (.inr ⟨(j, i), hji⟩) else 0
  beta_symm i j := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt_of_gt hij]
    · rfl
    · simp [hji, not_lt_of_gt hji]
  beta_diag i := by simp

/-- Passing from ordered symmetric pair terms to one term per unordered pair. -/
theorem symmetric_pair_sum {m : ℕ} (f : Fin m → Fin m → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ ij : Pair m, f ij.val.1 ij.val.2 := by
  classical
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt_of_gt hij]
    · simp [hdiag]
    · simp [hji, not_lt_of_gt hji, hsymm]
  have hsum : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) + (∑ i, ∑ j, if j < i then f j i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hsplit i j)
  have htri : (∑ i, ∑ j, if i < j then f i j else 0) = ∑ ij : Pair m, f ij.val.1 ij.val.2 := by
    rw [← Fintype.sum_prod_type (fun ij : Fin m × Fin m =>
      if ij.1 < ij.2 then f ij.1 ij.2 else 0), ← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [htri] at hsum
  have hother : (∑ i, ∑ j, if j < i then f j i else 0) = ∑ ij : Pair m, f ij.val.1 ij.val.2 := by
    rw [Finset.sum_comm]
    exact htri
  rw [hother] at hsum
  linarith

/-- The symmetric quadratic convention agrees with the unordered-coordinate pairing. -/
theorem coordinateDual_objective {m : ℕ} (p : Fin m → ℝ) (c : Coordinate m → ℝ) :
    objective p (coordinateDual c) = ∑ k, c k * target p k := by
  unfold objective
  rw [symmetric_pair_sum (fun i j => (coordinateDual c).beta i j * (p i * p j))
    (by intro i j; rw [Dual.beta_symm]; ring) (by intro i; simp [Dual.beta_diag])]
  simp only [coordinateDual]
  rw [Fintype.sum_sum_type]
  simp only [target]
  congr 1
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  apply Finset.sum_congr rfl
  intro ij _
  simp [ij.property]

/-- Every functional is its coordinate pairing in the standard basis. -/
theorem functional_pairing {m : ℕ} (y : Moments m →L[ℝ] ℝ) (v : Moments m) :
    (∑ k, y (Pi.single k 1) * v k) = y v := by
  have h := congrArg y ((Pi.basisFun ℝ (Coordinate m)).sum_repr v)
  simpa only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr, smul_eq_mul,
    mul_comm] using h

def functionalDual {m : ℕ} (y : Moments m →L[ℝ] ℝ) : Dual m :=
  coordinateDual (fun k => y (Pi.single k 1))

theorem functionalDual_objective {m : ℕ} (y : Moments m →L[ℝ] ℝ) (p : Fin m → ℝ) :
    objective p (functionalDual y) = y (target p) := by
  rw [functionalDual, coordinateDual_objective, functional_pairing]

theorem functionalDual_quadratic {m : ℕ} (y : Moments m →L[ℝ] ℝ) (X : Selection m) :
    quadratic (functionalDual y) X = y (column X) := functionalDual_objective y _

/-- A linear dual on nonempty columns is a feasible signed quadratic selector dual. -/
theorem functionalDual_feasible {m : ℕ} (y : Moments m →L[ℝ] ℝ)
    (hy : ∀ X : NonemptySelection m, y (column X.val) ≤ 1) :
    DualFeasible (functionalDual y) := by
  intro X
  by_cases hX : X = (fun _ => false)
  · simp [hX, quadratic_empty]
  · rw [functionalDual_quadratic]
    exact hy ⟨X, hX⟩

/-- Extend weights on nonempty subsets by zero at the empty assignment. -/
def liftWeights {m : ℕ} (w : NonemptySelection m → ℝ) (X : Selection m) : ℝ :=
  if hX : X ≠ (fun _ => false) then w ⟨X, hX⟩ else 0

theorem liftWeights_cost {m : ℕ} (w : NonemptySelection m → ℝ) :
    cost (liftWeights w) = FinitePrimal.cost w := by
  rw [cost, ← sum_nonempty (liftWeights w) (by simp [liftWeights])]
  apply Finset.sum_congr rfl
  intro X _
  simp [liftWeights, X.property]

theorem liftWeights_feasible {m : ℕ} (p : Fin m → ℝ) (w : NonemptySelection m → ℝ)
    (hw : FinitePrimal.Feasible (fun X : NonemptySelection m => column X.val) (target p) w) :
    PrimalFeasible p (liftWeights w) := by
  have hmoment : (∑ X : Selection m, liftWeights w X • column X) = target p := by
    rw [← sum_nonempty (fun X => liftWeights w X • column X) (by simp [liftWeights])]
    calc
      _ = ∑ X : NonemptySelection m, w X • column X.val := by
        apply Finset.sum_congr rfl
        intro X _
        simp [liftWeights, X.property]
      _ = target p := hw.2
  refine ⟨?_, by simp [liftWeights], ?_, ?_⟩
  · intro X
    unfold liftWeights
    split_ifs with hX
    · exact hw.1 ⟨X, hX⟩
    · exact le_rfl
  · intro i
    have h := congrFun hmoment (.inl i)
    simpa [column, target, Finset.sum_apply] using h
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := congrFun hmoment (.inr ⟨(i, j), hij⟩)
      simpa [column, target, Finset.sum_apply] using h
    · have h := congrFun hmoment (.inr ⟨(j, i), hji⟩)
      simpa [column, target, Finset.sum_apply, mul_comm] using h

/-- Interior product targets have attained exact selector primal and quadratic dual optima. -/
theorem exists_primal_dual {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    ∃ w : Selection m → ℝ, PrimalFeasible p w ∧
      ∃ D : Dual m, DualOptimal p D ∧ objective p D = cost w := by
  obtain ⟨w, hw, y, hy, hvalue, _⟩ := exists_linear_primal_dual p hp
  have hprimal := liftWeights_feasible p w hw
  have hdual := functionalDual_feasible y hy
  have heq : objective p (functionalDual y) = cost (liftWeights w) := by
    rw [functionalDual_objective, liftWeights_cost]
    exact hvalue
  refine ⟨liftWeights w, hprimal, functionalDual y, ⟨hdual, ?_⟩, heq⟩
  intro D hD
  rw [heq]
  exact Selector.weak_duality p _ D hprimal hD

/-- The finite selector dual optimum exists for every strictly interior product target. -/
theorem exists_optimal_dual {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) :
    ∃ D : Dual m, DualOptimal p D := by
  obtain ⟨_, _, D, hD, _⟩ := exists_primal_dual p hp
  exact ⟨D, hD⟩

end Erdos1017.SelectorLinearProgram

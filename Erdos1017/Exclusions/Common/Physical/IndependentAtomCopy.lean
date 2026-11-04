module

public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Copying an independent atom

A new independent type adjacent to the common old neighborhood is defined, with
a charge paying each copied edge once and compensating on the root atom; a
copied clique costs no more than the old clique obtained by expanding the new
vertex to its source pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.IndependentAtomCopy

/-- One new independent type sees exactly the common old neighborhood. -/
def adjacency {Ω : Type*} (A : Ω → Ω → Bool) (x y : Ω) : Option Ω → Option Ω → Bool
  | none, none => false
  | none, some z => A x z && A y z
  | some z, none => A x z && A y z
  | some z, some w => A z w

/-- Copying an adjacent pair pays its old edge once, with a compensating
increment on the common independent root atom. -/
def charge {Ω : Type*} (Y : Ω → Ω → ℝ) (I : Set Ω) (x y : Ω) : Option Ω → Option Ω → ℝ
  | none, none => 0
  | none, some z => Y x z + Y y z + Y x y * I.indicator (fun _ => 1) z
  | some z, none => Y x z + Y y z + Y x y * I.indicator (fun _ => 1) z
  | some z, some w => Y z w

/-- The copied root has exactly its declared row in every finite test. -/
theorem tupleCharge_copy_root {Ω : Type*} {n : ℕ} (Y : Ω → Ω → ℝ)
    (I : Set Ω) (x y : Ω) (v : Fin n → Ω) :
    FiniteArity.tupleCharge (charge Y I x y) (Fin.cons none (fun i => some (v i))) =
      FiniteArity.tupleCharge Y v + ∑ i,
        (Y x (v i) + Y y (v i) + Y x y * I.indicator (fun _ => 1) (v i)) := by
  rw [FiniteArity.tupleCharge_cons (charge Y I x y) none (fun i => some (v i))
    (fun _ => rfl)]
  change (∑ i, (Y x (v i) + Y y (v i) + Y x y * I.indicator (fun _ => 1) (v i))) +
    FiniteArity.tupleCharge Y v = _
  ring

/-- An old clique meets an independent root set in at most one coordinate. -/
theorem indicator_sum_le_one {Ω : Type*} {n : ℕ} (I : Set Ω) (v : Fin n → Ω)
    (hindependent : ∀ i j, i ≠ j → ¬(v i ∈ I ∧ v j ∈ I)) :
    (∑ i, I.indicator (fun _ => (1 : ℝ)) (v i)) ≤ 1 := by
  have hc : ((Finset.univ : Finset (Fin n)).filter (fun i => v i ∈ I)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hne
    exact hindependent i j hne ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  have he : (∑ i, I.indicator (fun _ => (1 : ℝ)) (v i)) =
      (((Finset.univ : Finset (Fin n)).filter (fun i => v i ∈ I)).card : ℝ) := by
    simp only [indicator, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [he]
  exact_mod_cast hc

/-- The literal copied clique is no more expensive than the old clique
obtained by expanding its new vertex to the adjacent source pair. -/
theorem tupleCharge_copy_le_expansion {Ω : Type*} {n : ℕ} (Y : Ω → Ω → ℝ)
    (I : Set Ω) (x y : Ω) (v : Fin n → Ω)
    (hxy : Y y x = Y x y) (hx : ∀ i, Y (v i) x = Y x (v i))
    (hy : ∀ i, Y (v i) y = Y y (v i)) (hq : 0 ≤ Y x y)
    (hindependent : ∀ i j, i ≠ j → ¬(v i ∈ I ∧ v j ∈ I)) :
    FiniteArity.tupleCharge (charge Y I x y) (Fin.cons none (fun i => some (v i))) ≤
      FiniteArity.tupleCharge Y (Fin.cons x (Fin.cons y v)) := by
  rw [tupleCharge_copy_root, FiniteArity.tupleCharge_cons _ x _
    (fun i => Fin.cases hxy hx i), FiniteArity.tupleCharge_cons _ y _ hy]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hb := mul_le_mul_of_nonneg_left (indicator_sum_le_one I v hindependent) hq
  nlinarith only [hb]

/-- Actual expanded old tests imply the new root test, including zero
source charge and empty leaf tuples. -/
theorem tupleCharge_copy_le_one {Ω : Type*} {n : ℕ} (Y : Ω → Ω → ℝ)
    (I : Set Ω) (x y : Ω) (v : Fin n → Ω)
    (hxy : Y y x = Y x y) (hx : ∀ i, Y (v i) x = Y x (v i))
    (hy : ∀ i, Y (v i) y = Y y (v i)) (hq : 0 ≤ Y x y)
    (hindependent : ∀ i j, i ≠ j → ¬(v i ∈ I ∧ v j ∈ I))
    (hfull : FiniteArity.tupleCharge Y (Fin.cons x (Fin.cons y v)) ≤ 1) :
    FiniteArity.tupleCharge (charge Y I x y) (Fin.cons none (fun i => some (v i))) ≤ 1 :=
  (tupleCharge_copy_le_expansion Y I x y v hxy hx hy hq hindependent).trans hfull

end Erdos1017.IndependentAtomCopy

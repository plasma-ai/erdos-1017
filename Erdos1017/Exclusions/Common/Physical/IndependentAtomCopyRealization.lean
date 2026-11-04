module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopySections
public import Erdos1017.Models.Capped.CappedUniversalVertices

/-!
# Realizing the independent atom copy on marked points

A marked point is either a fresh mark or an old point; the marked adjacency and
charge are defined, two fresh marks cannot share a clique, and the independent
fresh-cell law preserves every full scalar test for almost every source pair at
all masses and orders.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.IndependentAtomCopy

/-- A fresh mark is the new independent type; an old mark keeps its point. -/
def markedPoint {Ω : Type*} (z : Ω × Bool) : Option Ω :=
  if z.2 = true then none else some z.1

def markedAdjacency {Ω : Type*} (A : Ω → Ω → Bool) (x y : Ω)
    (z w : Ω × Bool) : Bool := adjacency A x y (markedPoint z) (markedPoint w)

/-- Absent pairs have zero charge, including pairs outside the copied
type's common neighborhood. Old clique charges are retained. -/
def markedCharge {Ω : Type*} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I : Set Ω) (x y : Ω) (z w : Ω × Bool) : ℝ :=
  if markedAdjacency A x y z w = true
  then charge Y I x y (markedPoint z) (markedPoint w) else 0

/-- Relabeling a finite tuple does not change its unordered charge. -/
theorem tupleCharge_comp_equiv {Ω : Type*} {n : ℕ} (Y : Ω → Ω → ℝ)
    (v : Fin n → Ω) (e : Fin n ≃ Fin n) :
    FiniteArity.tupleCharge Y (fun i => v (e i)) = FiniteArity.tupleCharge Y v := by
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  congr 1
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp only [e.injective.eq_iff]

/-- On a genuine clique the absent-pair zeroing has no effect. -/
theorem tupleCharge_marked_eq_raw {Ω : Type*} {n : ℕ}
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I : Set Ω) (x y : Ω)
    (v : Fin n → Ω × Bool) (hv : FiniteArity.TupleClique (markedAdjacency A x y) v) :
    FiniteArity.tupleCharge (markedCharge A Y I x y) v =
      FiniteArity.tupleCharge (charge Y I x y) (fun i => markedPoint (v i)) := by
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp only [hij, ite_true]
  · simp only [hij, ite_false, markedCharge, hv i j hij, ite_true]

/-- Two fresh independent marks cannot occur in one clique. -/
theorem unique_fresh_coordinate {Ω : Type*} {n : ℕ} (A : Ω → Ω → Bool) (x y : Ω)
    (v : Fin n → Ω × Bool) (hv : FiniteArity.TupleClique (markedAdjacency A x y) v)
    (r : Fin n) (hr : (v r).2 = true) : ∀ i, (v i).2 = true → i = r := by
  intro i hi
  by_contra hir
  have h := hv i r hir
  simp only [markedAdjacency, markedPoint, hi, hr, ite_true, adjacency] at h
  exact Bool.noConfusion h

/-- Every marked clique is either old, or expands to the licensed copied
root and an injectively selected tuple of old coordinates. -/
theorem marked_tuple_test {Ω : Type*} {n : ℕ}
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I : Set Ω) (x y : Ω)
    (v : Fin n → Ω × Bool)
    (hold : FiniteArity.TupleClique A (fun i => (v i).1) →
      FiniteArity.tupleCharge Y (fun i => (v i).1) ≤ 1)
    (hcopy : ∀ k, ∀ e : Fin k ↪ Fin n,
      FiniteArity.TupleClique A (fun i => (v (e i)).1) →
      (∀ i, A x (v (e i)).1 = true ∧ A y (v (e i)).1 = true) →
      FiniteArity.tupleCharge (charge Y I x y)
        (Fin.cons none (fun i => some (v (e i)).1)) ≤ 1) :
    FiniteArity.TupleClique (markedAdjacency A x y) v →
      FiniteArity.tupleCharge (markedCharge A Y I x y) v ≤ 1 := by
  intro hv
  rw [tupleCharge_marked_eq_raw A Y I x y v hv]
  by_cases hfresh : ∃ i, (v i).2 = true
  · obtain ⟨r, hr⟩ := hfresh
    cases n with
    | zero => exact r.elim0
    | succ n =>
      let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 r
      let f : Fin n ↪ Fin (n + 1) :=
        ⟨fun i => e i.succ, fun _ _ h => Fin.succ_inj.mp (e.injective h)⟩
      have he0 : e 0 = r := Equiv.swap_apply_left _ _
      have hf : ∀ i, (v (f i)).2 ≠ true := by
        intro i hi
        have he := unique_fresh_coordinate A x y v hv r hr (f i) hi
        have h := e.injective (he.trans he0.symm)
        exact Fin.succ_ne_zero i h
      have hpoint : (fun i => markedPoint (v (e i))) =
          Fin.cons none (fun i => some (v (f i)).1) := by
        funext i
        cases i using Fin.cases with
        | zero => simp only [he0, markedPoint, hr, ite_true, Fin.cons_zero]
        | succ i =>
          change markedPoint (v (f i)) = some (v (f i)).1
          exact ite_eq_right (hf i)
      rw [← tupleCharge_comp_equiv (charge Y I x y) (fun i => markedPoint (v i)) e,
        hpoint]
      apply hcopy n f
      · intro i j hij
        have he := hv (f i) (f j) (fun he => hij (f.injective he))
        simpa [markedAdjacency, markedPoint, hf i, hf j, adjacency] using he
      · intro i
        have hne : r ≠ f i := fun he => Fin.succ_ne_zero i
          (e.injective ((show e i.succ = f i from rfl).trans (he.symm.trans he0.symm)))
        have he := hv r (f i) hne
        simpa [markedAdjacency, markedPoint, hr, hf i, adjacency] using he
  · have hn : ∀ i, (v i).2 ≠ true := fun i hi => hfresh ⟨i, hi⟩
    have he : (fun i => markedPoint (v i)) = fun i => some (v i).1 := by
      funext i
      exact ite_eq_right (hn i)
    rw [he]
    change FiniteArity.tupleCharge Y (fun i => (v i).1) ≤ 1
    apply hold
    intro i j hij
    simpa [markedAdjacency, markedPoint, hn i, hn j, adjacency]
      using hv i j hij

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual independent fresh-cell law preserves every full scalar
test for almost every source pair, simultaneously at all masses and orders. -/
theorem ae_all_marked_feasibleOrder
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = true → 0 ≤ Y p.1 p.2 →
      ∀ t : unitInterval, ∀ n,
        FiniteArity.FeasibleOrder (CappedModel.universalMeasure μ t)
          (markedAdjacency A p.1 p.2) (markedCharge A Y I p.1 p.2) n := by
  filter_upwards [ae_all_copy_root_tests A hsym Y I hYsym hI hfull] with p hp hxy hq t n
  have hsub := FiniteArity.ae_all_subtuples μ n n
    (fun _ v => FiniteArity.TupleClique A v →
      (∀ i, A p.1 (v i) = true ∧ A p.2 (v i) = true) →
      FiniteArity.tupleCharge (charge Y I p.1 p.2)
        (Fin.cons none (fun i => some (v i))) ≤ 1)
    (fun k _ => (hp k).mono (fun v hv => hv hxy hq))
  have hmp := measurePreserving_pi (fun _ : Fin n => CappedModel.universalMeasure μ t)
    (fun _ => μ) (fun _ => CappedModel.universal_fst_measurePreserving (μ := μ) t)
  filter_upwards [hmp.quasiMeasurePreserving.ae (hfull n),
    hmp.quasiMeasurePreserving.ae hsub] with v hv hs
  apply marked_tuple_test A Y I p.1 p.2 v hv
  intro k e
  have hk : k ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  exact hs k hk e

end Erdos1017.IndependentAtomCopy

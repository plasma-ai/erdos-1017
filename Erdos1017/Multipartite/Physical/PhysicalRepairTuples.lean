module

public import Erdos1017.Multipartite.Physical.PhysicalPrimalAssembly
public import Mathlib.Tactic.FinCases

/-!
# Edges as two-vertex tuple laws

An edge with its joint law becomes a two-vertex tuple law whose two ordered
orientations are exactly its occupation, and a symmetric edge support condition
is an order-two clique test.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- A genuine edge as a two-vertex tuple, retaining its original joint law. -/
def edgeTuple (z : V × V) (i : Fin 2) : V := if i = 0 then z.1 else z.2

theorem edgeTuple_measurable : Measurable (edgeTuple (V := V)) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = 0
  · simpa [edgeTuple, hi] using (measurable_fst : Measurable (Prod.fst : V × V → V))
  · simpa [edgeTuple, hi] using (measurable_snd : Measurable (Prod.snd : V × V → V))

def edgeLaw (ρ : Measure (V × V)) : Measure (Fin 2 → V) := ρ.map edgeTuple

theorem edgeLaw_mass (ρ : Measure (V × V)) :
    (edgeLaw ρ).real Set.univ = ρ.real Set.univ := by
  simp [edgeLaw, measureReal_def, Measure.map_apply edgeTuple_measurable]

/-- The two ordered orientations of the edge law are exactly its occupation. -/
theorem edgeLaw_occupation (ρ : Measure (V × V)) :
    orderOccupation 2 (edgeLaw ρ) = ρ + ρ.map Prod.swap := by
  rw [orderOccupation_eq_sum]
  simp only [Fin.sum_univ_two]
  norm_num only [ne_eq, not_true_eq_false, ↓reduceIte, Fin.zero_ne_one,
    one_ne_zero, not_false_eq_true, zero_add, add_zero]
  have hmap (i j : Fin 2) : (edgeLaw ρ).map (fun v => (v i, v j)) =
      ρ.map (fun z => (edgeTuple z i, edgeTuple z j)) :=
    Measure.map_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) edgeTuple_measurable
  rw [hmap, hmap]
  simp [edgeTuple]
  rfl

/-- A symmetric edge support condition is a genuine order-two clique test. -/
theorem edgeLaw_clique (ρ : Measure (V × V)) (A : V → V → Prop)
    (hA : MeasurableSet {z : V × V | A z.1 z.2})
    (hsym : ∀ x y, A x y → A y x) (hρ : ∀ᵐ z ∂ρ, A z.1 z.2) :
    ∀ᵐ v ∂edgeLaw ρ, ∀ i j, i ≠ j → A (v i) (v j) := by
  apply (ae_map_iff edgeTuple_measurable.aemeasurable ?_).mpr
  · filter_upwards [hρ] with z hz
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [edgeTuple]
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => hA.preimage
        (show Measurable (fun v : Fin 2 → V => (v i, v j)) from
          (measurable_pi_apply i).prodMk (measurable_pi_apply j))

end Erdos1017.PhysicalPrimal

module

public import Erdos1017.Multipartite.Physical.PhysicalPrimalAssembly
public import Erdos1017.Multipartite.Physical.PhysicalCellCollapse

/-!
# Enumerating selected physical cliques as tuples

A selected physical clique is enumerated as a finite tuple and its joint sample
law is pushed forward, preserving clique support, every ordered
selected-coordinate marginal and, over all selections, the off-diagonal pair
loads after the labels are mapped.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.PhysicalCellLift

variable {ι κ Ω : Type*} [Fintype ι]
  [MeasurableSpace κ] [MeasurableSpace Ω]

/-- The actual selected coordinates, excluding all unused sample coordinates. -/
abbrev Selected (X : Multipartite.Selection ι) := {i : ι // X i = true}

/-- Enumerate a selected physical clique as an ordinary finite tuple. -/
def selectedTuple (e : ι → κ) (X : Multipartite.Selection ι) (x : ι → Ω) :
    Fin (Fintype.card (Selected X)) → κ × Ω := fun j =>
  let i := (Fintype.equivFin (Selected X)).symm j
  (e i.val, x i.val)

theorem selectedTuple_measurable (e : ι → κ) (X : Multipartite.Selection ι) :
    Measurable (selectedTuple (Ω := Ω) e X) := by
  apply Measurable.of_eval
  intro j
  exact measurable_const.prodMk (measurable_pi_apply _)

/-- Push the original joint sample law forward to its actual selected tuple. -/
def selectedLaw (e : ι → κ) (X : Multipartite.Selection ι) (ρ : Measure (ι → Ω)) :
    Measure (Fin (Fintype.card (Selected X)) → κ × Ω) := ρ.map (selectedTuple e X)

theorem selectedLaw_mass (e : ι → κ) (X : Multipartite.Selection ι) (ρ : Measure (ι → Ω)) :
    (selectedLaw e X ρ).real Set.univ = ρ.real Set.univ := by
  simp [selectedLaw, measureReal_def, Measure.map_apply (selectedTuple_measurable e X)]

/-- Tuple enumeration preserves actual clique support under the given law. -/
theorem selectedLaw_clique (e : ι → κ) (X : Multipartite.Selection ι) (ρ : Measure (ι → Ω))
    (A : κ × Ω → κ × Ω → Prop)
    (hA : MeasurableSet {z : (κ × Ω) × (κ × Ω) | A z.1 z.2})
    (hρ : ∀ᵐ x ∂ρ, ∀ i j, i ≠ j → X i = true → X j = true → A (e i, x i) (e j, x j)) :
    ∀ᵐ v ∂selectedLaw e X ρ, ∀ i j, i ≠ j → A (v i) (v j) := by
  apply (ae_map_iff (selectedTuple_measurable e X).aemeasurable ?_).mpr
  · filter_upwards [hρ] with x hx
    intro i j hij
    apply hx _ _ _ ((Fintype.equivFin (Selected X)).symm i).property
      ((Fintype.equivFin (Selected X)).symm j).property
    intro h
    exact hij ((Fintype.equivFin (Selected X)).symm.injective (Subtype.ext h))
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => hA.preimage
        (show Measurable (fun v : Fin (Fintype.card (Selected X)) → κ × Ω => (v i, v j)) from
          (measurable_pi_apply i).prodMk (measurable_pi_apply j))

/-- Enumeration preserves every ordered selected-coordinate marginal. -/
theorem selectedLaw_occupation [DecidableEq ι] (e : ι → κ) (X : Multipartite.Selection ι)
    (ρ : Measure (ι → Ω)) :
    PhysicalPrimal.orderOccupation (Fintype.card (Selected X)) (selectedLaw e X ρ) =
      ∑ i : Selected X, ∑ j : Selected X, if i ≠ j then
        ρ.map (fun x => ((e i.val, x i.val), (e j.val, x j.val))) else 0 := by
  classical
  rw [PhysicalPrimal.orderOccupation_eq_sum]
  have hm (i j : Fin (Fintype.card (Selected X))) :
      (selectedLaw e X ρ).map (fun v => (v i, v j)) =
        ρ.map (fun x => (selectedTuple e X x i, selectedTuple e X x j)) := by
    exact Measure.map_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      (selectedTuple_measurable e X)
  simp_rw [hm]
  rw [← (Fintype.equivFin (Selected X)).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (Fintype.equivFin (Selected X)).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp [selectedTuple]

/-- Trivial selections remain zero laws after enumeration. -/
theorem selectedLaw_small (e : ι → κ) (X : Multipartite.Selection ι)
    (ρ : Measure (ι → Ω)) (hρ : ¬Multipartite.Nontrivial X → ρ = 0)
    (hcard : Fintype.card (Selected X) ≤ 1) : selectedLaw e X ρ = 0 := by
  have htrivial : ¬Multipartite.Nontrivial X := by
    rintro ⟨i, j, hij, hi, hj⟩
    have h := Fintype.card_le_one_iff.mp hcard (⟨i, hi⟩ : Selected X) ⟨j, hj⟩
    exact hij (congrArg Subtype.val h)
  simp [selectedLaw, hρ htrivial]

/-- A selected-coordinate sum written on all labels, with actual selection
indicators and both ordered orientations. -/
theorem selectedLaw_occupation_full [DecidableEq ι] (e : ι → κ)
    (X : Multipartite.Selection ι) (ρ : Measure (ι → Ω)) :
    PhysicalPrimal.orderOccupation (Fintype.card (Selected X)) (selectedLaw e X ρ) =
      ∑ i, ∑ j, if i ≠ j ∧ X i = true ∧ X j = true then
        ρ.map (fun x => ((e i, x i), (e j, x j))) else 0 := by
  classical
  have hsum (f : ι → Measure ((κ × Ω) × (κ × Ω))) :
      (∑ i : Selected X, f i.val) = ∑ i, if X i = true then f i else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun i => X i = true)
      (Finset.univ.filter (fun i => X i = true)) (by simp) f).symm
  rw [selectedLaw_occupation]
  have hinner (i : Selected X) :
      (∑ j : Selected X, if i ≠ j then
        ρ.map (fun x => ((e i.val, x i.val), (e j.val, x j.val))) else 0) =
      ∑ j, if X j = true then if i.val ≠ j then
        ρ.map (fun x => ((e i.val, x i.val), (e j, x j))) else 0 else 0 := by
    convert hsum (fun j => if i.val ≠ j then
      ρ.map (fun x => ((e i.val, x i.val), (e j, x j))) else 0) using 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [ne_eq, Subtype.ext_iff]
  simp_rw [hinner]
  rw [hsum (fun i => ∑ j, if X j = true then if i ≠ j then
    ρ.map (fun x => ((e i, x i), (e j, x j))) else 0 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : X i = true
  · simp only [hi, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : X j = true <;> by_cases hij : i = j <;> simp [hj, hij]
  · simp [hi]

/-- All selected tuple laws together preserve the original off-diagonal pair
loads, after the physical labels are mapped by e. -/
theorem selectedLaws_occupation [DecidableEq ι] (e : ι → κ) (μ : ι → Measure Ω)
    (w : Multipartite.Selection ι → ℝ) :
    (∑ X, PhysicalPrimal.orderOccupation (Fintype.card (Selected X))
      (selectedLaw e X (law μ w X))) =
      ∑ i, ∑ j, if i ≠ j then (pairLoad μ w i j).map (tagPair (e i) (e j)) else 0 := by
  classical
  simp_rw [selectedLaw_occupation_full]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [ne_eq, hij, not_false_eq_true, true_and, ↓reduceIte]
    have hm : Measurable (tagPair (Ω := Ω) (e i) (e j)) :=
      (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
    rw [pairLoad, ← Measure.mapₗ_apply_of_measurable hm, map_sum]
    apply Finset.sum_congr rfl
    intro X _
    rw [Measure.mapₗ_apply_of_measurable hm]
    by_cases hX : X i = true ∧ X j = true
    · simp only [hX]
      have hcoord : Measurable (fun x : ι → Ω => (x i, x j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact (Measure.map_map hm hcoord).symm
    · simp [hX]

end Erdos1017.PhysicalCellLift

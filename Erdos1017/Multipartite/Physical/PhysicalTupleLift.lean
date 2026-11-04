module

public import Erdos1017.Multipartite.Physical.PhysicalSelectedTuples
public import Erdos1017.Multipartite.Physical.PhysicalRepairTuples

/-!
# Packaging the physical construction as tuple laws

The sampled clique laws and same-cell repairs are packaged as an unrestricted
all-orders law family (`tuplePartition`) that keeps the transported edge demand
and the computed cost and is feasible on the same physical graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.PhysicalCellLift

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSpace κ] [MeasurableSpace Ω]

/-- Mapping physical labels preserves the full completed pair occupation. -/
theorem occupation_map_labels (e : ι → κ) (he : Measurable e)
    (μ : ι → Measure Ω) (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ) (S : Finset ι) :
    (occupation μ a w S).map (Prod.map (collapse e) (collapse e)) =
      ∑ i, ∑ j, (completedPairLoad μ a w S i j).map (tagPair (e i) (e j)) := by
  have hm := (collapse_measurable (Ω := Ω) e he).prodMap (collapse_measurable (Ω := Ω) e he)
  unfold occupation
  rw [← Measure.mapₗ_apply_of_measurable hm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.mapₗ_apply_of_measurable hm]
  have ht : Measurable (tagPair (Ω := Ω) i j) :=
    (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  exact Measure.map_map hm ht

/-- The original occupation splits exactly into selected-clique and same-cell
repair contributions, with no discarded pair measures. -/
theorem occupation_split_labels (e : ι → κ) (he : Measurable e)
    (μ : ι → Measure Ω) (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ) (S : Finset ι) :
    (occupation μ a w S).map (Prod.map (collapse e) (collapse e)) =
      (∑ i, ∑ j, if i ≠ j then (pairLoad μ w i j).map (tagPair (e i) (e j)) else 0) +
      ∑ i ∈ S, (repair μ a i + (repair μ a i).map Prod.swap).map (tagPair (e i) (e i)) := by
  classical
  rw [occupation_map_labels e he]
  have hterm (i j : ι) : (completedPairLoad μ a w S i j).map (tagPair (e i) (e j)) =
      (if i ≠ j then (pairLoad μ w i j).map (tagPair (e i) (e j)) else 0) +
      if i = j then if i ∈ S then
        (repair μ a i + (repair μ a i).map Prod.swap).map (tagPair (e i) (e i)) else 0 else 0 := by
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ S <;> simp [completedPairLoad, hi]
    · simp [completedPairLoad, hij]
  simp_rw [hterm, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] in
/-- Turning a repair into a two-point tuple retains exactly both ordered
orientations of its tagged edge measure. -/
theorem repair_tuple_occupation (e : ι → κ) (μ : ι → Measure Ω)
    (a : ι → ℝ) (i : ι) :
    PhysicalPrimal.orderOccupation 2
      (PhysicalPrimal.edgeLaw ((repair μ a i).map (tagPair (e i) (e i)))) =
      (repair μ a i + (repair μ a i).map Prod.swap).map (tagPair (e i) (e i)) := by
  have ht : Measurable (tagPair (Ω := Ω) (e i) (e i)) :=
    (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  rw [PhysicalPrimal.edgeLaw_occupation, Measure.map_add _ _ ht]
  congr 1
  rw [Measure.map_map measurable_swap ht, Measure.map_map ht measurable_swap]
  rfl

/-- The actual enumerated selected tuples and actual edge-repair tuples have
exactly the already constructed transported occupation. -/
theorem tuple_occupation_eq (e : ι → κ) (he : Measurable e)
    (μ : ι → Measure Ω) (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ) (S : Finset ι) :
    (∑ X, PhysicalPrimal.orderOccupation (Fintype.card (Selected X))
      (selectedLaw e X (law μ w X))) +
      (∑ i ∈ S, PhysicalPrimal.orderOccupation 2
        (PhysicalPrimal.edgeLaw ((repair μ a i).map (tagPair (e i) (e i))))) =
      (occupation μ a w S).map (Prod.map (collapse e) (collapse e)) := by
  rw [selectedLaws_occupation, occupation_split_labels e he]
  simp_rw [repair_tuple_occupation]

/-- Selected cliques keep their selected cardinality; repairs have order two. -/
def tupleOrder (S : Finset ι) : Multipartite.Selection ι ⊕ {i // i ∈ S} → ℕ
  | .inl X => Fintype.card (Selected X)
  | .inr _ => 2

/-- The actual tuple laws, retaining the complete joint sample or repair law. -/
def tupleLaw (e : ι → κ) (μ : ι → Measure Ω) (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) :
    ∀ q, Measure (Fin (tupleOrder S q) → κ × Ω)
  | .inl X => selectedLaw e X (law μ w X)
  | .inr i => PhysicalPrimal.edgeLaw ((repair μ a i.val).map (tagPair (e i.val) (e i.val)))

/-- The finite physical construction as an unrestricted all-orders law family. -/
def tuplePartition (e : ι → κ) (μ : ι → Measure Ω) (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) : PhysicalPrimal.Laws (κ × Ω) :=
  PhysicalPrimal.assemble (tupleOrder S) (tupleLaw e μ a w S)

omit [DecidableEq ι] [MeasurableSpace ι] in
theorem tupleLaw_finite (e : ι → κ) (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) (q) :
    IsFiniteMeasure (tupleLaw e μ a w S q) := by
  cases q with
  | inl X =>
    have : IsFiniteMeasure (law μ w X) := Measure.smul_finite _ ENNReal.ofReal_ne_top
    exact Measure.isFiniteMeasure_map _ _
  | inr i =>
    have : IsFiniteMeasure (repair μ a i.val) := Measure.smul_finite _ ENNReal.ofReal_ne_top
    have : IsFiniteMeasure ((repair μ a i.val).map (tagPair (e i.val) (e i.val))) :=
      Measure.isFiniteMeasure_map _ _
    exact Measure.isFiniteMeasure_map _ _

omit [MeasurableSpace ι] in
theorem tuplePartition_finite (e : ι → κ) (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) (n : ℕ) :
    IsFiniteMeasure (tuplePartition e μ a w S n) := by
  have (q : Multipartite.Selection ι ⊕ {i // i ∈ S}) : IsFiniteMeasure (tupleLaw e μ a w S q) := tupleLaw_finite e μ a w S q
  exact PhysicalPrimal.assemble_finite _ _ n

/-- Assembly preserves the complete transported edge demand, before invoking
any finite primal moments or optimality. -/
theorem tuplePartition_occupation (e : ι → κ) (he : Measurable e)
    (μ : ι → Measure Ω) (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ) (S : Finset ι) :
    PhysicalPrimal.occupation (tuplePartition e μ a w S) =
      (occupation μ a w S).map (Prod.map (collapse e) (collapse e)) := by
  rw [tuplePartition, PhysicalPrimal.occupation_assemble, Fintype.sum_sum_type]
  simp only [tupleOrder, tupleLaw]
  rw [Finset.sum_coe_sort S (fun i => PhysicalPrimal.orderOccupation 2
    (PhysicalPrimal.edgeLaw ((repair μ a i).map (tagPair (e i) (e i)))))]
  exact tuple_occupation_eq e he μ a w S

omit [MeasurableSpace ι] in
/-- Tuple packaging preserves exactly the cost already computed for the
sampled laws and same-cell repairs. -/
theorem tuplePartition_cost (e : ι → κ) (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) :
    PhysicalPrimal.cost (tuplePartition e μ a w S) = cost μ a w S := by
  have hf (q : Multipartite.Selection ι ⊕ {i // i ∈ S}) :
      IsFiniteMeasure (tupleLaw e μ a w S q) := tupleLaw_finite e μ a w S q
  have hl (X : Multipartite.Selection ι) : IsFiniteMeasure (law μ w X) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hr (i : ι) : IsFiniteMeasure (repair μ a i) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hm (i : ι) : Measurable (tagPair (Ω := Ω) (e i) (e i)) :=
    (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  rw [tuplePartition, PhysicalPrimal.cost_assemble, Fintype.sum_sum_type]
  change (∑ X, (selectedLaw e X (law μ w X)).real Set.univ) +
    (∑ i : S, (PhysicalPrimal.edgeLaw ((repair μ a i.val).map
      (tagPair (e i.val) (e i.val)))).real Set.univ) = _
  simp_rw [selectedLaw_mass, PhysicalPrimal.edgeLaw_mass]
  simp only [measureReal_def, Measure.map_apply (hm _) MeasurableSet.univ, Set.preimage_univ]
  rw [Finset.sum_coe_sort S (fun i => (repair μ a i Set.univ).toReal)]
  unfold cost
  rw [ENNReal.toReal_sum (fun X _ => measure_ne_top _ _),
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]

/-- Tuple packaging turns the constructed transported family into an actual
feasible unrestricted law family on the same physical graph. -/
theorem tuplePartition_feasible [Fintype κ] [DecidableEq κ] [MeasurableEq κ] [MeasurableEq Ω]
    (e : ι → κ) (he : Measurable e) (ν : Measure Ω) (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) (T : Finset κ)
    (h : TransportedFeasible ν a w S e T) :
    PhysicalPrimal.Feasible (Adj T) (demand (fun _ => ν) (groupedMass e a) T)
      (tuplePartition e (fun _ => ν) a w S) := by
  have hA : MeasurableSet {z : (κ × Ω) × (κ × Ω) | Adj T z.1 z.2} := edgeSet_measurable T
  have hsym (x y : κ × Ω) (hxy : Adj T x y) : Adj T y x := by
    refine ⟨Ne.symm hxy.1, ?_⟩
    rcases hxy.2 with hne | hin
    · exact Or.inl (Ne.symm hne)
    · by_cases heq : x.1 = y.1
      · exact Or.inr (heq ▸ hin)
      · exact Or.inl (Ne.symm heq)
  apply PhysicalPrimal.feasible_assemble
  · intro q hsmall
    cases q with
    | inl X => exact selectedLaw_small e X _ (h.1 X) hsmall
    | inr i => norm_num [tupleOrder] at hsmall
  · intro q
    cases q with
    | inl X => exact selectedLaw_clique e X _ (Adj T) hA (h.2.1 X)
    | inr i =>
      apply PhysicalPrimal.edgeLaw_clique _ (Adj T) hA hsym
      have ht : Measurable (tagPair (Ω := Ω) (e i.val) (e i.val)) :=
        (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
      apply (ae_map_iff ht.aemeasurable hA).mpr
      exact h.2.2.1 i.val i.property
  · rw [← PhysicalPrimal.occupation_assemble]
    change PhysicalPrimal.occupation (tuplePartition e (fun _ => ν) a w S) = _
    rw [tuplePartition_occupation e he]
    exact h.2.2.2

end Erdos1017.PhysicalCellLift

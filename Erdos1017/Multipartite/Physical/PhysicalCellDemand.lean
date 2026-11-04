module

public import Erdos1017.Multipartite.Physical.PhysicalCellLift

/-!
# Edge demand of the completed physical graph

The physical vertex measure is the weighted sum of the cell laws, and the block
demand equals the product vertex mass restricted to the edges of the completed
multipartite physical graph (`demand_eq_restrict_product`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.PhysicalCellLift

open MeasureTheory
open scoped BigOperators

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSpace Ω] [MeasurableEq ι] [MeasurableEq Ω]

/-- The physical vertex measure is the sum of its weighted cell probability laws. -/
def vertexMeasure (μ : ι → Measure Ω) (a : ι → ℝ) : Measure (ι × Ω) :=
  Measure.sum (fun i => ENNReal.ofReal (a i) • (μ i).map (fun x => (i, x)))

/-- The measurable edge relation of the completed multipartite physical graph. -/
def edgeSet (S : Finset ι) : Set ((ι × Ω) × (ι × Ω)) :=
  {z | Adj S z.1 z.2}

omit [Fintype ι] [DecidableEq ι] in
theorem edgeSet_measurable (S : Finset ι) : MeasurableSet (edgeSet (Ω := Ω) S) := by
  have hlabel : MeasurableSet {z : (ι × Ω) × (ι × Ω) | z.1.1 = z.2.1} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)
  have hpoint : MeasurableSet {z : (ι × Ω) × (ι × Ω) | z.1.2 = z.2.2} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have hmem : MeasurableSet {z : (ι × Ω) × (ι × Ω) | z.1.1 ∈ S} :=
    S.finite_toSet.measurableSet.preimage (measurable_fst.comp measurable_fst)
  convert (hlabel.inter hpoint).compl.inter (hlabel.compl.union hmem) using 1
  ext z
  simp [edgeSet, Adj, Prod.ext_iff]

omit [Fintype ι] in
/-- On an off-diagonal block every physical pair is an edge; on a completed
same-cell block only a null diagonal is removed. -/
theorem restrict_pair_block (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (S : Finset ι) (i j : ι) :
    (((μ i).prod (μ j)).map (tagPair i j)).restrict (edgeSet S) =
      if i ≠ j ∨ i ∈ S then ((μ i).prod (μ j)).map (tagPair i j) else 0 := by
  have hm : Measurable (tagPair (Ω := Ω) i j) :=
    (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  rw [Measure.restrict_map hm (edgeSet_measurable S)]
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S
    · simp only [ne_eq, not_true_eq_false, hi, or_true, ↓reduceIte]
      congr 1
      apply Measure.restrict_eq_self_of_ae_mem
      have hne : ∀ᵐ z ∂(μ i).prod (μ i), z.1 ≠ z.2 := by
        rw [ae_iff]
        simpa only [not_not, Set.diagonal] using product_diagonal_null (μ i)
      filter_upwards [hne] with z hz
      exact ⟨fun h => hz (congrArg Prod.snd h), Or.inr hi⟩
    · simp [edgeSet, Adj, tagPair, hi]
  · have hpre : tagPair (Ω := Ω) i j ⁻¹' edgeSet S = Set.univ := by
      ext z
      simp only [Set.mem_preimage, edgeSet, Set.mem_ofPred_eq, tagPair, Adj, Set.mem_univ,
        iff_true]
      exact ⟨fun h => hij (congrArg Prod.fst h), Or.inl hij⟩
    simp [hij, hpre]

/-- The explicit block demand is exactly product vertex mass restricted to the
physical graph's edges. This identifies the target independently of the lift. -/
theorem demand_eq_restrict_product (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (S : Finset ι) :
    demand μ a S = ((vertexMeasure μ a).prod (vertexMeasure μ a)).restrict (edgeSet S) := by
  unfold vertexMeasure
  rw [Measure.prod_sum_left]
  simp_rw [Measure.prod_sum_right, Measure.restrict_sum_of_countable, Measure.sum_fintype]
  unfold demand
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_prod_map (μ i) (μ j) (f := fun x => (i, x)) (g := fun x => (j, x))
      (measurable_const.prodMk measurable_id) (measurable_const.prodMk measurable_id)]
  change (if i ≠ j ∨ i ∈ S then
      ENNReal.ofReal (a i * a j) • ((μ i).prod (μ j)).map (tagPair i j) else 0) =
    ((ENNReal.ofReal (a i) * ENNReal.ofReal (a j)) •
      ((μ i).prod (μ j)).map (tagPair i j)).restrict (edgeSet S)
  rw [Measure.restrict_smul, restrict_pair_block]
  rw [ENNReal.ofReal_mul (ha i)]
  split_ifs <;> simp

end Erdos1017.PhysicalCellLift

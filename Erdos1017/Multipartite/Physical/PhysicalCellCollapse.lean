module

public import Erdos1017.Multipartite.Physical.PhysicalCellDemand

/-!
# Merging labels of a sampled physical family

Merging artificial labels into one physical component adds their masses,
transports the vertex measure and pair demand, and keeps the sampled selections
cliques, so the whole sampled family stays feasible (`transported_feasible`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.PhysicalCellLift

open MeasureTheory
open scoped BigOperators ENNReal

variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Masses add when artificial labels are merged into one physical component. -/
def groupedMass (e : ι → κ) (a : ι → ℝ) (k : κ) : ℝ :=
  ∑ i, if e i = k then a i else 0

omit [Fintype κ] [DecidableEq ι] in
theorem groupedMass_nonneg (e : ι → κ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (k : κ) :
    0 ≤ groupedMass e a k := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact ha i
  · exact le_rfl

omit [DecidableEq ι] in
/-- Regroup a weighted finite sum along an arbitrary label map. -/
theorem weighted_group_sum {M : Type*} [AddCommMonoid M] [Module ℝ≥0∞ M]
    (e : ι → κ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (f : κ → M) :
    (∑ i, ENNReal.ofReal (a i) • f (e i)) = ∑ k, ENNReal.ofReal (groupedMass e a k) • f k := by
  have hsum (k : κ) : ENNReal.ofReal (groupedMass e a k) =
      ∑ i, if e i = k then ENNReal.ofReal (a i) else 0 := by
    rw [groupedMass, ENNReal.ofReal_sum_of_nonneg]
    · simp only [apply_ite, ENNReal.ofReal_zero]
    · intro i _
      split_ifs
      · exact ha i
      · exact le_rfl
  simp_rw [hsum, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

variable [MeasurableSpace ι] [MeasurableSpace κ] [MeasurableSpace Ω]

/-- Forget artificial cell labels while preserving the sampled physical point. -/
def collapse (e : ι → κ) (x : ι × Ω) : κ × Ω := (e x.1, x.2)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem collapse_measurable (e : ι → κ) (he : Measurable e) :
    Measurable (collapse (Ω := Ω) e) := (he.comp measurable_fst).prodMk measurable_snd

omit [DecidableEq ι] in
/-- Common cell laws become one component law after their weights are added. -/
theorem map_vertexMeasure (e : ι → κ) (he : Measurable e)
    (ν : Measure Ω) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (vertexMeasure (fun _ : ι => ν) a).map (collapse e) =
      vertexMeasure (fun _ : κ => ν) (groupedMass e a) := by
  have hm := collapse_measurable (Ω := Ω) e he
  simp only [vertexMeasure, Measure.sum_fintype, ← Measure.mapₗ_apply_of_measurable hm,
    map_sum, map_smul]
  have hterm (i : ι) : (Measure.mapₗ (collapse e)) (ν.map (fun x => (i, x))) =
      ν.map (fun x => (e i, x)) := by
    have hi : Measurable (fun x : Ω => (i, x)) := measurable_const.prodMk measurable_id
    rw [Measure.mapₗ_apply_of_measurable hm, Measure.map_map hm hi]
    rfl
  simp_rw [hterm]
  exact weighted_group_sum e a ha (fun k => ν.map (fun x => (k, x)))

/-- Express the block demand as two weighted sums, before merging labels. -/
theorem demand_weighted (ν : Measure Ω) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (S : Finset ι) :
    demand (fun _ : ι => ν) a S = ∑ i, ENNReal.ofReal (a i) •
      ∑ j, ENNReal.ofReal (a j) •
        (if i ≠ j ∨ i ∈ S then (ν.prod ν).map (tagPair i j) else 0) := by
  unfold demand
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_mul (ha i)]
  split_ifs <;> simp

/-- A label merge preserving completed blocks transports the entire pair demand.
No injectivity is required on completed dust labels. -/
theorem map_demand (e : ι → κ) (he : Measurable e)
    (ν : Measure Ω) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (S : Finset ι) (T : Finset κ)
    (hblocks : ∀ i j, (i ≠ j ∨ i ∈ S) ↔ (e i ≠ e j ∨ e i ∈ T)) :
    (demand (fun _ : ι => ν) a S).map (Prod.map (collapse e) (collapse e)) =
      demand (fun _ : κ => ν) (groupedMass e a) T := by
  have hm := (collapse_measurable (Ω := Ω) e he).prodMap (collapse_measurable (Ω := Ω) e he)
  rw [demand_weighted ν a ha S, demand_weighted ν _ (groupedMass_nonneg e a ha) T]
  simp only [← Measure.mapₗ_apply_of_measurable hm, map_sum, map_smul]
  have hterm (i j : ι) :
      Measure.mapₗ (Prod.map (collapse e) (collapse e))
        (if i ≠ j ∨ i ∈ S then (ν.prod ν).map (tagPair i j) else 0) =
      if e i ≠ e j ∨ e i ∈ T then (ν.prod ν).map (tagPair (e i) (e j)) else 0 := by
    simp only [hblocks]
    split_ifs
    · have ht : Measurable (tagPair (Ω := Ω) i j) :=
        (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
      rw [Measure.mapₗ_apply_of_measurable hm, Measure.map_map hm ht]
      rfl
    · exact map_zero _
  simp_rw [hterm]
  have hrow (i : ι) :
      (∑ j, ENNReal.ofReal (a j) •
        (if e i ≠ e j ∨ e i ∈ T then (ν.prod ν).map (tagPair (e i) (e j)) else 0)) =
      ∑ l, ENNReal.ofReal (groupedMass e a l) •
        (if e i ≠ l ∨ e i ∈ T then (ν.prod ν).map (tagPair (e i) l) else 0) :=
    weighted_group_sum e a ha (fun l =>
      if e i ≠ l ∨ e i ∈ T then (ν.prod ν).map (tagPair (e i) l) else 0)
  simp_rw [hrow]
  exact weighted_group_sum e a ha (fun k => ∑ l, ENNReal.ofReal (groupedMass e a l) •
    (if k ≠ l ∨ k ∈ T then (ν.prod ν).map (tagPair k l) else 0))

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] [MeasurableSpace ι] [MeasurableSpace κ] in
/-- Every pair of distinct coordinates avoids collision simultaneously under
the actual product-sampled law, including after artificial dust labels are merged. -/
theorem law_pairwise_distinct [MeasurableEq Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (w : Multipartite.Selection ι → ℝ) (X : Multipartite.Selection ι) :
    ∀ᵐ x ∂law (fun _ : ι => ν) w X, ∀ i j, i ≠ j → x i ≠ x j := by
  have hpi : ∀ᵐ x ∂Measure.pi (fun _ : ι => ν), ∀ i j, i ≠ j → x i ≠ x j := by
    simp only [ae_all_iff]
    intro i j hij
    have hm : Measurable (fun x : ι → Ω => (x i, x j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    have h := congrArg (fun μ : Measure (Ω × Ω) => μ (Set.diagonal Ω))
      (pair_map (fun _ : ι => ν) i j hij)
    rw [Measure.map_apply hm measurableSet_diagonal, product_diagonal_null ν] at h
    rw [ae_iff]
    simpa only [not_not, Set.diagonal, Set.preimage_ofPred_eq] using h
  exact (Measure.absolutelyContinuous_rfl.smul_left (ENNReal.ofReal (w X))) hpi

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] [MeasurableSpace ι] [MeasurableSpace κ] in
/-- After merging labels, the sampled selections still form actual cliques.
The finite simultaneous noncollision condition is proved from atomless sampling. -/
theorem collapsed_selected_clique [MeasurableEq Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (w : Multipartite.Selection ι → ℝ) (X : Multipartite.Selection ι)
    (e : ι → κ) (T : Finset κ)
    (hblocks : ∀ i j, i ≠ j → e i ≠ e j ∨ e i ∈ T) :
    ∀ᵐ x ∂law (fun _ : ι => ν) w X, ∀ i j, i ≠ j → X i = true → X j = true →
      Adj T (e i, x i) (e j, x j) := by
  filter_upwards [law_pairwise_distinct ν w X] with x hx
  intro i j hij _ _
  exact ⟨fun h => hx i j hij (congrArg Prod.snd h), hblocks i j hij⟩

/-- Feasibility after a physical label merge. The sample domains and masses
are retained, while every represented physical vertex is transported. -/
def TransportedFeasible (ν : Measure Ω) (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ)
    (S : Finset ι) (e : ι → κ) (T : Finset κ) : Prop :=
  (∀ X, ¬Multipartite.Nontrivial X → law (fun _ : ι => ν) w X = 0) ∧
    (∀ X, ∀ᵐ x ∂law (fun _ : ι => ν) w X,
      ∀ i j, i ≠ j → X i = true → X j = true → Adj T (e i, x i) (e j, x j)) ∧
    (∀ i ∈ S, ∀ᵐ z ∂repair (fun _ : ι => ν) a i, Adj T (e i, z.1) (e i, z.2)) ∧
    (occupation (fun _ : ι => ν) a w S).map (Prod.map (collapse e) (collapse e)) =
      demand (fun _ : κ => ν) (groupedMass e a) T

/-- The whole sampled family transports without losing pair demand, cost,
or actual clique support, even when several dust labels share one image. -/
theorem transported_feasible [MeasurableEq Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (w : Multipartite.Selection ι → ℝ)
    (hw : Multipartite.PrimalFeasible a w) (S : Finset ι) (e : ι → κ) (he : Measurable e)
    (T : Finset κ) (hblocks : ∀ i j, (i ≠ j ∨ i ∈ S) ↔ (e i ≠ e j ∨ e i ∈ T)) :
    TransportedFeasible ν a w S e T := by
  refine ⟨law_trivial _ a w hw, ?_, ?_, ?_⟩
  · intro X
    exact collapsed_selected_clique ν w X e T (fun i j hij => (hblocks i j).mp (Or.inl hij))
  · intro i hi
    have heT : e i ∈ T := by simpa using (hblocks i i).mp (Or.inr hi)
    have hne : ∀ᵐ z ∂repair (fun _ : ι => ν) a i, z.1 ≠ z.2 := by
      rw [ae_iff]
      simp only [not_not]
      change (ENNReal.ofReal (a i ^ 2 / 2) • ν.prod ν) (Set.diagonal Ω) = 0
      rw [Measure.smul_apply, product_diagonal_null ν, smul_zero]
    filter_upwards [hne] with z hz
    exact ⟨fun h => hz (congrArg Prod.snd h), Or.inr heT⟩
  · rw [occupation_eq_demand _ a w hw S, map_demand e he ν a ha S T hblocks]

end Erdos1017.PhysicalCellLift

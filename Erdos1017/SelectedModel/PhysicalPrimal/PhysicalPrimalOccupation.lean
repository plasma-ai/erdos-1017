module

public import Erdos1017.Multipartite.Physical.PhysicalGraphTail
public import Erdos1017.Multipartite.Physical.PhysicalPrimalAssembly
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# First occupation and coordinate marginals

The first occupation of a family of physical parents dominates every coordinate
marginal, the first marginal of graph demand is the degree-weighted vertex
measure, and for balanced laws every coordinate marginal is absolutely
continuous with respect to the vertex measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- First occupation counts every vertex of one genuine joint parent law. -/
def orderFirstOccupation (n : ℕ) (ρ : Measure (Fin n → V)) : Measure V :=
  ∑ i, ρ.map (fun v => v i)

/-- The first occupation of the entire family of physical parents. No probability
normalization, cap or symmetry of the original joint laws is imposed. -/
def firstOccupation (μ : Laws V) : Measure V :=
  Measure.sum (fun n => orderFirstOccupation n (μ n))

/-- Each vertex of an order-n parent occurs in exactly n-1 ordered pairs
as their first coordinate, without a symmetry assumption on that parent. -/
theorem fst_orderOccupation (n : ℕ) (ρ : Measure (Fin n → V)) :
    (orderOccupation n ρ).fst = (n - 1 : ℕ) • orderFirstOccupation n ρ := by
  classical
  rw [orderOccupation_eq_sum]
  simp only [Measure.fst, Measure.map_finset_sum measurable_fst.aemeasurable]
  have hpair (i j : Fin n) :
      (if i ≠ j then ρ.map (fun v => (v i, v j)) else 0).map Prod.fst =
        if i ≠ j then ρ.map (fun v => v i) else 0 := by
    split_ifs
    · exact Measure.map_map measurable_fst
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    · exact Measure.map_zero _
  simp_rw [hpair]
  rw [orderFirstOccupation, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun j : Fin n => i ≠ j) = Finset.univ.erase i := by
    ext j
    simp [ne_comm]
  rw [hfilter, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-- Every nontrivial parent's first occupation is bounded by the first
marginal of its ordered pair occupation. -/
theorem orderFirstOccupation_le_fst (n : ℕ) (ρ : Measure (Fin n → V)) (hn : 2 ≤ n) :
    orderFirstOccupation n ρ ≤ (orderOccupation n ρ).fst := by
  rw [fst_orderOccupation]
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞]
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact le_mul_of_one_le_left zero_le (by exact_mod_cast (show 1 ≤ n - 1 by omega))

/-- Exact ordered balance and exclusion of empty/singleton parents give
the true first-occupation bound. No cap or symmetry is needed. -/
theorem firstOccupation_le_fst_of_balance (μ : Laws V) (demand : Measure (V × V))
    (hzero : μ 0 = 0) (hone : μ 1 = 0) (hbalance : occupation μ = demand) :
    firstOccupation μ ≤ demand.fst := by
  rw [← hbalance, occupation, Measure.fst_sum]
  intro s
  simp only [firstOccupation, Measure.sum_apply_of_countable]
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases hn : 2 ≤ n
  · exact orderFirstOccupation_le_fst n (μ n) hn s
  · interval_cases n <;> simp [orderFirstOccupation, hzero, hone]

/-- Each original coordinate marginal is a submeasure of first occupation. -/
theorem coordinate_marginal_le_firstOccupation (μ : Laws V) (n : ℕ) (i : Fin n) :
    (μ n).map (fun v => v i) ≤ firstOccupation μ := by
  apply le_trans _ (Measure.le_sum (fun n => orderFirstOccupation n (μ n)) n)
  unfold orderFirstOccupation
  exact Finset.single_le_sum (f := fun j : Fin n => (μ n).map (fun v => v j))
    (fun _ _ => by intro s; exact bot_le) (Finset.mem_univ i)

/-- Every original coordinate is absolutely continuous with respect to
the first marginal of the identified demand, even for singular joint laws. -/
theorem coordinate_marginal_absolutelyContinuous_of_balance (μ : Laws V)
    (demand : Measure (V × V)) (hzero : μ 0 = 0) (hone : μ 1 = 0)
    (hbalance : occupation μ = demand) (n : ℕ) (i : Fin n) :
    (μ n).map (fun v => v i) ≪ demand.fst :=
  ((coordinate_marginal_le_firstOccupation μ n i).trans
    (firstOccupation_le_fst_of_balance μ demand hzero hone hbalance)).absolutelyContinuous

/-- The actual degree is the vertex mass of the measurable adjacency row. -/
def graphDegree (η : Measure V) (E : Set (V × V)) (x : V) : ℝ≥0∞ :=
  η (Prod.mk x ⁻¹' E)

theorem measurable_graphDegree (η : Measure V) [SFinite η] (E : Set (V × V))
    (hE : MeasurableSet E) : Measurable (graphDegree η E) :=
  measurable_measure_prodMk_left hE

/-- The first marginal of actual graph demand is exactly the degree-weighted
vertex measure, including merely measurable adjacency sets. -/
theorem graphDemand_fst_eq_withDensity (η : Measure V) [SFinite η]
    (E : Set (V × V)) (hE : MeasurableSet E) :
    (graphDemand η E).fst = η.withDensity (graphDegree η E) := by
  ext s hs
  rw [Measure.fst_apply hs, graphDemand, Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((measurable_fst hs).inter hE), withDensity_apply _ hs,
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · have hpre : Prod.mk x ⁻¹' Prod.fst ⁻¹' s = (Set.univ : Set V) := by ext y; simp [hx]
    simp [graphDegree, Set.preimage_inter, hpre, hx]
  · have hpre : Prod.mk x ⁻¹' Prod.fst ⁻¹' s = (∅ : Set V) := by ext y; simp [hx]
    simp [Set.preimage_inter, hpre, hx]

/-- Probability graph demand has first marginal at most the original vertex
measure on every measurable set. -/
theorem graphDemand_fst_le (η : Measure V) [IsProbabilityMeasure η] (E : Set (V × V)) :
    (graphDemand η E).fst ≤ η := by
  calc
    (graphDemand η E).fst ≤ (η.prod η).fst := Measure.fst_mono Measure.restrict_le_self
    _ = η := Measure.fst_prod

/-- Actual first occupation is bounded by the degree-weighted vertex measure
and hence by the probability vertex measure. -/
theorem firstOccupation_graphDemand_bounds (μ : Laws V) (η : Measure V)
    [IsProbabilityMeasure η] (E : Set (V × V)) (hE : MeasurableSet E)
    (hzero : μ 0 = 0) (hone : μ 1 = 0) (hbalance : occupation μ = graphDemand η E) :
    firstOccupation μ ≤ η.withDensity (graphDegree η E) ∧
      η.withDensity (graphDegree η E) ≤ η := by
  rw [← graphDemand_fst_eq_withDensity η E hE]
  exact ⟨firstOccupation_le_fst_of_balance μ _ hzero hone hbalance, graphDemand_fst_le η E⟩

/-- Every coordinate marginal of an actual balanced physical law is absolutely
continuous with respect to the original probability vertex measure. -/
theorem coordinate_marginal_absolutelyContinuous_graphDemand (μ : Laws V) (η : Measure V)
    [IsProbabilityMeasure η] (E : Set (V × V))
    (hzero : μ 0 = 0) (hone : μ 1 = 0) (hbalance : occupation μ = graphDemand η E)
    (n : ℕ) (i : Fin n) :
    (μ n).map (fun v => v i) ≪ η :=
  ((coordinate_marginal_le_firstOccupation μ n i).trans
    ((firstOccupation_le_fst_of_balance μ _ hzero hone hbalance).trans
      (graphDemand_fst_le η E))).absolutelyContinuous

end Erdos1017.PhysicalPrimal

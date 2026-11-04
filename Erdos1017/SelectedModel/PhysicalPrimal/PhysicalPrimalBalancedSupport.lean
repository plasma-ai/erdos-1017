module

public import Erdos1017.Multipartite.Physical.PhysicalGraphTail
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Support and tightness from exact pair balance

Exact pair balance dominates every ordered coordinate marginal, recovers clique
support from the identified pair demand, makes parent coordinates distinct
almost everywhere, and with equality in weak duality makes every parent tight
(`ae_tight_of_balance_and_cost_eq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- Exact occupation dominates every ordered coordinate marginal, including
when the joint parent laws are singular. -/
theorem pair_marginal_le_of_balance (μ : Laws V) (demand : Measure (V × V))
    (hbalance : occupation μ = demand) (n : ℕ) (ij : PairIndex n) :
    (μ n).map (fun v => (v ij.val.1, v ij.val.2)) ≤ demand := by
  rw [← hbalance]
  exact (pair_le_orderOccupation n (μ n) ij).trans
    (Measure.le_sum (fun k => orderOccupation k (μ k)) n)

/-- Pair absolute continuity follows from balance; joint absolute continuity
is neither required nor asserted. -/
theorem pair_marginal_absolutelyContinuous_of_balance (μ : Laws V)
    (demand : Measure (V × V)) (hbalance : occupation μ = demand)
    (n : ℕ) (ij : PairIndex n) :
    (μ n).map (fun v => (v ij.val.1, v ij.val.2)) ≪ demand :=
  (pair_marginal_le_of_balance μ demand hbalance n ij).absolutelyContinuous

/-- Actual clique support is recovered from the identified pair demand,
without a closedness assumption on the measurable clique locus. -/
theorem feasible_of_balance (μ : Laws V) (A : V → V → Prop)
    (demand : Measure (V × V)) (hzero : μ 0 = 0) (hone : μ 1 = 0)
    (hbalance : occupation μ = demand) (hA : ∀ᵐ z ∂demand, A z.1 z.2) :
    Feasible A demand μ := by
  exact ⟨hzero, hone, fun n => ae_all_pairs_of_balance μ demand hbalance
    (fun z => A z.1 z.2) hA n, hbalance⟩

/-- Diagonal-null pair demand makes the original parent coordinates distinct
almost everywhere, even for singular joint laws. -/
theorem ae_injective_of_balance (μ : Laws V) (demand : Measure (V × V))
    (hbalance : occupation μ = demand) (hne : ∀ᵐ z ∂demand, z.1 ≠ z.2) (n : ℕ) :
    ∀ᵐ v ∂μ n, Function.Injective v := by
  filter_upwards [ae_all_pairs_of_balance μ demand hbalance
    (fun z => z.1 ≠ z.2) hne n] with v hv
  intro i j hij
  by_contra hne
  exact hv i j hne hij

/-- The graph restriction itself supplies every actual edge after taking
the limit. No support condition is imposed on a limiting clique set. -/
theorem feasible_graphDemand_of_balance (μ : Laws V) (η : Measure V)
    (E : Set (V × V)) (hE : MeasurableSet E)
    (hzero : μ 0 = 0) (hone : μ 1 = 0)
    (hbalance : occupation μ = graphDemand η E) :
    Feasible (fun x y => (x, y) ∈ E) (graphDemand η E) μ := by
  exact feasible_of_balance μ _ _ hzero hone hbalance (ae_restrict_mem hE)

/-- Atomless graph demand excludes the physical diagonal from every parent.
The adjacency representative itself need not vanish pointwise there. -/
theorem ae_injective_graphDemand_of_balance [MeasurableEq V]
    (μ : Laws V) (η : Measure V) [SFinite η] [NullSingletonClass η]
    (E : Set (V × V)) (hbalance : occupation μ = graphDemand η E) (n : ℕ) :
    ∀ᵐ v ∂μ n, Function.Injective v := by
  have hdiag : (η.prod η) (Set.diagonal V) = 0 := by
    rw [Measure.prod_apply measurableSet_diagonal]
    have hpre (x : V) : Prod.mk x ⁻¹' Set.diagonal V = {x} := by
      ext y
      simp [Set.diagonal, eq_comm]
    simp_rw [hpre, measure_singleton]
    simp
  have hne : ∀ᵐ z ∂η.prod η, z.1 ≠ z.2 := by
    rw [ae_iff]
    simpa only [not_not, Set.diagonal] using hdiag
  apply ae_injective_of_balance μ _ hbalance
  exact ae_mono Measure.restrict_le_self hne

/-- Equality in actual weak duality makes every parent tight. This applies
to all orders and does not assume that the primal was already attained. -/
theorem ae_tight_of_balance_and_cost_eq (μ : Laws V)
    [∀ n, IsFiniteMeasure (μ n)] (demand : Measure (V × V)) [IsFiniteMeasure demand]
    (Y : V × V → ℝ) (hzero : μ 0 = 0) (hone : μ 1 = 0)
    (hbalance : occupation μ = demand) (hY : Integrable Y demand)
    (hfeasible : ∀ n, ∀ᵐ v ∂μ n, charge Y v ≤ 1)
    (hcost : cost μ = (∫ z, Y z ∂demand) / 2) (n : ℕ) :
    ∀ᵐ v ∂μ n, charge Y v = 1 := by
  have htotal : Integrable Y (Measure.sum (fun k => orderOccupation k (μ k))) := by
    change Integrable Y (occupation μ)
    rwa [hbalance]
  have hi (k : ℕ) : Integrable Y (orderOccupation k (μ k)) :=
    htotal.mono_measure (Measure.le_sum (fun k => orderOccupation k (μ k)) k)
  have hc (k : ℕ) := integral_charge k (μ k) Y (hi k)
  have hmass := summable_mass_of_balance μ demand hzero hone hbalance
  have hcharge : Summable (fun k => ∫ v, charge Y v ∂μ k) := by
    simp_rw [(hc _).2]
    exact (hasSum_integral_measure htotal).summable.div_const 2
  have hslack (k : ℕ) : 0 ≤ (μ k).real Set.univ - ∫ v, charge Y v ∂μ k := by
    apply sub_nonneg.mpr
    simpa using integral_mono_ae (hc k).1 (integrable_const (1 : ℝ)) (hfeasible k)
  have hsum : (∑' k, ((μ k).real Set.univ - ∫ v, charge Y v ∂μ k)) = 0 := by
    rw [hmass.tsum_sub hcharge]
    simp_rw [(hc _).2]
    rw [tsum_div_const, ← integral_sum_measure htotal]
    change cost μ - (∫ z, Y z ∂occupation μ) / 2 = 0
    rw [hbalance, hcost, sub_self]
  have hsingle : (μ n).real Set.univ - ∫ v, charge Y v ∂μ n = 0 := by
    apply le_antisymm
    · exact ((hmass.sub hcharge).le_tsum n (fun k _ => hslack k)).trans_eq hsum
    · exact hslack n
  have hint : Integrable (fun v => 1 - charge Y v) (μ n) :=
    (integrable_const 1).sub (hc n).1
  have hn : 0 ≤ᵐ[μ n] fun v => 1 - charge Y v := by
    filter_upwards [hfeasible n] with v hv
    exact sub_nonneg.mpr hv
  have heq : (∫ v, 1 - charge Y v ∂μ n) = 0 := by
    rw [integral_sub (integrable_const 1) (hc n).1]
    simpa using hsingle
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hn hint).mp heq] with v hv
  exact (sub_eq_zero.mp hv).symm

/-- A common pair-null license supplies feasibility for the balanced singular
laws, after which equality of cost and dual value gives complementary slackness. -/
theorem ae_tight_of_pairwise_tests (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (A : V → V → Prop) (demand : Measure (V × V)) [IsFiniteMeasure demand]
    (Y : V × V → ℝ) (hμ : Feasible A demand μ) (hY : Integrable Y demand)
    (P : V × V → Prop) (hP : ∀ᵐ z ∂demand, P z)
    (htest : ∀ n (v : Fin n → V),
      (∀ i j, i ≠ j → A (v i) (v j)) →
      (∀ i j, i ≠ j → P (v i, v j)) → charge Y v ≤ 1)
    (hcost : cost μ = (∫ z, Y z ∂demand) / 2) (n : ℕ) :
    ∀ᵐ v ∂μ n, charge Y v = 1 := by
  apply ae_tight_of_balance_and_cost_eq μ demand Y hμ.1 hμ.2.1 hμ.2.2.2 hY _ hcost n
  intro k
  filter_upwards [hμ.2.2.1 k, ae_all_pairs_of_balance μ demand hμ.2.2.2 P hP k] with v hv hPv
  exact htest k v hv hPv

end Erdos1017.PhysicalPrimal

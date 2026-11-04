module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalOptimalSampling
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalFiniteLimit
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalBalancedSupport
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalCliqueRepresentative
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# Attainment of the bounded-order physical primal

Optimal finite sampled partitions whose expected costs converge to the original
dual objective yield a bounded-order physical primal, and a finite-order
equality constructs such a primal for the original full feasible kernel
(`exists_primal_of_finite_order_equality`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Erdos1017.PhysicalPrimal

private theorem charge_eq_tupleCharge {Ω : Type*} {n : ℕ}
    (Y : Ω → Ω → ℝ) (v : Fin n → Ω) :
    charge (Function.uncurry Y) v = FiniteArity.tupleCharge Y v := by
  classical
  have hsum : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then Y (v i) (v j) else 0) =
      ∑ ij : PairIndex n, Y (v ij.val.1) (v ij.val.2) := by
    rw [← Fintype.sum_prod_type (fun ij : Fin n × Fin n =>
      if ij.1 ≠ ij.2 then Y (v ij.1) (v ij.2) else 0), ← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)) (by simp)
      (fun ij => Y (v ij.1) (v ij.2))
  simp only [ne_eq, ite_not] at hsum
  unfold charge FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  exact congrArg (fun x : ℝ => x / 2) hsum.symm

variable {V : Type*} [MeasurableSpace V] [MetricSpace V] [CompactSpace V] [BorelSpace V]
  [MeasurableSpace.CountablyGenerated V] {μ : Measure V}
  [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Actual optimal finite sampled partitions yield a bounded-order physical
primal when their expected costs converge to the original dual objective.
The common pair-null license and the limiting laws are constructed internally. -/
theorem exists_primal_of_sampled_cost_tendsto (N : ℕ) (hN : 2 ≤ N)
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (Y : V × V → ℝ) (hY : Measurable Y)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Y z| ≤ b)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique (Function.uncurry A) v → charge Y v ≤ 1)
    (hcost : Tendsto (fun m =>
      cost (PhysicalPrimalSampling.optimalSampledLaws (n := m + 2) μ N hN A hsym))
      atTop (nhds ((∫ z, Y z ∂graphDemand μ {p | A p.1 p.2 = true}) / 2))) :
    ∃ η : Laws V, (∀ n, IsFiniteMeasure (η n)) ∧
      (∀ n, n < 2 ∨ N < n → η n = 0) ∧
      (∀ n (σ : Equiv.Perm (Fin n)), (η n).map (fun v => v ∘ σ) = η n) ∧
      Feasible (fun x y => A x y = true) (graphDemand μ {p | A p.1 p.2 = true}) η ∧
      cost η = (∫ z, Y z ∂graphDemand μ {p | A p.1 p.2 = true}) / 2 ∧
      (∀ n, ∀ᵐ v ∂η n, Function.Injective v) ∧
      ∀ n, ∀ᵐ v ∂η n, charge Y v = 1 := by
  let E : Set (V × V) := {p | A p.1 p.2 = true}
  have hE : MeasurableSet E := hA (measurableSet_singleton true)
  have : IsFiniteMeasure (graphDemand μ E) := by unfold graphDemand; infer_instance
  let ν : FiniteMeasure (V × V) := ⟨graphDemand μ E, inferInstance⟩
  let ρ : ℕ → Laws V := fun m =>
    PhysicalPrimalSampling.optimalSampledLaws (n := m + 2) μ N hN A hsym
  obtain ⟨η, hfinite, hcap, hperm, hbalance, hvalue⟩ :=
    exists_symmetric_laws_cost_limit N ν ρ
      (fun _ => PhysicalPrimalSampling.optimalSampledLaws_zero_of_order μ N hN A hsym)
      (fun _ => PhysicalPrimalSampling.optimalSampledLaws_symmetric μ N hN A hsym)
      (fun _ => PhysicalPrimalSampling.optimalSampledLaws_occupation μ (by omega) N hN A hsym hA)
      _ hcost
  have hbalance : occupation η = graphDemand μ E := hbalance
  have hfeasible : Feasible (fun x y => A x y = true) (graphDemand μ E) η :=
    feasible_graphDemand_of_balance η μ E hE (hcap 0 (Or.inl (by omega)))
      (hcap 1 (Or.inl (by omega))) hbalance
  have hint : Integrable Y (graphDemand μ E) :=
    (PhysicalCliqueRepresentative.integrable_of_bounded (μ.prod μ) hY b hbound).mono_measure
      Measure.restrict_le_self
  obtain ⟨Z, _, hZ0, _, _, hlicense⟩ :=
    PhysicalCliqueRepresentative.exists_common_pair_null μ hA hY b hb hbound htest
  have havoid : ∀ᵐ z ∂graphDemand μ E, z ∉ Z :=
    ae_mono Measure.restrict_le_self (compl_mem_ae_iff.mpr hZ0)
  have : ∀ n, IsFiniteMeasure (η n) := hfinite
  refine ⟨η, hfinite, hcap, hperm, hfeasible, hvalue, ?_, ?_⟩
  · exact ae_injective_graphDemand_of_balance η μ E hbalance
  · exact ae_tight_of_pairwise_tests η (fun x y => A x y = true) (graphDemand μ E)
      Y hfeasible hint (fun z => z ∉ Z) havoid hlicense hvalue

/-- An actual finite-order equality constructs a physical primal for the
original full feasible kernel. Sampling cost convergence, common null-set
licensing, exact pair balance, support and tightness are all proved inputs.
Finite-order stabilization itself is the explicit equality hypothesis. -/
theorem exists_primal_of_finite_order_equality (N : ℕ) (hN : 2 ≤ N)
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (Y : V → V → ℝ)
    (hY : Measurable (Function.uncurry Y))
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Function.uncurry Y z| ≤ b)
    (hfull : ∀ n, 2 ≤ n → FiniteArity.FeasibleOrder μ A Y n)
    (hobjective : FiniteCappedSamplingCost.physicalObjective μ Y =
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ A))
    (hvalue : CappedModel.capValue V μ N (FiniteCappedSamplingCost.physicalDensity μ A) =
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ A)) :
    ∃ η : Laws V, (∀ n, IsFiniteMeasure (η n)) ∧
      (∀ n, n < 2 ∨ N < n → η n = 0) ∧
      (∀ n (σ : Equiv.Perm (Fin n)), (η n).map (fun v => v ∘ σ) = η n) ∧
      Feasible (fun x y => A x y = true) (graphDemand μ {p | A p.1 p.2 = true}) η ∧
      cost η = FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ A) ∧
      (∀ n, ∀ᵐ v ∂η n, Function.Injective v) ∧
      ∀ n, ∀ᵐ v ∂η n, charge (Function.uncurry Y) v = 1 := by
  let E : Set (V × V) := {p | A p.1 p.2 = true}
  have hE : MeasurableSet E := hA (measurableSet_singleton true)
  have hobj : (∫ z, Function.uncurry Y z ∂graphDemand μ E) / 2 =
      FiniteCappedSamplingCost.physicalObjective μ Y := by
    have heq : E.indicator (Function.uncurry Y) =ᵐ[μ.prod μ] Function.uncurry Y := by
      filter_upwards [hzero] with z hz
      by_cases h : A z.1 z.2 = true
      · simp [E, h]
      · have hf : A z.1 z.2 = false := Bool.eq_false_iff.mpr h
        simp [E, h, hz hf, Function.uncurry]
    rw [graphDemand, ← integral_indicator hE, integral_congr_ae heq]
    rfl
  have hdual := hobj.trans hobjective
  have hint := PhysicalCliqueRepresentative.integrable_of_bounded (μ.prod μ) hY b hbound
  have ht := FiniteCappedSamplingCost.expectedCappedCost_tendsto_densityLimit
    A hsym hA Y hint hYsym hzero N hN (fun k hk _ => hfull k hk) hobjective hvalue
  have hcost : Tendsto (fun m =>
      cost (PhysicalPrimalSampling.optimalSampledLaws (n := m + 2) μ N hN A hsym))
      atTop (nhds ((∫ z, Function.uncurry Y z ∂graphDemand μ E) / 2)) := by
    rw [hdual]
    have hshift : Tendsto (fun m =>
        FiniteCappedSamplingCost.expectedCappedCost μ A hsym N (m + 2)) atTop
        (nhds (FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ A))) :=
      ht.comp (Filter.tendsto_add_atTop_nat 2)
    simpa only [PhysicalPrimalSampling.optimalSampledLaws_cost μ N hN A hsym hA,
      FiniteCappedSamplingCost.expectedCappedCost] using hshift
  have htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique (Function.uncurry A) v →
        charge (Function.uncurry Y) v ≤ 1 := by
    intro n hn
    filter_upwards [hfull n hn] with v hv hclique
    rw [charge_eq_tupleCharge]
    exact hv hclique
  obtain ⟨η, hfinite, hcap, hperm, hfeasible, hcost, hinjective, htight⟩ :=
    exists_primal_of_sampled_cost_tendsto N hN A hsym hA (Function.uncurry Y) hY
      b hb hbound htest hcost
  exact ⟨η, hfinite, hcap, hperm, hfeasible, hcost.trans hdual, hinjective, htight⟩

end Erdos1017.PhysicalPrimal

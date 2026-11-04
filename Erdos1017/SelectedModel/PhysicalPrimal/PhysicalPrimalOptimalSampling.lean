module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalSampling
public import Erdos1017.SelectedModel.Capped.FractionalCappedBoundedDual

/-!
# Sampled laws from optimal capped partitions

Fixing one optimal capped fractional partition for each labeled graph and
sampling gives finite, symmetric, feasible, absolutely continuous laws with
distinct vertices whose cost is exactly the expected capped optimum
(`optimalSampledLaws_cost`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.PhysicalPrimalSampling

variable {V : Type*} [MeasurableSpace V]

/-- Fix one actual optimal capped fractional partition for each labeled graph. -/
def optimalCliqueWeights {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) :
    FractionalCappedGraph.Clique G N → ℝ :=
  Classical.choose (FractionalCappedGraph.exists_optimal G N hN)

theorem optimalCliqueWeights_feasible {n : ℕ} (G : SimpleGraph (Fin n))
    (N : ℕ) (hN : 2 ≤ N) :
    FractionalCappedGraph.Feasible G N (optimalCliqueWeights G N hN) :=
  (Classical.choose_spec (FractionalCappedGraph.exists_optimal G N hN)).1

/-- Extend the chosen optimal partition by zero to every finite vertex subset. -/
def optimalSubsetWeights {n : ℕ} (N : ℕ) (hN : 2 ≤ N)
    (G : SimpleGraph (Fin n)) : Finset (Fin n) → ℝ :=
  FractionalCappedGraph.extendWeights G N (optimalCliqueWeights G N hN)

theorem optimalSubsetWeights_feasible {n : ℕ} (N : ℕ) (hN : 2 ≤ N)
    (G : SimpleGraph (Fin n)) :
    FractionalCappedGraph.SubsetFeasible G N (optimalSubsetWeights N hN G) :=
  FractionalCappedGraph.extendWeights_feasible G N (optimalCliqueWeights G N hN)
    (optimalCliqueWeights_feasible G N hN)

theorem optimalSubsetWeights_cost {n : ℕ} (N : ℕ) (hN : 2 ≤ N)
    (G : SimpleGraph (Fin n)) :
    (∑ S, optimalSubsetWeights N hN G S) = FractionalCappedGraph.value G N := by
  have heq := FractionalCappedGraph.value_eq_optimal G N (optimalCliqueWeights G N hN)
    (optimalCliqueWeights_feasible G N hN)
    (Classical.choose_spec (FractionalCappedGraph.exists_optimal G N hN)).2
  have hsum := FractionalCappedGraph.extendWeights_sum G N (optimalCliqueWeights G N hN)
    (fun _ => 1)
  simpa only [mul_one, FinitePrimal.cost, optimalSubsetWeights, heq] using hsum

/-- Actual optimal finite partitions, averaged over physical samples and
symmetrized at every retained clique order. -/
def optimalSampledLaws (μ : Measure V) {n : ℕ} (N : ℕ) (hN : 2 ≤ N)
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x) : PhysicalPrimal.Laws V :=
  sampledLaws (n := n) μ A hsym (optimalSubsetWeights N hN)

instance optimalSampledLaws_finite (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (k : ℕ) : IsFiniteMeasure (optimalSampledLaws (n := n) μ N hN A hsym k) :=
  sampledLaws_finite μ A hsym _ k

theorem optimalSampledLaws_zero_of_order (μ : Measure V) {n : ℕ}
    (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (k : ℕ) (hk : k < 2 ∨ N < k) :
    optimalSampledLaws (n := n) μ N hN A hsym k = 0 :=
  sampledLaws_zero_of_order μ A hsym _
    (fun G => (optimalSubsetWeights_feasible N hN G).1)
    (fun G => (optimalSubsetWeights_feasible N hN G).2) k hk

theorem optimalSampledLaws_symmetric (μ : Measure V) {n : ℕ}
    (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (optimalSampledLaws (n := n) μ N hN A hsym k).map (fun v => v ∘ σ) =
      optimalSampledLaws (n := n) μ N hN A hsym k :=
  sampledLaws_symmetric μ A hsym _ k σ

theorem optimalSampledLaws_occupation (μ : Measure V) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) :
    PhysicalPrimal.occupation (optimalSampledLaws (n := n) μ N hN A hsym) =
      (μ.prod μ).restrict {p | A p.1 p.2 = true} :=
  sampledLaws_occupation μ hn A hsym hA _
    (fun G => (optimalSubsetWeights_feasible N hN G).1)

/-- This is the exact expected capped optimum used in the separate cost
convergence argument; no cost bound is supplied as a hypothesis. -/
theorem optimalSampledLaws_cost (μ : Measure V) [IsProbabilityMeasure μ]
    {n : ℕ} (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) :
    PhysicalPrimal.cost (optimalSampledLaws (n := n) μ N hN A hsym) =
      (∫ v, FractionalCappedGraph.value (sampleGraph A hsym v) N
        ∂Measure.pi (fun _ : Fin n => μ)) / ((n * (n - 1) : ℕ) : ℝ) := by
  have h := sampledLaws_cost (n := n) μ A hsym hA (optimalSubsetWeights N hN)
    (fun G => (optimalSubsetWeights_feasible N hN G).1.1)
  simpa only [optimalSampledLaws, optimalSubsetWeights_cost] using h

theorem optimalSampledLaws_feasible (μ : Measure V) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) :
    PhysicalPrimal.Feasible (fun x y => A x y = true)
      ((μ.prod μ).restrict {p | A p.1 p.2 = true})
      (optimalSampledLaws (n := n) μ N hN A hsym) :=
  sampledLaws_feasible μ hn A hsym hA _
    (fun G => (optimalSubsetWeights_feasible N hN G).1)
    (fun G => (optimalSubsetWeights_feasible N hN G).2)

theorem optimalSampledLaws_absolutelyContinuous (μ : Measure V) [IsProbabilityMeasure μ]
    {n : ℕ} (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (k : ℕ) :
    optimalSampledLaws (n := n) μ N hN A hsym k ≪ Measure.pi (fun _ : Fin k => μ) :=
  sampledLaws_absolutelyContinuous μ A hsym _ k

theorem optimalSampledLaws_distinct [MeasurableEq V] (μ : Measure V)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {n : ℕ}
    (N : ℕ) (hN : 2 ≤ N) (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (k : ℕ) :
    ∀ᵐ v ∂optimalSampledLaws (n := n) μ N hN A hsym k, Function.Injective v :=
  sampledLaws_distinct μ A hsym _ k

end Erdos1017.PhysicalPrimalSampling

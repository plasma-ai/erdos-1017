module

public import Erdos1017.SelectedModel.Capped.CappedFiniteOrderStabilization
public import Erdos1017.SelectedModel.Capped.CappedPhysicalPrimal
public import Erdos1017.Models.Selection.FullStationarySelection

/-!
# Physical primal of a strict-gap optimum

A full stationary optimum above the benchmark has a bounded-order physical
primal for its original adjacency and charge moments, and a failure of the
benchmark bound yields a full model selected at positive global excess together
with that primal.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual full stationary optimum above the benchmark has a genuine
bounded-order physical primal for its original adjacency and charge moments.
The finite-order equality and strict support are derived internally. -/
theorem FullStationaryClass.exists_physical_primal_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hdhalf : d < 1 / 2) (hgap : benchmark d < c) :
    ∃ N : ℕ, 2 ≤ N ∧ capValue Ω μ N d = FractionalGraph.densityLimit d ∧
      ∃ η : PhysicalPrimal.Laws Ω, (∀ n, IsFiniteMeasure (η n)) ∧
        (∀ n, n < 2 ∨ N < n → η n = 0) ∧
        (∀ n (σ : Equiv.Perm (Fin n)), (η n).map (fun v => v ∘ σ) = η n) ∧
        PhysicalPrimal.Feasible (fun x y => W.moment CappedColor.adjacency (x, y) = 1)
          ((μ.prod μ).withDensity (fun p => ENNReal.ofReal (W.moment CappedColor.adjacency p))) η ∧
        PhysicalPrimal.cost η = c ∧
        (∀ n, ∀ᵐ v ∂η n, Function.Injective v) ∧
        ∀ n, ∀ᵐ v ∂η n, PhysicalPrimal.charge (Function.uncurry (chargeKernel W)) v = 1 := by
  have hstructure := hW.strict_gap_structure_of_density_lt_half hdhalf hgap
  have hd0 : 0 ≤ d := hW.density_eq ▸ (density_mem W).1
  obtain ⟨N, hN, heq⟩ := exists_finite_order_equality_of_strict_gap (μ := μ) d hd0 hdhalf
    (hgap.trans_eq hW.optimal)
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have heqW : capValue Ω μ N (density W) = FractionalGraph.densityLimit (density W) := by
    simpa only [hW.density_eq] using heq
  obtain ⟨η, hfinite, hcap, hperm, hfeasible, hcost, hinjective, htight⟩ :=
    exists_original_physical_primal_of_finite_order_equality W hW.full hopt m
      hstructure.strict_support hW.deterministic N hN heqW
  exact ⟨N, hN, heq, η, hfinite, hcap, hperm, hfeasible,
    hcost.trans hW.objective_eq, hinjective, htight⟩

/-- A genuine failure of the benchmark bound constructs the actual full
model selected at positive global excess, together with its same-model
bounded-order physical primal. Both scalar selections are retained. -/
theorem exists_selected_full_positive_global_excess_with_physical_primal
    (hfailure : ∃ d ∈ Icc (0 : ℝ) (1 / 2), benchmark d < FractionalGraph.densityLimit d) :
    ∃ (d : ℝ) (W : Model Ω μ) (m : ℝ) (N : ℕ) (η : PhysicalPrimal.Laws Ω),
      d ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧
      FullStationaryClass d (FractionalGraph.densityLimit d) W m ∧
      0 < objective W - benchmark (density W) ∧
      (∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
        FullFeasible V → objective V - benchmark (density V) ≤
          objective W - benchmark (density W)) ∧
      (∀ (V : Model Ω μ) (n : ℝ),
        FullStationaryClass d (FractionalGraph.densityLimit d) V n → m ≤ n) ∧
      (∀ V : Model Ω μ, FullStationaryClass d (FractionalGraph.densityLimit d) V m →
        stationaryEnergy V m ≤ stationaryEnergy W m) ∧
      2 ≤ N ∧ capValue Ω μ N d = FractionalGraph.densityLimit d ∧
      (∀ n, IsFiniteMeasure (η n)) ∧
      (∀ n, n < 2 ∨ N < n → η n = 0) ∧
      (∀ n (σ : Equiv.Perm (Fin n)), (η n).map (fun v => v ∘ σ) = η n) ∧
      PhysicalPrimal.Feasible (fun x y => W.moment CappedColor.adjacency (x, y) = 1)
        ((μ.prod μ).withDensity (fun p => ENNReal.ofReal (W.moment CappedColor.adjacency p))) η ∧
      PhysicalPrimal.cost η = FractionalGraph.densityLimit d ∧
      (∀ n, ∀ᵐ v ∂η n, Function.Injective v) ∧
      ∀ n, ∀ᵐ v ∂η n, PhysicalPrimal.charge (Function.uncurry (chargeKernel W)) v = 1 := by
  obtain ⟨d, W, m, hd, hW, hpositive, hglobal, hmin, henergy⟩ :=
    exists_selected_full_positive_global_excess (Ω := Ω) (μ := μ) hfailure
  have hgap : benchmark d < FractionalGraph.densityLimit d := by
    have h := hpositive
    rw [hW.objective_eq, hW.density_eq] at h
    linarith
  obtain ⟨N, hN, heq, η, hfinite, hcap, hperm, hfeasible, hcost, hinjective, htight⟩ :=
    hW.exists_physical_primal_of_strict_gap hd.2 hgap
  exact ⟨d, W, m, N, η, hd, hW, hpositive, hglobal, hmin, henergy, hN, heq,
    hfinite, hcap, hperm, hfeasible, hcost, hinjective, htight⟩

end Erdos1017.CappedModel

module

public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalAttainment

/-!
# Physical primal for the decorated model

The decorated-model application of bounded-order physical primal attainment.
Finite-order equality remains explicit; the physical representative, sampled
costs, limiting laws and tightness are constructed by proved results.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Exact physical pair balance transfers the representative's charge to
the original model under arbitrary parent laws, including singular joint laws. -/
theorem ae_physical_charge_eq_original (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (η : PhysicalPrimal.Laws Ω)
    (hbalance : PhysicalPrimal.occupation η = PhysicalPrimal.graphDemand μ
      {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}) (n : ℕ) :
    (PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m))) =ᵐ[η n]
      PhysicalPrimal.charge (Function.uncurry (chargeKernel W)) := by
  have hpair : ∀ᵐ p ∂PhysicalPrimal.graphDemand μ
      {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true},
      PhysicalRepresentative.charge W m p.1 p.2 = chargeKernel W p.1 p.2 :=
    ae_mono Measure.restrict_le_self (PhysicalRepresentative.charge_ae_eq W m hsupport)
  filter_upwards [PhysicalPrimal.ae_all_pairs_of_balance η _ hbalance _ hpair n] with v hv
  unfold PhysicalPrimal.charge
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  exact hv ij.val.1 ij.val.2 ij.property

/-- The representative's exact graph demand is the original model's
adjacency-moment weighted product measure. -/
theorem physical_graphDemand_eq_momentDemand (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    PhysicalPrimal.graphDemand μ {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} =
      (μ.prod μ).withDensity (fun p => ENNReal.ofReal (W.moment CappedColor.adjacency p)) := by
  let E : Set (Ω × Ω) := {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have heq : E.indicator (1 : Ω × Ω → ℝ≥0∞) =ᵐ[μ.prod μ]
      fun p => ENNReal.ofReal (W.moment CappedColor.adjacency p) := by
    filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hsupport] with p hp
    rw [hp]
    by_cases h : PhysicalRepresentative.adjacency W m p.1 p.2 = true <;> simp [E, h]
  change (μ.prod μ).restrict E = _
  rw [← withDensity_indicator_one hE]
  exact withDensity_congr_ae heq

/-- Every parent of an exactly balanced physical law is an actual clique
for the original model's adjacency moment. Only pair absolute continuity is used. -/
theorem ae_physical_original_clique (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (η : PhysicalPrimal.Laws Ω)
    (hbalance : PhysicalPrimal.occupation η = PhysicalPrimal.graphDemand μ
      {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}) (n : ℕ) :
    ∀ᵐ v ∂η n, ∀ i j, i ≠ j → W.moment CappedColor.adjacency (v i, v j) = 1 := by
  have hE := (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hpair : ∀ᵐ p ∂PhysicalPrimal.graphDemand μ
      {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true},
      W.moment CappedColor.adjacency p = 1 := by
    filter_upwards [ae_mono Measure.restrict_le_self
      (PhysicalRepresentative.adjacency_moment_ae_eq W m hsupport), ae_restrict_mem hE] with p hp hG
    change PhysicalRepresentative.adjacency W m p.1 p.2 = true at hG
    simpa only [hG, ↓reduceIte] using hp
  exact PhysicalPrimal.ae_all_pairs_of_balance η _ hbalance _ hpair n

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [MeasurableSpace.CountablyGenerated Ω] [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- An actual fully feasible optimal decorated model and an actual
finite-order equality produce a capped physical primal for that model.
Tightness is for its original charge kernel, under the constructed laws. -/
theorem exists_physical_primal_of_finite_order_equality
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W)) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (N : ℕ) (hN : 2 ≤ N)
    (hvalue : capValue Ω μ N (density W) = FractionalGraph.densityLimit (density W)) :
    ∃ η : PhysicalPrimal.Laws Ω, (∀ n, IsFiniteMeasure (η n)) ∧
      (∀ n, n < 2 ∨ N < n → η n = 0) ∧
      (∀ n (σ : Equiv.Perm (Fin n)), (η n).map (fun v => v ∘ σ) = η n) ∧
      PhysicalPrimal.Feasible (fun x y => PhysicalRepresentative.adjacency W m x y = true)
        (PhysicalPrimal.graphDemand μ {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}) η ∧
      PhysicalPrimal.cost η = objective W ∧
      (∀ n, ∀ᵐ v ∂η n, Function.Injective v) ∧
      ∀ n, ∀ᵐ v ∂η n, PhysicalPrimal.charge (Function.uncurry (chargeKernel W)) v = 1 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hd : FiniteCappedSamplingCost.physicalDensity μ A = density W :=
    PhysicalRepresentative.density_eq W m hsupport
  have ho : FiniteCappedSamplingCost.physicalObjective μ Y = objective W :=
    PhysicalRepresentative.objective_eq W m hsupport
  have hphysicalObjective : FiniteCappedSamplingCost.physicalObjective μ Y =
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ A) := by
    rw [ho, hd]
    exact hopt
  have hphysicalValue : capValue Ω μ N (FiniteCappedSamplingCost.physicalDensity μ A) =
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ A) := by
    rw [hd]
    exact hvalue
  obtain ⟨η, hfinite, hcap, hperm, hfeasible, hcost, hinjective, htight⟩ :=
    PhysicalPrimal.exists_primal_of_finite_order_equality N hN A
      (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.measurable_adjacency W m)
      Y (PhysicalRepresentative.measurable_charge W m)
      (Filter.Eventually.of_forall (fun p => PhysicalRepresentative.charge_symm W m p.1 p.2))
      (Filter.Eventually.of_forall (fun p => PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2))
      3 (by norm_num) (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
      (fun n _ => PhysicalRepresentative.full_feasible W hW m hsupport hdet n)
      hphysicalObjective hphysicalValue
  have hcost : PhysicalPrimal.cost η = objective W := by
    rw [hd] at hcost
    exact hcost.trans hopt.symm
  refine ⟨η, hfinite, hcap, hperm, hfeasible, hcost, hinjective, ?_⟩
  intro n
  filter_upwards [htight n,
    ae_physical_charge_eq_original W m hsupport η hfeasible.2.2.2 n] with v hv heq
  rw [← heq]
  exact hv

/-- The same constructed laws give exact physical attainment written
entirely with the original decorated model's adjacency and charge moments. -/
theorem exists_original_physical_primal_of_finite_order_equality
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W)) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (N : ℕ) (hN : 2 ≤ N)
    (hvalue : capValue Ω μ N (density W) = FractionalGraph.densityLimit (density W)) :
    ∃ η : PhysicalPrimal.Laws Ω, (∀ n, IsFiniteMeasure (η n)) ∧
      (∀ n, n < 2 ∨ N < n → η n = 0) ∧
      (∀ n (σ : Equiv.Perm (Fin n)), (η n).map (fun v => v ∘ σ) = η n) ∧
      PhysicalPrimal.Feasible (fun x y => W.moment CappedColor.adjacency (x, y) = 1)
        ((μ.prod μ).withDensity (fun p => ENNReal.ofReal (W.moment CappedColor.adjacency p))) η ∧
      PhysicalPrimal.cost η = objective W ∧
      (∀ n, ∀ᵐ v ∂η n, Function.Injective v) ∧
      ∀ n, ∀ᵐ v ∂η n, PhysicalPrimal.charge (Function.uncurry (chargeKernel W)) v = 1 := by
  obtain ⟨η, hfinite, hcap, hperm, hfeasible, hcost, hinjective, htight⟩ :=
    exists_physical_primal_of_finite_order_equality W hW hopt m hsupport hdet N hN hvalue
  refine ⟨η, hfinite, hcap, hperm, ?_, hcost, hinjective, htight⟩
  exact ⟨hfeasible.1, hfeasible.2.1,
    ae_physical_original_clique W m hsupport η hfeasible.2.2.2,
    hfeasible.2.2.2.trans (physical_graphDemand_eq_momentDemand W m hsupport)⟩

end Erdos1017.CappedModel

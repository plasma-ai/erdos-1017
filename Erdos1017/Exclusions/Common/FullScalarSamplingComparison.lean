module

public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost
public import Erdos1017.LowerBound.WeightedGraphDual
public import Erdos1017.FractionalLimit.FractionalDensityLimit

/-!
# Density limit for scalar charges passing all clique tests

Integrable, or bounded measurable, signed scalar charges satisfying every clique
test obey the full fractional density limit, with no compact-color model or
fixed charge box.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Erdos1017.FiniteCappedSamplingCost

open CappedModel PhysicalPrimalSampling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- All scalar clique orders give the full signed finite dual on almost every
physical sample. No charge range or sign condition is used. -/
private theorem ae_tupleCharge_le_fractionalValue (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (Y : Ω → Ω → ℝ)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) (n : ℕ) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      FiniteArity.tupleCharge Y v ≤ FractionalGraph.value (sampleGraph A hsym v) := by
  filter_upwards [ae_sampled_capped_dual A hsym Y hYsym hzero n n
    (fun k _ _ => hfull k)] with v hv
  have hdual : WeightedGraph.DualFeasible (sampleGraph A hsym v)
      (fun i j => if i = j then 0 else Y (v i) (v j)) := by
    refine ⟨hv.1, hv.2.1, ?_⟩
    intro S hS
    exact hv.2.2 S (by simpa using Finset.card_le_card (Finset.subset_univ S)) hS
  have h := WeightedGraph.dual_objective_le_value (sampleGraph A hsym v) _ hdual
  simpa only [WeightedGraph.objective, one_mul, mul_one, FiniteArity.tupleCharge,
    FiniteArity.pairCharge, FiniteArity.crossSum] using h

/-- Integrable signed scalar charges satisfying every actual clique test obey
the full fractional density limit. No compact-color model is constructed. -/
theorem physicalObjective_le_densityLimit_of_full_scalar_tests (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    physicalObjective μ Y ≤ FractionalGraph.densityLimit (physicalDensity μ A) := by
  let d := physicalDensity μ A
  have hbound (n : ℕ) (hn : 2 ≤ n) :
      (1 - 1 / (n : ℝ)) * physicalObjective μ Y ≤
        FractionalGraph.densityLimit d +
          3 * ∫ v : Fin n → Ω, |sampleGraphDensity A hsym v - d|
            ∂Measure.pi (fun _ : Fin n => μ) := by
    have hn0 : 0 < n := by omega
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn0
    have herror := integrable_graph_observable (μ := μ) A hsym hA
      (fun G : SimpleGraph (Fin n) =>
        |(G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 - d|)
    have hcharge : Integrable (fun v : Fin n → Ω => FiniteArity.tupleCharge Y v)
        (Measure.pi (fun _ : Fin n => μ)) := by
      have hpairs (e : CliquePair n) : Integrable
          (fun v : Fin n → Ω => Y (v e.val.1) (v e.val.2))
          (Measure.pi (fun _ : Fin n => μ)) := by
        have hp := FiniteArity.measurePreserving_pair μ e.val.1 e.val.2 (ne_of_lt e.property)
        exact hp.integrable_comp_of_integrable hY
      have hupper : (fun v : Fin n → Ω => FiniteArity.tupleCharge Y v) =ᵐ[
          Measure.pi (fun _ : Fin n => μ)]
          fun v => ∑ e : CliquePair n, Y (v e.val.1) (v e.val.2) := by
        filter_upwards [FiniteArity.ae_all_pairs μ n _ hYsym] with v hv
        exact tupleCharge_eq_upper Y v hv
      exact (integrable_finsetSum _ (fun e _ => hpairs e)).congr hupper.symm
    have hpoint : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
        FiniteArity.tupleCharge Y v / (n : ℝ) ^ 2 ≤
          FractionalGraph.densityLimit d + 3 * |sampleGraphDensity A hsym v - d| := by
      filter_upwards [ae_tupleCharge_le_fractionalValue A hsym Y hYsym hzero hfull n]
        with v hv
      have hf := FractionalGraph.finite_graph_le_densityLimit
        (sampleGraph A hsym v) hn0 d
      have hdiv : FiniteArity.tupleCharge Y v / (n : ℝ) ^ 2 ≤
          FractionalGraph.value (sampleGraph A hsym v) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hv (sq_nonneg _)
      exact hdiv.trans (by simpa only [sampleGraphDensity] using (sub_le_iff_le_add.mp hf))
    have hi := integral_mono_ae (hcharge.div_const ((n : ℝ) ^ 2))
      ((integrable_const (FractionalGraph.densityLimit d)).add (herror.const_mul 3)) hpoint
    simp only [Pi.add_apply] at hi
    rw [integral_div, integral_add (integrable_const _) (herror.const_mul 3),
      integral_const, integral_const_mul, integral_tupleCharge Y hY hYsym n] at hi
    simp only [probReal_univ, one_smul] at hi
    have hchoose : (n.choose 2 : ℝ) * 2 / (n : ℝ) ^ 2 = 1 - 1 / (n : ℝ) := by
      rw [Nat.cast_choose_two]
      field_simp
    have hleft_eq : (n.choose 2 : ℝ) * (2 * physicalObjective μ Y) / (n : ℝ) ^ 2 =
        (1 - 1 / (n : ℝ)) * physicalObjective μ Y := by
      calc
        _ = ((n.choose 2 : ℝ) * 2 / (n : ℝ) ^ 2) * physicalObjective μ Y := by ring
        _ = _ := by rw [hchoose]
    simpa only [hleft_eq, sampleGraphDensity] using hi
  have hbias : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hleft : Tendsto (fun n : ℕ =>
      (1 - 1 / (n : ℝ)) * physicalObjective μ Y) atTop (𝓝 (physicalObjective μ Y)) := by
    simpa using hbias.mul_const (physicalObjective μ Y)
  have hright : Tendsto (fun n : ℕ => FractionalGraph.densityLimit d +
      3 * ∫ v : Fin n → Ω, |sampleGraphDensity A hsym v - d|
        ∂Measure.pi (fun _ : Fin n => μ)) atTop (𝓝 (FractionalGraph.densityLimit d)) := by
    simpa [d] using (tendsto_const_nhds.add
      ((sampleGraphDensity_abs_error_tendsto A hsym hA).const_mul 3))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact hbound n hn

/-- Bounded measurable signed scalar charges satisfy the integrability
required by the full-order sampling comparison, with no fixed charge box. -/
theorem physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    physicalObjective μ Y ≤ FractionalGraph.densityLimit (physicalDensity μ A) := by
  have hi : Integrable (Function.uncurry Y) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable B (Eventually.of_forall hB)
  exact physicalObjective_le_densityLimit_of_full_scalar_tests A hsym hA Y hi hYsym hzero hfull

end Erdos1017.FiniteCappedSamplingCost

module

public import Erdos1017.SelectedModel.Capped.CappedDeterministicTests
public import Erdos1017.SelectedModel.StationaryFeature
public import Erdos1017.SelectedModel.BoundedFeatureArity

/-!
# Finite-arity budget applied to the capped model

The feature representation and finite-arity theorem apply to the colored capped
model, so an explicit spectral budget gives full feasibility
(`fullFeasible_of_explicit_spectral_budget`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem boolean_shift_operator_eq (W : Model Ω μ) (m : ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => chargeKernel W p.1 p.2 + (-m) *
      (if positiveAdjacency W m p.1 p.2 then 1 else 0)) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖chargeKernel W p.1 p.2 + (-m) *
      (if positiveAdjacency W m p.1 p.2 then 1 else 0)‖ ≤ 4) :
    KernelOperator.operator (fun x y => chargeKernel W x y + (-m) *
      (if positiveAdjacency W m x y then 1 else 0)) (by norm_num) hK hB = shiftedOperator W m := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [shiftedOperator, KernelOperator.operator_inner]
  apply integral_congr_ae
  filter_upwards [boolean_shift_eq W m hA] with p hp
  rw [hp]

/-- The proved actual feature representation and finite-arity theorem
apply to the actual colored capped model. The spectral and stationary
gaps, source multiplier range, strict support, and finite test budget are
explicit hypotheses; no omitted sampled test is assumed. -/
theorem fullFeasible_of_explicit_spectral_budget [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (m ν g s₀ : ℝ) (hg : 0 < g) (hs₀ : 0 < s₀)
    (hm : -3 ≤ m ∧ m < 0) (hgap : g ≤ ν + m)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (hM : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hfinite : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)))
    (hindex : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 2)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : s₀ ≤ σ) (heigen : shiftedOperator W m w = σ • w)
    {r : ℕ} (hW : Feasible r W)
    (hbudget : FiniteArity.Certificate.testBudget (Real.sqrt (8 + 32 / s₀)) g ≤ r) :
    FullFeasible W ∧ ∀ n, FiniteArity.Certificate.testBudget (Real.sqrt (8 + 32 / s₀)) g < n →
      ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), FiniteArity.TupleClique (positiveAdjacency W m) x →
        FiniteArity.tupleCharge (chargeKernel W) x < 0 := by
  let A := positiveAdjacency W m
  let Y := chargeKernel W
  let K := fun x y => Y x y + (-m) * (if A x y then 1 else 0)
  have hEq : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = shiftedKernel W m p.1 p.2 := boolean_shift_eq W m hA
  have hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ) :=
    (shiftedKernel_measurable W m).congr (by
      filter_upwards [hEq] with p hp
      exact hp.symm)
  have hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ 4 := by
    filter_upwards [hEq, hM] with p he hp
    rw [he, shiftedKernel, Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2 := by
    filter_upwards [hEq, hM] with p he hp
    rw [he]
    exact hp.1
  have hsym : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = A p.2 p.1 ∧ Y p.1 p.2 = Y p.2 p.1 :=
    (positiveAdjacency_symm W m).and (chargeKernel_symm W)
  have hupper : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 ≤ 1 := by
    filter_upwards with p
    exact (charge_moment_le_adjacency W p).trans (adjacency_moment_mem W p).2
  have hsupport : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0 :=
    boolean_missing_charge_zero W m hA
  have hstationary : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν := by
    filter_upwards [Measure.ae_ae_of_ae_prod hEq, hrow] with x hx hr
    exact (integral_congr_ae hx).trans hr
  have hop : KernelOperator.operator K (by norm_num) hK hB = shiftedOperator W m :=
    boolean_shift_operator_eq W m hA hK hB
  have hfiniteK : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace
      (KernelOperator.operator K (by norm_num) hK hB)) := by rwa [hop]
  have hindexK : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace
      (KernelOperator.operator K (by norm_num) hK hB)) ≤ 2 := by rwa [hop]
  have heigenK : KernelOperator.operator K (by norm_num) hK hB w = σ • w := by rwa [hop]
  have hν : 0 < ν := by linarith [hm.2]
  obtain ⟨ι, hcount, F, J, hF, hbound, hself, hrepr⟩ :=
    KernelOperator.exists_uniform_feature_of_stationary_positive_index_two K hK hB hnonneg
      (by
        filter_upwards [hsym] with p hp
        change Y p.1 p.2 + (-m) * (if A p.1 p.2 then 1 else 0) = _
        rw [hp.1, hp.2])
      ν hν hstationary hfiniteK hindexK w hw hmean σ s₀ hs₀ hσ heigenK
  let := hcount
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  have hcap : ∀ n, 2 ≤ n → n ≤ FiniteArity.Certificate.testBudget (Real.sqrt (8 + 32 / s₀)) g →
      FiniteArity.FeasibleOrder μ A Y n := by
    intro n hn hnr
    exact (feasible_iff_scalar_orders W m hA hdet r).mp hW n hn (hnr.trans hbudget)
  obtain ⟨hfull, hnegative⟩ := FiniteArity.bounded_feature_arity_of_shifted_kernel μ A Y F hF J hself
    (Real.sqrt (8 + 32 / s₀)) g ν (-m) (Real.sqrt_pos.mpr (by positivity)) hg
    (by constructor <;> linarith [hm.1, hm.2]) (by linarith [hgap])
    hbound hsym hupper hsupport hnonneg hrepr hstationary hcap
  exact ⟨fullFeasible_of_scalar_orders W m hA hdet hfull, hnegative⟩

end Erdos1017.CappedModel

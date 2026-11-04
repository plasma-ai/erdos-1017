module

public import Erdos1017.Models.Capped.CappedWeightEdits
public import Erdos1017.Exclusions.Common.FullScalarSamplingComparison
public import Erdos1017.Models.Decorated.DecoratedAbsoluteContinuity

/-!
# Stationarity of bounded full scalar optima

A bounded full scalar optimum remains an upper bound under every
density-preserving vertex reweighting, and on a weight-regular graph it has its
own stationary multiplier with positive index at most two
(`exists_stationary_shift_of_bounded_full_scalar_optimum`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.FiniteCappedSamplingCost

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual bounded full scalar optimum remains an upper bound for
every density-preserving original vertex reweighting. No compact charge
box, multiplier or stationarity hypothesis is used. -/
theorem weight_local_max_of_bounded_full_scalar_optimum
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ)
    (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (hopt : physicalObjective μ Y = FractionalGraph.densityLimit (physicalDensity μ A))
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1)
    (hd : Variation.weightedPairIntegral (fun x y => if A x y = true then (1 : ℝ) else 0)
        (Variation.vertexWeight f) =
      Variation.weightedPairIntegral (fun x y => if A x y = true then (1 : ℝ) else 0)
        (Lp.const 2 μ (1 : ℝ))) :
    Variation.weightedPairIntegral Y (Variation.vertexWeight f) ≤
      Variation.weightedPairIntegral Y (Lp.const 2 μ (1 : ℝ)) := by
  let w := Variation.vertexWeight f
  have hw : Integrable w μ := (Lp.memLp w).integrable (by norm_num)
  have hw0 := Variation.vertexWeight_nonnegative f hf
  let ν := CappedModel.weightedMeasure (μ := μ) w
  let : IsProbabilityMeasure ν := CappedModel.weightedMeasure_probability
    hw hw0 (Variation.vertexWeight_integral f)
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hfullν : ∀ n, FiniteArity.FeasibleOrder ν A Y n := by
    intro n
    exact (DecoratedKernel.pi_absolutelyContinuous hac n).ae_le (hfull n)
  have hden : physicalDensity ν A = physicalDensity μ A := by
    unfold physicalDensity
    rw [CappedModel.integral_weightedMeasure_prod w (Lp.aestronglyMeasurable w).aemeasurable
      hw0 (fun x y => if A x y = true then (1 : ℝ) else 0)]
    change Variation.weightedPairIntegral
      (fun x y => if A x y = true then (1 : ℝ) else 0) (Variation.vertexWeight f) / 2 = _
    rw [hd, CappedModel.weightedPairIntegral_one]
  have hbound := physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    (μ := ν) A hsym hA Y hY B hB ((hac.prod hac).ae_le hYsym)
    ((hac.prod hac).ae_le hzero) hfullν
  rw [hden, ← hopt] at hbound
  unfold physicalObjective at hbound
  rw [CappedModel.integral_weightedMeasure_prod w (Lp.aestronglyMeasurable w).aemeasurable
    hw0 Y] at hbound
  rw [CappedModel.weightedPairIntegral_one]
  change Variation.weightedPairIntegral Y (Variation.vertexWeight f) / 2 ≤ _ at hbound
  linarith

/-- Every actual bounded full scalar optimum on a weight-regular graph
has its own stationary multiplier and positive index at most two. The real
kernel G is the displayed Boolean adjacency kernel; its measurable bounded
representation is explicit so that the regularity operator is unambiguous.
No original optimizer's multiplier or selected structure is transferred. -/
theorem exists_stationary_shift_of_bounded_full_scalar_optimum
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (hopt : physicalObjective μ Y = FractionalGraph.densityLimit (physicalDensity μ A))
    (G : Ω → Ω → ℝ) (hG : ∀ x y, G x y = if A x y = true then 1 else 0)
    (hGmeas : AEStronglyMeasurable (Function.uncurry G) (μ.prod μ))
    (hGone : ∀ᵐ p ∂μ.prod μ, ‖G p.1 p.2‖ ≤ 1)
    (hregular : Variation.weightFirstVariation
      (KernelOperator.operator G (by norm_num : (0 : ℝ) ≤ 1) hGmeas hGone) ≠ 0) :
    ∃ m ν D : ℝ, ∃ hD0 : 0 ≤ D,
      ∃ hM : AEStronglyMeasurable (fun p : Ω × Ω => Y p.1 p.2 - m * G p.1 p.2) (μ.prod μ),
      ∃ hD : ∀ᵐ p ∂μ.prod μ, ‖Y p.1 p.2 - m * G p.1 p.2‖ ≤ D,
      (∀ᵐ x ∂μ, (∫ y, Y x y - m * G x y ∂μ) = ν) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace
        (KernelOperator.operator (fun x y => Y x y - m * G x y) hD0 hM hD)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace
        (KernelOperator.operator (fun x y => Y x y - m * G x y) hD0 hM hD)) ≤ 2 := by
  have hGeq : G = fun x y => if A x y = true then (1 : ℝ) else 0 := by
    funext x y
    exact hG x y
  have hGsym : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = G p.2 p.1 := by
    exact Eventually.of_forall (fun p => by rw [hG, hG, hsym])
  apply Variation.exists_stationary_kernel_of_weight_local_max G Y (by norm_num) hB0
    hGmeas hY.aestronglyMeasurable hGone (Eventually.of_forall hB) hGsym hYsym hregular
    1 (by norm_num) le_rfl
  intro f hf hd
  rw [hGeq] at hd
  exact weight_local_max_of_bounded_full_scalar_optimum A hsym hA Y hY B hB
    hYsym hzero hfull hopt f hf hd

end Erdos1017.FiniteCappedSamplingCost

module

public import Erdos1017.Models.Decorated.DecoratedKernel
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Joint laws of decorated kernels

The joint law (`jointLaw`) of a latent pair and its conditional color keeps the
prescribed latent marginal, is symmetric under exchanging the two vertices, and
admits a weakly convergent subsequence whose limit keeps the marginal and
symmetry needed for disintegration.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

namespace Erdos1017.DecoratedKernel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The joint law of the latent pair and its conditional color. -/
def jointLaw (W : DecoratedKernel Ω C μ) : ProbabilityMeasure ((Ω × Ω) × C) :=
  ⟨μ.prod μ ⊗ₘ W.kernel, inferInstance⟩

@[simp] theorem toMeasure_jointLaw (W : DecoratedKernel Ω C μ) :
    (W.jointLaw : Measure ((Ω × Ω) × C)) = μ.prod μ ⊗ₘ W.kernel := rfl

/-- Joint laws retain exactly the prescribed latent-pair marginal. -/
@[simp] theorem jointLaw_fst (W : DecoratedKernel Ω C μ) :
    (W.jointLaw : Measure ((Ω × Ω) × C)).fst = μ.prod μ :=
  Measure.fst_compProd _ _

/-- Integrating a joint test agrees with conditional sampling of the color. -/
theorem integral_jointLaw (W : DecoratedKernel Ω C μ)
    {F : ((Ω × Ω) × C) → ℝ} (hF : Integrable F (W.jointLaw : Measure _)) :
    ∫ z, F z ∂(W.jointLaw : Measure _) =
      ∫ p, ∫ c, F (p, c) ∂W.kernel p ∂μ.prod μ :=
  Measure.integral_compProd hF

/-- Exchange the two latent vertices while keeping their pair color. -/
def swapPairColor (z : (Ω × Ω) × C) : (Ω × Ω) × C := (z.1.swap, z.2)

theorem measurable_swapPairColor : Measurable (swapPairColor (Ω := Ω) (C := C)) :=
  (measurable_swap.comp measurable_fst).prodMk measurable_snd

/-- Swapping the base of a composition-product pulls back its conditional kernel. -/
theorem map_swapPairColor_compProd (κ : Kernel (Ω × Ω) C) [IsSFiniteKernel κ] :
    (μ.prod μ ⊗ₘ κ).map swapPairColor =
      μ.prod μ ⊗ₘ κ.comap Prod.swap measurable_swap := by
  ext s hs
  rw [Measure.map_apply measurable_swapPairColor hs,
    Measure.compProd_apply (hs.preimage measurable_swapPairColor), Measure.compProd_apply hs]
  have h := lintegral_map
    (Kernel.measurable_kernel_prodMk_left (κ := κ.comap Prod.swap measurable_swap) hs)
    (μ := μ.prod μ) measurable_swap
  rw [Measure.prod_swap] at h
  have hpre (p : Ω × Ω) :
      Prod.mk p ⁻¹' (swapPairColor ⁻¹' s) = Prod.mk p.swap ⁻¹' s := rfl
  simpa only [hpre, Kernel.comap_apply, Prod.swap_swap] using h.symm

/-- Almost-everywhere symmetry of the conditional colors gives exact symmetry
of their joint probability law. -/
theorem jointLaw_swapPairColor (W : DecoratedKernel Ω C μ) :
    W.jointLaw.map swapPairColor = W.jointLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  change (μ.prod μ ⊗ₘ W.kernel).map swapPairColor = μ.prod μ ⊗ₘ W.kernel
  rw [map_swapPairColor_compProd]
  exact Measure.compProd_congr W.symm

omit [MeasurableSpace Ω] [MeasurableSpace C] in
theorem continuous_swapPairColor [TopologicalSpace Ω] [TopologicalSpace C] : Continuous (swapPairColor (Ω := Ω) (C := C)) :=
  (continuous_swap.comp continuous_fst).prodMk continuous_snd

section Compact

variable [MetricSpace Ω] [MetricSpace C] [CompactSpace Ω] [CompactSpace C]
  [BorelSpace Ω] [BorelSpace C]

/-- Joint laws admit a weakly convergent subsequence. The limit retains the
exact latent marginal and the symmetry needed for disintegration. -/
theorem exists_jointLaw_subsequence (W : ℕ → DecoratedKernel Ω C μ) :
    ∃ (ρ : ProbabilityMeasure ((Ω × Ω) × C)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => (W (φ n)).jointLaw) atTop (𝓝 ρ) ∧
      (ρ : Measure ((Ω × Ω) × C)).fst = μ.prod μ ∧
      ρ.map swapPairColor = ρ := by
  obtain ⟨ρ, φ, hφ, hconv⟩ := CompactSpace.tendsto_subseq (fun n => (W n).jointLaw)
  change Tendsto (fun n => (W (φ n)).jointLaw) atTop (𝓝 ρ) at hconv
  let base : ProbabilityMeasure (Ω × Ω) := ⟨μ.prod μ, inferInstance⟩
  have hfst : ρ.map Prod.fst = base := by
    apply tendsto_nhds_unique
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv continuous_fst)
    have hconst (n : ℕ) : (W (φ n)).jointLaw.map Prod.fst =
        base := by
      apply ProbabilityMeasure.toMeasure_injective
      exact jointLaw_fst (W (φ n))
    simpa only [Function.comp_apply, hconst] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        base) atTop (𝓝 base))
  refine ⟨ρ, φ, hφ, hconv, congrArg ProbabilityMeasure.toMeasure hfst, ?_⟩
  apply tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv continuous_swapPairColor)
  simpa only [Function.comp_apply, jointLaw_swapPairColor] using hconv

end Compact

end Erdos1017.DecoratedKernel

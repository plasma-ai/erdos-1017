module

public import Erdos1017.Models.Decorated.DecoratedCompactnessLaw
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Disintegration of limiting joint laws

A joint law with the prescribed latent marginal and vertex-exchange symmetry is
realized by an almost-everywhere symmetric conditional kernel (`ofJointLaw`), so
every sequence of decorated kernels has a subsequence whose joint color laws
converge weakly to the law of another decorated kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

namespace Erdos1017.DecoratedKernel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A joint law with the prescribed latent marginal and vertex-exchange
symmetry is realized by an almost-everywhere symmetric conditional kernel. -/
def ofJointLaw [StandardBorelSpace C] [Nonempty C]
    (ρ : ProbabilityMeasure ((Ω × Ω) × C))
    (hmarg : (ρ : Measure ((Ω × Ω) × C)).fst = μ.prod μ)
    (hsymm : ρ.map swapPairColor = ρ) : DecoratedKernel Ω C μ where
  kernel := (ρ : Measure ((Ω × Ω) × C)).condKernel
  markov := inferInstance
  symm := by
    have hdis : μ.prod μ ⊗ₘ (ρ : Measure ((Ω × Ω) × C)).condKernel =
        (ρ : Measure ((Ω × Ω) × C)) := by
      rw [← hmarg]
      exact Measure.disintegrate (ρ : Measure ((Ω × Ω) × C))
        (ρ : Measure ((Ω × Ω) × C)).condKernel
    have hswap : μ.prod μ ⊗ₘ
        ((ρ : Measure ((Ω × Ω) × C)).condKernel.comap Prod.swap measurable_swap) =
        μ.prod μ ⊗ₘ (ρ : Measure ((Ω × Ω) × C)).condKernel := by
      rw [← map_swapPairColor_compProd, hdis]
      exact congrArg ProbabilityMeasure.toMeasure hsymm
    have h := Kernel.ae_eq_of_compProd_eq hswap
    filter_upwards [h] with p hp
    exact hp

@[simp] theorem jointLaw_ofJointLaw [StandardBorelSpace C] [Nonempty C]
    (ρ : ProbabilityMeasure ((Ω × Ω) × C))
    (hmarg : (ρ : Measure ((Ω × Ω) × C)).fst = μ.prod μ)
    (hsymm : ρ.map swapPairColor = ρ) :
    (ofJointLaw ρ hmarg hsymm).jointLaw = ρ := by
  apply ProbabilityMeasure.toMeasure_injective
  change μ.prod μ ⊗ₘ (ρ : Measure ((Ω × Ω) × C)).condKernel = _
  rw [← hmarg]
  exact Measure.disintegrate (ρ : Measure ((Ω × Ω) × C))
    (ρ : Measure ((Ω × Ω) × C)).condKernel

section Compact

variable [MetricSpace Ω] [MetricSpace C] [CompactSpace Ω] [CompactSpace C]
  [BorelSpace Ω] [BorelSpace C] [Nonempty C]

/-- Every sequence of decorated kernels has a subsequence whose genuine
joint color laws converge weakly to the law of another decorated kernel. -/
theorem exists_jointLaw_limit (W : ℕ → DecoratedKernel Ω C μ) :
    ∃ (V : DecoratedKernel Ω C μ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => (W (φ n)).jointLaw) atTop (𝓝 V.jointLaw) := by
  obtain ⟨ρ, φ, hφ, hconv, hmarg, hsymm⟩ := exists_jointLaw_subsequence W
  exact ⟨ofJointLaw ρ hmarg hsymm, φ, hφ,
    (jointLaw_ofJointLaw ρ hmarg hsymm).symm ▸ hconv⟩

end Compact

end Erdos1017.DecoratedKernel

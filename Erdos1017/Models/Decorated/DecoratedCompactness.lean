module

public import Erdos1017.Models.Decorated.DecoratedCompactnessDisintegration
public import Erdos1017.Models.Decorated.DecoratedMomentIdentification
public import Erdos1017.Models.Decorated.DecoratedMomentBasis
public import Erdos1017.Models.Decorated.DecoratedPullbackMoments
public import Erdos1017.Models.Kernel.GraphonFamilyCompactness

/-!
# Decorated compactness in a common frame

A decorated limit realizes every continuous normalized moment in one common
frame, with the joint laws converging weakly in that same frame
(`compact_moments`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.DecoratedKernel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  [MetricSpace Ω] [MetricSpace C] [CompactSpace Ω] [CompactSpace C]
  [BorelSpace Ω] [BorelSpace C] [Nonempty C]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- A genuine decorated limit realizes every continuous normalized moment in
one common frame. The joint laws converge weakly in that same frame. -/
theorem compact_moments (W : ℕ → DecoratedKernel Ω C μ) :
    ∃ (V : DecoratedKernel Ω C μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ),
        Tendsto (fun n => ((W (φ n)).pullback (e n) (he n)).jointLaw)
          atTop (𝓝 V.jointLaw) ∧
        ∀ (f : C(C, ℝ)) (hbound : ∀ c, f c ∈ Set.Icc 0 1) ε, 0 < ε →
          ∃ N, ∀ n ≥ N,
            Graphon.cutNormDiff
              (Graphon.pullback ((W (φ n)).momentGraphon f
                f.continuous.stronglyMeasurable hbound) (e n) (he n))
              (V.momentGraphon f f.continuous.stronglyMeasurable hbound) < ε := by
  obtain ⟨tests, hdense⟩ := exists_dense_tests C
  let moments : ℕ → ℕ → Graphon Ω μ := fun n j =>
    (W n).momentGraphon (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2
  obtain ⟨L, φ, hφ, e, he, hcut⟩ := Erdos1017.GraphonFamily.compact_countable moments
  let A : ℕ → DecoratedKernel Ω C μ := fun n => (W (φ n)).pullback (e n) (he n)
  obtain ⟨V, ψ, hψ, hweak⟩ := exists_jointLaw_limit A
  have htests : ∀ j ε, 0 < ε → ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff
        ((A (ψ n)).momentGraphon (tests j).1
          (tests j).1.continuous.stronglyMeasurable (tests j).2)
        (V.momentGraphon (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2) < ε := by
    intro j
    apply momentGraphon_converges_of_jointLaw_tendsto (fun n => A (ψ n)) V
      (tests j).1 (tests j).2 (L j) hweak
    intro ε hε
    obtain ⟨N, hN⟩ := hcut j ε hε
    refine ⟨N, fun n hn => ?_⟩
    change Graphon.cutNormDiff
      (((W (φ (ψ n))).pullback (e (ψ n)) (he (ψ n))).momentGraphon
        (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2) (L j) < ε
    rw [momentGraphon_pullback]
    exact hN (ψ n) (hn.trans (hψ.id_le n))
  refine ⟨V, φ ∘ ψ, hφ.comp hψ, e ∘ ψ, (fun n => he (ψ n)), hweak, ?_⟩
  intro f hbound ε hε
  have h := momentGraphon_converges_of_dense_tests tests hdense
    (fun n => A (ψ n)) V htests ⟨f, hbound⟩ ε hε
  simpa only [A, Function.comp_apply, momentGraphon_pullback] using h

end Erdos1017.DecoratedKernel

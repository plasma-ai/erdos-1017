module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyMeasurable
public import Erdos1017.Models.Decorated.DecoratedAbsoluteContinuity

/-!
# Reweighted independent atom copies

One product-almost-everywhere source event licenses every absolutely continuous
reweighting of the marked copy, at every fresh-cell mass and scalar order, and
the bounded scalar comparison applies on that same event to all reweighted
copies.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One original product-AE source event licenses every absolutely
continuous reweighting, every fresh-cell mass and every scalar order. -/
theorem ae_all_marked_feasibleOrder_ac
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = true → 0 ≤ Y p.1 p.2 →
      ∀ (ν : Measure Ω) [IsProbabilityMeasure ν], ν ≪ μ → ∀ t : unitInterval, ∀ n,
        FiniteArity.FeasibleOrder (CappedModel.universalMeasure ν t)
          (markedAdjacency A p.1 p.2) (markedCharge A Y I p.1 p.2) n := by
  filter_upwards [ae_all_copy_root_tests A hsym Y I hYsym hI hfull] with p hp hxy hq
  intro ν _ hν t n
  have hsub := FiniteArity.ae_all_subtuples μ n n
    (fun _ v => FiniteArity.TupleClique A v →
      (∀ i, A p.1 (v i) = true ∧ A p.2 (v i) = true) →
      FiniteArity.tupleCharge (charge Y I p.1 p.2)
        (Fin.cons none (fun i => some (v i))) ≤ 1)
    (fun k _ => (hp k).mono (fun v hv => hv hxy hq))
  have hac := DecoratedKernel.pi_absolutelyContinuous hν n
  have hmp := measurePreserving_pi (fun _ : Fin n => CappedModel.universalMeasure ν t)
    (fun _ => ν) (fun _ => CappedModel.universal_fst_measurePreserving (μ := ν) t)
  filter_upwards [hmp.quasiMeasurePreserving.ae (hac.ae_le (hfull n)),
    hmp.quasiMeasurePreserving.ae (hac.ae_le hsub)] with v hv hs
  apply marked_tuple_test A Y I p.1 p.2 v hv
  intro k e
  have hk : k ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  exact hs k hk e

/-- Bounded scalar comparison applies on the same original source event
to all genuinely reweighted copies. No new source-pair selection is made. -/
theorem ae_copy_objective_le_densityLimit_ac
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hYsym : ∀ x y, Y x y = Y y x)
    (I : Set Ω) (hI : MeasurableSet I) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hindependent : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = true → 0 ≤ Y p.1 p.2 →
      ∀ (ν : Measure Ω) [IsProbabilityMeasure ν], ν ≪ μ → ∀ t : unitInterval,
        FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure ν t)
            (markedCharge A Y I p.1 p.2) ≤
          FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
            (CappedModel.universalMeasure ν t) (markedAdjacency A p.1 p.2)) := by
  filter_upwards [ae_all_marked_feasibleOrder_ac A hsym Y I
    (Eventually.of_forall (fun p => hYsym p.1 p.2)) hindependent hfull] with p hp hxy hq
  intro ν _ hν t
  exact FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    _ (markedAdjacency_symm A hsym p.1 p.2) (measurable_markedAdjacency A hA p.1 p.2)
    _ (measurable_markedCharge A hA Y hY I hI p.1 p.2) (3 * B)
    (fun z => markedCharge_bound A Y I B hB hbound p.1 p.2 z.1 z.2)
    (Eventually.of_forall (fun z => markedCharge_symm A hsym Y hYsym I p.1 p.2 z.1 z.2))
    (Eventually.of_forall (fun z => markedCharge_zero_of_nonedge A Y I p.1 p.2 z.1 z.2))
    (hp hxy hq ν hν t)

end Erdos1017.IndependentAtomCopy

module

public import Erdos1017.Exclusions.Common.Physical.PhysicalResidualCountTightness
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockMoments

/-!
# Residual tightness of the four-region charge

A feasible active four-region charge is tight on the unchanged no-`A` count law,
with pair balance licensing the singular parents and the block table identifying
the counts.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A feasible active four-region charge is tight on the unchanged
original no-A count law. Actual pair balance licenses the singular
parents; the literal table identifies their residual count tests. -/
theorem ae_residual_countTest (N : ℕ) (η : PhysicalPrimal.Laws Ω)
    [∀ n, IsFiniteMeasure (η n)]
    (G : Ω → Ω → Bool) (hG : Measurable (Function.uncurry G))
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hgraph : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = blockAdjacency (label p.1) (label p.2))
    (x : Coefficients) (hx : x ∈ feasible)
    (hη : PhysicalPrimal.Feasible (fun a b => G a b = true)
      (PhysicalPrimal.graphDemand μ {p | G p.1 p.2 = true}) η)
    (hroot : ∀ n, ∀ᵐ v ∂η n, ∃! i, label (v i) = 1)
    (hcost : PhysicalPrimal.cost η = objective
      (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) x) :
    ∀ᵐ z ∂PhysicalPrimal.countMeasure N
      (PhysicalPrimal.withoutRegion η (label ⁻¹' {0}))
      (label ⁻¹' {2}) (label ⁻¹' {3}), countTest z.1 z.2 x = 1 := by
  let Y := fun a b => blockCharge x (label a) (label b)
  have hY : Measurable (Function.uncurry Y) :=
    (measurable_of_countable (Function.uncurry (blockCharge x))).comp
      ((hlabel.comp measurable_fst).prodMk (hlabel.comp measurable_snd))
  let B := ∑ i : Fin 4, ∑ j : Fin 4, ‖blockCharge x i j‖
  have hbound (a b : Ω) : ‖Y a b‖ ≤ B :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (blockCharge x (label a) j))
      (Finset.mem_univ (label b))).trans
    (Finset.single_le_sum (fun i _ => Finset.sum_nonneg
      (fun j _ => norm_nonneg (blockCharge x i j))) (Finset.mem_univ (label a)))
  apply PhysicalPrimal.ae_residual_tight_of_label_tests N η G hG label blockAdjacency
    hgraph Y hY B hbound
    (fun a b hab => (block_charge_properties x).2.2 (label a) (label b) hab)
    (fun n v hv => block_tupleCharge_le_one x hx (fun i => label (v i)) hv)
    hη (hcost.trans (block_physicalObjective label hlabel x).symm)
    (label ⁻¹' {0}) (label ⁻¹' {2}) (label ⁻¹' {3})
    (hlabel (measurableSet_singleton 0)) (hlabel (measurableSet_singleton 2))
    (hlabel (measurableSet_singleton 3)) (label ⁻¹' {1}) hroot
    (fun z => countTest z.1 z.2 x)
  intro n v ha hb _
  have h0 : PhysicalPrimal.labelCount (fun i => label (v i)) 0 = 0 := by
    simpa only [PhysicalPrimal.labelCount, mem_preimage, mem_singleton_iff] using
      (show (∑ i : Fin n, if label (v i) = 0 then 1 else 0) = 0 by
        apply Finset.sum_eq_zero
        intro i _
        exact ite_eq_right (ha i))
  have h1 : PhysicalPrimal.labelCount (fun i => label (v i)) 1 = 1 := by
    simpa only [PhysicalPrimal.labelCount, PhysicalPrimal.tupleCount, mem_preimage,
      mem_singleton_iff] using PhysicalPrimal.tupleCount_eq_one_of_unique (label ⁻¹' {1}) v hb
  simpa only [Y, FiniteArity.tupleCharge, PhysicalPrimal.labelCount,
    PhysicalPrimal.tupleCount, mem_preimage, mem_singleton_iff] using
    block_tupleCharge_eq_countTest x (fun i => label (v i)) h0 h1

end Erdos1017.TwoAtomCountGate

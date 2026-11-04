module

public import Erdos1017.Exclusions.Common.Physical.PhysicalResidualCountMeasure

/-!
# Tightness on the residual count law

Parent events transport through the finite sum of count pushforwards, an event
conditional on avoiding `A` holds on the residual count measure, and a feasible
represented dual with the original objective is tight on the residual count law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Transport an actual parent event through the finite sum of literal
count pushforwards. No new parent sampling law is introduced. -/
theorem ae_countMeasure (N : ℕ) (η : Laws Ω) (R E : Set Ω)
    (hR : MeasurableSet R) (hE : MeasurableSet E) (P : ℕ × ℕ → Prop)
    (hP : ∀ n, ∀ᵐ v ∂η n, P (tupleCount R v, tupleCount E v)) :
    ∀ᵐ z ∂countMeasure N η R E, P z := by
  rw [countMeasure, ae_finsetSum_measure_iff]
  intro n _
  apply (ae_map_iff ((measurable_tupleCount R hR).prodMk
    (measurable_tupleCount E hE)).aemeasurable ((Set.to_countable _).measurableSet)).mpr
  exact hP n

/-- An original-parent event conditional on avoiding A holds on the
literal residual count measure, including for singular original laws. -/
theorem ae_residual_countMeasure (N : ℕ) (η : Laws Ω) (A R E : Set Ω)
    (hA : MeasurableSet A) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (P : ℕ × ℕ → Prop)
    (hP : ∀ n, ∀ᵐ v ∂η n, (∀ i, v i ∉ A) → P (tupleCount R v, tupleCount E v)) :
    ∀ᵐ z ∂countMeasure N (withoutRegion η A) R E, P z := by
  apply ae_countMeasure N (withoutRegion η A) R E hR hE P
  intro n
  exact (ae_restrict_iff' (measurableSet_avoidsRegion A hA)).mpr (hP n)

variable {ι : Type*} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual feasible represented dual with the original objective is
tight on the original residual count law. The count representation is a
literal finite tuple identity, not a tightness or moment assumption. -/
theorem ae_residual_tight_of_label_tests (N : ℕ) (η : Laws Ω)
    [∀ n, IsFiniteMeasure (η n)]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (q : Ω → ι) (H : ι → ι → Bool)
    (hgraph : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = H (q p.1) (q p.2))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hzero : ∀ x y, H (q x) (q y) = false → Y x y = 0)
    (htest : ∀ n (v : Fin n → Ω),
      FiniteArity.TupleClique (fun x y => H (q x) (q y)) v → FiniteArity.tupleCharge Y v ≤ 1)
    (hη : Feasible (fun x y => A x y = true) (graphDemand μ {p | A p.1 p.2 = true}) η)
    (hcost : cost η = (∫ p, Y p.1 p.2 ∂μ.prod μ) / 2)
    (T R E : Set Ω) (hT : MeasurableSet T) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (I : Set Ω) (hroot : ∀ n, ∀ᵐ v ∂η n, ∃! i, v i ∈ I)
    (F : ℕ × ℕ → ℝ)
    (hcount : ∀ n (v : Fin n → Ω), (∀ i, v i ∉ T) → (∃! i, v i ∈ I) →
      FiniteArity.TupleClique (fun x y => H (q x) (q y)) v →
      FiniteArity.tupleCharge Y v = F (tupleCount R v, tupleCount E v)) :
    ∀ᵐ z ∂countMeasure N (withoutRegion η T) R E, F z = 1 := by
  have hlicense : ∀ᵐ p ∂graphDemand μ {p | A p.1 p.2 = true},
      H (q p.1) (q p.2) = true := by
    filter_upwards [ae_restrict_of_ae hgraph,
      ae_restrict_mem (hA (measurableSet_singleton true))] with p hp he
    exact hp.symm.trans he
  apply ae_residual_countMeasure N η T R E hT hR hE (fun z => F z = 1)
  intro n
  filter_upwards [ae_tight_of_label_tests η A hA q H hgraph Y hY B hbound hzero htest
    hη hcost n, ae_all_pairs_of_balance η (graphDemand μ {p | A p.1 p.2 = true})
      hη.2.2.2 (fun p => H (q p.1) (q p.2) = true) hlicense n, hroot n] with v hv hc hr ht
  rw [charge_uncurry_eq_tupleCharge, hcount n v ht hr hc] at hv
  exact hv

end Erdos1017.PhysicalPrimal

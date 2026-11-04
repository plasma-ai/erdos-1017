module

public import Erdos1017.Exclusions.Common.CountableConditionalAveraging
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalBalancedSupport

/-!
# Conditional averaging of tight physical duals

A pointwise feasible label dual attaining the optimum value is tight on the
pair-balanced parents, even for jointly singular laws, and conditional averaging
preserves tightness on the unchanged physical primal.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.PhysicalPrimal

/-- The ordered physical charge and the scalar finite-arity charge use
the same factor of one half, without a symmetry assumption. -/
theorem charge_uncurry_eq_tupleCharge {Ω : Type*} {n : ℕ}
    (Y : Ω → Ω → ℝ) (v : Fin n → Ω) :
    charge (Function.uncurry Y) v = FiniteArity.tupleCharge Y v := by
  have hsum : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then Y (v i) (v j) else 0) =
      ∑ ij : PairIndex n, Y (v ij.val.1) (v ij.val.2) := by
    rw [← Fintype.sum_prod_type (fun ij : Fin n × Fin n =>
      if ij.1 ≠ ij.2 then Y (v ij.1) (v ij.2) else 0), ← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)) (by simp)
      (fun ij => Y (v ij.1) (v ij.2))
  simp only [ne_eq, ite_not] at hsum
  unfold charge FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  exact congrArg (fun z : ℝ => z / 2) hsum.symm

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A pointwise feasible label dual with the actual optimum value is
tight on the original pair-balanced parents, even when those laws are
jointly singular. Only pair-null events are transported to parents. -/
theorem ae_tight_of_label_tests (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (q : Ω → ι) (H : ι → ι → Bool)
    (hgraph : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = H (q p.1) (q p.2))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hzero : ∀ x y, H (q x) (q y) = false → Y x y = 0)
    (htest : ∀ n (v : Fin n → Ω),
      FiniteArity.TupleClique (fun x y => H (q x) (q y)) v → FiniteArity.tupleCharge Y v ≤ 1)
    (hη : Feasible (fun x y => A x y = true) (graphDemand μ {p | A p.1 p.2 = true}) η)
    (hcost : cost η = (∫ p, Y p.1 p.2 ∂μ.prod μ) / 2) (n : ℕ) :
    ∀ᵐ v ∂η n, charge (Function.uncurry Y) v = 1 := by
  let E := {p : Ω × Ω | A p.1 p.2 = true}
  have hE : MeasurableSet E := hA (measurableSet_singleton true)
  let : IsFiniteMeasure (graphDemand μ E) := by
    unfold graphDemand
    infer_instance
  have hi : Integrable (Function.uncurry Y) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable B (Eventually.of_forall (fun p => hbound p.1 p.2))
  have hvalue : (∫ p, Function.uncurry Y p ∂graphDemand μ E) =
      ∫ p, Y p.1 p.2 ∂μ.prod μ := by
    rw [graphDemand, ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [hgraph] with p hp
    by_cases he : A p.1 p.2 = true
    · simp [E, he, Function.uncurry]
    · have hz := hzero p.1 p.2 (hp ▸ Bool.eq_false_iff.mpr he)
      simp [E, he, hz]
  have hlicense : ∀ᵐ p ∂graphDemand μ E, H (q p.1) (q p.2) = true := by
    filter_upwards [ae_restrict_of_ae hgraph, ae_restrict_mem hE] with p hp he
    exact hp.symm.trans he
  apply ae_tight_of_balance_and_cost_eq η (graphDemand μ E) (Function.uncurry Y)
    hη.1 hη.2.1 hη.2.2.2 hi.restrict _ _ n
  · intro k
    filter_upwards [ae_all_pairs_of_balance η (graphDemand μ E) hη.2.2.2
      (fun p => H (q p.1) (q p.2) = true) hlicense k] with v hv
    rw [charge_uncurry_eq_tupleCharge]
    exact htest k v hv
  · rw [hvalue]
    exact hcost

variable [MeasurableSpace ι] [Countable ι] [DiscreteMeasurableSpace ι]

/-- Literal conditional averaging retains tightness on the unchanged
original physical primal. Its pointwise tests and exact cost identity
are derived from the original scalar dual and independent fiber sampling. -/
theorem ae_tight_conditional_average (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (q : Ω → ι) (hq : Measurable q) (hpos : ∀ i, 0 < μ (q ⁻¹' {i}))
    (H : ι → ι → Bool)
    (hgraph : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = H (q p.1) (q p.2))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (hbox : ∀ x y, Y x y ∈ Icc (-3 : ℝ) 1)
    (hzero : ∀ x y, A x y = false → Y x y = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (hη : Feasible (fun x y => A x y = true) (graphDemand μ {p | A p.1 p.2 = true}) η)
    (hcost : cost η = (∫ p, Y p.1 p.2 ∂μ.prod μ) / 2) (n : ℕ) :
    ∀ᵐ v ∂η n, charge (Function.uncurry (ConditionalAveraging.charge (μ := μ) q Y)) v = 1 := by
  have hbound (x y : Ω) : ‖Y x y‖ ≤ 3 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(hbox x y).1, (hbox x y).2.trans (by norm_num)⟩
  have hi : Integrable (Function.uncurry Y) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable 3 (Eventually.of_forall (fun p => hbound p.1 p.2))
  apply ae_tight_of_label_tests η A hA q H hgraph
    (ConditionalAveraging.charge (μ := μ) q Y) (ConditionalAveraging.measurable_charge q hq Y) 3
  · intro x y
    have hb := ConditionalAveraging.charge_mem_Icc q hpos Y hY hbox x y
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hb.1, hb.2.trans (by norm_num)⟩
  · exact ConditionalAveraging.charge_zero_of_nonedge q hq H A Y hgraph hzero
  · intro k v hv
    exact ConditionalAveraging.tupleCharge_le_one q hq hpos H A Y hY 3 hbound hgraph hfull v hv
  · exact hη
  · rw [ConditionalAveraging.integral_charge q hq hpos Y hi]
    exact hcost

end Erdos1017.PhysicalPrimal

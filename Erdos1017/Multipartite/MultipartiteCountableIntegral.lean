module

public import Erdos1017.Multipartite.MultipartiteCountableKernel

/-!
# Kernel integral of the countable demand

The integral over the retained prefix demand equals the finite coefficient
objective, discarding a vertex tail changes the half-integral by at most total
mass times omitted mass, and the full countable physical kernel integral is the
absolutely convergent coefficient objective.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableMeasure

open MeasureTheory
open scoped BigOperators

local instance : MeasurableSpace Label := ⊤
local instance (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤
local instance (n : ℕ) : MeasurableSpace (DustCommonRealization.Label n) := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω]

/-- The integral over the actual retained demand equals the finite coefficient
objective, with the genuine dust mass unchanged. -/
theorem integral_prefix_kernel (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (s : ℝ) (hs : 0 ≤ s) (D : MultipartiteCountableDual.Coefficients) (n : ℕ) :
    (∫ z, physicalKernel D z ∂PhysicalPrimal.graphDemand (prefixMeasure ν p s n) edgeSet) / 2 =
      MultipartiteDust.objective (fun i : Fin n => p i.val) s
        (MultipartiteCountableDual.restrict n D) := by
  have hm := (embedVertex_measurable (Ω := Ω) n).prodMap (embedVertex_measurable (Ω := Ω) n)
  change (∫ z, physicalKernel D z ∂PhysicalPrimal.graphDemand (prefixMeasure ν p s n)
    (PhysicalCellLift.edgeSet ({.inr ()} : Finset Label))) / 2 = _
  rw [← map_finite_graphDemand ν p s n,
    integral_map hm.aemeasurable (physicalKernel_measurable D).aestronglyMeasurable]
  have heq : (fun z => physicalKernel (Ω := Ω) D
      (Prod.map (embedVertex n) (embedVertex n) z)) =
      DustCommonRealization.physicalKernel (MultipartiteCountableDual.restrict n D) := by
    funext z
    exact kernel_embed D n z.1.1 z.2.1
  rw [heq, PhysicalPrimal.graphDemand]
  have ha (i : DustCommonRealization.Label n) :
      0 ≤ DustCommonRealization.masses (fun i : Fin n => p i.val) s i := by
    cases i with
    | inl i => cases i <;>
        simp [DustCommonRealization.masses, Multipartite.anchorMasses, Option.elim', hp]
    | inr i => exact hs
  rw [← PhysicalCellLift.demand_eq_restrict_product (fun _ => ν) _ ha]
  exact (DustCommonRealization.integral_physicalKernel ν (fun i : Fin n => p i.val)
    (fun i => hp i.val) s hs (MultipartiteCountableDual.restrict n D)).2

omit [MeasurableEq Ω] in
/-- For bounded kernels, discarding a vertex tail changes the half-integral
by at most total mass times omitted mass. -/
theorem integral_prefix_error (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hsum : Summable p) (s : ℝ)
    {D : MultipartiteCountableDual.Coefficients} (hD : D ∈ MultipartiteCountableDual.feasible)
    (n : ℕ) :
    |(∫ z, physicalKernel D z ∂PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet) / 2 -
      (∫ z, physicalKernel D z ∂PhysicalPrimal.graphDemand (prefixMeasure ν p s n) edgeSet) / 2| ≤
      ((prefixMeasure ν p s n).real Set.univ + (tailMeasure ν p n).real Set.univ) *
        (tailMeasure ν p n).real Set.univ := by
  have := prefixMeasure_finite ν p hsum s n
  have := tailMeasure_finite ν p hsum n
  have : IsFiniteMeasure (PhysicalPrimal.graphDemand (prefixMeasure ν p s n) edgeSet) := by
    unfold PhysicalPrimal.graphDemand
    infer_instance
  have : IsFiniteMeasure (PhysicalPrimal.tailDemand
      (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet) := by
    unfold PhysicalPrimal.tailDemand
    infer_instance
  rw [vertexMeasure_eq_prefix_add_tail ν p s n, PhysicalPrimal.graphDemand_add,
    integral_add_measure (physicalKernel_integrable hD _) (physicalKernel_integrable hD _)]
  have heq (a b : ℝ) : (a + b) / 2 - a / 2 = b / 2 := by ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb : |∫ z, physicalKernel D z ∂PhysicalPrimal.tailDemand
      (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet| ≤
      (PhysicalPrimal.tailDemand (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet).real
        Set.univ := by
    simpa only [Real.norm_eq_abs, one_mul] using
      (norm_integral_le_of_norm_le_const (μ := PhysicalPrimal.tailDemand
        (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet)
        (f := physicalKernel D) (C := 1)
        (Filter.Eventually.of_forall (fun z => norm_kernel_le_one hD z.1.1 z.2.1)))
  exact (div_le_div_of_nonneg_right hb (by norm_num)).trans
    (PhysicalPrimal.tailDemand_mass_bound (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet)

/-- The full countable physical kernel integral is the absolutely convergent
coefficient objective. Finite-prefix identities and the actual tail estimate
justify the limit without exchanging a signed integral with an unproved series. -/
theorem integral_kernel (ν : Measure Ω) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s)
    {D : MultipartiteCountableDual.Coefficients} (hD : D ∈ MultipartiteCountableDual.feasible) :
    (∫ z, physicalKernel D z ∂PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet) / 2 =
      MultipartiteCountableDual.objective p s D := by
  let I := (∫ z, physicalKernel D z ∂PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet) / 2
  let a (n : ℕ) := (∫ z, physicalKernel D z ∂PhysicalPrimal.graphDemand
    (prefixMeasure ν p s n) edgeSet) / 2
  have hmass (n : ℕ) : (prefixMeasure ν p s n).real Set.univ +
      (tailMeasure ν p n).real Set.univ = 1 + s + ∑' i, p i := by
    rw [prefixMeasure_mass ν p hp s hs, tailMeasure_mass ν p hp hsum]
    ring
  have hzero : Filter.Tendsto (fun n => I - a n) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Filter.Tendsto (fun n => (1 + s + ∑' i, p i) *
          (tailMeasure ν p n).real Set.univ) Filter.atTop (nhds 0) from by
        simpa using (tailMeasure_mass_tendsto_zero ν p hp hsum).const_mul
          (1 + s + ∑' i, p i))
    simpa only [Real.norm_eq_abs, hmass] using integral_prefix_error ν p hsum s hD n
  have hI : Filter.Tendsto a Filter.atTop (nhds I) := by
    simpa only [sub_sub_cancel, sub_zero] using
      (tendsto_const_nhds (x := I)).sub hzero
  have hobj : Filter.Tendsto a Filter.atTop
      (nhds (MultipartiteCountableDual.objective p s D)) := by
    dsimp only [a]
    simp_rw [integral_prefix_kernel ν p hp s hs]
    exact MultipartiteCountableDual.objective_restrict_tendsto p hp hsum s hD.1
  exact tendsto_nhds_unique hI hobj

end Erdos1017.MultipartiteCountableMeasure

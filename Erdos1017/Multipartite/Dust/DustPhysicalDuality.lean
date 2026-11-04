module

public import Erdos1017.Multipartite.Dust.DustPhysicalKernel

/-!
# Dual bounds for physical partitions

The homogeneous objective is half the integral of `physicalKernel` against the
fixed physical edge demand, so every bounded homogeneous dual bounds every
unrestricted physical law family, even with singular joint measures, and the
finite-head coefficient maximum is a lower bound for the full physical primal.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1017.DustCommonRealization

local instance (m : ℕ) : MeasurableSpace (Label m) := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- Homogeneous coefficients evaluated on actual physical vertex pairs. -/
def physicalKernel (C : MultipartiteDust.Coefficients m) (z : (Label m × Ω) × (Label m × Ω)) : ℝ :=
  kernel C z.1.1 z.2.1

theorem physicalKernel_measurable (C : MultipartiteDust.Coefficients m) :
    Measurable (physicalKernel (Ω := Ω) C) := by
  have h : Measurable (fun z : Label m × Label m => kernel C z.1 z.2) :=
    measurable_of_countable _
  exact h.comp (measurable_fst.fst.prodMk measurable_snd.fst)

/-- The exact homogeneous objective is half its integral against the actual
fixed physical edge demand. No primal feasibility is assumed here. -/
theorem integral_physicalKernel (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s)
    (C : MultipartiteDust.Coefficients m) :
    Integrable (physicalKernel C) (PhysicalCellLift.demand (fun _ => ν) (masses p s) {.inr ()}) ∧
      (∫ z, physicalKernel C z ∂PhysicalCellLift.demand (fun _ => ν) (masses p s) {.inr ()}) / 2 =
        MultipartiteDust.objective p s C := by
  classical
  let Y := physicalKernel (Ω := Ω) C
  let a := masses p s
  have ha (i : Label m) : 0 ≤ a i := by
    cases i with
    | inl i => cases i <;> simp [a, masses, Multipartite.anchorMasses, Option.elim', hp]
    | inr i => exact hs
  have hm (i j : Label m) : Measurable (PhysicalCellLift.tagPair (Ω := Ω) i j) :=
    (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  have hi (i j : Label m) : Integrable Y ((ν.prod ν).map (PhysicalCellLift.tagPair i j)) := by
    apply (integrable_map_measure (physicalKernel_measurable C).aestronglyMeasurable
      (hm i j).aemeasurable).mpr
    exact integrable_const (kernel C i j)
  have hv (i j : Label m) :
      (∫ z, Y z ∂(ν.prod ν).map (PhysicalCellLift.tagPair i j)) = kernel C i j := by
    rw [integral_map (hm i j).aemeasurable (hi i j).aestronglyMeasurable]
    exact integral_const (kernel C i j) |>.trans (by simp)
  let block (i j : Label m) : Measure ((Label m × Ω) × (Label m × Ω)) :=
    if i ≠ j ∨ i ∈ ({.inr ()} : Finset (Label m)) then
      ENNReal.ofReal (a i * a j) • ((ν.prod ν).map (PhysicalCellLift.tagPair i j)) else 0
  have hb (i j : Label m) : Integrable Y (block i j) := by
    dsimp only [block]
    split_ifs
    · exact (hi i j).smul_measure ENNReal.ofReal_ne_top
    · exact integrable_zero_measure
  have hsum : Integrable Y (∑ i, ∑ j, block i j) := by
    apply integrable_finsetSum_measure.mpr
    intro i _
    exact integrable_finsetSum_measure.mpr (fun j _ => hb i j)
  have hblock (i j : Label m) : (∫ z, Y z ∂block i j) = kernel C i j * a i * a j := by
    dsimp only [block]
    split_ifs with h
    · rw [integral_smul_measure, hv, ENNReal.toReal_ofReal (mul_nonneg (ha i) (ha j))]
      simp only [smul_eq_mul]
      ring
    · have hij : i = j := by simpa using not_or.mp h |>.1
      subst j
      have hn := (not_or.mp h).2
      cases i with
      | inl i => cases i <;> simp [kernel, Multipartite.anchorDual, DustCellRestriction.headDual]
      | inr i => exact False.elim (hn (by cases i; simp))
  refine ⟨hsum, ?_⟩
  change (∫ z, Y z ∂∑ i, ∑ j, block i j) / 2 = _
  rw [integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hb i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hb _ j), hblock]
  have h := kernel_weighted_sum C p s 1
  simpa [a, masses, Multipartite.anchorMasses, MultipartiteDust.objective] using h

/-- Every bounded homogeneous dual bounds every unrestricted physical law
family, even when its joint measures are singular. -/
theorem objective_le_physical_cost (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s)
    (C : MultipartiteDust.Coefficients m) (hC : C ∈ MultipartiteDust.feasible m)
    (μ : PhysicalPrimal.Laws (Label m × Ω)) [∀ n, IsFiniteMeasure (μ n)]
    (hμ : PhysicalPrimal.Feasible
      (PhysicalCellLift.Adj ({.inr ()} : Finset (Label m)))
      (PhysicalCellLift.demand (fun _ => ν) (masses p s) {.inr ()}) μ) :
    MultipartiteDust.objective p s C ≤ PhysicalPrimal.cost μ := by
  classical
  let demand := PhysicalCellLift.demand (fun _ : Label m => ν) (masses p s) {.inr ()}
  have hb (i j : Label m) : IsFiniteMeasure
      (if i ≠ j ∨ i ∈ ({.inr ()} : Finset (Label m)) then
        ENNReal.ofReal (masses p s i * masses p s j) •
          (ν.prod ν).map (PhysicalCellLift.tagPair i j) else 0) := by
    split_ifs
    · exact Measure.smul_finite _ ENNReal.ofReal_ne_top
    · infer_instance
  have : IsFiniteMeasure demand := by
    dsimp only [demand, PhysicalCellLift.demand]
    infer_instance
  have h := integral_physicalKernel ν p hp s hs C
  rw [← h.2]
  apply PhysicalPrimal.weak_duality_of_clique_tests μ
    (PhysicalCellLift.Adj ({.inr ()} : Finset (Label m))) (physicalKernel C) demand hμ h.1
  intro n v hv
  exact physical_clique_test C hC v hv

/-- The finite-head coefficient maximum is a lower bound for the full physical
primal, not merely for independently sampled partitions. -/
theorem value_le_physical_cost (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s)
    (μ : PhysicalPrimal.Laws (Label m × Ω)) [∀ n, IsFiniteMeasure (μ n)]
    (hμ : PhysicalPrimal.Feasible
      (PhysicalCellLift.Adj ({.inr ()} : Finset (Label m)))
      (PhysicalCellLift.demand (fun _ => ν) (masses p s) {.inr ()}) μ) :
    MultipartiteDust.value p s ≤ PhysicalPrimal.cost μ := by
  obtain ⟨C, hC, heq⟩ := MultipartiteDust.exists_value_eq p s
  rw [heq]
  exact objective_le_physical_cost ν p hp s hs C hC μ hμ

/-- The same lower bound with demand stated directly as the vertex product
restricted to the fixed graph, on the atomless realization. -/
theorem value_le_restricted_physical_cost [MeasurableEq Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s)
    (μ : PhysicalPrimal.Laws (Label m × Ω)) [∀ n, IsFiniteMeasure (μ n)]
    (hμ : PhysicalPrimal.Feasible
      (PhysicalCellLift.Adj ({.inr ()} : Finset (Label m)))
      (((PhysicalCellLift.vertexMeasure (fun _ => ν) (masses p s)).prod
        (PhysicalCellLift.vertexMeasure (fun _ => ν) (masses p s))).restrict
        (PhysicalCellLift.edgeSet ({.inr ()} : Finset (Label m)))) μ) :
    MultipartiteDust.value p s ≤ PhysicalPrimal.cost μ := by
  have ha (i : Label m) : 0 ≤ masses p s i := by
    cases i with
    | inl i => cases i <;> simp [masses, Multipartite.anchorMasses, Option.elim', hp]
    | inr i => exact hs
  apply value_le_physical_cost ν p hp s hs μ
  rwa [PhysicalCellLift.demand_eq_restrict_product (fun _ => ν) (masses p s) ha]

end Erdos1017.DustCommonRealization

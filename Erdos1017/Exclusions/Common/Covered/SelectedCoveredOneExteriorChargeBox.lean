module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorBlockMoments
public import Erdos1017.Exclusions.Common.TwoAtom.SelectedTwoAtomChargeBox

/-!
# Charge box of the active one-exterior model

Every vector of the child's feasible set obeys the full optimum, every
objective-preserving one-exterior-part dual lies inside the lower charge
boundary on its positive blocks, and the active one-exterior-part model is
constructed with its own stationary record, tuple tests, boxing and strict
support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CoveredOneExterior

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every vector in the child's original feasible set obeys the actual
optimum. Finite-range boundedness and full scalar sampling pay the global
comparison before any compact charge box or active record is constructed. -/
theorem block_objective_le_full_optimum (W : Model Ω μ)
    (hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W))
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hgraph : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if blockAdjacency (label p.1) (label p.2) = true then 1 else 0)
    (x : Coefficients) (hx : x ∈ feasible) :
    objective (μ.real (label ⁻¹' {1})) (μ.real (label ⁻¹' {2}))
      (μ.real (label ⁻¹' {3})) x ≤
        CappedModel.objective W - μ.real (label ⁻¹' {0}) * μ.real (label ⁻¹' {1}) := by
  have hpair : Measurable (fun p : Ω × Ω => (label p.1, label p.2)) :=
    (hlabel.comp measurable_fst).prodMk (hlabel.comp measurable_snd)
  have hG : Measurable (fun p : Ω × Ω => blockAdjacency (label p.1) (label p.2)) :=
    (measurable_of_countable (Function.uncurry blockAdjacency)).comp hpair
  have hy : Measurable (fun p : Ω × Ω => blockCharge x (label p.1) (label p.2)) :=
    (measurable_of_countable (Function.uncurry (blockCharge x))).comp hpair
  obtain ⟨hGsym, hysym, hyzero⟩ := block_charge_properties x
  obtain ⟨B, hB⟩ := (Set.finite_range
    (fun ij : Fin 4 × Fin 4 => ‖blockCharge x ij.1 ij.2‖)).bddAbove
  have hbound :=
    FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
      (fun a b => blockAdjacency (label a) (label b)) (fun a b => hGsym _ _) hG
      (fun a b => blockCharge x (label a) (label b)) hy B
      (fun p => hB ⟨(label p.1, label p.2), rfl⟩)
      (Eventually.of_forall (fun p => hysym (label p.1) (label p.2)))
      (Eventually.of_forall (fun p hp => hyzero (label p.1) (label p.2) hp))
      (block_full_scalar_tests x hx μ label)
  have hdW : density W = FiniteCappedSamplingCost.physicalDensity μ
      (fun a b => blockAdjacency (label a) (label b)) := by
    unfold density FiniteCappedSamplingCost.physicalDensity
    congr 1
    exact integral_congr_ae hgraph
  rw [← hdW, ← hopt] at hbound
  have hc := block_physicalObjective (μ := μ) label hlabel x
  dsimp only at hc
  rw [hc] at hbound
  linarith only [hbound]

/-- Every actual objective-preserving finite one-exterior-part dual is strictly
inside the lower charge boundary on its positive present blocks. The entry
model and all four positive fibers remain literal premises. -/
theorem active_block_charges_mem_Ioc (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < CappedModel.objective W)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y₀ : Fin 4 → Fin 4 → ℝ)
    (hentry : ∀ᵐ p ∂μ.prod μ,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = y₀ (label p.1) (label p.2))
    (x : Coefficients) (hx : x ∈ feasible)
    (hcost : objective (μ.real (label ⁻¹' {1})) (μ.real (label ⁻¹' {2}))
      (μ.real (label ⁻¹' {3})) x =
        CappedModel.objective W - μ.real (label ⁻¹' {0}) * μ.real (label ⁻¹' {1})) :
    ∀ i j, blockAdjacency i j = true → blockCharge x i j ∈ Ioc (-3 : ℝ) 1 := by
  obtain ⟨hGsym, hysym, hyzero⟩ := block_charge_properties x
  apply finite_block_charges_mem_Ioc_of_full_scalar_optimum W hW hopt hphysical hd hgap
    label hlabel hpositive blockAdjacency hGsym y₀ (blockCharge x) hentry hysym hyzero
    (block_full_scalar_tests x hx μ label)
  have hc := block_physicalObjective (μ := μ) label hlabel x
  dsimp only at hc
  exact hc.trans (by linarith only [hcost])

/-- Construct the actual active one-exterior-part model and its own stationary
record. All tuple tests, boxing and strict support are derived internally;
the original countable-to-one-exterior-part reduction is not asserted here. -/
theorem exists_active_block_fullStationaryClass (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < CappedModel.objective W)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y₀ : Fin 4 → Fin 4 → ℝ)
    (hentry : ∀ᵐ p ∂μ.prod μ,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = y₀ (label p.1) (label p.2))
    (x : Coefficients) (hx : x ∈ feasible)
    (hcost : objective (μ.real (label ⁻¹' {1})) (μ.real (label ⁻¹' {2}))
      (μ.real (label ⁻¹' {3})) x =
        CappedModel.objective W - μ.real (label ⁻¹' {0}) * μ.real (label ⁻¹' {1})) :
    ∃ (V : Model Ω μ) (m : ℝ),
      FullStationaryClass (density W) (CappedModel.objective W) V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) ∧
      (∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z) ∧
      FullStrictGapStructure V m (2 * (CappedModel.objective W - m * density W)) := by
  obtain ⟨hGsym, hysym, hyzero⟩ := block_charge_properties x
  apply exists_finite_block_fullStationaryClass_of_full_scalar_optimum W hW hopt hphysical
    hd hgap label hlabel hpositive blockAdjacency hGsym y₀ (blockCharge x) hentry hysym hyzero
    (block_full_scalar_tests x hx μ label)
  have hc := block_physicalObjective (μ := μ) label hlabel x
  dsimp only at hc
  exact hc.trans (by linarith only [hcost])

end Erdos1017.CoveredOneExterior

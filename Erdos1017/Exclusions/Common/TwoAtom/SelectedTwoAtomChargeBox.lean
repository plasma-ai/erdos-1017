module

public import Erdos1017.Exclusions.Common.FiniteBlockDualBox
public import Erdos1017.Exclusions.Common.FullScalarSamplingComparison
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockMoments

/-!
# Charge box and stationary record of the active block

A finite same-graph active dual receives its own model and stationary record,
every signed all-count feasible vector obeys the original optimum, and an
objective-preserving four-region dual lies strictly inside the lower charge
boundary on its positive present blocks.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

namespace CappedModel

/-- An arbitrary finite same-graph active dual receives its own actual
model and stationary record. The charge need not belong to a sliced family;
all-order feasibility and the original objective equality are the inputs. -/
theorem exists_finite_block_fullStationaryClass_of_full_scalar_optimum
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < objective W)
    (label : Ω → ι) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i}))
    (G : ι → ι → Bool) (hGsym : ∀ i j, G i j = G j i) (y₀ y₁ : ι → ι → ℝ)
    (hentry : ∀ᵐ p ∂μ.prod μ,
      W.moment CappedColor.adjacency p =
        (if G (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = y₀ (label p.1) (label p.2))
    (h₁sym : ∀ i j, y₁ i j = y₁ j i)
    (h₁zero : ∀ i j, G i j = false → y₁ i j = 0)
    (h₁full : ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => G (label a) (label b)) (fun a b => y₁ (label a) (label b)) n)
    (h₁cost : FiniteCappedSamplingCost.physicalObjective μ
      (fun a b => y₁ (label a) (label b)) = objective W) :
    ∃ (V : Model Ω μ) (m : ℝ), FullStationaryClass (density W) (objective W) V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if G (label p.1) (label p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p = y₁ (label p.1) (label p.2)) ∧
      (∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z) ∧
      FullStrictGapStructure V m (2 * (objective W - m * density W)) := by
  have hbox := finite_block_charges_mem_Ioc_of_full_scalar_optimum W hW hopt hphysical
    hd hgap label hlabel hpositive G hGsym y₀ y₁ hentry h₁sym h₁zero h₁full h₁cost
  have hbox' : ∀ i j, y₁ i j ∈ Icc (-3 : ℝ) 1 := by
    intro i j
    cases hij : G i j
    · rw [h₁zero i j hij]
      norm_num
    · exact ⟨(hbox i j hij).1.le, (hbox i j hij).2⟩
  obtain ⟨V, hV, hmom, hdV, hcV, hdet⟩ := exists_boxed_finite_block_model
    label hlabel G hGsym y₁ h₁sym h₁zero hbox' h₁full
  have hdW : density W = FiniteCappedSamplingCost.physicalDensity μ
      (fun a b => G (label a) (label b)) := by
    unfold density FiniteCappedSamplingCost.physicalDensity
    congr 1
    exact integral_congr_ae (hentry.mono (fun _ h => h.1))
  have hdVW : density V = density W := hdV.trans hdW.symm
  have hcVW : objective V = objective W := hcV.trans h₁cost
  have hoptV : objective V = FractionalGraph.densityLimit (density V) := by
    rw [hcVW, hdVW]
    exact hopt
  have hdV' : density V ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdVW ▸ hd
  have hgapV : benchmark (density V) < objective V := by
    rw [hdVW, hcVW]
    exact hgap
  obtain ⟨m, hm⟩ := exists_same_model_fullStationaryClass V hV hoptV hdet hdV' hgapV
  have hm' : FullStationaryClass (density W) (objective W) V m := by
    rwa [hdVW, hcVW] at hm
  exact ⟨V, m, hm', hmom, hdet, hm'.strict_gap_structure hd hgap⟩

end CappedModel

namespace TwoAtomCountGate

open CappedModel

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every signed all-count feasible vector obeys the actual original
optimum. Finite-range boundedness and full scalar sampling pay the global
comparison before any compact charge box or active record is constructed. -/
theorem block_objective_le_full_optimum (W : Model Ω μ)
    (hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W))
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hgraph : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if blockAdjacency (label p.1) (label p.2) = true then 1 else 0)
    (x : Coefficients) (hx : x ∈ feasible) :
    objective (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) x ≤ CappedModel.objective W := by
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
  exact (block_physicalObjective label hlabel x).symm.trans_le hbound

/-- Every actual objective-preserving finite four-region dual is strictly
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
    (hcost : objective (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) x = CappedModel.objective W) :
    ∀ i j, blockAdjacency i j = true → blockCharge x i j ∈ Ioc (-3 : ℝ) 1 := by
  obtain ⟨hGsym, hysym, hyzero⟩ := block_charge_properties x
  apply finite_block_charges_mem_Ioc_of_full_scalar_optimum W hW hopt hphysical hd hgap
    label hlabel hpositive blockAdjacency hGsym y₀ (blockCharge x) hentry hysym hyzero
    (block_full_scalar_tests x hx μ label)
  exact (block_physicalObjective label hlabel x).trans hcost

/-- Construct the actual active four-region model and its own stationary
record. All tuple tests, boxing and strict support are derived internally;
the original countable-to-four-region reduction is not asserted here. -/
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
    (hcost : objective (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) x = CappedModel.objective W) :
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
  exact (block_physicalObjective label hlabel x).trans hcost

end TwoAtomCountGate

end Erdos1017

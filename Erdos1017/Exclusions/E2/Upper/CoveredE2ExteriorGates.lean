module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredOneExteriorChargeBox
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorOwnRows
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorPhysicalPrimal
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoExteriorChargeBox
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorRepeatObstruction
public import Erdos1017.Exclusions.Common.Covered.FullCoveredTwoExteriorCopy
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards

/-!
# Exterior gates at the `E₂` contact

An `A/B/C/E` optimum and a positive `A/B/C1/C2/E` optimum cannot lie at the `E₂`
value and derivative contact (`no_e2_one_exterior`, `no_e2_five_region`); every
optimal child dual receives its own model, stationary rows and obstruction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CoveredOneExterior

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {d c m q : ℝ}

/-- An actual A/B/C/E optimum cannot lie at the genuine E2 value/derivative contact.
Every optimal child dual receives its own actual model, stationary rows,
full-repeat obstruction and attained physical child cost law internally. -/
theorem no_e2_one_exterior (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hbenchmark : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → CappedModel.objective V - benchmark (density V) ≤
        CappedModel.objective W - benchmark (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i}))
    (y₀ : Coefficients) (hy₀ : y₀ ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y₀ (label p.1) (label p.2)) : False := by
  let a := μ.real (label ⁻¹' {0})
  let b := μ.real (label ⁻¹' {1})
  let x := μ.real (label ⁻¹' {2})
  let e := μ.real (label ⁻¹' {3})
  have hpos (i : Fin 4) : 0 < μ.real (label ⁻¹' {i}) :=
    ENNReal.toReal_pos (hpositive i).ne' (measure_ne_top _ _)
  have hb : 0 < b := hpos 1
  have hx : 0 < x := hpos 2
  have he : 0 < e := hpos 3
  have hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hmax (y : Coefficients) (hy : y ∈ feasible) : objective b x e y ≤ c - a * b := by
    have h := block_objective_le_full_optimum W hopt label hlabel
      (Eventually.of_forall (fun p => (hmom p).1)) y hy
    rwa [hW.objective_eq] at h
  have hvalue : objective b x e y₀ = c - a * b := by
    have hi := block_physicalObjective (μ := μ) label hlabel y₀
    have ho : FiniteCappedSamplingCost.physicalObjective μ
        (fun v w => blockCharge y₀ (label v) (label w)) = CappedModel.objective W := by
      unfold CappedModel.objective FiniteCappedSamplingCost.physicalObjective
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
    rw [ho, hW.objective_eq] at hi
    dsimp only at hi
    change objective b x e y₀ = c - a * b
    linarith only [hi]
  apply no_optimal_face_with_own_rows_moments hb hx he ⟨y₀, hy₀, hvalue⟩ hmax
  intro y hy
  obtain ⟨V, m', hV, hmomV, _, _⟩ := exists_active_block_fullStationaryClass W hW.full hopt
    hphysical (by rwa [hW.density_eq]) (by rwa [hW.density_eq, hW.objective_eq])
    label hlabel hpositive (blockCharge y₀) (Eventually.of_forall hmom) y hy.1
    (by simpa only [hW.objective_eq] using hy.2)
  have hV' : FullStationaryClass d c V m' := by
    rwa [hW.density_eq, hW.objective_eq] at hV
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → CappedModel.objective T - benchmark (density T) ≤
        CappedModel.objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV'.objective_eq, hV'.density_eq] using
      hglobal ν T hT
  obtain ⟨_, hell, _⟩ :=
    hV'.e2_general_contact_parameters hq hdq hbenchmark hderiv hgap hglobalV
  obtain ⟨hcoords, ht, hrow, hrepeat⟩ := own_row_parameters hV' hd hgap label hlabel
    hpositive y hy.1 hmomV
  have hmoment := exists_tightMomentData_of_fullStationaryClass label hlabel y hy.1 V hV'
    hd hgap hmomV
  exact ⟨-m', hcoords, ht, hell.1, hrow, hmoment, hrepeat⟩

end Erdos1017.CoveredOneExterior

namespace Erdos1017.CoveredTwoExterior

open CappedModel VertexClassification

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

/-- An actual positive A/B/C1/C2/E optimum cannot lie at genuine E2
value/derivative contact. Every optimal child receives its own model and multiplier,
physical copy floors and repeat obstruction before the vertex theorem applies. -/
theorem no_e2_five_region (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hbenchmark : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → CappedModel.objective V - benchmark (density V) ≤
        CappedModel.objective W - benchmark (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i}))
    (x₀ : Coefficients) (hx₀ : x₀ ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x₀ (label p.1) (label p.2)) : False := by
  let a := μ.real (label ⁻¹' {0})
  let b := μ.real (label ⁻¹' {1})
  let c1 := μ.real (label ⁻¹' {2})
  let c2 := μ.real (label ⁻¹' {3})
  let e := μ.real (label ⁻¹' {4})
  have hpos (i : Fin 5) : 0 < μ.real (label ⁻¹' {i}) :=
    ENNReal.toReal_pos (hpositive i).ne' (measure_ne_top _ _)
  have hb : 0 < b := hpos 1
  have hc1 : 0 < c1 := hpos 2
  have hc2 : 0 < c2 := hpos 3
  have he : 0 < e := hpos 4
  have hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hmax (x : Coefficients) (hx : x ∈ feasible) :
      TwoHeadVertexComparison.objective b c1 c2 e x ≤ c - a * b := by
    have h := block_objective_le_full_optimum W hopt label hlabel
      (Eventually.of_forall (fun p => (hmom p).1)) x hx
    rwa [hW.objective_eq] at h
  have hvalue : TwoHeadVertexComparison.objective b c1 c2 e x₀ = c - a * b := by
    have hi := block_physicalObjective (μ := μ) label hlabel x₀
    have ho : FiniteCappedSamplingCost.physicalObjective μ
        (fun v w => blockCharge x₀ (label v) (label w)) = CappedModel.objective W := by
      unfold CappedModel.objective FiniteCappedSamplingCost.physicalObjective
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
    rw [ho, hW.objective_eq] at hi
    change TwoHeadVertexComparison.objective b c1 c2 e x₀ = c - a * b
    linarith only [hi]
  apply TwoHeadVertexComparison.no_optimal_face_with_strict_repeat hb hc1 hc2 he
    ⟨x₀, hx₀, hvalue⟩ hmax
  · intro x hx
    obtain ⟨V, m', hV, hmomV, _, _⟩ := exists_active_block_fullStationaryClass W hW.full hopt
      hphysical (by rwa [hW.density_eq]) (by rwa [hW.density_eq, hW.objective_eq])
      label hlabel hpositive (blockCharge x₀) (Eventually.of_forall hmom) x hx.1
      (by simpa only [hW.objective_eq] using hx.2)
    have hV' : FullStationaryClass d c V m' := by
      rwa [hW.density_eq, hW.objective_eq] at hV
    have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
        FullFeasible T → CappedModel.objective T - benchmark (density T) ≤
          CappedModel.objective V - benchmark (density V) := by
      intro ν _ T hT
      simpa only [hW.objective_eq, hW.density_eq, hV'.objective_eq, hV'.density_eq] using
        hglobal ν T hT
    obtain ⟨_, hell, _⟩ :=
      hV'.e2_general_contact_parameters hq hdq hbenchmark hderiv hgap hglobalV
    have hA (z w : Ω) : adjacencyKernel V z w =
        if blockAdjacency (label z) (label w) = true then 1 else 0 := (hmomV (z, w)).1
    have hY (z w : Ω) : chargeKernel V z w = blockCharge x (label z) (label w) :=
      (hmomV (z, w)).2
    obtain ⟨_, _, _, _, hrow, _⟩ :=
      hV'.coveredTwoExterior_own_rows hd hgap x label hlabel hpositive hA hY
    obtain ⟨hgamma, hc1, hc2, hq⟩ :=
      hV'.coveredTwoExterior_copy_margins hd hgap x hx.1 label hlabel hpositive hA hY
    have hstars := stars_gt_own_multiplier hV' hd hgap label hlabel hpositive x hx.1 hmomV
    exact ⟨-m', 2 * (c - m' * d) + m' - m' * a, hell.1, hgamma,
      hstars.1.le, hstars.2.le, hc1, hc2, hq, hrow⟩
  · intro x hx y hy D hD hfull
    obtain ⟨V, m', hV, hmomV, _, _⟩ := exists_active_block_fullStationaryClass W hW.full hopt
      hphysical (by rwa [hW.density_eq]) (by rwa [hW.density_eq, hW.objective_eq])
      label hlabel hpositive (blockCharge x₀) (Eventually.of_forall hmom) x hx.1
      (by simpa only [hW.objective_eq] using hx.2)
    have hV' : FullStationaryClass d c V m' := by
      rwa [hW.density_eq, hW.objective_eq] at hV
    have hnot := no_affordable_repeat hV' hd hgap label hlabel hpositive x hx.1 hmomV
    by_contra hbound
    have hbound : D ≤ x 3 := le_of_not_gt hbound
    rcases hy with hy | hy
    · subst y
      exact hnot (Or.inl ⟨D, hD, hbound, hfull⟩)
    · subst y
      exact hnot (Or.inr ⟨D, hD, by simpa [VertexRepeat.swap] using hbound, hfull⟩)

end Erdos1017.CoveredTwoExterior

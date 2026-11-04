module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoNeighborChargeBox
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoNeighborRepeatObstruction
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoNeighborCopyBounds
public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak

/-!
# Two-neighbor gate at the smooth `W` contact

A positive `A/B/C1/C2/R` optimum cannot lie at the smooth-`W` contact; its own
`R` row proves `a < b` before the corrected optimal face is selected
(`no_smoothW_five_region`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CoveredTwoExteriorNeighbor

open CappedModel VertexClassification

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m : ℝ}

/-- An actual positive A/B/C1/C2/R optimum cannot lie at the smooth-W
contact. Its own R row proves a<b before selecting the corrected optimal
face. Every active child receives its own model, contact and copy bounds. -/
theorem no_smoothW_five_region (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hepsilon : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
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
  let u := μ.real (label ⁻¹' {4})
  have hpos (i : Fin 5) : 0 < μ.real (label ⁻¹' {i}) :=
    ENNReal.toReal_pos (hpositive i).ne' (measure_ne_top _ _)
  have hb : 0 < b := hpos 1
  have hc1 : 0 < c1 := hpos 2
  have hc2 : 0 < c2 := hpos 3
  have hu : 0 < u := hpos 4
  have hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hmax (x : Coefficients) (hx : x ∈ feasible) :
      CoveredTwoExteriorNeighbor.objective a b c1 c2 u x ≤ c - a * b := by
    have h := block_objective_le_full_optimum W hopt label hlabel
      (Eventually.of_forall (fun p => (hmom p).1)) x hx
    rwa [hW.objective_eq] at h
  have hvalue : CoveredTwoExteriorNeighbor.objective a b c1 c2 u x₀ = c - a * b := by
    have hi := block_physicalObjective (μ := μ) label hlabel x₀
    have ho : FiniteCappedSamplingCost.physicalObjective μ
        (fun v w => blockCharge x₀ (label v) (label w)) = CappedModel.objective W := by
      unfold CappedModel.objective FiniteCappedSamplingCost.physicalObjective
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
    rw [ho, hW.objective_eq] at hi
    change CoveredTwoExteriorNeighbor.objective a b c1 c2 u x₀ = c - a * b
    linarith only [hi]
  have hab : a < b :=
    a_lt_b_of_fullStationaryClass hW hd hgap label hlabel hpositive x₀ hx₀ hmom
  apply no_optimal_face_with_strict_repeat hab hb hc1 hc2 hu
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
    obtain ⟨_, _, hell, _, _, _⟩ :=
      hV'.smoothW_contact_parameters hd hgap hepsilon hactive hglobalV
    exact own_coefficients_pos hV' hd hgap label hlabel hpositive x hx.1 hell.1 hmomV
  · intro x hx y hy D _hD hfull
    obtain ⟨V, m', hV, hmomV, _, _⟩ := exists_active_block_fullStationaryClass W hW.full hopt
      hphysical (by rwa [hW.density_eq]) (by rwa [hW.density_eq, hW.objective_eq])
      label hlabel hpositive (blockCharge x₀) (Eventually.of_forall hmom) x hx.1
      (by simpa only [hW.objective_eq] using hx.2)
    have hV' : FullStationaryClass d c V m' := by
      rwa [hW.density_eq, hW.objective_eq] at hV
    exact repeat_penalties_gt_cross hV' hd hgap label hlabel hpositive x hx.1 hmomV
      y hy D hfull

end Erdos1017.CoveredTwoExteriorNeighbor

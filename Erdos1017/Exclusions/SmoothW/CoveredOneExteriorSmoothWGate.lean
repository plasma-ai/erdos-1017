module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredOneExteriorChargeBox
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorOwnRows
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorPhysicalPrimal
public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak

/-!
# One-exterior gate at the smooth `W` contact

An `A/B/C/E` optimum cannot lie at the smooth-`W` contact; every optimal child
dual receives its own model, stationary rows and full-repeat obstruction
(`no_smoothW_one_exterior`).
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
  {W : Model Ω μ} {d c m : ℝ}

/-- An actual A/B/C/E optimum cannot lie at the smooth-W contact.
Every optimal child dual receives its own actual model, stationary rows,
full-repeat obstruction and attained physical child cost law internally. -/
theorem no_smoothW_one_exterior (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hepsilon : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
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
  obtain ⟨_, _, hell, _, _, _⟩ :=
    hV'.smoothW_contact_parameters hd hgap hepsilon hactive hglobalV
  obtain ⟨hcoords, ht, hrow, hrepeat⟩ := own_row_parameters hV' hd hgap label hlabel
    hpositive y hy.1 hmomV
  have hmoment := exists_tightMomentData_of_fullStationaryClass label hlabel y hy.1 V hV' hd hgap hmomV
  exact ⟨-m', hcoords, ht, hell.1, hrow, hmoment, hrepeat⟩

end Erdos1017.CoveredOneExterior

module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomNeutralStationarity
public import Erdos1017.Exclusions.SmoothW.TwoAtomSmoothWParameters
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomPhysicalCopyBudgets
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomEStarCompletion
public import Erdos1017.Exclusions.SmoothW.TwoAtomLowSlopeGate

/-!
# No four-region optimum at a smooth point of `W`

A positive four-region optimum cannot lie at the smooth-`W` contact; the
argument runs through each selected active dual's own model, multiplier, rows,
floors and copy budgets (`no_smoothW_four_region`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.TwoAtomCountGate

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m : ℝ}

/-- An actual positive four-region optimum cannot lie at the smooth-W
contact. Every selected active dual's own model, multiplier, rows, floors,
copy budgets and completion inequality are constructed inside the proof.
The original graph reduction and weak physical demand order remain explicit. -/
theorem no_smoothW_four_region (hW : FullStationaryClass d c W m)
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
    (x₀ : Coefficients) (hx₀ : x₀ ∈ feasible) (hh₀ : 0 < x₀ 0)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x₀ (label p.1) (label p.2))
    (hweak : μ.real (label ⁻¹' {2}) ≤ μ.real (label ⁻¹' {1})) : False := by
  let a := μ.real (label ⁻¹' {0})
  let b := μ.real (label ⁻¹' {1})
  let u := μ.real (label ⁻¹' {2})
  let e := μ.real (label ⁻¹' {3})
  have hmass : a + b + u + e = 1 := four_fiber_masses_sum_one label hlabel
  have hpos (i : Fin 4) : 0 < μ.real (label ⁻¹' {i}) :=
    ENNReal.toReal_pos (hpositive i).ne' (measure_ne_top _ _)
  have ha : 0 < a := hpos 0
  have hb : 0 < b := hpos 1
  have hu : 0 < u := hpos 2
  have he : 0 < e := hpos 3
  have hrows₀ := fourRegionShiftedRows_of_block_stationary hW label hlabel hpositive x₀ hmom
  obtain ⟨hhfloor, _, _, _, hBE, _⟩ := own_block_present_floors hW hd hgap label hpositive x₀ hmom
  have hab : a < b := hrows₀.a_lt_b hh₀ hu.le he (by linarith) hBE
  have hbu : u < b := u_lt_b_of_fullStationaryClass hW hd hgap hphysical
    label hlabel hpositive x₀ hx₀ hh₀ hmom hweak
  have hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hmax (x : Coefficients) (hx : x ∈ feasible) : objective a b u e x ≤ c := by
    have h := block_objective_le_full_optimum W hopt label hlabel
      (Eventually.of_forall (fun p => (hmom p).1)) x hx
    rwa [hW.objective_eq] at h
  have hvalue : objective a b u e x₀ = c := by
    rw [← block_physicalObjective (μ := μ) label hlabel x₀, ← hW.objective_eq]
    unfold CappedModel.objective FiniteCappedSamplingCost.physicalObjective
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
  apply no_optimal_face_with_own_ell_le_two_thirds hab hb hu he hbu
    ⟨x₀, ⟨hx₀, hvalue⟩, hh₀⟩ hmax
  intro x hx hh
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
  obtain ⟨hell, hgamma, _, hbonus⟩ := smoothW_own_parameters hV' hd hgap
    hepsilon hactive hglobalV label hlabel (Eventually.of_forall (fun p => (hmomV p).1))
  have hrows := fourRegionShiftedRows_of_block_stationary hV' label hlabel hpositive x hmomV
  obtain ⟨hAR, hRR, hEE, hRE, _, _⟩ := own_block_present_floors hV' hd hgap label hpositive x hmomV
  have hrowE := hrows.own_E_charge hmass
  have hrowE' : (2 * (c - m' * d) + m') + -m' * a = b * x 1 - x 4 * u - x 3 * e := by
    convert hrowE using 1
    ring
  have hmax' (y : Coefficients) (hy : y ∈ feasible) :
      objective a b u e y ≤ objective a b u e x := by
    rw [hx.2]
    exact hmax y hy
  obtain ⟨hcoeff, _⟩ := positive_coefficients_and_contact_of_own_E_row hbu he x hx.1 hh
    ha.le hb.le hu.le (by linarith [hell.1]) hgamma hrowE' hmax'
  have hv := v_gt_ell_of_fullStationaryClass label hlabel hpositive x
    (fun i => (hcoeff i).le) V hV' hd hgap hmomV
  have hbody : ∀ᵐ p ∂μ.prod μ, label p.1 ≠ 1 → label p.2 ≠ 1 →
      chargeKernel V p.1 p.2 ≤ 0 := by
    apply Eventually.of_forall
    intro p hp hq
    change V.moment CappedColor.charge p ≤ 0
    rw [(hmomV p).2]
    have hi : label p.1 = 0 ∨ label p.1 = 2 ∨ label p.1 = 3 := by omega
    have hj : label p.2 = 0 ∨ label p.2 = 2 ∨ label p.2 = 3 := by omega
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
      simp [blockCharge, hi, hj, (hcoeff _).le]
  have hcopy := hV'.twoAtom_copy_gain_budgets hd hgap label hlabel hpositive x hx.1 hmomV hbody
  obtain ⟨hp, hq, hr⟩ := hcopy.strict_penalty_floors hx.1 ha.le hb
    (by linarith [hell.1]) hh.le (by simpa only [sub_neg_eq_add] using hbonus)
  have hvone := hx.1.2.2.1 0 1
  norm_num [countTest_apply] at hvone
  refine ⟨-m', ?_, hell.2.le⟩
  exact ⟨hh, hell.1, hAR, hRR, hEE, hRE, hv, hvone, hp, hq, hr⟩

end Erdos1017.TwoAtomCountGate

module

public import Erdos1017.Exclusions.Common.TwoAtom.SelectedTwoAtomChargeBox
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomPhysicalStationarity
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomPhysicalCopyBudgets
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomEStarCompletion

/-!
# Own count data from the half slope and signed bonus

A represented four-region optimum derives its own count guards and stationary
rows from its half slope and signed bonus, with coefficient positivity
established first.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.TwoAtomCountGate

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {V : Model Ω μ} {d c m : ℝ}

/-- A represented actual four-region optimum derives its own count guards
and stationary rows from its own half-slope and signed bonus. Coefficient
positivity precedes body signs and copying; completion pays the upper slope. -/
theorem own_count_data_of_half_slope_bonus (hV : FullStationaryClass d c V m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i}))
    (x : Coefficients) (hx : x ∈ feasible) (hh : 0 < x 0)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2))
    (hbu : μ.real (label ⁻¹' {2}) < μ.real (label ⁻¹' {1}))
    (hell : 1 / 2 < -m)
    (hbonus : μ.real (label ⁻¹' {1}) * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    OwnCountGuards x (-m) ∧ OwnCountRows x
      (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) (-m) := by
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
  have hrows := fourRegionShiftedRows_of_block_stationary hV label hlabel hpositive x hmom
  obtain ⟨hAR, hRR, hEE, hRE, _, hgamma⟩ :=
    own_block_present_floors hV hd hgap label hpositive x hmom
  have hrowE := hrows.own_E_charge hmass
  have hrowE' : (2 * (c - m * d) + m) + -m * a =
      b * x 1 - x 4 * u - x 3 * e := by
    convert hrowE using 1
    ring
  have hopt : CappedModel.objective V = FractionalGraph.densityLimit (density V) := by
    rw [hV.objective_eq, hV.density_eq]
    exact hV.optimal
  have hcost : objective a b u e x = CappedModel.objective V := by
    rw [← block_physicalObjective (μ := μ) label hlabel x]
    unfold CappedModel.objective FiniteCappedSamplingCost.physicalObjective
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
  have hmax (y : Coefficients) (hy : y ∈ feasible) : objective a b u e y ≤ objective a b u e x := by
    rw [hcost]
    exact block_objective_le_full_optimum V hopt label hlabel
      (Eventually.of_forall (fun p => (hmom p).1)) y hy
  obtain ⟨hcoeff, _⟩ := positive_coefficients_and_contact_of_own_E_row hbu he x hx hh
    ha.le hb.le hu.le (by linarith [hell]) hgamma hrowE' hmax
  have hv := v_gt_ell_of_fullStationaryClass label hlabel hpositive x
    (fun i => (hcoeff i).le) V hV hd hgap hmom
  have hbody : ∀ᵐ p ∂μ.prod μ, label p.1 ≠ 1 → label p.2 ≠ 1 →
      chargeKernel V p.1 p.2 ≤ 0 := by
    apply Eventually.of_forall
    intro p hp hq
    change V.moment CappedColor.charge p ≤ 0
    rw [(hmom p).2]
    have hi : label p.1 = 0 ∨ label p.1 = 2 ∨ label p.1 = 3 := by omega
    have hj : label p.2 = 0 ∨ label p.2 = 2 ∨ label p.2 = 3 := by omega
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
      simp [blockCharge, hi, hj, (hcoeff _).le]
  have hcopy := hV.twoAtom_copy_gain_budgets hd hgap label hlabel hpositive x hx hmom hbody
  obtain ⟨hp, hq, hr⟩ := hcopy.strict_penalty_floors hx ha.le hb
    (by linarith [hell]) hh.le (by simpa only [sub_neg_eq_add] using hbonus)
  have hvone := hx.2.2.1 0 1
  norm_num [countTest_apply] at hvone
  exact ⟨⟨hh, hell, hAR, hRR, hEE, hRE, hv, hvone, hp, hq, hr⟩, hrows.ownCountRows⟩

end Erdos1017.TwoAtomCountGate

module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass
public import Erdos1017.Exclusions.Common.SelectedRootRows
public import Erdos1017.Exclusions.Common.Flows.FullForwardQuarterFloor

/-!
# Head degree sign of a two-center recovery at `E₂`

The adjacency degree of a plateau head is at most one minus its recovered
height, and a height above the missing mass makes the two-head baseline strictly
negative in the degree direction; at an `E₂` contact the reverse budget forces
such a height.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The original head mass and its original receipt fraction add to the
actual recovered plateau height. -/
private theorem head_mass_add_fraction_integral (r : S.I) (hr : r ∈ R.plateau) :
    μ.real {x | S.ρ x = r.val} + (∫ x, R.headFraction r x ∂μ) = R.height := by
  have hcode := (R.data.code_mem_iff_plateauLabels R.codePlateau R.active_codePlateau r).mpr hr
  have hm := (R.mass_eq_iff (R.data.code r)).mpr hcode
  have hbase : R.data.a (R.data.code r) = μ.real {x | S.ρ x = r.val} := by
    rw [R.data.ha]
    simp only [reverseAtomMass, R.data.label_at_code r (R.plateau_eligible r hr)]
  rwa [ReverseAssignment.mass, hbase, ← (R.headFraction_properties r).2.2] at hm

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual fractional receipt into one head is bounded by one on the
original law, including points outside HIGH. -/
private theorem ae_headFraction_le_one (r : S.I) :
    ∀ᵐ x ∂μ, R.headFraction r x ≤ 1 := by
  have hb := (ae_restrict_iff' S.hpartition.1).mp
    ((R.feasible.box (R.data.code r)).mono (fun _ hx => hx.2))
  filter_upwards [hb] with x hx
  by_cases hH : x ∈ S.H
  · simpa only [headFraction, MissingFlow.RestrictedAtomicAssignment.liftFraction,
      indicator_of_mem hH] using hx hH
  · simp only [headFraction, MissingFlow.RestrictedAtomicAssignment.liftFraction,
      indicator_of_notMem hH, zero_le_one]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual original adjacency degree of a plateau head is at most
one minus its recovered height. The bound counts its own independent
fiber and the original fractional receipts among its missing mass. -/
theorem wholeRowDegree_le_one_sub_height (r : S.I) (hr : r ∈ R.plateau) :
    wholeRowDegree r.val ≤ 1 - R.height := by
  let I : Set Ω := {x | S.ρ x = r.val}
  let J : Set Ω := {x | 0 < r.val x}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hJ : MeasurableSet J :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable r.val).measurable
  have hiI : Integrable (I.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hI
  have hiJ : Integrable (J.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hJ
  have hiF := (R.headFraction_properties r).1
  have hzero := (ae_restrict_iff' hI).mp (S.root_row_zero_on_fiber r)
  have hnotH := (ae_restrict_iff' hI).mp (R.plateau_eligible r hr)
  have hpoint : ∀ᵐ x ∂μ,
      J.indicator (fun _ => (1 : ℝ)) x + I.indicator (fun _ => (1 : ℝ)) x +
        R.headFraction r x ≤ 1 := by
    filter_upwards [hzero, hnotH, R.ae_headFraction_le_one r,
      R.headFraction_zero_off_missing r hr] with x hz hn hbound hsupport
    by_cases hxI : x ∈ I
    · have hxJ : x ∉ J := by
        change ¬0 < r.val x
        rw [hz hxI]
        exact lt_irrefl 0
      have hfrac : R.headFraction r x = 0 := by
        simp only [headFraction, MissingFlow.RestrictedAtomicAssignment.liftFraction,
          indicator_of_notMem (hn hxI)]
      simp only [indicator_of_notMem hxJ, indicator_of_mem hxI, hfrac,
        zero_add, add_zero, le_refl]
    · by_cases hxJ : x ∈ J
      · have hmissing : x ∉ KernelOperator.wholeFiberMissingSet S.ρ r.val := by
          intro h
          exact not_lt_of_ge h.2 hxJ
        simp only [indicator_of_mem hxJ, indicator_of_notMem hxI,
          hsupport hmissing, add_zero, le_refl]
      · simpa only [indicator_of_notMem hxJ, indicator_of_notMem hxI,
          zero_add] using hbound
  have hint := integral_mono_ae ((hiJ.add hiI).add hiF) (integrable_const (1 : ℝ)) hpoint
  rw [integral_add' (hiJ.add hiI) hiF, integral_add' hiJ hiI,
    integral_indicator hI, setIntegral_const, smul_eq_mul, mul_one,
    integral_const, probReal_univ, one_smul] at hint
  have hdegree : (∫ x, J.indicator (fun _ => (1 : ℝ)) x ∂μ) = wholeRowDegree r.val := by
    rfl
  rw [hdegree] at hint
  have hmass := R.head_mass_add_fraction_integral r hr
  change μ.real I + _ = R.height at hmass
  linarith

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The original two-head baseline has its degree pairing bounded by
its original recovered height, before changing the law. -/
theorem mean_head_degree_inner_le (r u : S.I) (hr : r ∈ R.plateau)
    (hu : u ∈ R.plateau) {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ ≤ 1 - R.height - 2 * d := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hhead (v : S.I) : ⟪g, S.normalizedHead v⟫ = wholeRowDegree v.val := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers v.val v.property).2.1 g _
      (wholeRowFiber_degree W m S.ρ v.val (S.hfibers v.val v.property).2.2.2)
  have hone : ⟪g, Lp.const 2 μ (1 : ℝ)⟫ = 2 * d := by
    change ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ = _
    rw [← weighted_adjacency_eq, weightedPairIntegral_one]
    have hdW := hW.density_eq
    unfold density at hdW
    change (∫ p, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 = d at hdW
    linarith
  change ⟪g, (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
    Lp.const 2 μ (1 : ℝ)⟫ ≤ _
  rw [inner_sub_right, real_inner_smul_right, inner_add_right, hhead r, hhead u, hone]
  linarith [R.wholeRowDegree_le_one_sub_height r hr,
    R.wholeRowDegree_le_one_sub_height u hu]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A recovered height above the original missing mass makes the original
two-head baseline strictly negative in the degree direction. -/
theorem mean_head_degree_inner_neg_of_height_gt_missing
    (r u : S.I) (hr : r ∈ R.plateau) (hu : u ∈ R.plateau)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hheight : 1 - 2 * d < R.height) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0 := by
  have hbound := R.mean_head_degree_inner_le r u hr hu hW
  linarith

/-- The actual E2 gap floor strictly exceeds the reverse height budget
at the original missing mass throughout the positive contact interval. -/
private theorem e2_gapFloor_gt_missing_square {q : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    2 * (1 - LowerE2Scalar.multiplier q) * (LowerE2Scalar.missingMass q) ^ 2 <
      LowerE2Scalar.gapFloor q := by
  let P : ℝ := 17 * q ^ 6 + 86 * q ^ 5 + 14 * q ^ 4 -
    500 * q ^ 3 - 455 * q ^ 2 - 122 * q - 12
  have hq4 : q ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := pow_le_pow_left₀ hq.1.le hq.2 4
  have hq5 : q ^ 5 ≤ (1 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ hq.1.le hq.2 5
  have hq6 : q ^ 6 ≤ (1 / 5 : ℝ) ^ 6 := pow_le_pow_left₀ hq.1.le hq.2 6
  have hP : P < 0 := by
    dsimp only [P]
    nlinarith [sq_nonneg q, pow_nonneg hq.1.le 3, hq.1]
  have hQ := LowerE2Scalar.denominator_pos hq.1.le
  have hQne := hQ.ne'
  have hq2 : 2 + q ≠ 0 := by linarith [hq.1]
  have hid : 16 * LowerE2Scalar.denominator q ^ 4 *
      (LowerE2Scalar.gapFloor q - 2 * (1 - LowerE2Scalar.multiplier q) *
        (LowerE2Scalar.missingMass q) ^ 2) = -9 * q ^ 2 * P := by
    dsimp only [LowerE2Scalar.gapFloor, LowerE2Scalar.multiplier,
      LowerE2Scalar.missingMass, P]
    field_simp
    unfold LowerE2Scalar.denominator
    ring
  have hpositive : 0 < -9 * q ^ 2 * P :=
    mul_pos_of_neg_of_neg (by nlinarith [sq_pos_of_pos hq.1]) hP
  rw [← hid] at hpositive
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity :
    0 < 16 * LowerE2Scalar.denominator q ^ 4)).mp hpositive)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The same actual two-center reverse budget at an E2 contact forces its
height above the original missing mass. No height or scalar budget hypothesis
is used. -/
theorem e2_height_gt_missing (r u : S.I) (hru : r ≠ u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hp : R.plateau = {r, u}) : 1 - 2 * d < R.height := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq hdq hgap hglobal
  have hcard : R.plateau.card = 2 := by rw [hp, Finset.card_pair hru]
  have hb := R.isFullReverseFlow.plateau_budget hW hd hgap R.plateau R.height
    (R.classMass_le hW) (fun v hv => (R.classMass_eq_iff hW v).mpr hv)
  rw [hcard] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have henergy := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hpaid : 2 * (c - m * d) + m ≤ 2 * (1 + m) * R.height ^ 2 := by
    nlinarith only [hb.1, hb.2, henergy]
  have hgapSquare := e2_gapFloor_gt_missing_square hq
  have hmissing : LowerE2Scalar.missingMass q = 1 - 2 * d := by linarith [hdq]
  rw [hmissing, ← neg_eq_iff_eq_neg.mpr hm] at hgapSquare
  by_contra hn
  have ht : R.height ≤ 1 - 2 * d := le_of_not_gt hn
  have hsq : R.height ^ 2 ≤ (1 - 2 * d) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr ht)
      (show 0 ≤ 1 - 2 * d + R.height by linarith [R.height_pos])
    nlinarith only [hp]
  have hcoef : 0 ≤ 2 * (1 + m) := by linarith [hell.2]
  have hscaled := mul_le_mul_of_nonneg_left hsq hcoef
  nlinarith [hgamma, hpaid, hgapSquare, hscaled]

/-- The original two-head baseline degree sign at the actual selected E2
contact is derived from its original reverse budget and receipt fractions. -/
theorem e2_mean_head_degree_inner_neg (r u : S.I) (hru : r ≠ u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hp : R.plateau = {r, u}) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0 := by
  exact R.mean_head_degree_inner_neg_of_height_gt_missing r u
    (by rw [hp]; simp) (by rw [hp]; simp)
    hW (R.e2_height_gt_missing r u hru hW hq hdq hgap hglobal hp)

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

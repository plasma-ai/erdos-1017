module

public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Erdos1017.Exclusions.Common.Physical.IndependentClassMissingMass

/-!
# Atom guards at the `E₂` contact

The `E₂` contact density stays inside the model interval, the contact slope is
strictly between one half and one, and every independent block of any `E₂`
contact has the same strict bonus, which any selected atom inherits from its
positive independent fiber (`e2_atom_contact_guards`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.LowerE2Scalar

/-- The literal E2 density stays inside the actual model interval on the
whole stated parameter range, without asserting benchmark activity. -/
theorem contact_density_mem {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (2 / 9)) :
    (1 - missingMass q) / 2 ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
  have hqpos := hq.1
  have hR := denominator_pos hqpos.le
  have hq1 : q < 1 := by linarith [hq.2]
  have hq3 : q ^ 3 < 1 := by nlinarith [mul_pos (sub_pos.mpr hq1) (show 0 < 1 + q + q ^ 2 by positivity)]
  have hpos : 0 < missingMass q := by unfold missingMass; positivity
  have hid : (1 / 2 - missingMass q) * (8 * denominator q ^ 2) =
      9 * q * (4 + 15 * q - q ^ 3) := by
    unfold missingMass
    field_simp
    unfold denominator
    ring
  have hbrace : 0 < 4 + 15 * q - q ^ 3 := by linarith
  have hpositive : 0 < 9 * q * (4 + 15 * q - q ^ 3) := by positivity
  have hsmall : missingMass q < 1 / 2 := by
    rw [← hid] at hpositive
    exact sub_pos.mp ((mul_pos_iff_of_pos_right (by positivity)).mp hpositive)
  constructor <;> linarith

/-- The E2 contact slope is strictly between one half and one. -/
theorem contact_multiplier_mem {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (2 / 9)) :
    multiplier q ∈ Ioo (1 / 2 : ℝ) 1 := by
  have hden : 0 < 2 + q := by linarith [hq.1]
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith [hq.2]
  · apply (div_lt_one hden).mpr
    linarith [hq.1]

/-- The exact stationary-family shifted-row floor is positive. -/
theorem contact_gapFloor_pos {q : ℝ} (hq : 0 < q) : 0 < gapFloor q := by
  unfold gapFloor
  exact div_pos (mul_pos hq (by linarith)) (mul_pos (by norm_num) (denominator_pos hq.le))

/-- This is the literal squared Phi quotient, before any model or atom
mass is introduced. Every denominator is paid by the actual positive q. -/
theorem contact_phi_sq {q : ℝ} (hq : 0 < q) :
    missingMass q * (1 - multiplier q) ^ 2 / (gapFloor q) ^ 2 =
      2 * (1 + 4 * q + 13 * q ^ 2) / (1 + 2 * q) ^ 2 := by
  have hR := (denominator_pos hq.le).ne'
  have hq0 := hq.ne'
  have hq2 : 2 + q ≠ 0 := by linarith
  have hq1 : 1 + 2 * q ≠ 0 := by linarith
  unfold missingMass multiplier gapFloor
  field_simp
  ring

/-- The exact Phi-square margin is strict throughout 0<q≤2/9. -/
theorem contact_phi_sq_lt_four {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (2 / 9)) :
    2 * (1 + 4 * q + 13 * q ^ 2) / (1 + 2 * q) ^ 2 < 4 := by
  have hqpos := hq.1
  have hq1 : q < 1 := by linarith [hq.2]
  have hden : 0 < (1 + 2 * q) ^ 2 := by positivity
  have hden0 : 1 + 2 * q ≠ 0 := by positivity
  have hid : 4 - 2 * (1 + 4 * q + 13 * q ^ 2) / (1 + 2 * q) ^ 2 =
      2 * (1 - q) * (1 + 5 * q) / (1 + 2 * q) ^ 2 := by
    field_simp [hden0]
    ring
  have hp : 0 < 2 * (1 - q) * (1 + 5 * q) / (1 + 2 * q) ^ 2 := by positivity
  linarith only [hid, hp]

/-- The square-cleared bonus bound avoids any supplied radical or Phi
certificate in the actual model application. -/
theorem contact_squared_bonus {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (2 / 9)) :
    missingMass q * (1 - multiplier q) ^ 2 < 4 * (gapFloor q) ^ 2 := by
  have hfloor := contact_gapFloor_pos hq.1
  apply (div_lt_iff₀ (sq_pos_of_pos hfloor)).mp
  rw [contact_phi_sq hq.1]
  exact contact_phi_sq_lt_four hq

/-- Any actual independent mass below the original missing-square
inventory has the strict contact bonus at any larger actual intercept. -/
theorem contact_atom_bonus {q b gamma : ℝ} (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hb : 0 ≤ b) (hsquare : b ^ 2 ≤ missingMass q) (hgamma : gapFloor q < gamma) :
    b * (1 - multiplier q) < 2 * gamma := by
  have hell := contact_multiplier_mem hq
  have hfloor := contact_gapFloor_pos hq.1
  have hs := contact_squared_bonus hq
  have hprod := mul_nonneg (sub_nonneg.mpr hsquare) (sq_nonneg (1 - multiplier q))
  have hnonneg := mul_nonneg hb (show 0 ≤ 1 - multiplier q by linarith [hell.2])
  have hgammapos := hfloor.trans hgamma
  nlinarith

end Erdos1017.LowerE2Scalar

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A genuine measurable independent square contributes its entire mass
square to the displayed model's original missing density. -/
theorem independent_set_mass_sq_le_missing_density (W : Model Ω μ) (I : Set Ω)
    (hI : MeasurableSet I)
    (hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), adjacencyKernel W p.1 p.2 = 0) :
    (μ.real I) ^ 2 ≤ 1 - 2 * density W := by
  have hzero := hind
  rw [Measure.prod_restrict] at hzero
  have hz := (ae_restrict_iff' (hI.prod hI)).mp hzero
  have hi := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  have hle : (∫ p, (I ×ˢ I).indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ) ≤
      ∫ p, 1 - W.moment CappedColor.adjacency p ∂μ.prod μ := by
    apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator (hI.prod hI))
      ((integrable_const 1).sub hi)
    filter_upwards [hz] with p hp
    change (I ×ˢ I).indicator (fun _ => (1 : ℝ)) p ≤ 1 - W.moment CappedColor.adjacency p
    by_cases hm : p ∈ I ×ˢ I
    · have hzero : W.moment CappedColor.adjacency p = 0 := hp hm
      simp only [indicator_of_mem hm, hzero, sub_zero, le_refl]
    · simp only [indicator_of_notMem hm]
      exact sub_nonneg.mpr (adjacency_moment_mem W p).2
  rw [integral_indicator (hI.prod hI), setIntegral_const, smul_eq_mul, mul_one,
    measureReal_prod_prod, integral_sub (integrable_const 1) hi] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  unfold density
  nlinarith only [hle]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The E2 benchmark value and derivative contact identify this
actual optimum's own multiplier and strict shifted-row floor. No activity
beyond the supplied contact is asserted. -/
theorem FullStationaryClass.e2_general_contact_parameters
    {d c m q : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    m = -LowerE2Scalar.multiplier q ∧ -m ∈ Ioo (1 / 2 : ℝ) 1 ∧
      LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq
  have hm := full_stationary_multiplier_eq_benchmark_deriv W hW.full hglobal
    (by simpa only [hW.density_eq] using hderiv) m _ hW.stationary
    (hW.strict_gap_structure hd hgap).nonconstant_degree
  refine ⟨hm, by simpa only [hm, neg_neg] using LowerE2Scalar.contact_multiplier_mem hq, ?_⟩
  have hid := LowerE2Scalar.gapFloor_eq_twoHeadValue hq.1.le
  rw [hvalue] at hgap
  rw [hm, hdq]
  nlinarith only [hid, hgap]

/-- Every measurable independent block of any actual own E2 contact has
the same strict bonus. No selected structure, peak or original multiplier
assignment appears in this active-model interface. -/
theorem FullStationaryClass.e2_independent_set_contact_guards
    {d c m q : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (I : Set Ω) (hI : MeasurableSet I)
    (hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), adjacencyKernel W p.1 p.2 = 0) :
    m = -LowerE2Scalar.multiplier q ∧ -m ∈ Ioo (1 / 2 : ℝ) 1 ∧
      LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m ∧
      (μ.real I) ^ 2 ≤ 1 - 2 * d ∧
      μ.real I * (1 + m) < 2 * (2 * (c - m * d) + m) ∧
      μ.real I * (1 + m) / (2 * (c - m * d) + m) < 2 := by
  obtain ⟨hm, hell, hfloor⟩ := hW.e2_general_contact_parameters hq hdq hvalue hderiv hgap hglobal
  have hsq := independent_set_mass_sq_le_missing_density W I hI hind
  rw [hW.density_eq] at hsq
  have hsq' : (μ.real I) ^ 2 ≤ LowerE2Scalar.missingMass q := by rw [hdq] at hsq; linarith
  have hb := LowerE2Scalar.contact_atom_bonus hq measureReal_nonneg hsq' hfloor
  have hbonus : μ.real I * (1 + m) < 2 * (2 * (c - m * d) + m) := by
    simpa only [hm, sub_eq_add_neg] using hb
  have hgamma : 0 < 2 * (c - m * d) + m := (LowerE2Scalar.contact_gapFloor_pos hq.1).trans hfloor
  exact ⟨hm, hell, hfloor, hsq, hbonus, (div_lt_iff₀ hgamma).mpr (by linarith only [hbonus])⟩

end Erdos1017.CappedModel

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- Any original selected atom inherits the own E2 contact guards from
its actual measurable positive independent fiber. No second atom is used. -/
theorem e2_atom_contact_guards (S : SelectedHighLowStructure W m) (r : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    m = -LowerE2Scalar.multiplier q ∧ -m ∈ Ioo (1 / 2 : ℝ) 1 ∧
      LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m ∧
      (S.originalAtomMass r) ^ 2 ≤ 1 - 2 * d ∧
      S.originalAtomMass r * (1 + m) < 2 * (2 * (c - m * d) + m) ∧
      S.originalAtomMass r * (1 + m) / (2 * (c - m * d) + m) < 2 :=
  hW.e2_independent_set_contact_guards hq hdq hvalue hderiv hgap hglobal
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 (S.hfibers r.val r.property).2.2.1

end Erdos1017.CappedModel.SelectedHighLowStructure

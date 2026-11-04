module

public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic
public import Erdos1017.Exclusions.E2.Upper.UpperE2ParameterGuards
public import Erdos1017.SelectedModel.SelectedBodyEnergy
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards

/-!
# Normalized trace bounds for the universal body

The universal body capped by its own penalty satisfies the sharper normalized
trace, the exact upper-`E₂` trace constants exclude the closed mass threshold,
and the upper-`E₂` contact excludes the large-mass branch once a conditional
body cap is supplied.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An AE cap on the same positive body strengthens the copy trace by
normalizing a measurable clipped representative. Null exceptions never
become pointwise kernel hypotheses. -/
theorem copy_row_trace_bound_of_ae_cap (K J : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hK0 : ∀ x y, 0 ≤ K x y) (hJB : ∀ x y, ‖J x y‖ ≤ 1)
    (hsym : ∀ x y, K x y = K y x)
    (a g ell : ℝ) (hell : 0 < ell) (hg : 0 ≤ g) (hag : 0 ≤ a + g / ell)
    (hcap : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ≤ ell)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    (horthogonal : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1)) :
    (a + g / ell) ^ 2 ≤ 2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) := by
  let L := fun x y => min (K x y) ell / ell
  have hL : Measurable (Function.uncurry L) :=
    (hK.min measurable_const).div_const ell
  have hL01 (x y : Ω) : L x y ∈ Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (le_min (hK0 x y) hell.le) hell.le,
      (div_le_one hell).mpr (min_le_right _ _)⟩
  have hLsym (x y : Ω) : L x y = L y x := by
    dsimp only [L]
    rw [hsym x y]
  have hsame : ∀ᵐ p ∂μ.prod μ, L p.1 p.2 = K p.1 p.2 / ell :=
    hcap.mono (fun _ hp => by dsimp only [L]; rw [min_eq_left hp])
  have hpositiveL : 0 < ∫ p : Ω × Ω, (L p.1 p.2) ^ 2 ∂μ.prod μ := by
    have heq : (∫ p : Ω × Ω, (L p.1 p.2) ^ 2 ∂μ.prod μ) =
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) / ell ^ 2 := by
      calc
        _ = ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 / ell ^ 2 ∂μ.prod μ := by
          apply integral_congr_ae
          filter_upwards [hsame] with p hp
          rw [hp, div_pow]
        _ = _ := integral_div _ _
    rw [heq]
    exact div_pos hpositive (sq_pos_of_pos hell)
  have horthogonalL : (∫ p : Ω × Ω, J p.1 p.2 * L p.1 p.2 ∂μ.prod μ) = 0 := by
    calc
      _ = ∫ p : Ω × Ω, (J p.1 p.2 * K p.1 p.2) / ell ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [hsame] with p hp
        rw [hp, mul_div_assoc]
      _ = (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) / ell := integral_div _ _
      _ = 0 := by rw [horthogonal, zero_div]
  have hsections := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hsame)
  have hcomposed : ∀ᵐ p ∂μ.prod μ, composedKernel (μ := μ) J L p.1 p.2 =
      composedKernel (μ := μ) J K p.1 p.2 / ell := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hsections] with p hp
    change (∫ z, J p.1 z * L z p.2 ∂μ) = (∫ z, J p.1 z * K z p.2 ∂μ) / ell
    calc
      _ = ∫ z, (J p.1 z * K z p.2) / ell ∂μ := by
        apply integral_congr_ae
        filter_upwards [hp] with z hz
        change L z p.2 = K z p.2 / ell at hz
        rw [hz, mul_div_assoc]
      _ = _ := integral_div _ _
  have hrowL : ∀ᵐ p ∂μ.prod μ, a * (L p.1 p.2) ^ 2 + (g / ell) * L p.1 p.2 ≤
      L p.1 p.2 * (composedKernel (μ := μ) J L p.1 p.2 +
        composedKernel (μ := μ) J L p.2 p.1) := by
    filter_upwards [hrow, hsame, hcomposed,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hcomposed]
      with p hp he hc hcr
    change composedKernel (μ := μ) J L p.2 p.1 =
      composedKernel (μ := μ) J K p.2 p.1 / ell at hcr
    rw [he, hc, hcr]
    convert div_le_div_of_nonneg_right hp (sq_nonneg ell) using 1 <;>
      field_simp [hell.ne']
  exact copy_row_trace_bound L J hL hJ hL01 hJB hLsym a (g / ell)
    (div_nonneg hg hell.le) hag hpositiveL horthogonalL hrowL

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original universal body capped by its own penalty satisfies the
sharper normalized trace. Original positive energy licenses the division. -/
theorem universal_positive_body_trace_of_cap (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val})
    (hcap : ∀ᵐ p ∂μ.prod μ,
      IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} p.1 p.2 ≤ -m) :
    (S.originalAtomMass r + (2 * (c - m * d) + m) / (-m)) ^ 2 ≤
      2 * (1 - 2 * d - (S.originalAtomMass r) ^ 2) := by
  let Y := PhysicalRepresentative.charge W m
  let A := PhysicalRepresentative.adjacency W m
  let I := {x | S.ρ x = r.val}
  let K := IndependentAtomCopy.positiveBody Y I
  let J := IndependentAtomCopy.missingBody A I
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hgamma := (hW.strict_gap_structure hd hgap).gamma_pos
  have hell : 0 < -m := neg_pos.mpr (hW.strict_gap_structure hd hgap).multiplier_neg
  have hphysical : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ := by
    rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap I hI] at hpositive
    exact hpositive
  have horth : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0 := by
    calc
      _ = ∫ _p : Ω × Ω, (0 : ℝ) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => IndependentAtomCopy.missingBody_positiveBody_mul
          A Y I (PhysicalRepresentative.charge_zero_of_nonedge W m) p.1 p.2)
      _ = 0 := integral_zero _ _
  have htrace := KernelOperator.copy_row_trace_bound_of_ae_cap K J
    (IndependentAtomCopy.measurable_positiveBody Y
      (PhysicalRepresentative.measurable_charge W m) I hI)
    (IndependentAtomCopy.measurable_missingBody A
      (PhysicalRepresentative.measurable_adjacency W m) I hI)
    (fun x y => (IndependentAtomCopy.positiveBody_mem Y I hY1 x y).1)
    (fun x y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem A I x y).1]
      exact (IndependentAtomCopy.missingBody_mem A I x y).2)
    (IndependentAtomCopy.positiveBody_symm Y I (PhysicalRepresentative.charge_symm W m))
    (S.originalAtomMass r) (2 * (c - m * d) + m) (-m) hell hgamma.le
    (add_nonneg measureReal_nonneg (div_nonneg hgamma.le hell.le)) hcap hphysical horth
    (S.ae_universal_positive_body_row r hW hd hgap hN)
  have hinventory := S.universal_missing_body_square_integral r hW hd hgap hN
  change (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) =
    1 - 2 * d - (S.originalAtomMass r) ^ 2 at hinventory
  rw [hinventory] at htrace
  exact htrace

end Erdos1017.CappedModel.SelectedHighLowStructure

namespace Erdos1017.UpperE2Parameter

/-- The exact upper-E2 trace constants exclude the closed mass threshold. -/
theorem mass_lt_cutoff_of_normalized_trace {A x h : ℝ}
    (hx : (77 / 1098 : ℝ) ≤ x) (hh : h ≤ 3509 / 14884)
    (htrace : (A + x) ^ 2 ≤ 2 * (h - A ^ 2)) : A < 93 / 250 := by
  by_contra hn
  have hA : (93 / 250 : ℝ) ≤ A := le_of_not_gt hn
  have hA2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 93 / 250) hA 2
  have hsum : (93 / 250 : ℝ) + 77 / 1098 ≤ A + x := add_le_add hA hx
  have hsum2 := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 93 / 250 + 77 / 1098) hsum 2
  norm_num at hA2 hsum2
  nlinarith

end Erdos1017.UpperE2Parameter

namespace Erdos1017.UpperE2Parameter

/-- Above the forbidden mass threshold, the genuine head-mass capacity
and same-parameter gamma floor pay the body-cap price guard. -/
theorem body_cap_price_guard_of_mass_ge_cutoff {A b gamma ell : ℝ}
    (hell : 0 < ell) (hA : (93 / 250 : ℝ) ≤ A)
    (hb : b ≤ 1 - 2 * A) (hgamma : (77 / 1098 : ℝ) ≤ gamma / ell) :
    b * ell - gamma ≤ ell * (6 * A - 2) := by
  have hscaled := (le_div_iff₀ hell).mp hgamma
  have hmargin : (3 : ℝ) - 8 * A ≤ 77 / 1098 := by linarith
  have hm := mul_le_mul_of_nonneg_right hmargin hell.le
  have hb' := mul_le_mul_of_nonneg_right hb hell.le
  nlinarith

end Erdos1017.UpperE2Parameter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual upper-E2 contact excludes the large-mass branch once its
conditional original body cap is supplied. The final caller derives that
cap from original bad-region geometry and the paid price guard. -/
theorem universal_upperE2_mass_lt_cutoff_of_body_cap
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val})
    (hcap : (93 / 250 : ℝ) ≤ S.originalAtomMass r → ∀ᵐ p ∂μ.prod μ,
      IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} p.1 p.2 ≤ -m) : S.originalAtomMass r < 93 / 250 := by
  have hmissing := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith [hmissing.1, hmissing.2]
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨hm, hell, hfloor⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hratio : (77 / 1098 : ℝ) ≤ (2 * (c - m * d) + m) / (-m) := by
    have hfloorRatio := UpperE2Parameter.gapFloor_div_multiplier_ge hq
    rw [← neg_eq_iff_eq_neg.mpr hm] at hfloorRatio
    exact hfloorRatio.trans (div_le_div_of_nonneg_right hfloor.le (by linarith [hell.1]))
  by_contra hn
  have htrace := S.universal_positive_body_trace_of_cap r hW hd hgap hN hpositive
    (hcap (le_of_not_gt hn))
  apply (not_lt_of_ge (le_of_not_gt hn))
  apply UpperE2Parameter.mass_lt_cutoff_of_normalized_trace hratio hmissing.2
  have hmissingEq : 1 - 2 * d = LowerE2Scalar.missingMass q := by rw [hdq]; ring
  rw [hmissingEq] at htrace
  exact htrace

end Erdos1017.CappedModel.SelectedHighLowStructure

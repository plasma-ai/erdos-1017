module

public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Multiplier bracketed by the one-sided benchmark slopes

Along a density-changing quadratic curve the one-sided derivatives bracket the
first variation of the objective, so at a global maximum of the benchmark excess
the stationary multiplier lies between the left and right benchmark derivatives,
also for a strict-gap member of `FullStationaryClass`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace Topology

namespace Erdos1017.SmoothContact

private theorem quadratic_hasDerivAt_zero (c a q : ℝ) :
    HasDerivAt (fun t : ℝ => c + t * a + t ^ 2 * q / 2) a 0 := by
  convert ((hasDerivAt_const (0 : ℝ) c).add ((hasDerivAt_id 0).mul_const a)).add
    ((((hasDerivAt_id 0).pow 2).mul_const q).div_const 2) using 1
  · rfl
  · simp

private theorem right_derivative_nonpos {f : ℝ → ℝ} {v : ℝ}
    (hf : HasDerivWithinAt f v (Ici 0) 0) (hmax : IsLocalMax f 0) : v ≤ 0 := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
    hf.Ioi_of_Ici
  apply le_of_tendsto ht
  filter_upwards [hmax.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with t hft ht0
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hft) (by simpa using le_of_lt ht0)

/-- Actual one-sided derivatives bracket the first objective variation
along a density-changing quadratic curve. Both density-side inclusions
are derived from its positive first coefficient. -/
theorem quadratic_one_sided_first_variation {B : ℝ → ℝ}
    {d c a y qA qY bleft bright : ℝ} (ha : 0 < a)
    (hleft : HasDerivWithinAt B bleft (Iic d) d)
    (hright : HasDerivWithinAt B bright (Ici d) d)
    (hmax : IsLocalMax
      (fun t : ℝ => c + t * y + t ^ 2 * qY / 2 - B (d + t * a + t ^ 2 * qA / 2)) 0) :
    bleft * a ≤ y ∧ y ≤ bright * a := by
  let D := fun t : ℝ => d + t * a + t ^ 2 * qA / 2
  let Y := fun t : ℝ => c + t * y + t ^ 2 * qY / 2
  let H := fun t : ℝ => Y t - B (D t)
  have hD0 : D 0 = d := by simp [D]
  have hD : HasDerivAt D a 0 := quadratic_hasDerivAt_zero d a qA
  have hY : HasDerivAt Y y 0 := quadratic_hasDerivAt_zero c y qY
  have hc : ContinuousAt (fun t : ℝ => a + t * qA / 2) 0 := by fun_prop
  have hpositive : ∀ᶠ t : ℝ in nhds 0, 0 < a + t * qA / 2 :=
    hc.eventually (eventually_gt_nhds (by simpa using ha))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpositive
  have hcoefficient (t : ℝ) (ht : t ∈ Icc (-ε / 2) (ε / 2)) :
      0 < a + t * qA / 2 := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hmapsRight : MapsTo D (Icc 0 (ε / 2)) (Ici d) := by
    intro t ht
    have hp := hcoefficient t ⟨by linarith [ht.1], ht.2⟩
    change d ≤ d + t * a + t ^ 2 * qA / 2
    nlinarith [mul_nonneg ht.1 hp.le]
  have hmapsLeft : MapsTo D (Icc (-ε / 2) 0) (Iic d) := by
    intro t ht
    have hp := hcoefficient t ⟨ht.1, by linarith [ht.2]⟩
    change d + t * a + t ^ 2 * qA / 2 ≤ d
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ht.2 hp.le]
  have hcompRight := hright.comp_of_eq 0
    (hD.hasDerivWithinAt (s := Icc 0 (ε / 2))) hmapsRight hD0.symm
  have hcompRight' : HasDerivWithinAt (B ∘ D) (bright * a) (Ici 0) 0 :=
    hcompRight.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith))
  have hcompLeft := hleft.comp_of_eq 0
    (hD.hasDerivWithinAt (s := Icc (-ε / 2) 0)) hmapsLeft hD0.symm
  have hcompLeft' : HasDerivWithinAt (B ∘ D) (bleft * a) (Iic 0) 0 :=
    hcompLeft.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE (by linarith))
  have hHright : HasDerivWithinAt H (y - bright * a) (Ici 0) 0 :=
    hY.hasDerivWithinAt.sub hcompRight'
  have hHleft : HasDerivWithinAt H (y - bleft * a) (Iic 0) 0 :=
    hY.hasDerivWithinAt.sub hcompLeft'
  have hHmax : IsLocalMax H 0 := hmax
  have hrightSign := right_derivative_nonpos hHright hHmax
  have hnegmaps : MapsTo (fun t : ℝ => -t) (Ici 0) (Iic 0) := by
    intro t ht
    exact neg_nonpos.mpr ht
  have hHneg : HasDerivWithinAt (H ∘ fun t : ℝ => -t)
      ((y - bleft * a) * (-1)) (Ici 0) 0 :=
    hHleft.comp_of_eq 0 (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt hnegmaps (by simp)
  have hmaxneg : IsLocalMax (H ∘ fun t : ℝ => -t) 0 := by
    have hneg : Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
      simpa only [neg_zero] using continuous_neg.tendsto (0 : ℝ)
    have ht := hneg.eventually (show ∀ᶠ t : ℝ in nhds 0, H t ≤ H 0 from hHmax)
    change ∀ᶠ t : ℝ in nhds 0, H (-t) ≤ H (-0)
    simpa only [neg_zero] using ht
  have hleftSign := right_derivative_nonpos hHneg hmaxneg
  constructor <;> linarith

end Erdos1017.SmoothContact

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Global benchmark-excess maximality brackets this original stationary
multiplier by the actual left and right benchmark derivatives. The bounded
transverse direction and both genuine density-changing sides are derived. -/
theorem full_stationary_multiplier_mem_slope_interval (W : Model Ω μ) (hW : FullFeasible W)
    (hmax : ∀ (η : Measure Ω) [IsProbabilityMeasure η] (U : Model Ω η),
      FullFeasible U → objective U - benchmark (density U) ≤
        objective W - benchmark (density W))
    {bleft bright : ℝ}
    (hleft : HasDerivWithinAt benchmark bleft (Iic (density W)) (density W))
    (hright : HasDerivWithinAt benchmark bright (Ici (density W)) (density W))
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hnonconstant : ¬ ∃ a : ℝ, ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = a) :
    m ∈ Icc bleft bright := by
  have hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0 := by
    intro hz
    apply hnonconstant
    exact (Variation.kernel_weightFirstVariation_eq_zero_iff (adjacencyKernel W)
      (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)).mp hz
  have hex : ∃ f : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) f ≠ 0 := by
    by_contra h
    push Not at h
    exact hregular (LinearMap.ext h)
  obtain ⟨g, hg⟩ := hex
  have hpositive : ∃ f : Variation.WeightDirections μ,
      0 < Variation.weightFirstVariation (adjacencyOperator W) f := by
    rcases lt_or_gt_of_ne hg with hneg | hpos
    · exact ⟨-g, by simpa only [map_neg] using neg_pos.mpr hneg⟩
    · exact ⟨g, hpos⟩
  obtain ⟨f, hf⟩ := hpositive
  have hfirst := firstVariation_identity_of_shifted_zero W m
    (shiftedFirstVariation_zero_of_stationary W m ν hrow)
  have hcharge := LinearMap.congr_fun hfirst f
  simp only [LinearMap.smul_apply, smul_eq_mul] at hcharge
  have ha : 0 < Variation.weightFirstVariation (adjacencyOperator W) f / 2 := by positivity
  have hbracket := SmoothContact.quadratic_one_sided_first_variation ha hleft hright
    (full_benchmark_reweight_local_max W hW hmax f)
  have hy : Variation.weightFirstVariation (chargeOperator W) f / 2 =
      m * (Variation.weightFirstVariation (adjacencyOperator W) f / 2) := by
    rw [hcharge]
    ring
  rw [hy] at hbracket
  exact ⟨(mul_le_mul_iff_of_pos_right ha).mp hbracket.1,
    (mul_le_mul_iff_of_pos_right ha).mp hbracket.2⟩

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual strict-gap structure supplies nonconstant degree for the
same class member. Only its genuine one-sided benchmark derivatives and
global excess comparison remain contact inputs. -/
theorem FullStationaryClass.multiplier_mem_one_sided_slopes_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ (η : Measure Ω) [IsProbabilityMeasure η] (U : Model Ω η),
      FullFeasible U → objective U - benchmark (density U) ≤
        objective W - benchmark (density W))
    {bleft bright : ℝ} (hleft : HasDerivWithinAt benchmark bleft (Iic d) d)
    (hright : HasDerivWithinAt benchmark bright (Ici d) d) : m ∈ Icc bleft bright := by
  have hs := hW.strict_gap_structure hd hgap
  apply full_stationary_multiplier_mem_slope_interval W hW.full hmax
    (hW.density_eq ▸ hleft) (hW.density_eq ▸ hright) m _ hW.stationary hs.nonconstant_degree

end Erdos1017.CappedModel

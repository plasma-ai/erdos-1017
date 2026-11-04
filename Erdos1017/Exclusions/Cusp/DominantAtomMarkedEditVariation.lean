module

public import Erdos1017.Exclusions.Cusp.DominantAtomMarkedEditValues
public import Erdos1017.Exclusions.Cusp.DominantAtomMarkedEditCorrection
public import Erdos1017.Exclusions.Common.CopyWeightExpansion
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Variation of the dominant-atom marked edit

Every bounded pair kernel has the exact quadratic moment under a bounded
probability reweighting, and the original multiplier pays the marked U-P filling
once all positive U-exterior charges, including the whole remainder, are
removed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every bounded original pair kernel has the exact quadratic moment
under the same actual bounded probability reweighting. -/
theorem pairIntegral_vertexWeight_curve (u : Variation.WeightDirections μ) (s : ℝ)
    (hs : ‖s • u‖ < 1) (K : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (B : ℝ) (hB : ∀ x y, ‖K x y‖ ≤ B) :
    (∫ p : Ω × Ω, K p.1 p.2
      ∂(weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))).prod
        (weightedMeasure (μ := μ) (Variation.vertexWeight (s • u)))) =
      (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) +
        s * (∫ p : Ω × Ω, K p.1 p.2 * Variation.directionToL2 u p.1 +
          K p.1 p.2 * Variation.directionToL2 u p.2 ∂μ.prod μ) +
        s ^ 2 * (∫ p : Ω × Ω, K p.1 p.2 * Variation.directionToL2 u p.2 *
          Variation.directionToL2 u p.1 ∂μ.prod μ) := by
  have hbound : ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B := Eventually.of_forall (fun p => hB _ _)
  have hu := (Lp.memLp (Variation.directionToL2 u)).integrable (by norm_num)
  have hi : Integrable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound hK.aestronglyMeasurable B hbound
  have hfirst : Integrable (fun p : Ω × Ω => K p.1 p.2 * Variation.directionToL2 u p.1) (μ.prod μ) := by
    simpa only [mul_one] using KernelOperator.integrable_kernel_bilinear hK.aestronglyMeasurable
      hbound (integrable_const (1 : ℝ)) hu
  have hsecond : Integrable (fun p : Ω × Ω => K p.1 p.2 * Variation.directionToL2 u p.2) (μ.prod μ) := by
    simpa only [mul_one] using KernelOperator.integrable_kernel_bilinear hK.aestronglyMeasurable
      hbound hu (integrable_const (1 : ℝ))
  have hquad := KernelOperator.integrable_kernel_bilinear hK.aestronglyMeasurable hbound hu hu
  rw [integral_weightedMeasure_prod _ (Lp.aestronglyMeasurable _).aemeasurable
    (Variation.vertexWeight_nonnegative _ hs)]
  have he : (fun p : Ω × Ω => K p.1 p.2 * Variation.vertexWeight (s • u) p.2 *
      Variation.vertexWeight (s • u) p.1) =ᵐ[μ.prod μ]
      fun p => K p.1 p.2 + s * (K p.1 p.2 * Variation.directionToL2 u p.1 +
        K p.1 p.2 * Variation.directionToL2 u p.2) +
        s ^ 2 * (K p.1 p.2 * Variation.directionToL2 u p.2 * Variation.directionToL2 u p.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (vertexWeight_curve_ae u s),
      Measure.quasiMeasurePreserving_snd.ae (vertexWeight_curve_ae u s)] with p hp hq
    rw [hp, hq]
    ring
  have hadd := integral_add (hi.add ((hfirst.add hsecond).const_mul s)) (hquad.const_mul (s ^ 2))
  have hfirstadd := integral_add hi ((hfirst.add hsecond).const_mul s)
  simp only [Pi.add_apply] at hadd hfirstadd
  rw [integral_congr_ae he, hadd, hfirstadd, integral_const_mul, integral_const_mul]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The original multiplier pays the actual marked U-P filling after all
positive U-exterior charges, including the whole remainder, are removed.
The exact density correction is a constructed bounded old-law reweighting. -/
theorem dominant_marked_cost_payment (W : Model Ω μ) {m d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (I P U : Set Ω)
    (hI : MeasurableSet I) (hP : MeasurableSet P) (hUmeas : MeasurableSet U)
    (hU : U ⊆ DominantAtomMarkedEdit.exterior I P) (hIP : Disjoint I P)
    (hIPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ P →
      PhysicalRepresentative.adjacency W m p.1 p.2 = false)
    (hUPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ U → p.2 ∈ P →
      PhysicalRepresentative.adjacency W m p.1 p.2 = false) :
    -m * (∫ p : Ω × Ω, DominantAtomMarkedEdit.densityLinear
      (PhysicalRepresentative.adjacency W m) P U p.1 p.2 ∂μ.prod μ) ≤
        ∫ p : Ω × Ω, DominantAtomMarkedEdit.costLinear
          (PhysicalRepresentative.charge W m) I P U p.1 p.2 ∂μ.prod μ := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let K := DominantAtomMarkedEdit.densityLinear A P U
  let R := DominantAtomMarkedEdit.costLinear Y I P U
  let Q := DominantAtomMarkedEdit.costQuadratic Y U
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hK := DominantAtomMarkedEdit.measurable_densityLinear A P U hA hP hUmeas
  have hR := DominantAtomMarkedEdit.measurable_costLinear Y I P U hY hI hP hUmeas
  have hQ := DominantAtomMarkedEdit.measurable_costQuadratic Y U hY hUmeas
  have hstructure := hW.strict_gap_structure hd hgap
  have hdis : Disjoint U P := disjoint_left.mpr (fun _ hu hp => hU hu (Or.inr hp))
  have hfull := PhysicalRepresentative.full_feasible W hW.full m hstructure.strict_support hW.deterministic
  obtain ⟨u, hu⟩ : ∃ u : Variation.WeightDirections μ,
      0 < Variation.weightFirstVariation (adjacencyOperator W) u := by
    have hex : ∃ u, Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 := by
      by_contra h
      push Not at h
      exact hstructure.regular (LinearMap.ext h)
    obtain ⟨u, hu⟩ := hex
    rcases lt_or_gt_of_ne hu with hu | hu
    · exact ⟨-u, by simpa using neg_pos.mpr hu⟩
    · exact ⟨u, hu⟩
  have hm := firstVariation_identity_of_shifted_zero W m
    (shiftedFirstVariation_zero_of_stationary W m (2 * (c - m * d)) hW.stationary)
  have hmfirst := LinearMap.congr_fun hm u
  simp only [LinearMap.smul_apply, smul_eq_mul] at hmfirst
  let first := fun H : Ω → Ω → ℝ => ∫ p : Ω × Ω,
    H p.1 p.2 * Variation.directionToL2 u p.1 + H p.1 p.2 * Variation.directionToL2 u p.2 ∂μ.prod μ
  let second := fun H : Ω → Ω → ℝ => ∫ p : Ω × Ω,
    H p.1 p.2 * Variation.directionToL2 u p.2 * Variation.directionToL2 u p.1 ∂μ.prod μ
  let a := ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ
  let R₀ := ∫ p : Ω × Ω, R p.1 p.2 ∂μ.prod μ
  let Q₀ := ∫ p : Ω × Ω, Q p.1 p.2 ∂μ.prod μ
  let b := Variation.weightFirstVariation (adjacencyOperator W) u / 2
  let d₂ := Variation.weightSecondVariation (adjacencyOperator W) u u / 2
  let B := Variation.weightFirstVariation (chargeOperator W) u / 2
  let D := Variation.weightSecondVariation (chargeOperator W) u u / 2
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity)
  have hεle : ε ≤ 1 := (div_le_one (by positivity : 0 < ‖u‖ + 1)).mpr (by linarith [norm_nonneg u])
  have hsign : -R₀ - m * a ≤ 0 := by
    apply Variation.marking_sign_of_local_max a b (first K) d₂ (second K)
      (-R₀) Q₀ B (-first R) (first Q) D (-second R) (second Q) m
      (by dsimp only [b]; linarith) (by dsimp only [B, b]; linarith) ε hε
    intro alpha s halpha hsmallalpha hs hroot
    have hnorm : ‖s • u‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
      nlinarith only [hmul, hεeq, hs, norm_nonneg u]
    let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))
    let : IsProbabilityMeasure ν := weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative _ hnorm) (Variation.vertexWeight_integral _)
    have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
    let alpha' : unitInterval := ⟨alpha, halpha, hsmallalpha.le.trans hεle⟩
    have hden := DominantAtomMarkedEdit.density_marked (μ := ν) alpha' A P U hA hP hUmeas hdis
      (PhysicalRepresentative.adjacency_symm W m)
    have hcost := DominantAtomMarkedEdit.objective_marked (μ := ν) alpha' Y I P U hY hI hP hUmeas
      hU (PhysicalRepresentative.charge_symm W m) 3 (by norm_num) (PhysicalRepresentative.charge_bound W m)
    have hdold := physicalDensity_vertexWeight_curve W m hstructure.strict_support u s hnorm
    have hcold := physicalObjective_vertexWeight_curve W m hstructure.strict_support u s hnorm
    have hKcurve := pairIntegral_vertexWeight_curve u s hnorm K hK 1
      (DominantAtomMarkedEdit.densityLinear_bound A P U)
    have hRcurve := pairIntegral_vertexWeight_curve u s hnorm R hR 6
      (by
        intro x y
        simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using
          DominantAtomMarkedEdit.costLinear_bound Y I P U 3 (by norm_num)
            (PhysicalRepresentative.charge_bound W m) x y)
    have hQcurve := pairIntegral_vertexWeight_curve u s hnorm Q hQ 3
      (DominantAtomMarkedEdit.costQuadratic_bound Y U 3 (by norm_num) (PhysicalRepresentative.charge_bound W m))
    rw [hW.density_eq] at hdold
    rw [hW.objective_eq] at hcold
    change FiniteCappedSamplingCost.physicalDensity ν A = d + _ at hdold
    change FiniteCappedSamplingCost.physicalObjective ν Y = c + _ at hcold
    change (∫ p : Ω × Ω, K p.1 p.2 ∂ν.prod ν) = a + s * first K + s ^ 2 * second K at hKcurve
    change (∫ p : Ω × Ω, R p.1 p.2 ∂ν.prod ν) = R₀ + s * first R + s ^ 2 * second R at hRcurve
    change (∫ p : Ω × Ω, Q p.1 p.2 ∂ν.prod ν) = Q₀ + s * first Q + s ^ 2 * second Q at hQcurve
    rw [hdold, hKcurve] at hden
    rw [hcold, hRcurve, hQcurve] at hcost
    have hdeneq : FiniteCappedSamplingCost.physicalDensity (universalMeasure ν alpha')
        (DominantAtomMarkedEdit.adjacency A P U) = d := by
      rw [hden]
      change d + _ + alpha * (a + s * first K + s ^ 2 * second K) = d
      dsimp only [b, d₂] at hroot
      nlinarith only [hroot]
    have hmax := DominantAtomMarkedEdit.objective_le_densityLimit_ac A Y I P U hA hY hI hP hUmeas hU hIP
      (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m)
      3 (by norm_num) (PhysicalRepresentative.charge_bound W m)
      (PhysicalRepresentative.charge_zero_of_nonedge W m) hIPmiss hUPmiss hfull ν hac alpha'
    rw [hdeneq, ← hW.optimal, hcost] at hmax
    dsimp only [R₀, Q₀, B, D]
    change _ ≤ c at hmax
    nlinarith only [hmax]
  change -m * a ≤ R₀
  linarith only [hsign]

end Erdos1017.CappedModel

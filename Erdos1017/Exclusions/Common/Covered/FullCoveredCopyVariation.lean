module

public import Erdos1017.Exclusions.Common.Covered.CoveredPairCopy
public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyValues
public import Erdos1017.Exclusions.Common.CopyWeightExpansion
public import Erdos1017.Exclusions.Common.CopyMassCorrection
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Shifted-row inequality from a covered pair copy

A full optimum in `FullStationaryClass` with an independent positive-charge
cover obeys its own shifted pair-copy row inequality for either source-charge
sign (`ae_covered_copy_shifted_row_le_stationary`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual full optimum with an independent positive-charge cover obeys
its own shifted pair-copy row inequality for either source-charge sign.
Actual feasible copies and bounded exact-density correction are constructed;
no selected row structure or copied-model certificate is an input. -/
theorem FullStationaryClass.ae_covered_copy_shifted_row_le_stationary
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (I : Set Ω) (hI : MeasurableSet I)
    (hind : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ I → p.2 ∈ I → adjacencyKernel W p.1 p.2 = 0)
    (hbody : ∀ᵐ p ∂μ.prod μ,
      p.1 ∉ I → p.2 ∉ I → chargeKernel W p.1 p.2 ≤ 0) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      (∫ z, IndependentAtomCopy.rowCharge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) I p.1 p.2 z ∂μ) -
        m * (∫ z, IndependentAtomCopy.rowAdjacency
          (PhysicalRepresentative.adjacency W m) p.1 p.2 z ∂μ) ≤ 2 * (c - m * d) := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hbound := PhysicalRepresentative.charge_bound W m
  have hYzero := PhysicalRepresentative.charge_zero_of_nonedge W m
  have hstructure := hW.strict_gap_structure hd hgap
  have hindependent : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false := by
    filter_upwards [hind, PhysicalRepresentative.adjacency_moment_ae_eq W m
      hstructure.strict_support] with p hp he hx hy
    have hz := hp hx hy
    change W.moment CappedColor.adjacency p = 0 at hz
    change W.moment CappedColor.adjacency p = (if A p.1 p.2 = true then 1 else 0) at he
    exact Bool.eq_false_iff.mpr (fun ha => by simp [ha, hz] at he)
  have hbodyY : ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I → Y p.1 p.2 ≤ 0 := by
    filter_upwards [hbody, PhysicalRepresentative.charge_ae_eq W m hstructure.strict_support]
      with p hp he hx hy
    change Y p.1 p.2 = chargeKernel W p.1 p.2 at he
    rw [he]
    exact hp hx hy
  have hcomparison := IndependentAtomCopy.ae_covered_copy_objective_le_densityLimit_ac
    A (PhysicalRepresentative.adjacency_symm W m) hA Y hY
    (PhysicalRepresentative.charge_symm W m) I hI 3 (by norm_num) hbound hindependent hbodyY
    (PhysicalRepresentative.full_feasible W hW.full m hstructure.strict_support hW.deterministic)
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
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity)
  filter_upwards [hcomparison]
    with p hp hxI hyI hxy
  let arow := IndependentAtomCopy.rowAdjacency A p.1 p.2
  let yrow := IndependentAtomCopy.rowCharge A Y I p.1 p.2
  have ha : StronglyMeasurable arow :=
    (IndependentAtomCopy.measurable_rowAdjacency A hA p.1 p.2).stronglyMeasurable
  have hy : StronglyMeasurable yrow :=
    (IndependentAtomCopy.measurable_rowCharge A hA Y hY I hI p.1 p.2).stronglyMeasurable
  have habound : ∀ z, ‖arow z‖ ≤ 1 := by
    intro z
    dsimp only [arow, IndependentAtomCopy.rowAdjacency]
    split_ifs <;> norm_num
  have hybound : ∀ z, ‖yrow z‖ ≤ 9 := by
    intro z
    simpa only [show (3 : ℝ) * 3 = 9 by norm_num] using
      IndependentAtomCopy.rowCharge_bound A Y I 3 (by norm_num) hbound p.1 p.2 z
  let a := (∫ z, arow z ∂μ) - 2 * d
  let b := Variation.weightFirstVariation (adjacencyOperator W) u / 2
  let b₂ := Variation.weightSecondVariation (adjacencyOperator W) u u / 2
  let a₁ := ∫ z, arow z * Variation.directionToL2 u z ∂μ
  let C := (∫ z, yrow z ∂μ) - 2 * c
  let B := Variation.weightFirstVariation (chargeOperator W) u / 2
  let B₂ := Variation.weightSecondVariation (chargeOperator W) u u / 2
  let C₁ := ∫ z, yrow z * Variation.directionToL2 u z ∂μ
  have hsign : C - m * a ≤ 0 := by
    apply Variation.copy_mass_sign_of_local_max a (-d) b a₁ b₂ C (-c) B C₁ B₂ m
      (by dsimp only [b]; linarith) (by dsimp only [B, b]; linarith) ε hε
    intro τ s hτ hτε hs hroot
    have hnorm : ‖s • u‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
      nlinarith [norm_nonneg u]
    let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))
    let : IsProbabilityMeasure ν := weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative _ hnorm) (Variation.vertexWeight_integral _)
    have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
    have hden := IndependentAtomCopy.density_marked_mass (μ := ν) A hA p.1 p.2 τ hτ
    have hcost := IndependentAtomCopy.objective_marked_mass (μ := ν)
      A hA Y hY I hI 3 (by norm_num) hbound p.1 p.2 hYzero τ hτ
    have hdold := physicalDensity_vertexWeight_curve W m hstructure.strict_support u s hnorm
    have hcold := physicalObjective_vertexWeight_curve W m hstructure.strict_support u s hnorm
    have harow := integral_vertexWeight_curve u s hnorm arow ha 1 habound
    have hyrow := integral_vertexWeight_curve u s hnorm yrow hy 9 hybound
    rw [hW.density_eq] at hdold
    rw [hW.objective_eq] at hcold
    change FiniteCappedSamplingCost.physicalDensity ν A = _ at hdold
    change FiniteCappedSamplingCost.physicalObjective ν Y = _ at hcold
    change (∫ z, arow z ∂ν) = _ at harow
    change (∫ z, yrow z ∂ν) = _ at hyrow
    change FiniteCappedSamplingCost.physicalDensity _ _ =
      (FiniteCappedSamplingCost.physicalDensity ν A + τ * ∫ z, arow z ∂ν) / (1 + τ) ^ 2 at hden
    change FiniteCappedSamplingCost.physicalObjective _ _ =
      (FiniteCappedSamplingCost.physicalObjective ν Y + τ * ∫ z, yrow z ∂ν) / (1 + τ) ^ 2 at hcost
    rw [hdold, harow] at hden
    rw [hcold, hyrow] at hcost
    have hdeneq : FiniteCappedSamplingCost.physicalDensity
        (universalMeasure ν (universalFraction τ hτ))
        (IndependentAtomCopy.markedAdjacency A p.1 p.2) = d := by
      rw [hden]
      apply (div_eq_iff (by positivity : (1 + τ) ^ 2 ≠ 0)).mpr
      dsimp only [a, b, b₂, a₁] at hroot
      nlinarith only [hroot]
    have hmax := hp hxI hyI hxy ν hac (universalFraction τ hτ)
    change FiniteCappedSamplingCost.physicalObjective _
      (IndependentAtomCopy.markedCharge A Y I p.1 p.2) ≤ _ at hmax
    rw [hdeneq, ← hW.optimal, hcost] at hmax
    have hmul := (div_le_iff₀ (by positivity : 0 < (1 + τ) ^ 2)).mp hmax
    dsimp only [C, B, B₂, C₁]
    nlinarith only [hmul]
  change (∫ z, yrow z ∂μ) - m * (∫ z, arow z ∂μ) ≤ _
  dsimp only [C, a] at hsign
  linarith

end Erdos1017.CappedModel

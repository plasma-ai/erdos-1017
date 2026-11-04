module

public import Erdos1017.Exclusions.Common.Covered.CoveredPairCopy
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyUniversal
public import Erdos1017.Exclusions.Common.SelectedAtomCopyVariation
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality

/-!
# Pair copies in the selected zero-body model

The zero-body geometry licenses the full covered pair copy under all absolutely
continuous reweightings, the copy obeys the shifted-row bound for either
source-charge sign, and every adjacent exterior pair obeys the original
missing-row copy inequality (`ae_zero_body_copy_inequality`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Actual zero-body geometry licenses the full covered pair copy under
all original absolutely continuous probability reweightings. -/
theorem ae_covered_copy_objective_le_densityLimit_ac
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      ∀ (ν : Measure Ω) [IsProbabilityMeasure ν], ν ≪ μ → ∀ t : unitInterval,
        FiniteCappedSamplingCost.physicalObjective (universalMeasure ν t)
            (IndependentAtomCopy.markedCharge (PhysicalRepresentative.adjacency W m)
              (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val} p.1 p.2) ≤
          FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
            (universalMeasure ν t)
            (IndependentAtomCopy.markedAdjacency
              (PhysicalRepresentative.adjacency W m) p.1 p.2)) := by
  have hbody : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.charge W m p.1 p.2 ≤ 0 := by
    filter_upwards [S.zero_body_ae_charge_nonpositive r hzero,
      PhysicalRepresentative.charge_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with p hb he hx hy
    exact he.trans_le (hb hx hy)
  exact IndependentAtomCopy.ae_covered_copy_objective_le_densityLimit_ac
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.adjacency_symm W m)
    (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.charge W m)
    (PhysicalRepresentative.measurable_charge W m) (PhysicalRepresentative.charge_symm W m)
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 3 (by norm_num)
    (PhysicalRepresentative.charge_bound W m)
    (S.ae_root_fiber_physical_independent r hW hd hgap) hbody
    (PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic)

/-- The covered pair copy obeys the original shifted-row bound for either
source-charge sign. Genuine full scalar competitors and bounded density
correction supply the first variation, including negative source edges. -/
theorem ae_covered_copy_shifted_row_le_stationary (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ,
      S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      (∫ z, IndependentAtomCopy.rowCharge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val} p.1 p.2 z ∂μ) -
        m * (∫ z, IndependentAtomCopy.rowAdjacency
          (PhysicalRepresentative.adjacency W m) p.1 p.2 z ∂μ) ≤ 2 * (c - m * d) := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hI := (S.hfibers r.val r.property).1
  have hbound := PhysicalRepresentative.charge_bound W m
  have hYzero := PhysicalRepresentative.charge_zero_of_nonedge W m
  have hstructure := hW.strict_gap_structure hd hgap
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
  filter_upwards [S.ae_covered_copy_objective_le_densityLimit_ac r hW hd hgap hzero]
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

/-- Every actual adjacent exterior pair in the zero-body model obeys
the original missing-row copy inequality. Negative source charges are
licensed by the proved covered copy, not the positive-source theorem. -/
theorem ae_zero_body_copy_inequality (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      μ.real {x | S.ρ x = r.val} * PhysicalRepresentative.charge W m p.1 p.2 +
        (2 * (c - m * d) + m) - m * μ.real
          (IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.1 ∩
            IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.2) ≤
        (∫ z in IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.1,
          PhysicalRepresentative.charge W m p.2 z ∂μ) +
        (∫ z in IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.2,
          PhysicalRepresentative.charge W m p.1 z ∂μ) := by
  have hN := S.root_neutral_of_zero_body r hW hd hgap hzero
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  have huniversal := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_physical_adjacency r hW hd hgap hN)
  have hrow : ∀ᵐ x ∂μ, S.ρ x ≠ r.val → ∀ᵐ z ∂μ, z ∈ I → A x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod huniversal] with x hx hxr
    filter_upwards [hx] with z hz hzr
    change PhysicalRepresentative.adjacency W m x z = true
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact (hz hzr).mpr hxr
  have hflat := S.ae_physical_shifted_stationary hW hd hgap
  filter_upwards [S.ae_covered_copy_shifted_row_le_stationary r hW hd hgap hzero,
    Measure.quasiMeasurePreserving_fst.ae hrow, Measure.quasiMeasurePreserving_snd.ae hrow,
    Measure.quasiMeasurePreserving_fst.ae hflat, Measure.quasiMeasurePreserving_snd.ae hflat]
    with p hp hx hy hfx hfy hpx hpy hA
  have hcommon : ∀ᵐ z ∂μ, z ∈ I → A p.1 z = true ∧ A p.2 z = true := by
    filter_upwards [hx hpx, hy hpy] with z hx hy hi
    exact ⟨hx hi, hy hi⟩
  have he := IndependentAtomCopy.integrated_row_inventory A
    (PhysicalRepresentative.measurable_adjacency W m) Y
    (PhysicalRepresentative.measurable_charge W m) I (S.hfibers r.val r.property).1
    3 (by norm_num) (PhysicalRepresentative.charge_bound W m)
    (PhysicalRepresentative.charge_zero_of_nonedge W m) m p.1 p.2 hcommon
  have hb := hp hpx hpy hA
  change (∫ z, IndependentAtomCopy.rowCharge A Y I p.1 p.2 z ∂μ) -
    m * (∫ z, IndependentAtomCopy.rowAdjacency A p.1 p.2 z ∂μ) ≤ _ at hb
  rw [hfx, hfy] at he
  dsimp only [I, A, Y] at he hb
  linarith only [he, hb]

end Erdos1017.CappedModel.SelectedHighLowStructure

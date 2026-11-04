module

public import Erdos1017.Exclusions.Cusp.SelectedCuspFourSourceGuards
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceFinitePivot
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceScore

/-!
# Normalized child for the fourth-cusp source

A fully feasible child supplies the normalized signed score at the fourth cusp;
its four source resources use one original budget
(`exists_cusp_four_normalized_child`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

set_option maxHeartbeats 800000 in
/-- A genuine fully feasible child supplies the normalized signed score.
Its four source resources use one original budget, and its correlated
resource bound comes from an actual finite original-law comparison. -/
theorem exists_cusp_four_normalized_child (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 15 / 32) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) :
    let T := R.height
    let X := S.originalAtomMass i / T
    let t := μ.real (R.cuspSourceRemainder i) / T
    let y := (1 / 16 : ℝ) / T ^ 2
    let ρ := (3 / 2 + m) / (-m - 1)
    let q := R.cuspOutsideSquares r i / T ^ 2
    let e := (c - 3 / 64) / T ^ 2
    let V := kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ R.cuspPartialFlow) / T ^ 2
    let cI := R.cuspPeakCredit r i / T
    let CJ := R.cuspRemainderCredit r i / T ^ 2
    let Phi := R.cuspCrossEnergy i / T
    let FJ := R.cuspRemainderEnergy i / T ^ 2
    0 < e ∧ 0 ≤ V ∧ 0 ≤ cI ∧ 0 ≤ CJ ∧ 0 ≤ Phi ∧ 0 ≤ FJ ∧
      FJ / 2 ≤ ((t + Real.sqrt (t ^ 2 + 2 * X * t)) / 2) * Phi ∧
      e + V / 2 + (X * cI + CJ + X * Phi + FJ / 2) ≤
        (-m - 1) / 2 * (ρ * (1 - y) - q) ∧
      ∃ C : ℝ, C ≤ max (1 / 4) q ∧
        C - 1 / 4 = e + V / 2 + (-m - 1) / 2 *
          (ρ * y + 1 / 2 + (3 + 2 * ρ) * q) -
          ((1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
            ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t)) := by
  let T := R.height
  let A := S.originalAtomMass i
  let b := S.originalAtomMass r
  let z := μ.real (R.cuspSourceRemainder i)
  let E := kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow)
  let V := kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow)
  let cI := R.cuspPeakCredit r i
  let CJ := R.cuspRemainderCredit r i
  let Phi := R.cuspCrossEnergy i
  let FJ := R.cuspRemainderEnergy i
  let Q := R.cuspOutsideSquares r i
  let e := c - 3 / 64
  let ρ := (3 / 2 + m) / (-m - 1)
  have hdk' : d = (1 - 1 / (4 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  have hp := hW.cusp_contact_parameters 4 (by norm_num) hdk' hgap hglobal
  have hd := hp.1
  have hell : -m ∈ Ioo (11 / 10 : ℝ) (3 / 2) := by
    have h := hp.2.1
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hden : 0 < -m - 1 := by linarith only [hell.1]
  have he : 0 < e := by
    have h := hp.2.2.2.2
    rw [hdk] at h
    norm_num at h
    dsimp [e]
    linarith only [h]
  have hsourceEdge := R.cusp_source_edge_integral_pos 4 (by norm_num) hdk' hW hgap hglobal
  have hz : 0 < z := R.cuspSourceRemainder_mass_pos i hsourceEdge
  have hA : 0 < A := ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne'
    (measure_ne_top μ _)
  have hT : 0 < T := R.height_pos
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  have hs : A + z = μ.real R.cuspSource := by
    have h := R.cuspSource_mass_decomposition i
    rwa [R.cuspSourcePeak_mass_original i hinside] at h
  have hheight : T = b + A + z := by
    have h := R.singleton_height_eq_mass_add_source r hr
    change R.height = b + μ.real (S.reverseCompulsorySource {r}) at h
    have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
    rw [← hc, ← hs] at h
    exact h.trans (by ring)
  have hV : 0 ≤ V := R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap
    R.measurableSet_source.compl
  have hcI : 0 ≤ cI := R.cuspPeakCredit_nonnegative hW hd hgap r i hr hinside
  have hCJ : 0 ≤ CJ := R.cuspRemainderCredit_nonnegative hW hd hgap r i hr
  have hPhi : 0 ≤ Phi := R.cuspCrossEnergy_nonnegative hW i
  have hFJ : 0 ≤ FJ := R.cuspRemainderEnergy_nonnegative hW i
  have htrace := R.cusp_source_finite_pivot_energy_le r i hW hd hgap hr hinside hpeak hsourceEdge
  change FJ / 2 ≤ (z + Real.sqrt (z ^ 2 + 2 * A * z)) / 2 * Phi at htrace
  have hfull := R.cusp_full_flow_energy hW hd hgap r i hr hinside
  change E = V + 2 * (A * cI + CJ) + 2 * A * Phi + FJ at hfull
  have hbudget := R.cusp_endpoint_source_budget r i 4 (by norm_num)
    hdk' hW hgap hglobal hr hinside
  norm_num only [Nat.cast_ofNat] at hbudget
  change e + E / 2 + (-m - 1) * Q / 2 ≤ (3 / 2 + m) * (T ^ 2 - 1 / 16) / 2 at hbudget
  have hrawbudget : e + V / 2 + (A * cI + CJ + A * Phi + FJ / 2) ≤
      (3 / 2 + m) * (T ^ 2 - 1 / 16) / 2 - (-m - 1) * Q / 2 := by
    linarith only [hfull, hbudget]
  have hvalue : c = (1 - 1 / 4 : ℝ) * (1 / 4 : ℝ) ^ 2 + e := by dsimp [e]; ring
  obtain ⟨child, _, hcost, hscore⟩ := R.exists_cusp_source_child_score r i hW hd hgap hr
    (show 1 - 2 * d = (1 / 4 : ℝ) ^ 2 by norm_num [hdk]) hvalue hinside hsourceEdge
  change objective child ≤ max (T ^ 2 / 4) Q at hcost
  change objective child - T ^ 2 / 4 =
    e + (2 - 2 * (1 / 4) - (-m)) * (1 / 4) ^ 2 / 2 + (-m) * Q / 2 + V / 2 +
      (-m - 1) * T ^ 2 / 4 - (T / 2 - A) * cI - ((T / 2 - z) / z) * CJ +
      ((T / 2 - A) * (T / 2 - z) / z) * Phi - (A + b) * FJ / (2 * z) at hscore
  change 0 < e / T ^ 2 ∧ 0 ≤ V / T ^ 2 ∧ 0 ≤ cI / T ∧ 0 ≤ CJ / T ^ 2 ∧
    0 ≤ Phi / T ∧ 0 ≤ FJ / T ^ 2 ∧
    FJ / T ^ 2 / 2 ≤ ((z / T + Real.sqrt ((z / T) ^ 2 + 2 * (A / T) * (z / T))) / 2) *
      (Phi / T) ∧
    e / T ^ 2 + V / T ^ 2 / 2 + ((A / T) * (cI / T) + CJ / T ^ 2 +
      (A / T) * (Phi / T) + FJ / T ^ 2 / 2) ≤
      (-m - 1) / 2 * (ρ * (1 - (1 / 16 : ℝ) / T ^ 2) - Q / T ^ 2) ∧
    ∃ C : ℝ, C ≤ max (1 / 4) (Q / T ^ 2) ∧
      C - 1 / 4 = e / T ^ 2 + V / T ^ 2 / 2 + (-m - 1) / 2 *
        (ρ * ((1 / 16 : ℝ) / T ^ 2) + 1 / 2 + (3 + 2 * ρ) * (Q / T ^ 2)) -
        ((1 / 2 - A / T) * (cI / T) + ((1 / 2 - z / T) / (z / T)) * (CJ / T ^ 2) -
          ((1 / 2 - A / T) * (1 / 2 - z / T) / (z / T)) * (Phi / T) +
          (1 - z / T) * (FJ / T ^ 2) / (2 * (z / T)))
  refine ⟨div_pos he hT2, div_nonneg hV hT2.le, div_nonneg hcI hT.le,
    div_nonneg hCJ hT2.le, div_nonneg hPhi hT.le, div_nonneg hFJ hT2.le, ?_, ?_,
    objective child / T ^ 2, ?_, ?_⟩
  · have hsqrt : Real.sqrt ((z / T) ^ 2 + 2 * (A / T) * (z / T)) =
        Real.sqrt (z ^ 2 + 2 * A * z) / T := by
      rw [show (z / T) ^ 2 + 2 * (A / T) * (z / T) =
        (z ^ 2 + 2 * A * z) / T ^ 2 by field_simp]
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq hT.le]
    rw [hsqrt]
    have hl : FJ / T ^ 2 / 2 = (FJ / 2) / T ^ 2 := by ring
    have hr : ((z / T + Real.sqrt (z ^ 2 + 2 * A * z) / T) / 2) * (Phi / T) =
        ((z + Real.sqrt (z ^ 2 + 2 * A * z)) / 2 * Phi) / T ^ 2 := by ring
    rw [hl, hr]
    exact (div_le_div_iff_of_pos_right hT2).mpr htrace
  · have hl : e / T ^ 2 + V / T ^ 2 / 2 + ((A / T) * (cI / T) + CJ / T ^ 2 +
        (A / T) * (Phi / T) + FJ / T ^ 2 / 2) =
        (e + V / 2 + (A * cI + CJ + A * Phi + FJ / 2)) / T ^ 2 := by ring
    have hr : (-m - 1) / 2 * (ρ * (1 - (1 / 16 : ℝ) / T ^ 2) - Q / T ^ 2) =
        ((3 / 2 + m) * (T ^ 2 - 1 / 16) / 2 - (-m - 1) * Q / 2) / T ^ 2 := by
      dsimp [ρ]
      field_simp
    rw [hl, hr]
    exact (div_le_div_iff_of_pos_right hT2).mpr hrawbudget
  · rw [show max (1 / 4 : ℝ) (Q / T ^ 2) = max (T ^ 2 / 4) Q / T ^ 2 by
      rw [← max_div_div_right hT2.le]; congr 1; field_simp]
    exact (div_le_div_iff_of_pos_right hT2).mpr hcost
  · have hab : A + b = T - z := by linarith only [hheight]
    rw [show objective child / T ^ 2 - 1 / 4 =
      (objective child - T ^ 2 / 4) / T ^ 2 by field_simp, hscore, hab]
    dsimp [ρ]
    field_simp
    ring

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

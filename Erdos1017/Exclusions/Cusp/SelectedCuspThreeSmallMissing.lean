module

public import Erdos1017.Exclusions.Cusp.MarkedMissingEditVariation
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeNeighborhoodTrace
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopeUniversal

/-!
# The missing region exceeds gamma at the low-slope third cusp

At the selected low-slope third cusp the entire missing-region mass strictly
exceeds the original gamma; marked-source surgery excludes a nonuniversal peak
whose neighborhood body has no positive charge (`no_cusp_three_small_missing`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

/-- Actual marked-source surgery excludes a nonuniversal third-cusp peak
when its literal original neighborhood body has no positive charge. -/
theorem no_cusp_three_small_missing_of_nonpositive_body
    (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1))
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.rootNeighborhood i → p.2 ∈ S.rootNeighborhood i →
      PhysicalRepresentative.charge W m p.1 p.2 ≤ 0) : False := by
  let J := S.cuspThreeMissingRegion i
  let A := S.originalAtomMass i
  let t := μ.real J
  let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
  let v := ∫ p in J ×ˢ S.rootNeighborhood i, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  let FJ := ∫ p in J ×ˢ J, shiftedKernel W m p.1 p.2 ∂μ.prod μ
  have hreturn := S.cusp_three_missing_return i hdk hW hgap hglobal hell hpeak hnonuniv
  change 0 ≤ z ∧ 0 ≤ FJ ∧ 0 < v - 2 * z ∧
    (0 < z → 0 < FJ ∧ (2 + A / t) * z < v) ∧
    (z = 0 → FJ = 0 ∧ 0 < v) ∧ FJ ≤ 2 * (1 - m) * z at hreturn
  obtain ⟨hz, _, _, hpositive, hzero, hcap⟩ := hreturn
  have hsign := S.cusp_three_missing_edit_sign i hdk hW hgap hglobal hell hpeak hnonuniv hbody
  change (5 / 6) * v - FJ + (-2 * m - 5 / 3) * z ≤ 0 at hsign
  by_cases hz0 : z = 0
  · obtain ⟨hFJ, hv⟩ := hzero hz0
    rw [hz0, hFJ] at hsign
    linarith only [hv, hsign]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hv := (hpositive hzpos).2
    obtain ⟨_, hfloor, _⟩ := S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
    obtain ⟨ht, _, _, hsmall, _⟩ :=
      S.cusp_three_low_slope_missing_region i hdk hW hgap hglobal hell hpeak hnonuniv
    change 0 < t at ht
    change t < 2 / 39 at hsmall
    change 11 / 39 < A at hfloor
    have hratio : 11 / 2 < A / t := (lt_div_iff₀ ht).mpr (by linarith only [hsmall, hfloor])
    have hpaid := mul_nonneg (by linarith only [hratio] : (0 : ℝ) ≤ A / t - 11 / 2) hz
    nlinarith only [hv, hpaid, hcap, hsign, hzpos]

/-- At the selected low-slope third cusp, the entire missing-region mass
strictly exceeds the original gamma. Universal peaks and the original
neighborhood body's sign are derived internally before actual marking. -/
theorem no_cusp_three_small_missing (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hsmall : μ.real (S.cuspThreeMissingRegion i) ≤ 2 * (c - m * d) + m) : False := by
  have hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1) :=
    fun huniv => S.no_cusp_three_low_slope_universal_peak i hdk hW hgap hglobal hell hpeak huniv
  have hbody := S.cusp_three_small_missing_body_nonpos i hdk hW hgap hglobal hell hpeak hsmall
  exact S.no_cusp_three_small_missing_of_nonpositive_body i hdk hW hgap hglobal hell hpeak hnonuniv hbody

end Erdos1017.CappedModel.SelectedHighLowStructure

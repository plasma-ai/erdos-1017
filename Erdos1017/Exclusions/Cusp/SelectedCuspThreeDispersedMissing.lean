module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeDispersedComparison
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeMixedSourceTax
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeMissingInventory
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeMissingEdgeCap
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeSmallMissing
public import Erdos1017.Exclusions.Cusp.BenchmarkCuspThreeDispersedComparison

/-!
# No dispersed missing region at the low-slope third cusp

A dispersed missing region of a low-slope third-cusp common peak is impossible,
combining universality, the small missing region, and the mass and gamma windows
(`no_cusp_three_dispersed_missing`); the mixed-source missing row square equals
the region-neighborhood missing indicator square.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [MetricSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] in
/-- The mixed-source missing row square is the literal original
region-neighborhood missing indicator square. -/
theorem mixedSourceMissing_sq_eq_cross (S : SelectedHighLowStructure W m) (i : S.I) :
    (∫ p : Ω × Ω, (IndependentAtomCopy.mixedSourceMissing (PhysicalRepresentative.adjacency W m)
      (S.cuspThreeMissingRegion i) (S.rootNeighborhood i) p.1 p.2) ^ 2 ∂μ.prod μ) =
      ∫ p : Ω × Ω, ((S.cuspThreeMissingRegion i ×ˢ S.rootNeighborhood i).indicator
        (fun p => if PhysicalRepresentative.adjacency W m p.1 p.2 then (0 : ℝ) else 1) p) ^ 2
        ∂μ.prod μ := by
  congr 1
  funext p
  by_cases hx : p.1 ∈ S.cuspThreeMissingRegion i <;>
    by_cases hy : p.2 ∈ S.rootNeighborhood i <;>
    cases hg : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    simp [IndependentAtomCopy.mixedSourceMissing, Set.indicator, hx, hy, hg]

/-- The genuine dispersed missing region of an actual low-slope third-cusp
common peak is impossible. Universality, the small missing region, the mass
and gamma windows, the original hole cap, the density return, the missing
edge cap and the edited-value ratio are all derived from the actual selected
structure, its peak and the selected global excess maximum. -/
theorem no_cusp_three_dispersed_missing (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hdispersed : (μ.real (S.cuspThreeMissingRegion i)) ^ 2 / 42 ≤
      (∫ p in S.cuspThreeMissingRegion i ×ˢ S.cuspThreeMissingRegion i,
        adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2) : False := by
  let J := S.cuspThreeMissingRegion i
  let N := S.rootNeighborhood i
  let A := S.originalAtomMass i
  let t := μ.real J
  let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
  let v := ∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  let YJJ := ∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂μ.prod μ
  let L := ∫ p : Ω × Ω, IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
    Nᶜ p.1 p.2 ∂μ.prod μ
  let H := ∫ p in N ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1) :=
    fun huniv => S.no_cusp_three_low_slope_universal_peak i hdk hW hgap hglobal hell hpeak huniv
  -- Mass windows of the original peak and its entire missing region.
  obtain ⟨ht, _, hmass, htsmall, _⟩ :=
    S.cusp_three_low_slope_missing_region i hdk hW hgap hglobal hell hpeak hnonuniv
  change 0 < t at ht
  change A + t < 1 / 3 at hmass
  change t < 2 / 39 at htsmall
  obtain ⟨_, hA, _⟩ := S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
  change 11 / 39 < A at hA
  -- The contact margin bounds gamma; the small-missing exit places t above it.
  obtain ⟨_, _, _, _, hcontact⟩ := hW.cusp_contact_parameters 3 (by norm_num)
    (show d = (1 - 1 / (3 : ℝ) ^ 2) / 2 by norm_num [hdk]) hgap hglobal
  have hgamma : 1 / 27 < 2 * (c - m * d) + m := by
    norm_num at hcontact
    linarith only [hcontact, hell]
  have hgt : 2 * (c - m * d) + m < t := lt_of_not_ge
    (fun hsmall => S.no_cusp_three_small_missing i hdk hW hgap hglobal hell hpeak hsmall)
  -- The actual density return of the dispersed region.
  change t ^ 2 / 42 ≤ z at hdispersed
  have hz : 0 < z := lt_of_lt_of_le (div_pos (sq_pos_of_pos ht) (by norm_num)) hdispersed
  have hreturn := S.cusp_three_missing_return i hdk hW hgap hglobal hell hpeak hnonuniv
  change 0 ≤ z ∧ _ ∧ 0 < v - 2 * z ∧ (0 < z → _ ∧ (2 + A / t) * z < v) ∧ _ at hreturn
  obtain ⟨_, _, hv2, hpositive, _⟩ := hreturn
  have hret := (hpositive hz).2
  -- The original hole identity caps the edited density below 9/20.
  have hhole := S.cusp_three_missing_hole_inventory i hW hd hgap
  change 1 - 2 * d = (A + t) ^ 2 - (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) +
    2 * v + H at hhole
  have hzint : (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) = 2 * z := by
    dsimp only [z]
    ring
  rw [hzint] at hhole
  have hH0 : 0 ≤ H := by
    change 0 ≤ ∫ p in S.rootNeighborhood i ×ˢ S.rootNeighborhood i,
      1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
    rw [S.cusp_three_neighborhood_missing_square i hW hd hgap]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hdint : 4 / 9 + v - z ∈ Icc (4 / 9 : ℝ) (9 / 20) := by
    rw [hdk] at hhole
    have hB : 112 / 351 < A + t := by linarith only [hA, hgamma, hgt]
    constructor
    · linarith only [hv2, hz]
    · nlinarith only [hhole, hH0, hB]
  -- The actual edge cap and the actual edited value give the body ratio.
  have hcharge := S.cusp_three_missing_charge_le_edge_mass i hdk hW hgap hglobal hell hpeak
  change YJJ ≤ 8 / 21 * z at hcharge
  have hvalue := S.cusp_three_dispersed_edit_value i hdk hW hgap hglobal
  change 2 / 27 - YJJ / 2 - L / 2 ≤ benchmark (4 / 9 + v - z) at hvalue
  have hratio := Benchmark.cusp_three_dispersed_body_ratio hA ht hmass hz.le hret hdint
    hcharge hvalue
  -- The original numerical hole cap.
  have hHcap := S.cusp_three_dispersed_missing_bound_of_mass i hdk hW hgap hglobal hell hpeak
    hnonuniv hdispersed (by linarith only [hgamma, hgt])
  -- The mixed-source missing square is the same cross inventory.
  have hcross : (∫ p : Ω × Ω, (IndependentAtomCopy.mixedSourceMissing
      (PhysicalRepresentative.adjacency W m) J N p.1 p.2) ^ 2 ∂μ.prod μ) = v := by
    rw [S.mixedSourceMissing_sq_eq_cross i,
      ← S.cusp_three_cross_missing_square i hW hd hgap]
  refine S.cusp_three_dispersed_false i hdk hW hgap hglobal hell hpeak hmass.le hgt
    (by linarith only [htsmall, hgamma]) hHcap ?_ ?_
  · rw [hcross]
    linarith only [hv2, hz]
  · rw [hcross]
    exact hratio.le

end Erdos1017.CappedModel.SelectedHighLowStructure

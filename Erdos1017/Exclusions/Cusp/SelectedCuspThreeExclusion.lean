module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeDominantMissing
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeDispersedMissing
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeHighExclusion

/-!
# Exclusion of the third reciprocal cusp

The third reciprocal cusp is excluded for every original multiplier: for own
penalty below one the argument splits on whether one original atom dominates the
entire missing region, and the high-slope case includes the shared endpoint at
penalty one (`no_cusp_three_contact`).
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

/-- Every selected positive global excess at the third cusp with own
penalty below one is excluded. The entire missing region is either
dominated by one original atom or satisfies the dispersed edge bound. -/
theorem no_cusp_three_low_contact (S : SelectedHighLowStructure W m)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : -m < 1) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  obtain ⟨_, i, _, _, hpeak, _, _, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
  change S.IsCommonForwardPeak d c i at hpeak
  have hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1) :=
    fun huniv => S.no_cusp_three_low_slope_universal_peak i hdk hW hgap hglobal hell hpeak huniv
  rcases S.cusp_three_missing_dominant_or_dispersed i hdk hW hgap hglobal hell hpeak
      hnonuniv with hdominant | hdispersed
  · obtain ⟨j, _, hinside, hmass⟩ := hdominant
    have hwhole : μ.real (S.cuspThreeDominantAtom i j) = S.originalAtomMass j := by
      apply measureReal_congr
      filter_upwards [(ae_restrict_iff' (S.hfibers j.val j.property).1).mp hinside]
        with x hx
      change (x ∈ {x | S.ρ x = j.val} ∩ S.cuspThreeMissingRegion i) =
        (x ∈ {x | S.ρ x = j.val})
      exact propext ⟨And.left, fun hj => ⟨hj, hx hj⟩⟩
    have hpartition := (S.cusp_three_dominant_masses i j).1
    rw [hwhole] at hpartition
    apply S.no_cusp_three_dominant_missing_atom i j hdk hW hgap hglobal hell hpeak
    rw [hwhole]
    linarith only [hpartition, hmass]
  · exact S.no_cusp_three_dispersed_missing i hdk hW hgap hglobal hell hpeak hdispersed

/-- The third reciprocal cusp is excluded for every original multiplier.
The high-slope case includes the shared endpoint at penalty one. -/
theorem no_cusp_three_contact (S : SelectedHighLowStructure W m)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  rcases le_or_gt 1 (-m) with hell | hell
  · exact S.no_cusp_three_high_contact hdk hW hgap hglobal hell
  · exact S.no_cusp_three_low_contact hdk hW hgap hglobal hell

end Erdos1017.CappedModel.SelectedHighLowStructure

module

public import Erdos1017.Exclusions.E2.Middle.MiddleE2UniversalParameterGuards
public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalIntegratedDeficitFloor
public import Erdos1017.Exclusions.Common.Universal.SelectedTwoUniversalE2

/-!
# Positive partner-hole mass at universal `E₂` contacts

A universal saturated atom has positive partner-hole mass at every `E₂` contact
with `0 < q ≤ 1/5` (`universal_partner_hole_pos_e2`), since a null hole would
make its saturated partner universal as well.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

private theorem middle_partner_universal_of_empty_holes (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hnull : μ (S.universalPartnerHoleRegion r p) = 0) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = p.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = p.val then 0 else 1 := by
  have hnotH : ∀ᵐ x ∂μ, x ∉ S.universalPartnerHoleRegion r p :=
    compl_mem_ae_iff.mpr hnull
  have hSAT := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hpair.symm.row_on_other
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hsets : ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood p ↔ S.ρ x ≠ p.val := by
    filter_upwards [hnotH, hSAT] with x hn hs
    constructor
    · exact fun h => h.1
    · intro hxp
      by_cases hxr : S.ρ x = r.val
      · exact ⟨hxp, by rw [hs hxr]; linarith only [hmneg]⟩
      · by_contra hnot
        exact hn (by
          intro hh
          rcases hh with (hh | hh) | hh
          · exact hxr hh
          · exact hxp hh
          · exact hnot hh)
  filter_upwards [S.ae_root_adjacency p hW hd hgap,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    Measure.quasiMeasurePreserving_snd.ae hsets] with z hz ha hs hzp
  change adjacencyKernel W z.1 z.2 =
    (if PhysicalRepresentative.adjacency W m z.1 z.2 = true then 1 else 0) at ha
  by_cases hy : S.ρ z.2 = p.val
  · have hf : PhysicalRepresentative.adjacency W m z.1 z.2 = false :=
      Bool.eq_false_iff.mpr (fun he => (hs.mp ((hz hzp).mp he)) hy)
    simpa only [hf, Bool.false_eq_true, ite_false, hy, ite_true] using ha
  · have ht := (hz hzp).mpr (hs.mpr hy)
    simpa only [ht, ite_true, hy, ite_false] using ha

/-- A universal saturated original atom has positive entire partner-hole
mass at every legal positive E2 contact. Its null boundary would make the
actual saturated partner universal as well. -/
theorem universal_partner_hole_pos_e2 (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1) :
    0 < μ (S.universalPartnerHoleRegion r p) := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ Benchmark.e2_density_mem hq
  apply bot_lt_iff_ne_bot.mpr
  intro hnull
  exact hpair.not_both_universal_e2 hW hq hdq hgap hglobal huniv
    (S.middle_partner_universal_of_empty_holes r p hpair hW hd hgap hnull)

end Erdos1017.CappedModel.SelectedHighLowStructure

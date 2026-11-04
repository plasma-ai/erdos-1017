module

public import Erdos1017.Exclusions.Corner.SelectedCornerPositiveSource
public import Erdos1017.Exclusions.Corner.SelectedCornerTwoCenter
public import Erdos1017.Exclusions.Corner.SelectedCornerEmptySource

/-!
# Single center of the corner recovery

A corner recovery has exactly one original center, its finite positive plateau
and two-center exit being derived, and corner contact forces a universal common
peak with a saturated partner, covering both whole-source alternatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- Actual corner recovery has one original center. Its finite positive
plateau, own cardinality bound and complete two-center exit are derived. -/
theorem ReverseRecovery.corner_plateau_card_eq_one (R : S.ReverseRecovery)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : R.plateau.card = 1 := by
  have hell := (hW.corner_contact_parameters hd hgap he heq hglobal).1
  have hcard := R.card_le_two_of_half_lt_neg_multiplier hW hd hgap
    (by linarith only [hell.1])
    (by linarith only [he.1, Benchmark.tenth_lt_epsilonC])
  have hpositive := Finset.card_pos.mpr R.plateau_nonempty
  by_contra hnot
  have htwo : R.plateau.card = 2 := by omega
  exact R.no_corner_two_center hW hd hgap he heq hglobal htwo

/-- Genuine corner contact forces an actual original universal common
peak with a saturated partner. Both entire-source alternatives and all
recovered plateau cardinalities are handled internally. -/
theorem exists_corner_universal_saturated_peak (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    ∃ r p : S.I, S.IsCommonForwardPeak d c r ∧ S.IsSaturatedAtomPair r p ∧
      ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val →
        adjacencyKernel W z.1 z.2 = if S.ρ z.2 = r.val then 0 else 1 := by
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  have hcard := R.corner_plateau_card_eq_one hW hd hgap he heq hglobal
  by_cases hnull : μ (S.reverseCompulsorySource R.plateau) = 0
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
    have hpeak := (R.empty_source_is_original_peak r hr hW hd hgap hnull).1
    have huniv := R.empty_source_head_adjacency r hr hW hd hgap hnull
    by_cases hsat : ∃ p : S.I, S.IsSaturatedAtomPair r p
    · obtain ⟨p, hpair⟩ := hsat
      exact ⟨r, p, hpeak, hpair, huniv⟩
    · exact False.elim (R.no_corner_unsaturated_empty_source r hr hW hd hgap he heq
        hglobal hnull (fun p _ hpair => hsat ⟨p, hpair⟩))
  · obtain ⟨_, r, _, hpeak, _, _⟩ := S.exists_sharp_corner_peak hW hd hgap he heq hglobal
    change S.IsCommonForwardPeak d c r at hpeak
    obtain ⟨p, _, _, hpair, huniv⟩ := R.exists_corner_one_center_saturated_universal
      hW hd hgap he heq hglobal hcard (pos_iff_ne_zero.mpr hnull) r hpeak
    exact ⟨r, p, hpeak, hpair, huniv⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

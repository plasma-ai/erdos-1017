module

public import Erdos1017.SelectedModel.Recovery.SelectedReverseRecovery
public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak

/-!
# Plateau of the smooth `W` recovery

Smooth-`W` contact derives the own slope and missing-density floor needed by the
original recovery's physical plateau budget, and the same recovery has one or
two original plateau labels, with neither a cardinality nor a nonemptiness
certificate supplied (`smoothW_plateau_card_eq_one_or_two`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private theorem one_twelfth_lt_epsilonStar : (1 / 12 : ℝ) < Benchmark.epsilonStar := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  unfold Benchmark.epsilonStar
  nlinarith

/-- Genuine smooth-W contact derives the own slope and missing-density
floor needed by the actual original recovery's physical plateau budget. -/
theorem smoothW_plateau_card_le_two (R : S.ReverseRecovery)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : R.plateau.card ≤ 2 := by
  obtain ⟨_, _, hell, _, _, _⟩ := hW.smoothW_contact_parameters hd hgap he hactive hglobal
  exact R.card_le_two_of_half_lt_neg_multiplier hW hd hgap hell.1
    (one_twelfth_lt_epsilonStar.trans he.1)

/-- The same original recovery has one or two genuine original plateau
labels; neither a cardinality nor a nonemptiness certificate is supplied. -/
theorem smoothW_plateau_card_eq_one_or_two (R : S.ReverseRecovery)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : R.plateau.card = 1 ∨ R.plateau.card = 2 := by
  have hbound := R.smoothW_plateau_card_le_two hW hd hgap he hactive hglobal
  have hpos := Finset.card_pos.mpr R.plateau_nonempty
  omega

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

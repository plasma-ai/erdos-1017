module

public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak
public import Erdos1017.Exclusions.Common.Physical.IndependentClassMissingMass

/-!
# Covered-model guards at the smooth `W` contact

Smooth-`W` contact gives the covered-model slope and strict bonus for any two
original independent atoms, while exterior atoms may remain
(`smoothW_covered_contact_guards`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Actual smooth-W contact gives the covered-model slope and strict
bonus for any two original independent atoms. Exterior atoms may remain. -/
theorem smoothW_covered_contact_guards (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    -m ∈ Ioo (1 / 2 : ℝ) (2 / 3) ∧
      0 < 2 * (c - m * d) + m ∧ S.originalAtomMass r < 1 / 2 ∧
      S.originalAtomMass r * (1 + m) < 2 * (2 * (c - m * d) + m) ∧
      S.originalAtomMass r * (1 + m) / (2 * (c - m * d) + m) < 2 := by
  obtain ⟨_, _, hell, hdelta, hgamma, hmissing⟩ :=
    hW.smoothW_contact_parameters hd hgap he hactive hglobal
  have hsquares := S.two_originalAtomMass_sq_le_missing_density r a hra
  rw [hW.density_eq] at hsquares
  have hb : S.originalAtomMass r < 1 / 2 := by
    by_contra h
    have hlarge : 1 / 2 ≤ S.originalAtomMass r := le_of_not_gt h
    nlinarith only [hsquares, hmissing, hlarge, sq_nonneg (S.originalAtomMass a)]
  have hproduct := mul_nonneg (sub_nonneg.mpr hb.le)
    (show 0 ≤ 1 + m by linarith [hell.2])
  have hbonus : S.originalAtomMass r * (1 + m) < 2 * (2 * (c - m * d) + m) := by
    nlinarith only [hproduct, hdelta, hgamma]
  have hg : 0 < 2 * (c - m * d) + m := by linarith only [hgamma]
  exact ⟨hell, hg, hb, hbonus, (div_lt_iff₀ hg).mpr (by nlinarith only [hbonus])⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

module

public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak
public import Erdos1017.Exclusions.Common.Physical.IndependentClassMissingMass

/-!
# Atom guards at the smooth `W` contact

One original independent atom already contributes its entire square to the
original missing density (`originalAtomMass_sq_le_missing_density`), and own
smooth-`W` contact gives the strict bonus for any original independent atom,
including a universal cover with no saturated partner
(`smoothW_atom_contact_guards`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- One original independent atom already contributes its entire square
to the original missing density, without a second-atom premise. -/
theorem originalAtomMass_sq_le_missing_density (S : SelectedHighLowStructure W m) (r : S.I) :
    (S.originalAtomMass r) ^ 2 ≤ 1 - 2 * density W := by
  let : Countable S.I := S.hI.to_subtype
  have hs : Summable (fun i => (S.originalAtomMass i) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ S.originalAtomMass_summable.2
    intro i
    have hn := S.originalAtomMass_summable.1 i
    have hb : S.originalAtomMass i ≤ 1 := measureReal_le_one
    nlinarith
  have h := Summable.sum_le_tsum (s := {r}) (fun i _ => sq_nonneg (S.originalAtomMass i)) hs
  simpa only [Finset.sum_singleton] using h.trans S.originalAtomMass_sq_sum_le_missing_density

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Genuine own smooth-W contact gives the strict bonus for any original
independent atom, including a universal cover with no saturated partner. -/
theorem smoothW_atom_contact_guards (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
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
  have hsquare := S.originalAtomMass_sq_le_missing_density r
  rw [hW.density_eq] at hsquare
  have hb : S.originalAtomMass r < 1 / 2 := by
    by_contra h
    have hlarge : 1 / 2 ≤ S.originalAtomMass r := le_of_not_gt h
    nlinarith only [hsquare, hmissing, hlarge]
  have hproduct := mul_nonneg (sub_nonneg.mpr hb.le)
    (show 0 ≤ 1 + m by linarith [hell.2])
  have hbonus : S.originalAtomMass r * (1 + m) < 2 * (2 * (c - m * d) + m) := by
    nlinarith only [hproduct, hdelta, hgamma]
  have hg : 0 < 2 * (c - m * d) + m := by linarith only [hgamma]
  exact ⟨hell, hg, hb, hbonus, (div_lt_iff₀ hg).mpr (by nlinarith only [hbonus])⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

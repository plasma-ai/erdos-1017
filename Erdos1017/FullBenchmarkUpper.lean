module

public import Erdos1017.ContactLocation.SelectedRemainingContact
public import Erdos1017.Exclusions.E2.Lower.SelectedLowerE2Exclusion
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2Exclusion
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2Exclusion
public import Erdos1017.Exclusions.Cusp.SelectedCuspExclusion
public import Erdos1017.Exclusions.Corner.SelectedCornerFinalExclusion
public import Erdos1017.IntegerTransfer.IntegerBenchmarkTransfer
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Global upper bound from the exclusions and the cover

This module assembles the selected-contact exclusions into the global fractional
upper bound `densityLimit_le_benchmark_of_cover`, conditional only on the finite
fixed-point cover, and combines it with the same-graph integer transfer to
obtain the uniform asymptotic statement under the same premise. It is used in
`FinalAssembly`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1017

/-- The actual selected-contact exclusions prove the global fractional
upper bound, conditional only on the literal finite fixed-point cover. -/
theorem densityLimit_le_benchmark_of_cover
    (hcover : MiddleE2LargeUniversal.FixedPoint.cover 80
      MiddleE2LargeUniversal.FixedPoint.IBox.root = true)
    (d : ℝ) (hd : d ∈ Icc (0 : ℝ) (1 / 2)) :
    FractionalGraph.densityLimit d ≤ benchmark d := by
  have : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  by_contra hfailure
  have hfailure : ∃ d ∈ Icc (0 : ℝ) (1 / 2),
      benchmark d < FractionalGraph.densityLimit d :=
    ⟨d, hd, lt_of_not_ge hfailure⟩
  obtain ⟨d, W, m, hd, hW, hgap, hglobal, S, hcontact⟩ :=
    CappedModel.exists_selected_remaining_contact (Ω := unitInterval) (μ := volume) hfailure
  rcases hcontact with hE2 | hcorner | hcusp
  · obtain ⟨q, hq, _, _, hdq, hvalue, hderiv, _⟩ := hE2
    by_cases hlower : q ≤ 1 / 10
    · exact S.no_lowerE2_contact hW ⟨hq.1, hlower⟩ hdq hgap hglobal
    · by_cases hupper : 1 / 5 ≤ q
      · exact S.no_upperE2_contact hW ⟨hupper, hq.2.le⟩ hdq hvalue hderiv hgap hglobal
      · exact S.no_middle_e2_contact_of_cover hcover hW
          ⟨lt_of_not_ge hlower, lt_of_not_ge hupper⟩ hdq hvalue hderiv hgap hglobal
  · obtain ⟨he, heq⟩ := hcorner
    exact S.no_corner_global_excess hW hd hgap ⟨he.1.le, he.2.le⟩ heq hglobal
  · obtain ⟨k, hk, _, hdk⟩ := hcusp
    exact S.no_cusp_contact k hk hdk hW hgap hglobal

/-- The same-graph integer transfer yields the original uniform target
from the global upper bound under the same literal cover premise. -/
theorem uniformAsymptotic_of_cover
    (hcover : MiddleE2LargeUniversal.FixedPoint.cover 80
      MiddleE2LargeUniversal.FixedPoint.IBox.root = true) :
    UniformAsymptotic :=
  finalUniformAsymptotic (densityLimit_le_benchmark_of_cover hcover)

end Erdos1017

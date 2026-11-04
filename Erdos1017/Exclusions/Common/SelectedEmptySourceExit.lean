module

public import Erdos1017.Exclusions.Common.SelectedEmptySource
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalRootless

/-!
# Exit from the empty-source case

A null entire singleton source supplies the universal root, whose unsaturated
exposure and physical count give the half-quota objective bound, so in the
sector where the benchmark is at least one eighth a recovered unsaturated
singleton has nonnull entire source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- A null entire singleton source supplies the universal original root
internally. Its actual unsaturated exposure and physical count then give
the half-quota objective bound under the stated original scalar gate. -/
theorem empty_source_unsaturated_objective_le_half_root_quota
    (r : S.I) (hr : R.plateau = {r}) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m)) :
    c ≤ μ.real {x | S.ρ x = r.val} * (1 - μ.real {x | S.ρ x = r.val}) / 2 :=
  S.unsaturated_universal_objective_le_half_root_quota r hW hd hgap
    (R.empty_source_head_neutral r hr hW hd hgap hnull) hstar hA hell hmargin

/-- In the actual benchmark-at-least-one-eighth sector, a recovered
unsaturated singleton has nonnull entire source. The required A>1/3 is
derived from the original empty-source square bound and strict gap. -/
theorem entire_source_ne_zero_of_unsaturated_benchmark_ge_eighth
    (r : S.I) (hr : R.plateau = {r}) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m))
    (hbenchmark : (1 / 8 : ℝ) ≤ benchmark d) :
    μ (S.reverseCompulsorySource R.plateau) ≠ 0 := by
  intro hnull
  have hsq := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  have hA0 : 0 ≤ μ.real {x | S.ρ x = r.val} := measureReal_nonneg
  have hA : 1 / 3 < μ.real {x | S.ρ x = r.val} := by
    by_contra hbad
    have hp := mul_nonpos_of_nonneg_of_nonpos hA0 (sub_nonpos.mpr (le_of_not_gt hbad))
    nlinarith
  have hbound := R.empty_source_unsaturated_objective_le_half_root_quota r hr hW hd hgap
    hnull hstar hA hell hmargin
  nlinarith [sq_nonneg (μ.real {x | S.ρ x = r.val} - 1 / 2)]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

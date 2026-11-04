module

public import Erdos1017.Exclusions.Common.MultipartiteCollisionEnvelope
public import Erdos1017.Exclusions.Cusp.BenchmarkSplitCubicEnvelopes

/-!
# Cubic bound on the shifted multipartite value

The exact cubic maximum for the shifted multipartite value, its excess strictly
below `1/50` on the reciprocal-cusp interval, and the cubic shifted bound for
every fully feasible countable multipartite law with largest class attained
internally, dust included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace Erdos1017.MultipartiteClassMasses

open CappedModel

/-- The exact cubic maximum used for the shifted multipartite value. -/
theorem shifted_cubic_le {ell x : ℝ} (hell : ell ≤ 2) (hx : 0 ≤ x) :
    (2 - ell) * x ^ 2 - 7 / 4 * x ^ 3 ≤ 64 * (2 - ell) ^ 3 / 1323 := by
  have h := mul_nonneg (sq_nonneg (21 * x - 8 * (2 - ell)))
    (show 0 ≤ 21 * x + 4 * (2 - ell) by linarith)
  nlinarith

/-- The reciprocal-cusp interval makes the cubic excess strictly less than 1/50. -/
theorem shifted_cubic_excess_lt {ell : ℝ} (hlo : 29 / 21 ≤ ell) (hhi : ell ≤ 2) :
    64 * (2 - ell) ^ 3 / 1323 < 1 / 50 := by
  have h := pow_le_pow_left₀ (show 0 ≤ 2 - ell by linarith)
    (show 2 - ell ≤ (13 / 21 : ℝ) by linarith) 3
  norm_num at h
  linarith

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

local instance shiftedBoundOptionMeasurable : MeasurableSpace (Option ι) := ⊤

/-- Every actual fully feasible countable multipartite law satisfies the
cubic shifted bound. Its largest class is attained internally; pure dust
is included. No optimality or stationary multiplier is assigned to this law. -/
theorem shifted_objective_le_cubic (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (ell : ℝ) (hlo : 1 ≤ ell) (hhi : ell ≤ 2) :
    2 * objective W - ell * (1 - 2 * density W) ≤ 64 * (2 - ell) ^ 3 / 1323 := by
  have hmissing := one_sub_two_density_eq_tsum_classMass_sq W q hq hsupport
  by_cases hpos : ∃ i, 0 < classMass μ q i
  · obtain ⟨i, hi, hmax⟩ := exists_largest_class q hq hpos
    have hcollision := objective_le_split_add_tail W hW q hq hsupport i hi hmax
    have hcurve := Benchmark.splitValue_le_seven_eighths
      ⟨hi.le, classMass_le_one (μ := μ) q i⟩
    have hsq := (classMass_sq_summable (μ := μ) q hq).le_tsum i (fun _ _ => sq_nonneg _)
    rw [← hmissing] at hsq
    have htail := mul_nonneg (show 0 ≤ ell - 1 by linarith)
      (show 0 ≤ 1 - 2 * density W - (classMass μ q i) ^ 2 by linarith)
    have hcubic := shifted_cubic_le hhi hi.le
    nlinarith
  · have hnull : ∀ i, classMass μ q i = 0 := fun i =>
      le_antisymm (le_of_not_gt (fun hi => hpos ⟨i, hi⟩)) (classMass_nonneg μ q i)
    have hcost := objective_le_zero_of_null_classMass W hW q hsupport hnull
    simp only [hnull, zero_pow (by decide : 2 ≠ 0), tsum_zero] at hmissing
    have hcubic : 0 ≤ 64 * (2 - ell) ^ 3 / 1323 := by positivity
    rw [hmissing]
    linarith

end Erdos1017.MultipartiteClassMasses

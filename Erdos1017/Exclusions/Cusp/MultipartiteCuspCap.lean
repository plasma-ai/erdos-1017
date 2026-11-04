module

public import Erdos1017.Exclusions.Cusp.BenchmarkCuspCap
public import Erdos1017.Exclusions.Common.MultipartiteCollisionEnvelope
public import Erdos1017.Benchmark.BenchmarkContactGeometry

/-!
# Affine missing-density bound for a capped multipartite model

A multipartite model whose attained largest class is capped at a reciprocal cusp
obeys its affine missing-density bound (`objective_le_cusp_cap`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace Erdos1017.MultipartiteClassMasses

open CappedModel

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

local instance cuspCapOptionMeasurable : MeasurableSpace (Option ι) := ⊤

/-- An actual multipartite model whose attained largest class is capped
at a reciprocal cusp obeys its affine missing-density bound. -/
theorem objective_le_cusp_cap (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i : ι) (hpos : 0 < classMass μ q i) (hmax : ∀ j, classMass μ q j ≤ classMass μ q i)
    (k : ℕ) (hk : 4 ≤ k) (hcap : classMass μ q i ≤ 1 / (k : ℝ)) :
    objective W ≤ ((k : ℝ) - 1) / (k : ℝ) ^ 3 +
      (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) *
        (1 - 2 * density W - 1 / (k : ℝ) ^ 2) / 2 := by
  have hcollision := objective_le_split_add_tail W hW q hq hsupport i hpos hmax
  have hcurve := Benchmark.splitValue_le_cusp_cap k hk ⟨hpos.le, hcap⟩
  have hmissing := one_sub_two_density_eq_tsum_classMass_sq W q hq hsupport
  have hsq := (classMass_sq_summable (μ := μ) q hq).le_tsum i (fun _ _ => sq_nonneg _)
  rw [← hmissing] at hsq
  have hL := Benchmark.split_cusp_lower_slope_ge_eleven_tenths k hk
  have hprod := mul_nonneg
    (show 0 ≤ (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) - 1 by linarith)
    (sub_nonneg.mpr hsq)
  nlinarith

end Erdos1017.MultipartiteClassMasses

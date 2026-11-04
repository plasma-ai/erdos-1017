module

public import Erdos1017.Exclusions.Common.FractionalSupportSymmetrization
public import Erdos1017.Exclusions.Common.FullScalarSamplingComparison
public import Erdos1017.Models.Decorated.DecoratedKernel
public import Mathlib.Probability.ConditionalProbability

/-!
# Support bound for bounded feasible kernels

The support bound `densityLimit d + d ≤ 25/48` holds on `[0, 1/2]`, and every
integrable feasible signed kernel on a probability space, or bounded one on a
finite measure, satisfies the corresponding bound at its own physical density.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017.FractionalGraph

/-- The actual finite support bound passes to the full density limit.
The penalty in its definition pays every density mismatch. -/
theorem densityLimit_add_density_le {d : ℝ} (hd : d ∈ Icc (0 : ℝ) (1 / 2)) :
    densityLimit d + d ≤ 25 / 48 := by
  have hbound : densityLimit d ≤ 25 / 48 - d := by
    apply csSup_le (densityCandidates_nonempty d)
    rintro c (rfl | ⟨N, G, rfl⟩)
    · linarith [hd.2]
    · have hn : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      have hfinite := value_add_edge_count_le_all G
      have hnormalized : value G / ((N + 1 : ℕ) : ℝ) ^ 2 +
          (G.edgeSet.ncard : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 25 / 48 := by
        rw [← add_div]
        apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
        linarith
      have habs := neg_abs_le ((G.edgeSet.ncard : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 - d)
      have hnonneg := abs_nonneg ((G.edgeSet.ncard : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 - d)
      linarith
  linarith

end Erdos1017.FractionalGraph

namespace Erdos1017.FiniteCappedSamplingCost

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Every integrable feasible signed kernel on a probability space obeys
the support bound at its own physical density. -/
theorem physicalObjective_add_density_le [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    physicalObjective μ Y + physicalDensity μ A ≤ 25 / 48 := by
  have hvalue := physicalObjective_le_densityLimit_of_full_scalar_tests
    A hsym hA Y hY hYsym hzero hfull
  have hsupport := FractionalGraph.densityLimit_add_density_le
    (physicalDensity_mem_Icc (μ := μ) A hsym hA)
  linarith

/-- The actual support bound holds for bounded feasible signed kernels
on every finite measure, including zero mass and arbitrary restrictions. -/
theorem physicalObjective_add_density_le_mass_sq [IsFiniteMeasure μ]
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    physicalObjective μ Y + physicalDensity μ A ≤ 25 * (μ.real univ) ^ 2 / 48 := by
  by_cases hμ : μ = 0
  · subst μ
    simp [physicalObjective, physicalDensity]
  have hmass : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  let ν := μ[|univ]
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure hmass
  have hac : ν ≪ μ := cond_absolutelyContinuous
  have hpac := hac.prod hac
  have hfullν : ∀ n, FiniteArity.FeasibleOrder ν A Y n :=
    fun n => (DecoratedKernel.pi_absolutelyContinuous hac n).ae_le (hfull n)
  have hi : Integrable (Function.uncurry Y) (ν.prod ν) :=
    Integrable.of_bound hY.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hprob := physicalObjective_add_density_le A hsym hA Y hi
    (hpac.ae_le hYsym) (hpac.ae_le hzero) hfullν
  have hnormal : μ = (μ univ) • ν := by
    dsimp [ν, ProbabilityTheory.cond]
    rw [Measure.restrict_univ, smul_smul,
      ENNReal.mul_inv_cancel hmass (measure_ne_top μ univ), one_smul]
  have hproduct : μ.prod μ = (μ univ) ^ 2 • ν.prod ν := by
    calc
      μ.prod μ = ((μ univ) • ν).prod ((μ univ) • ν) :=
        congrArg₂ Measure.prod hnormal hnormal
      _ = (μ univ) ^ 2 • ν.prod ν := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, pow_two]
  have hscale (f : Ω × Ω → ℝ) :
      (∫ p, f p ∂μ.prod μ) = (μ.real univ) ^ 2 * ∫ p, f p ∂ν.prod ν := by
    rw [hproduct, integral_smul_measure]
    simp only [ENNReal.toReal_pow, measureReal_def, smul_eq_mul]
  have hobjective : physicalObjective μ Y = (μ.real univ) ^ 2 * physicalObjective ν Y := by
    unfold physicalObjective
    rw [hscale]
    ring
  have hdensity : physicalDensity μ A = (μ.real univ) ^ 2 * physicalDensity ν A := by
    unfold physicalDensity
    rw [hscale]
    ring
  rw [hobjective, hdensity, ← mul_add]
  have hscaled := mul_le_mul_of_nonneg_left hprob (sq_nonneg (μ.real univ))
  linarith

end Erdos1017.FiniteCappedSamplingCost

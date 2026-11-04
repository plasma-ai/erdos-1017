module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorVertex
public import Mathlib.Analysis.Convex.KreinMilman

/-!
# The optimal face of the one-exterior child

This module defines the linear `objective` and `optimalFace` of the one-exterior
child; the face is closed, exposed and compact under positive physical weights,
so it supplies a vertex of the all-count feasible set without any vertex or
active-rank input (`exists_optimal_vertex`).
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology BigOperators Classical

namespace Erdos1017.CoveredOneExterior

def objective (b x e : ℝ) : Coefficients →ₗ[ℝ] ℝ :=
  (b * x) • (LinearMap.proj 0 : Coefficients →ₗ[ℝ] ℝ) +
    (b * e) • (LinearMap.proj 1 : Coefficients →ₗ[ℝ] ℝ) -
    (x * e) • (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ) -
    (e ^ 2 / 2) • (LinearMap.proj 3 : Coefficients →ₗ[ℝ] ℝ)

theorem objective_apply (b x e : ℝ) (y : Coefficients) :
    objective b x e y = b * x * y 0 + b * e * y 1 - x * e * y 2 - e ^ 2 * y 3 / 2 := by
  simp only [objective, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  ring

def optimalFace (b x e V : ℝ) : Set Coefficients :=
  {y ∈ feasible | objective b x e y = V}

theorem feasible_isClosed : IsClosed feasible := by
  unfold feasible
  simp_rw [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter (fun i : Fin 4 =>
      isClosed_le continuous_const (continuous_apply i : Continuous (fun y : Coefficients => y i)))
  · exact isClosed_iInter (fun s => isClosed_iInter (fun n =>
      isClosed_le (test s n).continuous_of_finiteDimensional continuous_const))

theorem optimalFace_isClosed (b x e V : ℝ) : IsClosed (optimalFace b x e V) :=
  feasible_isClosed.inter (isClosed_eq (objective b x e).continuous_of_finiteDimensional
    continuous_const)

theorem root_star_bounds {y : Coefficients} (hy : y ∈ feasible) :
    y 0 ≤ 1 ∧ y 1 ≤ 1 := by
  constructor
  · simpa [test_eq_value, constant, slope, TightCounts.value] using hy.2 true 0
  · simpa [test_eq_value, constant, slope, TightCounts.value] using hy.2 false 1

/-- Positive physical weights make the entire sign-feasible optimal face
compact. No upper penalty box is assumed. -/
theorem optimalFace_isCompact {b x e V : ℝ} (hb : 0 < b) (hx : 0 < x) (he : 0 < e) :
    IsCompact (optimalFace b x e V) := by
  let B := b * x + b * e - V
  let upper : Coefficients := ![1, 1, B / (x * e), 2 * B / e ^ 2]
  apply (isCompact_Icc : IsCompact (Icc (0 : Coefficients) upper)).of_isClosed_subset
    (optimalFace_isClosed b x e V)
  intro y hy
  have hstar := root_star_bounds hy.1
  have hpen2 := mul_nonneg (show 0 ≤ x * e by positivity) (hy.1.1 2)
  have hpen3 := mul_nonneg (sq_nonneg e) (hy.1.1 3)
  have hstar0 := mul_le_mul_of_nonneg_left hstar.1 (show 0 ≤ b * x by positivity)
  have hstar1 := mul_le_mul_of_nonneg_left hstar.2 (show 0 ≤ b * e by positivity)
  have hobj := hy.2
  rw [objective_apply] at hobj
  refine ⟨hy.1.1, ?_⟩
  intro i
  fin_cases i
  · exact hstar.1
  · exact hstar.2
  · change y 2 ≤ B / (x * e)
    apply (le_div_iff₀ (show 0 < x * e by positivity)).mpr
    dsimp only [B]
    nlinarith only [hobj, hstar0, hstar1, hpen3]
  · change y 3 ≤ 2 * B / e ^ 2
    apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
    dsimp only [B]
    nlinarith only [hobj, hstar0, hstar1, hpen2]

theorem optimalFace_isExposed (b x e V : ℝ)
    (hmax : ∀ y ∈ feasible, objective b x e y ≤ V) :
    IsExposed ℝ feasible (optimalFace b x e V) := by
  rintro ⟨z, hz⟩
  refine ⟨(objective b x e).toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hye⟩
    refine ⟨hy, ?_⟩
    intro w hw
    change objective b x e w ≤ objective b x e y
    rw [hye]
    exact hmax w hw
  · rintro ⟨hy, hym⟩
    refine ⟨hy, le_antisymm (hmax y hy) ?_⟩
    have h := hym z hz.1
    change objective b x e z ≤ objective b x e y at h
    rwa [hz.2] at h

/-- The actual compact optimal face supplies a vertex of the original
all-count feasible set. No vertex or active rank is an input. -/
theorem exists_optimal_vertex {b x e V : ℝ} (hb : 0 < b) (hx : 0 < x) (he : 0 < e)
    (hne : (optimalFace b x e V).Nonempty)
    (hmax : ∀ y ∈ feasible, objective b x e y ≤ V) :
    ∃ y ∈ feasible.extremePoints ℝ, objective b x e y = V := by
  obtain ⟨y, hy⟩ := (optimalFace_isCompact hb hx he (V := V)).extremePoints_nonempty hne
  exact ⟨y, (optimalFace_isExposed b x e V hmax).isExtreme.extremePoints_subset_extremePoints hy,
    hy.1.2⟩

end Erdos1017.CoveredOneExterior

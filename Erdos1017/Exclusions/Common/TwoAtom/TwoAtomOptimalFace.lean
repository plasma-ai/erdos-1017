module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountSpace

/-!
# Optimal face of the two-atom system

This module defines the complete optimal face before any sign restriction on `h`
or `r`, proves it closed, compact in the signed charge coordinates and exposed
by global maximality, and maximizes `h` on it to select an extreme point that is
a vertex of the full all-count sliced set.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- The actual complete optimal face, before any sign restriction on h or r. -/
def optimalFace (a b u e V : ℝ) : Set Coefficients :=
  {x ∈ feasible | objective a b u e x = V}

theorem optimalFace_isClosed (a b u e V : ℝ) : IsClosed (optimalFace a b u e V) :=
  feasible_isClosed.inter (isClosed_eq
    (continuous_const.add (linearObjective a b u e).continuous_of_finiteDimensional)
    continuous_const)

/-- A fixed physical objective bounds every actual charge coordinate below,
using only the positive physical weights and their genuine upper bounds. -/
theorem optimalFace_charge_lower {a b u e V : ℝ} (hab : a < b) (hb : 0 < b)
    (hu : 0 < u) (he : 0 < e) {x : Coefficients} (hx : x ∈ optimalFace a b u e V)
    (i : Fin 5) :
    1 - ((∑ j, objectiveWeights a b u e j) - (V - a * b)) / objectiveWeights a b u e i ≤
      chargeCoordinate x i := by
  have hw := objectiveWeights_pos hab hb hu he
  have hdef (j : Fin 5) : 0 ≤ objectiveWeights a b u e j * (1 - chargeCoordinate x j) :=
    mul_nonneg (hw j).le (sub_nonneg.mpr (chargeCoordinate_le_one hx.1 j))
  have hsum : (∑ j, objectiveWeights a b u e j * (1 - chargeCoordinate x j)) =
      (∑ j, objectiveWeights a b u e j) - (V - a * b) := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, ← linearObjective_eq_sum]
    have ho := hx.2
    change a * b + linearObjective a b u e x = V at ho
    linarith
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hdef j) (Finset.mem_univ i)
  rw [hsum] at hi
  have hdiv : 1 - chargeCoordinate x i ≤
      ((∑ j, objectiveWeights a b u e j) - (V - a * b)) / objectiveWeights a b u e i :=
    (le_div_iff₀ (hw i)).mpr (by nlinarith only [hi])
  linarith

/-- Compactness is proved in the actual signed charge coordinates; no
penalty positivity at arbitrary points of the optimal face is assumed. -/
theorem optimalFace_isCompact {a b u e V : ℝ} (hab : a < b) (hb : 0 < b)
    (hu : 0 < u) (he : 0 < e) : IsCompact (optimalFace a b u e V) := by
  let L : Coefficients := fun i =>
    1 - ((∑ j, objectiveWeights a b u e j) - (V - a * b)) / objectiveWeights a b u e i
  let lower : Coefficients := fun i => if i < 2 then L i else -1
  let upper : Coefficients := fun i => if i < 2 then 1 else -L i
  apply (isCompact_Icc : IsCompact (Icc lower upper)).of_isClosed_subset
    (optimalFace_isClosed a b u e V)
  intro x hx
  have hlo := optimalFace_charge_lower hab hb hu he hx
  have hhi := chargeCoordinate_le_one hx.1
  constructor
  · intro i
    have hl := hlo i
    have hh := hhi i
    dsimp only [lower]
    by_cases hi : i < 2
    · simpa only [hi, ite_true, chargeCoordinate] using hl
    · simp only [chargeCoordinate, hi, ite_false] at hh
      simp only [hi, ite_false]
      linarith
  · intro i
    have hl := hlo i
    have hh := hhi i
    dsimp only [upper]
    by_cases hi : i < 2
    · simpa only [chargeCoordinate, hi, ite_true] using hh
    · simp only [chargeCoordinate, hi, ite_false] at hl
      simp only [hi, ite_false]
      change x i ≤ -(1 - ((∑ j, objectiveWeights a b u e j) - (V - a * b)) /
        objectiveWeights a b u e i)
      linarith

/-- Global physical maximality makes the entire fixed-objective set a face. -/
theorem optimalFace_isExposed (a b u e V : ℝ)
    (hmax : ∀ x ∈ feasible, objective a b u e x ≤ V) :
    IsExposed ℝ feasible (optimalFace a b u e V) := by
  rintro ⟨x, hx⟩
  refine ⟨(linearObjective a b u e).toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    intro z hz
    have hb := hmax z hz
    have hye := hy.2
    change a * b + linearObjective a b u e y = V at hye
    change linearObjective a b u e z ≤ linearObjective a b u e y
    change a * b + linearObjective a b u e z ≤ V at hb
    linarith
  · intro hy
    refine ⟨hy.1, ?_⟩
    have hb := hmax y hy.1
    have hc := hy.2 x hx.1
    have hxe := hx.2
    change a * b + linearObjective a b u e x = V at hxe
    change a * b + linearObjective a b u e y ≤ V at hb
    change linearObjective a b u e x ≤ linearObjective a b u e y at hc
    change a * b + linearObjective a b u e y = V
    linarith

/-- Maximize h on the actual optimal face, then select an extreme point
of that maximizing face. It is a vertex of the full all-count sliced set. -/
theorem exists_h_maximizing_optimal_vertex {a b u e V : ℝ}
    (hab : a < b) (hb : 0 < b) (hu : 0 < u) (he : 0 < e)
    (hne : (optimalFace a b u e V).Nonempty)
    (hmax : ∀ x ∈ feasible, objective a b u e x ≤ V) :
    ∃ x ∈ feasible.extremePoints ℝ, objective a b u e x = V ∧
      ∀ y ∈ optimalFace a b u e V, y 0 ≤ x 0 := by
  have hcompact := optimalFace_isCompact hab hb hu he (V := V)
  obtain ⟨z, hz, hzh⟩ := hcompact.exists_isMaxOn hne (continuous_apply 0).continuousOn
  let F : Set Coefficients := {x ∈ optimalFace a b u e V | x 0 = z 0}
  have hFcompact : IsCompact F := hcompact.inter_right
    (isClosed_eq (continuous_apply 0) continuous_const)
  have hFn : F.Nonempty := ⟨z, hz, rfl⟩
  obtain ⟨x, hx⟩ := hFcompact.extremePoints_nonempty hFn
  have hFface : IsExposed ℝ (optimalFace a b u e V) F := by
    intro _
    refine ⟨(LinearMap.proj 0 : Coefficients →ₗ[ℝ] ℝ).toContinuousLinearMap, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hye⟩
      refine ⟨hy, ?_⟩
      intro w hw
      change w 0 ≤ y 0
      rw [hye]
      exact hzh hw
    · rintro ⟨hy, hym⟩
      refine ⟨hy, le_antisymm (hzh hy) ?_⟩
      exact hym z hz
  have hxFace := hFface.isExtreme.extremePoints_subset_extremePoints hx
  have hxFull :=
    (optimalFace_isExposed a b u e V hmax).isExtreme.extremePoints_subset_extremePoints hxFace
  refine ⟨x, hxFull, hx.1.1.2, ?_⟩
  intro y hy
  exact (hzh hy).trans_eq hx.1.2.symm

end Erdos1017.TwoAtomCountGate

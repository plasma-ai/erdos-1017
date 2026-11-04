module

public import Erdos1017.FractionalLimit.FinitePrimal
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Finite linear programming duality

Weak duality, complementary slackness and attained primal and dual optima with
equal values are proved for a finite equality-constrained unit-cost program with
a strictly positive feasible point and spanning columns (`exists_primal_dual`).
-/

@[expose] public section

namespace Erdos1017.FiniteLinearProgram

open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every feasible functional gives a lower bound on the cost of every partition. -/
theorem weak_duality (a : ι → E) (b : E) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmoment : ∑ i, w i • a i = b)
    (y : E →L[ℝ] ℝ) (hy : ∀ i, y (a i) ≤ 1) : y b ≤ ∑ i, w i := by
  rw [← hmoment, map_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [map_smul, smul_eq_mul, mul_one] using mul_le_mul_of_nonneg_left (hy i) (hw i)

/-- Every positively weighted column in an optimal primal solution is dual-tight. -/
theorem complementary_slackness (a : ι → E) (b : E) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmoment : ∑ i, w i • a i = b)
    (y : E →L[ℝ] ℝ) (hy : ∀ i, y (a i) ≤ 1) (hvalue : y b = ∑ i, w i)
    {i : ι} (hi : 0 < w i) : y (a i) = 1 := by
  have hsum : ∑ i, w i * (1 - y (a i)) = 0 := by
    rw [← hmoment, map_sum] at hvalue
    simp only [map_smul, smul_eq_mul] at hvalue
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hw j) (sub_nonneg.mpr (hy j)))).mp hsum
  have hzero := (mul_eq_zero.mp (hterm i (Finset.mem_univ i))).resolve_left hi.ne'
  linarith

/-- Strict primal feasibility forces a supporting cost coefficient to be negative. -/
theorem normalize_support (a : ι → E) (b : E) (p : ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hmoment : ∑ i, w i • a i = b)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤)
    (f : E × ℝ →L[ℝ] ℝ) (hf : f ≠ 0)
    (hcolumns : ∀ i, f (a i, 1) ≤ 0) (hcost : f (0, 1) ≤ 0)
    (hsupport : f (b, p) = 0) :
    ∃ y : E →L[ℝ] ℝ, (∀ i, y (a i) ≤ 1) ∧ y b = p := by
  let g : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hsplit (x : E) (t : ℝ) : f (x, t) = g x + t * f (0, 1) := by
    have heq : (x, t) = (x, 0) + t • (0, (1 : ℝ)) := by simp
    rw [heq, map_add, map_smul]
    rfl
  have hnegative : f (0, 1) < 0 := by
    apply lt_of_le_of_ne hcost
    intro hzero
    have hcol : ∀ i, g (a i) ≤ 0 := by
      intro i
      have h := hcolumns i
      rw [hsplit, hzero, mul_zero, add_zero] at h
      exact h
    have hb : g b = 0 := by
      rw [hsplit, hzero, mul_zero, add_zero] at hsupport
      exact hsupport
    have hsum : ∑ i, w i * g (a i) = 0 := by
      rw [← hmoment, map_sum] at hb
      simpa only [map_smul, smul_eq_mul] using hb
    have hterm : ∀ i, w i * g (a i) = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonpos
        (fun i (_ : i ∈ Finset.univ) => mul_nonpos_of_nonneg_of_nonpos (hw i).le (hcol i))).mp hsum
      exact fun i => h i (Finset.mem_univ i)
    have hg : g.toLinearMap = 0 := by
      apply LinearMap.ext_on_range hspan
      intro i
      exact (mul_eq_zero.mp (hterm i)).resolve_left (hw i).ne'
    apply hf
    apply ContinuousLinearMap.ext
    rintro ⟨x, t⟩
    have hgx : g x = 0 := congrArg (fun h : E →ₗ[ℝ] ℝ => h x) hg
    rw [hsplit, hgx, hzero, mul_zero, add_zero]
    rfl
  refine ⟨(-f (0, 1))⁻¹ • g, ?_, ?_⟩
  · intro i
    change (-f (0, 1))⁻¹ * g (a i) ≤ 1
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ (neg_pos.mpr hnegative)).mpr
    have h := hcolumns i
    rw [hsplit] at h
    linarith
  · change (-f (0, 1))⁻¹ * g b = p
    rw [← div_eq_inv_mul]
    apply (div_eq_iff (neg_ne_zero.mpr hnegative.ne)).mpr
    rw [hsplit] at hsupport
    linarith

/-- A finite equality-constrained unit-cost program with a strictly positive feasible
point and spanning columns has attained primal and dual optima with equal values. -/
theorem exists_primal_dual [FiniteDimensional ℝ E] (a : ι → E) (b : E) (w₀ : ι → ℝ)
    (hw₀ : ∀ i, 0 < w₀ i) (hmoment : FinitePrimal.moment a w₀ = b)
    (hspan : Submodule.span ℝ (Set.range a) = ⊤) :
    ∃ w, FinitePrimal.Feasible a b w ∧ ∃ y : E →L[ℝ] ℝ,
      (∀ i, y (a i) ≤ 1) ∧ y b = FinitePrimal.cost w ∧
        ∀ v, FinitePrimal.Feasible a b v → FinitePrimal.cost w ≤ FinitePrimal.cost v := by
  obtain ⟨w, hw, _, hoptimal⟩ := FinitePrimal.exists_optimal a b w₀ ⟨fun i => (hw₀ i).le, hmoment⟩
  obtain ⟨f, hf, hsupport⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (FinitePrimal.augmentedCone_convex a) (FinitePrimal.optimal_not_mem_interior a b w hoptimal)
    (FinitePrimal.augmentedCone_interior_nonempty a hspan)
  have hpoint : f (b, FinitePrimal.cost w) = 0 := by
    have hzero := hsupport 0 (FinitePrimal.zero_mem_augmentedCone a)
    have htwice : ((2 : ℝ) • b, 2 * FinitePrimal.cost w) ∈ FinitePrimal.augmentedCone a := by
      refine ⟨fun i => 2 * w i, fun i => mul_nonneg (by norm_num) (hw.1 i), ?_, ?_⟩
      · change (∑ i, (2 * w i) • a i) = (2 : ℝ) • b
        simp only [mul_smul, ← Finset.smul_sum]
        exact congrArg (fun x => (2 : ℝ) • x) hw.2
      · simp [FinitePrimal.cost, Finset.mul_sum]
    have htwo := hsupport _ htwice
    change f ((2 : ℝ) • (b, FinitePrimal.cost w)) ≤ f (b, FinitePrimal.cost w) at htwo
    rw [map_smul] at htwo
    simp only [map_zero, smul_eq_mul] at hzero htwo
    linarith
  have hcolumns : ∀ i, f (a i, 1) ≤ 0 := by
    intro i
    simpa only [hpoint] using hsupport _ (FinitePrimal.column_mem_augmentedCone a i)
  have hcost : f (0, 1) ≤ 0 := by
    simpa only [hpoint] using hsupport _ (FinitePrimal.costUnit_mem_augmentedCone a)
  obtain ⟨y, hy, hvalue⟩ := normalize_support a b (FinitePrimal.cost w) w₀ hw₀ hmoment
    hspan f hf hcolumns hcost hpoint
  exact ⟨w, hw, y, hy, hvalue, hoptimal⟩

end Erdos1017.FiniteLinearProgram

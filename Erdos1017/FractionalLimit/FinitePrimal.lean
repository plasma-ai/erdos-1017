module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Finite unit-cost linear programs and their moment-cost cone

This module defines finite unit-cost linear programs by their moment
constraints, proves that feasibility gives an attained minimum
(`exists_optimal`), and introduces the convex moment-cost cone `augmentedCone`,
full-dimensional when the moment columns span, with no optimal point in its
interior.
-/

@[expose] public section

open Set
open scoped BigOperators Topology

namespace Erdos1017.FinitePrimal

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The equality constraints of a finite unit-cost linear program. -/
def moment (a : ι → E) (w : ι → ℝ) : E := ∑ i, w i • a i

/-- Every column has unit cost. -/
def cost (w : ι → ℝ) : ℝ := ∑ i, w i

def Feasible (a : ι → E) (b : E) (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ moment a w = b

theorem coordinate_le_cost {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (i : ι) :
    w i ≤ cost w := by
  exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)

/-- Feasibility alone gives an attained minimum for nonnegative unit costs. -/
theorem exists_optimal (a : ι → E) (b : E) (w₀ : ι → ℝ)
    (hw₀ : Feasible a b w₀) :
    ∃ w, Feasible a b w ∧ cost w ≤ cost w₀ ∧
      ∀ v, Feasible a b v → cost w ≤ cost v := by
  let K : Set (ι → ℝ) := Icc 0 (fun _ => cost w₀) ∩ {w | moment a w = b}
  have hcontinuous : Continuous (moment a) := by unfold moment; fun_prop
  have hcompact : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_eq hcontinuous continuous_const)
  have hmem {w : ι → ℝ} (hw : Feasible a b w) (hc : cost w ≤ cost w₀) : w ∈ K := by
    exact ⟨⟨hw.1, fun i => (coordinate_le_cost hw.1 i).trans hc⟩, hw.2⟩
  have hcost : Continuous (cost : (ι → ℝ) → ℝ) := by unfold cost; fun_prop
  obtain ⟨w, hw, hmin⟩ := hcompact.exists_isMinOn ⟨w₀, hmem hw₀ le_rfl⟩ hcost.continuousOn
  have hw' : Feasible a b w := ⟨hw.1.1, hw.2⟩
  have hc : cost w ≤ cost w₀ := hmin (hmem hw₀ le_rfl)
  refine ⟨w, hw', hc, fun v hv => ?_⟩
  by_cases hv' : cost v ≤ cost w₀
  · exact hmin (hmem hv hv')
  · exact hc.trans (le_of_not_ge hv')

/-- The moment-cost cone includes nonnegative slack in the cost coordinate. -/
def augmentedCone (a : ι → E) : Set (E × ℝ) :=
  {z | ∃ w, (∀ i, 0 ≤ w i) ∧ moment a w = z.1 ∧ cost w ≤ z.2}

theorem augmentedCone_convex (a : ι → E) : Convex ℝ (augmentedCone a) := by
  rintro x ⟨u, hu, hux, huc⟩ y ⟨v, hv, hvy, hvc⟩ s t hs ht _
  refine ⟨fun i => s * u i + t * v i, fun i => add_nonneg
    (mul_nonneg hs (hu i)) (mul_nonneg ht (hv i)), ?_, ?_⟩
  · simp only [moment, add_smul, mul_smul, Finset.sum_add_distrib,
      ← Finset.smul_sum] at *
    exact congrArg₂ (fun x y => s • x + t • y) hux hvy
  · change ∑ i, (s * u i + t * v i) ≤ s * x.2 + t * y.2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left huc hs) (mul_le_mul_of_nonneg_left hvc ht)

theorem zero_mem_augmentedCone (a : ι → E) : (0 : E × ℝ) ∈ augmentedCone a := by
  refine ⟨0, by simp, ?_, ?_⟩ <;> simp [moment, cost]

theorem column_mem_augmentedCone (a : ι → E) (i : ι) : (a i, 1) ∈ augmentedCone a := by
  classical
  refine ⟨Pi.single i 1, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j = i <;> simp [h]
  · simp [moment, Pi.single_apply, ite_smul]
  · simp [cost, Pi.single_apply]

theorem costUnit_mem_augmentedCone (a : ι → E) : (0, (1 : ℝ)) ∈ augmentedCone a := by
  refine ⟨0, by simp, ?_, ?_⟩ <;> simp [moment, cost]

/-- Spanning moment columns give a full-dimensional moment-cost cone. -/
theorem augmentedCone_interior_nonempty [FiniteDimensional ℝ E] (a : ι → E)
    (hspan : Submodule.span ℝ (range a) = ⊤) : (interior (augmentedCone a)).Nonempty := by
  rw [(augmentedCone_convex a).interior_nonempty_iff_affineSpan_eq_top,
    affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ (zero_mem_augmentedCone a))]
  have hfull : Submodule.span ℝ (augmentedCone a) = ⊤ := by
    apply top_unique
    intro z _
    have hcost : (0, (1 : ℝ)) ∈ Submodule.span ℝ (augmentedCone a) :=
      Submodule.subset_span (costUnit_mem_augmentedCone a)
    have hcolumn (i : ι) : (a i, (0 : ℝ)) ∈ Submodule.span ℝ (augmentedCone a) := by
      have h := (Submodule.span ℝ (augmentedCone a)).sub_mem
        (Submodule.subset_span (column_mem_augmentedCone a i)) hcost
      simpa using h
    have hfirst (x : E) (hx : x ∈ Submodule.span ℝ (range a)) :
        (x, (0 : ℝ)) ∈ Submodule.span ℝ (augmentedCone a) := by
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hcolumn i
      | zero => exact (Submodule.span ℝ (augmentedCone a)).zero_mem
      | add x y _ _ hx hy => simpa using (Submodule.span ℝ (augmentedCone a)).add_mem hx hy
      | smul c x _ hx => simpa using (Submodule.span ℝ (augmentedCone a)).smul_mem c hx
    have hsecond := (Submodule.span ℝ (augmentedCone a)).smul_mem z.2 hcost
    simpa using (Submodule.span ℝ (augmentedCone a)).add_mem
      (hfirst z.1 (by rw [hspan]; trivial)) hsecond
  rw [hfull]
  rfl

/-- Decreasing the cost coordinate rules out an interior optimal point. -/
theorem optimal_not_mem_interior (a : ι → E) (b : E) (w : ι → ℝ)
    (hoptimal : ∀ v, Feasible a b v → cost w ≤ cost v) :
    (b, cost w) ∉ interior (augmentedCone a) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h)
  have hnear : (b, cost w - ε / 2) ∈ Metric.ball (b, cost w) ε := by
    simp only [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    have habs : |cost w - ε / 2 - cost w| = ε / 2 := by
      rw [show cost w - ε / 2 - cost w = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    rw [habs, max_eq_right (by linarith)]
    linarith
  obtain ⟨v, hv, hmoment, hcost⟩ := hball hnear
  have hmin := hoptimal v ⟨hv, hmoment⟩
  linarith

end Erdos1017.FinitePrimal

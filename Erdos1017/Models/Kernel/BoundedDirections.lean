module

public import Erdos1017.Models.Kernel.WeightMultiplier

/-!
# Bounded mean-zero weight directions

Every essentially bounded mean-zero L² class comes from a bounded weight
direction with the same class, and a bounded L² row annihilating all bounded
mean-zero directions is constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every essentially bounded mean-zero L² class comes from an actual
bounded weight direction, with exactly the same L² class. -/
theorem exists_direction_of_bounded_mean_zero (f : Lp ℝ 2 μ)
    (hf : f ∈ KernelOperator.boundedL2Submodule μ) (hmean : (∫ x, f x ∂μ) = 0) :
    ∃ g : WeightDirections μ, directionToL2 g = f := by
  obtain ⟨C, hC, hbound⟩ := hf
  have htop : MemLp (fun x => f x) ∞ μ := MemLp.of_bound (Lp.memLp f).aestronglyMeasurable C hbound
  let g := htop.toLp (fun x => f x)
  have heq : boundedToL2 g = f := by
    apply Lp.ext
    exact htop.coeFn_toLp
  have hzero : boundedMean g = 0 := by
    change ⟪Lp.const 2 μ (1 : ℝ), boundedToL2 g⟫ = 0
    rw [heq, KernelOperator.inner_constant_one, hmean]
  exact ⟨⟨g, hzero⟩, heq⟩

theorem constant_one_bounded : Lp.const 2 μ (1 : ℝ) ∈ KernelOperator.boundedL2Submodule μ := by
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with x hx
  rw [hx]
  norm_num

/-- A bounded L² row annihilating all bounded mean-zero directions is
constant. The row itself supplies the centered test, so no density theorem
is assumed. -/
theorem bounded_row_constant_of_annihilates_directions
    (v : Lp ℝ 2 μ) (hv : v ∈ KernelOperator.boundedL2Submodule μ)
    (hann : ∀ f : WeightDirections μ, ⟪v, directionToL2 f⟫ = 0) :
    v = (∫ x, v x ∂μ) • Lp.const 2 μ (1 : ℝ) := by
  let c := ∫ x, v x ∂μ
  let u := Lp.const 2 μ (1 : ℝ)
  have hu : ⟪u, u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  have hcenter : v - c • u ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem hv
      ((KernelOperator.boundedL2Submodule μ).smul_mem c constant_one_bounded)
  have hmean : (∫ x, (v - c • u) x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one, inner_sub_right, real_inner_smul_right]
    change ⟪u, v⟫ - c * ⟪u, u⟫ = 0
    rw [hu]
    rw [KernelOperator.inner_constant_one]
    simp [c]
  obtain ⟨f, hf⟩ := exists_direction_of_bounded_mean_zero (v - c • u) hcenter hmean
  have horth : ⟪v, v - c • u⟫ = 0 := by rw [← hf]; exact hann f
  have hunit : ⟪u, v - c • u⟫ = 0 := by
    rw [KernelOperator.inner_constant_one]
    exact hmean
  have hz : ⟪v - c • u, v - c • u⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, horth, hunit, mul_zero, sub_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

end Erdos1017.Variation

module

public import Erdos1017.Models.Kernel.BoundedDirections
public import Erdos1017.Models.Kernel.KernelBoundedRange
public import Erdos1017.Models.Kernel.RangePositiveIndex

/-!
# Regular local maxima under vertex weights

Regular local maximality under vertex weights supplies a constant shifted row
and positive spectral index at most two
(`exists_stationary_shift_of_weight_local_max`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Regular local maximality under vertex weights supplies both a constant
shifted row and positive spectral index at most two. The compact operators
are required to have bounded ranges, as actual bounded kernels do. -/
theorem exists_stationary_shift_of_weight_local_max
    (A Y : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hAcompact : IsCompactOperator A) (hYcompact : IsCompactOperator Y)
    (hA : A.toLinearMap.IsSymmetric) (hY : Y.toLinearMap.IsSymmetric)
    (hArange : ∀ f, A f ∈ KernelOperator.boundedL2Submodule μ)
    (hYrange : ∀ f, Y f ∈ KernelOperator.boundedL2Submodule μ)
    (hregular : weightFirstVariation A ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hmax : ∀ f : WeightDirections μ, ‖f‖ < ε →
      ⟪A (Lp.const 2 μ (1 : ℝ) + directionToL2 f), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ =
        ⟪A (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ →
      ⟪Y (Lp.const 2 μ (1 : ℝ) + directionToL2 f), Lp.const 2 μ (1 : ℝ) + directionToL2 f⟫ ≤
        ⟪Y (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) :
    ∃ m ν : ℝ, weightFirstVariation Y = m • weightFirstVariation A ∧
      (Y - m • A) (Lp.const 2 μ (1 : ℝ)) = ν • Lp.const 2 μ (1 : ℝ) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (Y - m • A)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (Y - m • A)) ≤ 2 := by
  obtain ⟨m, hm, hquad, _⟩ := exists_multiplier_of_weight_local_max A Y hA hY hregular ε hε hεone hmax
  let M := Y - m • A
  let u := Lp.const 2 μ (1 : ℝ)
  have hMrange (f : Lp ℝ 2 μ) : M f ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem (hYrange f)
      ((KernelOperator.boundedL2Submodule μ).smul_mem m (hArange f))
  have hann (f : WeightDirections μ) : ⟪M u, directionToL2 f⟫ = 0 := by
    have h := LinearMap.congr_fun hm f
    change 2 * ⟪Y u, directionToL2 f⟫ = m * (2 * ⟪A u, directionToL2 f⟫) at h
    change ⟪Y u - m • A u, directionToL2 f⟫ = 0
    rw [inner_sub_left, real_inner_smul_left]
    linarith
  have hrow := bounded_row_constant_of_annihilates_directions (M u) (hMrange u) hann
  let C := (innerSL ℝ u).toLinearMap.prod (innerSL ℝ (A u)).toLinearMap
  have htest (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ) (hc : C f = 0) :
      ⟪M f, f⟫ ≤ 0 := by
    have hmean : (∫ x, f x ∂μ) = 0 := by
      rw [← KernelOperator.inner_constant_one]
      exact congrArg Prod.fst hc
    obtain ⟨g, hg⟩ := exists_direction_of_bounded_mean_zero f hf hmean
    have hz : weightFirstVariation A g = 0 := by
      change 2 * ⟪A u, directionToL2 g⟫ = 0
      rw [hg]
      have hh : ⟪A u, f⟫ = 0 := congrArg Prod.snd hc
      rw [hh, mul_zero]
    have h := hquad g hz
    rwa [hg] at h
  have hMcompact : IsCompactOperator M := hYcompact.sub (hAcompact.smul m)
  have hMsym : M.toLinearMap.IsSymmetric := hY.sub (hA.smul (by simp))
  have hindex := KernelOperator.positive_subspace_dimension_le_range_constraints
    M hMcompact hMsym C (KernelOperator.boundedL2Submodule μ) hMrange htest
  refine ⟨m, ∫ x, M u x ∂μ, hm, hrow, hindex.1, ?_⟩
  simpa using hindex.2

end Erdos1017.Variation

module

public import Erdos1017.Models.Kernel.KernelOperator
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith

/-!
# Compactness of bounded kernel operators

A common pointwise bound upgrades almost-everywhere convergence to L2
convergence, and the integral operator of a bounded measurable kernel sends
bounded weakly convergent sequences to strongly convergent ones, so it is a
compact operator on a separable L2 space (`operator_isCompact`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- A bounded sequence in a separable real Hilbert space has a subsequence
converging against every Hilbert test vector. -/
theorem exists_weak_subsequence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : E, ‖v‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ w : E, Tendsto (fun n => ⟪u (φ n), w⟫) atTop (𝓝 ⟪v, w⟫) := by
  let d : ℕ → WeakDual ℝ E := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u n))
  have hd (n : ℕ) : d n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) C := by
    simpa [d, Metric.mem_closedBall, dist_zero_right] using hu n
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E 0 C) hd
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual v), ?_, φ, hφ, ?_⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using hv
  · intro w
    have h := ((WeakDual.eval_continuous w).tendsto v).comp hlim
    simpa [d, Function.comp_def, InnerProductSpace.toDual_symm_apply] using h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A common pointwise bound upgrades almost-everywhere convergence to L2
convergence on a probability space. -/
theorem bounded_ae_tendsto_L2 (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hu : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ C)
    (hv : ∀ᵐ x ∂μ, ‖v x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto u atTop (𝓝 v) := by
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖‖u n x - v x‖ ^ 2‖ ≤ (2 * C) ^ 2 := by
    filter_upwards [hu n, hv] with x hx hy
    have hd := (norm_sub_le (u n x) (v x)).trans (add_le_add hx hy)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (u n x - v x)]
  have hs := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => ‖u n x - v x‖ ^ 2) (f := fun _ => 0)
    (fun _ => (2 * C) ^ 2)
    (fun n => ((Lp.memLp (u n)).aestronglyMeasurable.sub
      (Lp.memLp v).aestronglyMeasurable).norm.pow 2)
    (integrable_const _) hbound (hlim.mono fun x hx => by
      simpa using ((hx.sub (tendsto_const_nhds (x := v x))).norm.pow 2))
  have heq (n : ℕ) : (∫ x, ‖u n x - v x‖ ^ 2 ∂μ) = ‖u n - v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) v] with x hx
    rw [hx, Pi.sub_apply, real_inner_self_eq_norm_sq]
  simp only [heq, integral_zero] at hs
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- Kernel rows are L2 vectors for almost every row. -/
theorem ae_memLp_row {K : Ω → Ω → ℝ} {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) :
    ∀ᵐ x ∂μ, MemLp (K x) 2 μ := by
  have hi : Integrable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ) :=
    (show MemLp (fun z : Ω × Ω => K z.1 z.2) 1 (μ.prod μ) from
      MemLp.of_bound hK B hB).integrable le_rfl
  filter_upwards [hi.prod_right_ae, Measure.ae_ae_of_ae_prod hB] with x hx hb
  exact MemLp.of_bound hx.aestronglyMeasurable B hb

omit [IsProbabilityMeasure μ] in
theorem applyKernel_eq_inner {K : Ω → Ω → ℝ} {x : Ω}
    (hx : MemLp (K x) 2 μ) (f : Lp ℝ 2 μ) :
    applyKernel (μ := μ) K f x = ⟪f, hx.toLp (K x)⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx.coeFn_toLp] with y hy
  simp only [RCLike.inner_apply, conj_trivial, hy]

/-- The integral operator sends bounded weakly convergent sequences to
strongly convergent sequences. -/
theorem operator_tendsto_of_weak (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) (hv : ‖v‖ ≤ C)
    (hweak : ∀ w : Lp ℝ 2 μ,
      Tendsto (fun n => ⟪u n, w⟫) atTop (𝓝 ⟪v, w⟫)) :
    Tendsto (fun n => operator K hB0 hK hB (u n)) atTop
      (𝓝 (operator K hB0 hK hB v)) := by
  have hbnd (f : Lp ℝ 2 μ) (hf : ‖f‖ ≤ C) :
      ∀ᵐ x ∂μ, ‖onL2 K hK hB f x‖ ≤ B * C := by
    filter_upwards [onL2_coe K hK hB f,
      applyKernel_bound hB ((Lp.memLp f).integrable (by norm_num))] with x hx hb
    rw [hx]
    exact hb.trans (mul_le_mul_of_nonneg_left ((integral_norm_le_L2 f).trans hf) hB0)
  apply bounded_ae_tendsto_L2 _ _ (B * C) (mul_nonneg hB0 hC)
    (fun n => hbnd (u n) (hu n)) (hbnd v hv)
  have hall : ∀ᵐ x ∂μ, ∀ n, onL2 K hK hB (u n) x = applyKernel (μ := μ) K (u n) x :=
    ae_all_iff.mpr (fun n => onL2_coe K hK hB (u n))
  filter_upwards [ae_memLp_row hK hB, hall, onL2_coe K hK hB v] with x hx hurow hvrow
  simp_rw [hurow, hvrow, applyKernel_eq_inner hx]
  exact hweak _

/-- Bounded measurable kernels define compact operators on a separable L2
space. This includes the standard atomless realization used by the source. -/
theorem operator_isCompact [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) :
    IsCompactOperator (operator K hB0 hK hB) := by
  let T := operator K hB0 hK hB
  have hcompact : IsSeqCompact (T '' Metric.closedBall (0 : Lp ℝ 2 μ) 1) := by
    intro u hu
    choose f hf hfeq using hu
    have hfn (n : ℕ) : ‖f n‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hf n
    obtain ⟨v, hv, φ, hφ, hweak⟩ := exists_weak_subsequence f 1 hfn
    refine ⟨T v, ⟨v, ?_, rfl⟩, φ, hφ, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    · have hlim := operator_tendsto_of_weak K hB0 hK hB (fun n => f (φ n)) v 1
        zero_le_one (fun n => hfn (φ n)) hv hweak
      simpa only [Function.comp_def, ← hfeq] using hlim
  exact (isCompactOperator_iff_image_closedBall_subset_compact T.toLinearMap zero_lt_one).mpr
    ⟨_, hcompact.isCompact, Set.Subset.rfl⟩

end Erdos1017.KernelOperator

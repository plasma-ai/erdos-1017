module

public import Erdos1017.Models.PhysicalPrimal.FiniteEnergyBound
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert feature maps from countable coordinates

Countable, almost-everywhere square-summable measurable coordinates define a
strongly measurable Hilbert feature map (`l2Feature`) whose norm is the sum of
the coordinate energies, and a family with summable weighted energy has a
measurable Hilbert realization with the same energy bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The coordinate family, interpreted in Hilbert space wherever it is square
summable, and set to zero elsewhere. -/
def l2Feature (f : ι → Ω → ℝ) (x : Ω) : lp (fun _ : ι => ℝ) 2 := by
  classical
  exact if h : Memℓp (fun i => f i x) 2 then ⟨fun i => f i x, h⟩ else 0

theorem memℓp_of_summable_sq (a : ι → ℝ) (ha : Summable (fun i => (a i) ^ 2)) :
    Memℓp a 2 := by
  apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
  simpa using ha

omit [MeasurableSpace Ω] in
theorem l2Feature_apply (f : ι → Ω → ℝ) (x : Ω)
    (hx : Summable (fun i => (f i x) ^ 2)) (i : ι) : l2Feature f x i = f i x := by
  classical
  simp [l2Feature, memℓp_of_summable_sq _ hx]

/-- Countable, almost-everywhere square-summable measurable coordinates define
an almost-everywhere strongly measurable Hilbert feature map. -/
theorem l2Feature_aestronglyMeasurable [Countable ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hsum : ∀ᵐ x ∂μ, Summable (fun i => (f i x) ^ 2)) :
    AEStronglyMeasurable (l2Feature f) μ := by
  classical
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, lp.single 2 i (f i x))
  · intro s
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : ι => ℝ) 2 i).continuous.comp_aestronglyMeasurable (hf i)
  · filter_upwards [hsum] with x hx
    have h := lp.hasSum_single (p := 2) (by norm_num) (l2Feature f x)
    simpa only [HasSum, SummationFilter.unconditional, l2Feature_apply f x hx] using h

omit [MeasurableSpace Ω] in
/-- The Hilbert norm is exactly the sum of the coordinate energies. -/
theorem l2Feature_norm_sq (f : ι → Ω → ℝ) (x : Ω)
    (hx : Summable (fun i => (f i x) ^ 2)) :
    ‖l2Feature f x‖ ^ 2 = ∑' i, (f i x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  simp only [RCLike.inner_apply, conj_trivial, l2Feature_apply f x hx, ← pow_two]

/-- A countable family with summable weighted energy has a measurable Hilbert
realization with exactly those coordinates and the same energy bound. -/
theorem exists_weighted_l2Feature [Countable ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (D : ℝ)
    (henergy : ∀ᵐ x ∂μ, Summable (fun i => w i * (f i x) ^ 2) ∧
      (∑' i, w i * (f i x) ^ 2) ≤ D) :
    ∃ F : Ω → lp (fun _ : ι => ℝ) 2, AEStronglyMeasurable F μ ∧
      (∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt (w i) * f i x) ∧
      ∀ᵐ x ∂μ, ‖F x‖ ^ 2 ≤ D := by
  let g : ι → Ω → ℝ := fun i x => Real.sqrt (w i) * f i x
  have heq (x : Ω) : (fun i => (g i x) ^ 2) = (fun i => w i * (f i x) ^ 2) := by
    funext i
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hsum : ∀ᵐ x ∂μ, Summable (fun i => (g i x) ^ 2) := by
    filter_upwards [henergy] with x hx
    rw [heq]
    exact hx.1
  refine ⟨l2Feature g, l2Feature_aestronglyMeasurable g (fun i => (hf i).const_mul _) hsum, ?_, ?_⟩
  · filter_upwards [hsum] with x hx
    exact fun i => l2Feature_apply g x hx i
  · filter_upwards [hsum, henergy] with x hx he
    rw [l2Feature_norm_sq g x hx, heq]
    exact he.2

end Erdos1017.KernelOperator

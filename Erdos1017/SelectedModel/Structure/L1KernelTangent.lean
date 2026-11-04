module

public import Erdos1017.SelectedModel.Structure.IntegrableRealClips
public import Erdos1017.SelectedModel.Structure.DegreeStraddle

/-!
# Tangent inequality for integrable inputs

This module defines the unhalved physical kernel energy `kernelEnergy` for `L¹`
inputs and extends the bounded tangent inequality to every integrable tangent
input by clipping and exact mean and degree corrections, with the transverse
direction supplied by regularity or a strict benchmark gap.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace Topology

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual unhalved physical kernel energy, defined also for L¹ inputs. -/
def kernelEnergy (K : Ω → Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∫ p : Ω × Ω, K p.1 p.2 * f p.2 * f p.1 ∂μ.prod μ

/-- Bounded kernels have integrable bilinear products on actual L¹ inputs. -/
theorem integrable_kernel_bilinear
    {K : Ω → Ω → ℝ} {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun p : Ω × Ω => K p.1 p.2 * f p.2 * g p.1) (μ.prod μ) := by
  apply ((hg.norm.mul_prod hf.norm).const_mul B).mono'
    ((hK.mul hf.aestronglyMeasurable.comp_snd).mul hg.aestronglyMeasurable.comp_fst)
  filter_upwards [hB] with p hp
  simp only [Pi.mul_apply, norm_mul]
  calc
    ‖K p.1 p.2‖ * ‖f p.2‖ * ‖g p.1‖ ≤ B * ‖f p.2‖ * ‖g p.1‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (norm_nonneg _)
    _ = B * (‖g p.1‖ * ‖f p.2‖) := by ring

/-- Actual clipping and exact mean/degree corrections extend the bounded
physical tangent inequality to every integrable tangent input. The supplied
transverse direction is an actual bounded mean-zero function; no
approximation or energy bound is assumed. -/
theorem integrable_tangent_nonpositive
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g μ)
    {Cg : ℝ} (hgBound : ∀ᵐ x ∂μ, ‖g x‖ ≤ Cg)
    (u : Ω → ℝ) (hu : Integrable u μ) {Cu : ℝ} (hCu : 0 ≤ Cu)
    (huBound : ∀ᵐ x ∂μ, ‖u x‖ ≤ Cu) (humean : (∫ x, u x ∂μ) = 0)
    (htrans : (∫ x, g x * u x ∂μ) ≠ 0)
    (hnonpos : ∀ v : Ω → ℝ, Integrable v μ →
      (∃ C ≥ (0 : ℝ), ∀ᵐ x ∂μ, ‖v x‖ ≤ C) →
      (∫ x, v x ∂μ) = 0 → (∫ x, g x * v x ∂μ) = 0 → kernelEnergy (μ := μ) K v ≤ 0)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hmean : (∫ x, f x ∂μ) = 0) (hdegree : (∫ x, g x * f x ∂μ) = 0) :
    kernelEnergy (μ := μ) K f ≤ 0 := by
  let F (n : ℕ) (x : Ω) := realClip n (f x)
  let a (n : ℕ) := ∫ x, F n x ∂μ
  let e := ∫ x, g x * u x ∂μ
  let b (n : ℕ) := ((∫ x, g x * F n x ∂μ) - a n * ∫ x, g x ∂μ) / e
  let v (n : ℕ) (x : Ω) := F n x - a n - b n * u x
  have hgInt : Integrable g μ := (integrable_const Cg).mono' hg hgBound
  have hgu := integrable_bounded_mul hg hgBound hu
  have hF (n : ℕ) : Integrable (F n) μ := realClip_integrable n hf
  have hgF (n : ℕ) : Integrable (fun x => g x * F n x) μ :=
    integrable_bounded_mul hg hgBound (hF n)
  have hv (n : ℕ) : Integrable (v n) μ :=
    ((hF n).sub (integrable_const (a n))).sub (hu.const_mul (b n))
  have hvBound (n : ℕ) : ∃ C ≥ (0 : ℝ), ∀ᵐ x ∂μ, ‖v n x‖ ≤ C := by
    refine ⟨(n : ℝ) + ‖a n‖ + ‖b n‖ * Cu, by positivity, ?_⟩
    filter_upwards [huBound] with x hx
    calc
      ‖v n x‖ ≤ ‖F n x‖ + ‖a n‖ + ‖b n * u x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (n : ℝ) + ‖a n‖ + ‖b n‖ * Cu := by
        rw [norm_mul]
        exact add_le_add (add_le_add (realClip_norm_le n (f x)) le_rfl)
          (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hvm (n : ℕ) : (∫ x, v n x ∂μ) = 0 := by
    have hc : Integrable (fun x => F n x - a n) μ := (hF n).sub (integrable_const (a n))
    rw [show v n = (fun x => F n x - a n - b n * u x) from rfl,
      integral_sub hc (hu.const_mul (b n)),
      integral_sub (hF n) (integrable_const (a n)), integral_const_mul, humean]
    simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero]
    exact sub_self _
  have hvd (n : ℕ) : (∫ x, g x * v n x ∂μ) = 0 := by
    have heq : (fun x => g x * v n x) =
        (fun x => (g x * F n x - a n * g x) - b n * (g x * u x)) := by
      funext x
      dsimp only [v]
      ring
    have hc : Integrable (fun x => g x * F n x - a n * g x) μ :=
      (hgF n).sub (hgInt.const_mul (a n))
    rw [heq, integral_sub hc (hgu.const_mul (b n)),
      integral_sub (hgF n) (hgInt.const_mul (a n)), integral_const_mul, integral_const_mul]
    change (∫ x, g x * F n x ∂μ) - a n * (∫ x, g x ∂μ) - b n * e = 0
    rw [show b n * e = (∫ x, g x * F n x ∂μ) - a n * ∫ x, g x ∂μ from
      div_mul_cancel₀ _ htrans, sub_self]
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [hmean] using integral_realClip_tendsto hf
  have hb : Tendsto b atTop (𝓝 0) := by
    have hw := integral_mul_realClip_tendsto hg hgBound hf
    have h := (hw.sub (ha.mul_const (∫ x, g x ∂μ))).div_const e
    simpa only [hdegree, zero_mul, sub_self, zero_div] using h
  have hvlim (x : Ω) : Tendsto (fun n => v n x) atTop (𝓝 (f x)) := by
    have h := ((realClip_tendsto (f x)).sub ha).sub (hb.mul_const (u x))
    simpa only [sub_zero, zero_mul] using h
  let H (x : Ω) := ‖f x‖ + 1 + Cu
  have hH : Integrable H μ := (hf.norm.add (integrable_const 1)).add (integrable_const Cu)
  have hHpos (x : Ω) : 0 ≤ H x := by dsimp only [H]; positivity
  have hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, ‖v n x‖ ≤ H x := by
    have hasmall := ha.norm.eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ < 1 by norm_num))
    have hbsmall := hb.norm.eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ < 1 by norm_num))
    filter_upwards [hasmall, hbsmall] with n han hbn
    filter_upwards [huBound] with x hx
    have hbux : ‖b n * u x‖ ≤ Cu := by
      rw [norm_mul]
      calc
        ‖b n‖ * ‖u x‖ ≤ 1 * Cu := mul_le_mul hbn.le hx (norm_nonneg _) (by norm_num)
        _ = Cu := one_mul _
    calc
      ‖v n x‖ ≤ ‖F n x‖ + ‖a n‖ + ‖b n * u x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ H x := add_le_add (add_le_add (realClip_norm_le_self n (f x)) han.le) hbux
  have hq (n : ℕ) : kernelEnergy (μ := μ) K (v n) ≤ 0 :=
    hnonpos (v n) (hv n) (hvBound n) (hvm n) (hvd n)
  have hlimit : Tendsto (fun n => kernelEnergy (μ := μ) K (v n)) atTop
      (𝓝 (kernelEnergy (μ := μ) K f)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p : Ω × Ω => B * (H p.1 * H p.2))
    · exact Eventually.of_forall (fun n =>
        (hK.mul (hv n).aestronglyMeasurable.comp_snd).mul (hv n).aestronglyMeasurable.comp_fst)
    · filter_upwards [hdom] with n hn
      filter_upwards [hB, Measure.quasiMeasurePreserving_fst.ae hn,
        Measure.quasiMeasurePreserving_snd.ae hn] with p hp hpx hpy
      simp only [norm_mul]
      calc
        ‖K p.1 p.2‖ * ‖v n p.2‖ * ‖v n p.1‖ ≤ B * H p.2 * H p.1 :=
          mul_le_mul (mul_le_mul hp hpy (norm_nonneg _) hB0) hpx (norm_nonneg _)
            (mul_nonneg hB0 (hHpos _))
        _ = B * (H p.1 * H p.2) := by ring
    · exact (hH.mul_prod hH).const_mul B
    · exact Eventually.of_forall (fun p => (tendsto_const_nhds.mul (hvlim p.2)).mul (hvlim p.1))
  exact le_of_tendsto hlimit (Eventually.of_forall hq)

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original full optimum's regularity constructs a bounded transverse
direction, so its tangent inequality holds for every integrable physical
function. The function need not belong to L² or be essentially bounded. -/
theorem FullStationaryClass.integrable_tangent_nonpositive
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (f : Ω → ℝ) (hf : Integrable f μ) (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * f x ∂μ) = 0) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) f ≤ 0 := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hgBound : g ∈ KernelOperator.boundedL2Submodule μ :=
    KernelOperator.operator_range_bounded _ _ _ _ _
  obtain ⟨Cg, _, hgBound⟩ := hgBound
  have hex : ∃ v : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hregular (LinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  let u := Variation.directionToL2 v
  have huBound : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖v.val‖ := Variation.bounded_ae_norm_le v.val
  have hinner (q : Lp ℝ 2 μ) : ⟪g, q⟫ = ∫ x, g x * q x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring)
  have htrans : (∫ x, g x * u x ∂μ) ≠ 0 := by
    intro hz
    apply hv
    change 2 * ⟪g, u⟫ = 0
    rw [hinner, hz, mul_zero]
  apply KernelOperator.integrable_tangent_nonpositive (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    (g : Ω → ℝ) (Lp.memLp g).aestronglyMeasurable hgBound
    (u : Ω → ℝ) ((Lp.memLp u).integrable (by norm_num)) (norm_nonneg v.val)
    huBound (Variation.direction_integral_zero v) htrans ?_ f hf hmean hdegree
  intro z hz hzb hzm hzd
  obtain ⟨C, hC, hzBound⟩ := hzb
  have hzLp : MemLp z 2 μ := MemLp.of_bound hz.aestronglyMeasurable C hzBound
  let q := hzLp.toLp z
  have hqBound : q ∈ KernelOperator.boundedL2Submodule μ := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [hzLp.coeFn_toLp, hzBound] with x hx hb
    rwa [hx]
  have hqm : (∫ x, q x ∂μ) = 0 := (integral_congr_ae hzLp.coeFn_toLp).trans hzm
  have hqd : ⟪g, q⟫ = 0 := by
    rw [hinner]
    calc
      _ = ∫ x, g x * z x ∂μ := integral_congr_ae
        (hzLp.coeFn_toLp.mono (fun x hx => by rw [hx]))
      _ = 0 := hzd
  have hq := hW.bounded_tangent_nonpositive hregular q hqBound hqm hqd
  have heq : ⟪shiftedOperator W m q, q⟫ =
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) z := by
    rw [shiftedOperator, KernelOperator.operator_inner]
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hzLp.coeFn_toLp,
      Measure.quasiMeasurePreserving_snd.ae hzLp.coeFn_toLp] with p hp hq
    rw [hp, hq]
  rwa [heq] at hq

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A genuine strict benchmark gap supplies the original regularity needed
to extend the same model's tangent inequality to arbitrary integrable inputs. -/
theorem FullStationaryClass.integrable_tangent_nonpositive_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (f : Ω → ℝ) (hf : Integrable f μ) (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * f x ∂μ) = 0) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) f ≤ 0 :=
  hW.integrable_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular f hf hmean hdegree

end Erdos1017.CappedModel

module

public import Erdos1017.SelectedModel.Flows.IntegrableDensityReturn

/-!
# Relative tilt directions for integrable weights

An interior affine law from an integrable direction is equivalent to the
original law, and the relative direction `relativeTiltDirection` is bounded,
integrable and mean zero under the changed law, with an exact kernel pairing
expansion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The old direction expressed relative to its own affine changed law. -/
def relativeTiltDirection (v : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  v x / integrableTiltWeight v t x

omit [IsProbabilityMeasure μ] in
/-- Interior affine weights have a positive lower bound even when the
original integrable direction is unbounded above. -/
theorem integrableTiltWeight_lower (v : Ω → ℝ) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : 0 ≤ t) : ∀ᵐ x ∂μ, 1 - t ≤ integrableTiltWeight v t x := by
  filter_upwards [hbelow] with x hx
  change 1 - t ≤ 1 + t * v x
  nlinarith [mul_nonneg ht (show 0 ≤ v x + 1 by linarith)]

/-- An interior affine law is equivalent to the original probability law. -/
theorem integrableTilt_measure_equivalent (v : Ω → ℝ) (hv : Integrable v μ)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    μ ≪ weightedMeasure (μ := μ) (integrableTiltWeight v t) ∧
      weightedMeasure (μ := μ) (integrableTiltWeight v t) ≪ μ := by
  refine ⟨?_, withDensity_absolutelyContinuous _ _⟩
  apply withDensity_absolutelyContinuous'
    (integrableTiltWeight_integrable v hv t).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  filter_upwards [integrableTiltWeight_lower v hbelow t ht.1.le] with x hx
  exact (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le (sub_pos.mpr ht.2) hx)).ne'

omit [IsProbabilityMeasure μ] in
/-- The relative direction is bounded by an explicit finite constant under
the original measure. The two one-sided bounds use only v≥−1 and 0<t<1. -/
theorem relativeTiltDirection_bound (v : Ω → ℝ) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, ‖relativeTiltDirection v t x‖ ≤ (1 - t)⁻¹ + t⁻¹ := by
  filter_upwards [hbelow, integrableTiltWeight_lower v hbelow t ht.1.le] with x hx hρ
  have hρpos : 0 < integrableTiltWeight v t x := (sub_pos.mpr ht.2).trans_le hρ
  have hlo : -1 / (1 - t) ≤ relativeTiltDirection v t x := by
    apply (div_le_div_iff₀ (sub_pos.mpr ht.2) hρpos).mpr
    change -1 * (1 + t * v x) ≤ v x * (1 - t)
    nlinarith
  have hhi : relativeTiltDirection v t x ≤ 1 / t := by
    apply (div_le_div_iff₀ hρpos ht.1).mpr
    change v x * t ≤ 1 * (1 + t * v x)
    nlinarith
  rw [Real.norm_eq_abs, abs_le]
  have hleft : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr (sub_pos.mpr ht.2).le
  have hright : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.1.le
  simp only [neg_div, one_div] at hlo hhi
  constructor <;> linarith

omit [IsProbabilityMeasure μ] in
/-- Multiplying the actual relative direction by its positive weight
recovers the old physical direction almost everywhere. -/
theorem relativeTiltDirection_mul_weight (v : Ω → ℝ) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, integrableTiltWeight v t x * relativeTiltDirection v t x = v x := by
  filter_upwards [integrableTiltWeight_lower v hbelow t ht.1.le] with x hx
  have hp : 0 < integrableTiltWeight v t x := (sub_pos.mpr ht.2).trans_le hx
  exact mul_div_cancel₀ _ hp.ne'

omit [IsProbabilityMeasure μ] in
/-- A real weighted integral is exactly its old-measure density integral. -/
theorem integral_weightedMeasure_real (w : Ω → ℝ) (hw : AEMeasurable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (f : Ω → ℝ) :
    (∫ x, f x ∂weightedMeasure (μ := μ) w) = ∫ x, w x * f x ∂μ := by
  rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul₀ hw.ennreal_ofReal]
  · apply integral_congr_ae
    filter_upwards [hw0] with x hx
    simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- The actual relative direction has zero mean under the changed law. -/
theorem relativeTiltDirection_integral (v : Ω → ℝ) (hv : Integrable v μ)
    (hmean : (∫ x, v x ∂μ) = 0) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x, relativeTiltDirection v t x
      ∂weightedMeasure (μ := μ) (integrableTiltWeight v t)) = 0 := by
  rw [integral_weightedMeasure_real _
    (integrableTiltWeight_integrable v hv t).aestronglyMeasurable.aemeasurable
    (integrableTiltWeight_nonnegative v hbelow t ⟨ht.1.le, ht.2.le⟩)]
  exact (integral_congr_ae (relativeTiltDirection_mul_weight v hbelow t ht)).trans hmean

/-- The relative direction is an actual integrable bounded function under
the returned probability law, without assuming boundedness of the old v. -/
theorem relativeTiltDirection_integrable_bound (v : Ω → ℝ) (hv : Integrable v μ)
    (hmean : (∫ x, v x ∂μ) = 0) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (relativeTiltDirection v t) (weightedMeasure (μ := μ) (integrableTiltWeight v t)) ∧
      ∀ᵐ x ∂weightedMeasure (μ := μ) (integrableTiltWeight v t),
        ‖relativeTiltDirection v t x‖ ≤ (1 - t)⁻¹ + t⁻¹ := by
  have := integrableTilt_probability v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩
  have hac := (integrableTilt_measure_equivalent v hv hbelow t ht).2
  have hm : AEStronglyMeasurable (relativeTiltDirection v t) μ :=
    (hv.aestronglyMeasurable.aemeasurable.div
      (integrableTiltWeight_integrable v hv t).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hb := hac.ae_le (relativeTiltDirection_bound v hbelow t ht)
  exact ⟨Integrable.of_bound (hm.mono_ac hac) _ hb, hb⟩

/-- Both slots of an actual physical kernel pairing acquire the real
vertex density when the probability law is changed. -/
theorem kernelPairing_weightedMeasure (w : Ω → ℝ) (hw : AEMeasurable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (K : Ω → Ω → ℝ) (f g : Ω → ℝ) :
    KernelOperator.kernelPairing (μ := weightedMeasure (μ := μ) w) K f g =
      KernelOperator.kernelPairing (μ := μ) K (fun x => w x * f x) (fun x => w x * g x) := by
  rw [KernelOperator.kernelPairing, integral_weightedMeasure_prod w hw hw0
    (fun x y => K x y * f y * g x)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by ring)

/-- Testing the changed law against its bounded relative direction equals
an actual old-law test against v; no changed multiplier is substituted. -/
theorem kernelPairing_relativeTilt (v : Ω → ℝ) (hv : Integrable v μ)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (K : Ω → Ω → ℝ) :
    KernelOperator.kernelPairing
      (μ := weightedMeasure (μ := μ) (integrableTiltWeight v t)) K
        (fun _ => 1) (relativeTiltDirection v t) =
      KernelOperator.kernelPairing (μ := μ) K (integrableTiltWeight v t) v := by
  rw [kernelPairing_weightedMeasure _
    (integrableTiltWeight_integrable v hv t).aestronglyMeasurable.aemeasurable
    (integrableTiltWeight_nonnegative v hbelow t ⟨ht.1.le, ht.2.le⟩)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (relativeTiltDirection_mul_weight v hbelow t ht)] with p hp
  simp only [mul_one, hp]

/-- The relative test's changed-law pairing expands exactly as the old
linear pairing plus t times the old unhalved quadratic energy. -/
theorem kernelPairing_relativeTilt_eq (v : Ω → ℝ) (hv : Integrable v μ)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) :
    KernelOperator.kernelPairing
      (μ := weightedMeasure (μ := μ) (integrableTiltWeight v t)) K
        (fun _ => 1) (relativeTiltDirection v t) =
      KernelOperator.kernelPairing (μ := μ) K (fun _ => 1) v +
        t * KernelOperator.kernelEnergy (μ := μ) K v := by
  rw [kernelPairing_relativeTilt v hv hbelow t ht]
  have heq : (fun p : Ω × Ω => K p.1 p.2 * integrableTiltWeight v t p.2 * v p.1) =
      (fun p => K p.1 p.2 * 1 * v p.1 + t * (K p.1 p.2 * v p.2 * v p.1)) := by
    funext p
    dsimp only [integrableTiltWeight]
    ring
  rw [KernelOperator.kernelPairing, heq,
    integral_add (KernelOperator.integrable_kernel_bilinear hK hB (integrable_const 1) hv)
      ((KernelOperator.integrable_kernel_bilinear hK hB hv hv).const_mul t), integral_const_mul]
  rfl

/-- The physical mixed pairing respects the original scalar shift for
arbitrary integrable arguments. -/
theorem shifted_kernelPairing (W : Model Ω μ) (m : ℝ) (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) f g =
      KernelOperator.kernelPairing (μ := μ) (chargeKernel W) f g -
        m * KernelOperator.kernelPairing (μ := μ) (adjacencyKernel W) f g := by
  have heq : (fun p : Ω × Ω => shiftedKernel W m p.1 p.2 * f p.2 * g p.1) =
      (fun p => chargeKernel W p.1 p.2 * f p.2 * g p.1 -
        m * (adjacencyKernel W p.1 p.2 * f p.2 * g p.1)) := by
    funext p
    rw [shiftedKernel, shiftedMoment_eq]
    change (chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2) * _ * _ = _
    ring
  rw [KernelOperator.kernelPairing, heq,
    integral_sub (KernelOperator.integrable_kernel_bilinear
      (chargeKernel_measurable W) (chargeKernel_bound W) hf hg)
      ((KernelOperator.integrable_kernel_bilinear
        (adjacencyKernel_measurable W) (adjacencyKernel_bound W) hf hg).const_mul m),
    integral_const_mul]
  rfl

end Erdos1017.CappedModel

module

public import Erdos1017.Exclusions.Common.Flows.FullForwardDiffuseRerouting

/-!
# Energy credit of the uniform recipient subflow

The uniform recipient subflow `uniformSubflow` is dominated by the convexly
rerouted flow, and the full interpolated flow pays at least the uniform
recipient energy through this subflow and same-model energy monotonicity; basic
kernel-energy lemmas are included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual unhalved kernel energy respects equality on the original law. -/
theorem kernelEnergy_congr_ae (K : Ω → Ω → ℝ) {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
    kernelEnergy (μ := μ) K f = kernelEnergy (μ := μ) K g := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfg,
    Measure.quasiMeasurePreserving_snd.ae hfg] with p hx hy
  rw [hx, hy]

omit [IsProbabilityMeasure μ] in
/-- Scalar multiplication of an actual density squares its energy factor. -/
theorem kernelEnergy_const_mul (K : Ω → Ω → ℝ) (f : Ω → ℝ) (a : ℝ) :
    kernelEnergy (μ := μ) K (fun x => a * f x) = a ^ 2 * kernelEnergy (μ := μ) K f := by
  unfold kernelEnergy
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

/-- A nonnegative kernel has nonnegative energy on every nonnegative density;
this asserts no positivity on arbitrary signed inputs. -/
theorem kernelEnergy_nonnegative_of_nonnegative (K : Ω → Ω → ℝ)
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2) (f : Ω → ℝ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) : 0 ≤ kernelEnergy (μ := μ) K f := by
  apply integral_nonneg_of_ae
  filter_upwards [hK0, Measure.quasiMeasurePreserving_fst.ae hf0,
    Measure.quasiMeasurePreserving_snd.ae hf0] with p hp hx hy
  exact mul_nonneg (mul_nonneg hp hy) hx

end Erdos1017.KernelOperator

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual uniform recipient subflow uses the original measure on C,
with the displayed fraction of every original source in J. -/
def uniformSubflow (μ : Measure Ω) (C J : Set Ω) (θ : ℝ) (p : Ω × Ω) : ℝ :=
  θ * C.indicator (fun _ => 1 / μ.real C) p.1 * J.indicator (fun _ => 1) p.2

theorem integrable_uniformSubflow (C J : Set Ω) (hC : MeasurableSet C)
    (hJ : MeasurableSet J) (θ : ℝ) : Integrable (uniformSubflow μ C J θ) (μ.prod μ) :=
  (((integrable_const _).indicator hC).const_mul θ).mul_prod ((integrable_const _).indicator hJ)

omit [IsProbabilityMeasure μ] in
theorem uniformSubflow_nonnegative (C J : Set Ω) (θ : ℝ) (hθ : 0 ≤ θ) (p : Ω × Ω) :
    0 ≤ uniformSubflow μ C J θ p :=
  mul_nonneg (mul_nonneg hθ (indicator_nonneg (fun _ _ => by positivity) _))
    (indicator_nonneg (fun _ _ => zero_le_one) _)

omit [IsProbabilityMeasure μ] in
/-- The uniform subflow has its actual receipt-minus-supply direction,
without a prescribed marginal certificate. -/
theorem direction_uniformSubflow (C J : Set Ω) (hC : MeasurableSet C)
    (hJ : MeasurableSet J) (hpos : 0 < μ.real C) (θ : ℝ) :
    direction μ (uniformSubflow μ C J θ) = fun x =>
      (θ * μ.real J) * C.indicator (fun _ => 1 / μ.real C) x -
        θ * J.indicator (fun _ => 1) x := by
  funext x
  unfold direction receipt supply uniformSubflow
  change (∫ y, (θ * C.indicator (fun _ => 1 / μ.real C) x) *
    J.indicator (fun _ => (1 : ℝ)) y ∂μ) -
    (∫ y, (θ * C.indicator (fun _ => 1 / μ.real C) y) *
      J.indicator (fun _ => (1 : ℝ)) x ∂μ) = _
  rw [integral_const_mul, integral_mul_const, integral_const_mul,
    integral_indicator hJ, integral_indicator hC, setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [mul_one_div, div_self hpos.ne']
  ring

omit [IsProbabilityMeasure μ] in
/-- The actual uniform subflow is dominated by the actual convexly
rerouted flow. Retained old columns are nonnegative. -/
theorem uniformSubflow_le_interpolation (q : Ω × Ω → ℝ)
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (C J : Set Ω)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ p ∂μ.prod μ, uniformSubflow μ C J θ p ≤
      (1 - θ) * q p + θ * redirect μ q C J p := by
  filter_upwards [hq0] with p hp
  by_cases hJ : p.2 ∈ J
  · simp only [uniformSubflow, redirect, ite_eq_left hJ, indicator_of_mem hJ, mul_one]
    exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hθ.2) hp)
  · simp only [uniformSubflow, redirect, ite_eq_right hJ, indicator_of_notMem hJ, mul_zero]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hθ.2) hp) (mul_nonneg hθ.1 hp)

/-- A genuine missing recipient-source rectangle removes the mixed term.
The supplier self-energy is nonnegative, rather than assumed zero. -/
theorem uniformSubflow_energy_ge (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → K p.1 p.2 = 0) (θ : ℝ) :
    (θ * μ.real J) ^ 2 * KernelOperator.kernelEnergy (μ := μ) K
        (C.indicator (fun _ => 1 / μ.real C)) ≤
      KernelOperator.kernelEnergy (μ := μ) K (direction μ (uniformSubflow μ C J θ)) := by
  let ρ := C.indicator (fun _ => 1 / μ.real C)
  let s := J.indicator (fun _ => (1 : ℝ))
  have hρ : Integrable ρ μ := (integrable_const _).indicator hC
  have hs : Integrable s μ := (integrable_const _).indicator hJ
  have hcross : KernelOperator.kernelPairing (μ := μ) K (fun x => (θ * μ.real J) * ρ x) s = 0 := by
    rw [KernelOperator.kernelPairing_symm K hsym]
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with p hp
    change K p.1 p.2 * s p.2 * ((θ * μ.real J) * ρ p.1) = 0
    by_cases hx : p.1 ∈ C
    · by_cases hy : p.2 ∈ J
      · simp only [hp hx hy, zero_mul]
      · simp only [s, indicator_of_notMem hy, mul_zero, zero_mul]
    · simp only [ρ, indicator_of_notMem hx, mul_zero]
  have hself := KernelOperator.kernelEnergy_nonnegative_of_nonnegative K hK0 s
    (Eventually.of_forall (fun x => indicator_nonneg (fun _ _ => zero_le_one) x))
  rw [direction_uniformSubflow C J hC hJ hpos θ,
    KernelOperator.kernelEnergy_sub_mul K hK hB hsym _ s (hρ.const_mul _) hs θ,
    hcross, KernelOperator.kernelEnergy_const_mul]
  nlinarith [mul_nonneg (sq_nonneg θ) hself]

end Erdos1017.MissingFlow

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- The actual full interpolated flow pays at least the original uniform
recipient energy through its contained subflow and same-model energy monotonicity. -/
theorem diffuse_interpolation_energy_credit (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (θ * μ.real J) ^ 2 * KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (C.indicator (fun _ => 1 / μ.real C)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)) := by
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hp => hp.symm)
  have hcredit := MissingFlow.uniformSubflow_energy_ge (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    (hW.moment_mem.mono (fun _ hp => hp.1)) C J hC hJ hpos hzero θ
  have hr := hq.redirect_diffuse C J hC hJ hpos hCD hCH hJL hJI hzero
  have ht := hq.convex hr θ hθ
  exact hcredit.trans (hW.missing_flow_energy_mono hd hgap
    (MissingFlow.uniformSubflow μ C J θ) _
    (MissingFlow.integrable_uniformSubflow C J hC hJ θ) ht.integrable
    (Eventually.of_forall (MissingFlow.uniformSubflow_nonnegative C J θ hθ.1))
    (MissingFlow.uniformSubflow_le_interpolation q hq.nonnegative C J θ hθ) ht.oriented_support)

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

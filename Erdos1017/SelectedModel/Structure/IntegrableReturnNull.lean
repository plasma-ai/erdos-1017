module

public import Erdos1017.SelectedModel.Structure.IntegrableRelativeWeight
public import Erdos1017.SelectedModel.Selection.FullReweightRows
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Null directions from a zero-energy density return

A constant physical row annihilates every integrable mean-zero test, and at an
interior zero-energy density return the changed full optimum's regular
multiplier is the original one, so the original shifted kernel annihilates the
original integrable direction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A constant physical row annihilates every integrable mean-zero test. -/
theorem kernelPairing_one_eq_zero_of_constant_row (K : Ω → Ω → ℝ) {B a : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hrow : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = a)
    (f : Ω → ℝ) (hf : Integrable f μ) (hmean : (∫ x, f x ∂μ) = 0) :
    KernelOperator.kernelPairing (μ := μ) K (fun _ => 1) f = 0 := by
  rw [KernelOperator.kernelPairing_one_eq_row K hK hB f hf]
  calc
    _ = ∫ x, a * f x ∂μ := integral_congr_ae (hrow.mono (fun x hx => by rw [hx]))
    _ = 0 := by rw [integral_const_mul, hmean, mul_zero]

variable [MeasurableSpace.CountablyGenerated Ω]

/-- At an actual interior zero-energy density return, the changed full
optimum's own regular multiplier is the original multiplier. Its constant
shifted row is derived under its own probability law. -/
theorem FullStationaryClass.integrable_return_stationary
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (hL : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) ≠ 0)
    (hE : KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v = 0)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hreturn : density (integrableTilt W v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩) = d) :
    ∀ᵐ x ∂weightedMeasure (μ := μ) (integrableTiltWeight v t),
      (∫ y, shiftedKernel W m x y
        ∂weightedMeasure (μ := μ) (integrableTiltWeight v t)) = 2 * (c - m * d) := by
  let ν := weightedMeasure (μ := μ) (integrableTiltWeight v t)
  have : IsProbabilityMeasure ν := integrableTilt_probability v hv hmean hbelow t
    ⟨ht.1.le, ht.2.le⟩
  have : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℝ 2 ν) := inferInstance
  let V : Model Ω ν := integrableTilt W v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩
  let w := relativeTiltDirection v t
  have hw : Integrable w ν := (relativeTiltDirection_integrable_bound v hv hmean hbelow t ht).1
  have hwmean : (∫ x, w x ∂ν) = 0 := relativeTiltDirection_integral v hv hmean hbelow t ht
  let L := ∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ
  have hlinear : L + t * KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) v = -L := by
    have hp := density_integrableTilt W v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩
    rw [hreturn, hW.density_eq] at hp
    have ht0 : 0 < t := ht.1
    change d = d + t * L + t ^ 2 * _ / 2 at hp
    have hz : t * (2 * L + t * KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) v) = 0 := by
      nlinarith [hp]
    have := (mul_eq_zero.mp hz).resolve_left ht0.ne'
    linarith
  have hG : KernelOperator.kernelPairing (μ := ν) (adjacencyKernel V) (fun _ => 1) w = -L := by
    change KernelOperator.kernelPairing (μ := ν) (adjacencyKernel W) (fun _ => 1) w = -L
    rw [kernelPairing_relativeTilt_eq v hv hbelow t ht _
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W),
      adjacency_kernelPairing_one_eq_degree W v hv]
    exact hlinear
  have hM : KernelOperator.kernelPairing (μ := ν) (shiftedKernel V m) (fun _ => 1) w = 0 := by
    change KernelOperator.kernelPairing (μ := ν) (shiftedKernel W m) (fun _ => 1) w = 0
    rw [kernelPairing_relativeTilt_eq v hv hbelow t ht _
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m),
      hW.shifted_kernelPairing_one_eq_zero v hv hmean, hE, mul_zero, add_zero]
  have hregular : Variation.weightFirstVariation (adjacencyOperator V) ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := (Variation.kernel_weightFirstVariation_eq_zero_iff
      (adjacencyKernel V) (by norm_num) (adjacencyKernel_measurable V)
      (adjacencyKernel_bound V)).mp hz
    have hzero := kernelPairing_one_eq_zero_of_constant_row _
      (adjacencyKernel_measurable V) (adjacencyKernel_bound V) ha w hw hwmean
    rw [hG] at hzero
    exact hL (neg_eq_zero.mp hzero)
  have hfull : FullFeasible V := fullFeasible_integrableTilt W hW.full v hv hmean hbelow t
    ⟨ht.1.le, ht.2.le⟩
  have hopt : objective V = FractionalGraph.densityLimit (density V) := by
    have hp := hW.objective_integrableTilt v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩
    change objective V = _ at hp
    change density V = d at hreturn
    rw [hreturn, hE] at hp
    simpa only [sub_self, mul_zero, zero_div, add_zero, hreturn, hW.optimal] using hp
  obtain ⟨n, a, _, heigen, _, _⟩ := exists_full_regular_multiplier V hfull hopt hregular
  have hrow : ∀ᵐ x ∂ν, (∫ y, shiftedKernel V n x y ∂ν) = a := by
    apply KernelOperator.stationary_of_constant_one_eigenvector _ (by positivity)
      (shiftedKernel_measurable V n) (shiftedKernel_bound V n) a
    change shiftedOperator V n (Lp.const 2 ν (1 : ℝ)) = _
    rwa [shiftedOperator_eq]
  have hnzero := kernelPairing_one_eq_zero_of_constant_row _
    (shiftedKernel_measurable V n) (shiftedKernel_bound V n) hrow w hw hwmean
  rw [shifted_kernelPairing V n _ w (integrable_const 1) hw, hG] at hnzero
  rw [shifted_kernelPairing V m _ w (integrable_const 1) hw, hG] at hM
  have hnm : n = m := by
    apply (mul_eq_mul_right_iff.mp (show n * L = m * L by linarith)).resolve_right hL
  rw [hnm] at hrow
  have ha := shifted_stationary_value V m a hrow
  have hc := hW.objective_integrableTilt v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩
  rw [hreturn, hE] at hc
  have hc' : objective V = c := by simpa using hc
  rw [hc', hreturn] at ha
  rw [ha] at hrow
  exact hrow

/-- An actual zero-energy interior return forces the original shifted
kernel to annihilate the original integrable direction. The returned
stationarity used here was derived from its own full optimality. -/
theorem FullStationaryClass.integrable_return_null
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (hL : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) ≠ 0)
    (hE : KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v = 0)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hreturn : density (integrableTilt W v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩) = d) :
    ∀ᵐ x ∂μ, KernelOperator.applyKernel (μ := μ) (shiftedKernel W m) v x = 0 := by
  have hrow := (integrableTilt_measure_equivalent v hv hbelow t ht).1.ae_le
    (hW.integrable_return_stationary v hv hmean hbelow hL hE t ht hreturn)
  have h1 := KernelOperator.integrable_joint (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) (integrable_const (1 : ℝ))
  have hvjoint := KernelOperator.integrable_joint (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) hv
  filter_upwards [hrow, hW.stationary, h1.prod_right_ae, hvjoint.prod_right_ae]
    with x hnew hold hi1 hiv
  rw [integral_weightedMeasure_eq_applyKernel _
    (integrableTiltWeight_integrable v hv t).aestronglyMeasurable.aemeasurable
    (integrableTiltWeight_nonnegative v hbelow t ⟨ht.1.le, ht.2.le⟩)] at hnew
  have hexp : KernelOperator.applyKernel (μ := μ) (shiftedKernel W m)
      (integrableTiltWeight v t) x = (∫ y, shiftedKernel W m x y ∂μ) +
        t * KernelOperator.applyKernel (μ := μ) (shiftedKernel W m) v x := by
    have hi : Integrable (fun y => shiftedKernel W m x y) μ := by simpa using hi1
    have heq : (fun y => shiftedKernel W m x y * integrableTiltWeight v t y) =
        (fun y => shiftedKernel W m x y + t * (shiftedKernel W m x y * v y)) := by
      funext y
      dsimp only [integrableTiltWeight]
      ring
    rw [KernelOperator.applyKernel, heq, integral_add hi (hiv.const_mul t), integral_const_mul]
    rfl
  rw [hexp, hold] at hnew
  have hz : t * KernelOperator.applyKernel (μ := μ) (shiftedKernel W m) v x = 0 := by
    linarith
  exact (mul_eq_zero.mp hz).resolve_left ht.1.ne'

end Erdos1017.CappedModel

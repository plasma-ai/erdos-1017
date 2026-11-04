module

public import Erdos1017.Models.Decorated.DecoratedSamplingConcentration
public import Erdos1017.Models.Capped.CappedAttainment

/-!
# Uniform omitted-order error for capped models

Averaging the finite capped bound keeps its exact finite-size bias and measured
density error, so every capped feasible model, and the attained capped supremum,
obeys a uniform omitted-order error bound from sampling concentration and the
finite partition repair.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integrable_sample_test (W : Model Ω μ) (n : ℕ)
    (F : C(CliquePair n → CappedColor, ℝ)) :
    Integrable F (sampledColorLaw W n : Measure _) :=
  Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
    (Eventually.of_forall fun c => F.norm_coe_le_norm c)

/-- Averaging the actual finite capped bound retains its exact finite-size
bias and its measured density error. -/
theorem sampled_cap_bound (W : Model Ω μ) {r : ℕ} (hr : 2 ≤ r)
    (hW : Feasible r W) (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (n : ℝ)) * objective W ≤
      FractionalGraph.densityLimit (density W) +
        3 * (∫ c, |sampleDensity c - density W|
          ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) +
        ((1 - 1 / (n : ℝ)) * density W) / (r.choose 2 : ℝ) := by
  let A : C(CliquePair n → CappedColor, ℝ) :=
    ⟨sampleDensity, by unfold sampleDensity; fun_prop⟩
  let C : C(CliquePair n → CappedColor, ℝ) :=
    ⟨sampleCharge, by unfold sampleCharge; fun_prop⟩
  let E : C(CliquePair n → CappedColor, ℝ) :=
    ⟨fun c => |sampleDensity c - density W|, by unfold sampleDensity; fun_prop⟩
  have hA := integrable_sample_test W n A
  have hC := integrable_sample_test W n C
  have hE := integrable_sample_test W n E
  have hconst : Integrable (fun _ : CliquePair n → CappedColor =>
      FractionalGraph.densityLimit (density W)) (sampledColorLaw W n : Measure _) :=
    integrable_const _
  have hR := (hconst.add (hE.const_mul 3)).add (hA.div_const (r.choose 2 : ℝ))
  have hmeas : MeasurableSet {c : CliquePair n → CappedColor |
      C c ≤ FractionalGraph.densityLimit (density W) + 3 * E c + A c / (r.choose 2 : ℝ)} :=
    isClosed_le C.continuous (by fun_prop) |>.measurableSet
  have hsample : ∀ᵐ c ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor)),
      C c ≤ FractionalGraph.densityLimit (density W) + 3 * E c + A c / (r.choose 2 : ℝ) := by
    apply Measure.ae_comp_of_ae_ae hmeas
    exact ae_sampleCharge_le_densityLimit W hr hW n hn (density W)
  have h := integral_mono_ae hC hR hsample
  have hadd := integral_add (hconst.add (hE.const_mul 3)) (hA.div_const (r.choose 2 : ℝ))
  have hinner := integral_add hconst (hE.const_mul 3)
  simp only [Pi.add_apply] at hadd hinner
  simp only [Pi.add_apply] at h
  rw [hadd, hinner, integral_const_mul, integral_div] at h
  dsimp only [A, C, E] at h
  simp only [ContinuousMap.coe_mk] at h
  simpa only [integral_sampleCharge W n hn, integral_sampleDensity W n hn,
    integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- Every actual capped feasible model obeys the uniform omitted-order
error bound. Sampling concentration and the finite partition repair supply
the estimate; no full feasibility or physical optimizer is assumed. -/
theorem objective_le_densityLimit_add_cap_error (W : Model Ω μ) {r : ℕ}
    (hr : 2 ≤ r) (hW : Feasible r W) :
    objective W ≤ FractionalGraph.densityLimit (density W) +
      density W / (r.choose 2 : ℝ) := by
  have hbias : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hleft := hbias.mul_const (objective W)
  have hconstant : Tendsto (fun _ : ℕ => FractionalGraph.densityLimit (density W)) atTop
      (𝓝 (FractionalGraph.densityLimit (density W))) := tendsto_const_nhds
  have hright := (hconstant.add
    ((sampleDensity_abs_error_tendsto W).const_mul 3)).add
    ((hbias.mul_const (density W)).div_const (r.choose 2 : ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop,
      (1 - 1 / (n : ℝ)) * objective W ≤
        FractionalGraph.densityLimit (density W) +
          3 * (∫ c, |sampleDensity c - density W|
            ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) +
          ((1 - 1 / (n : ℝ)) * density W) / (r.choose 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact sampled_cap_bound W hr hW n (by omega)
  simpa using le_of_tendsto_of_tendsto hleft hright hbound

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- The attained capped supremum has the same uniform error estimate. -/
theorem capValue_le_densityLimit_add_error (r : ℕ) (hr : 2 ≤ r) (d : ℝ)
    (hd : d ∈ Set.Icc 0 (1 / 2)) :
    capValue Ω μ r d ≤ FractionalGraph.densityLimit d + d / (r.choose 2 : ℝ) := by
  obtain ⟨W, hW, hdW, hoW, _⟩ := exists_fixedMeasureMaximizer (μ := μ) r d hd
  simpa only [hdW, hoW] using objective_le_densityLimit_add_cap_error W hr hW

end Erdos1017.CappedModel

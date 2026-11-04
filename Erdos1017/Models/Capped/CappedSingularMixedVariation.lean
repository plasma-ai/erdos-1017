module

public import Erdos1017.Models.Capped.CappedMixtureOperator
public import Erdos1017.Models.Selection.QuadraticMixtureLimit
public import Erdos1017.Models.Kernel.SingularWeightStationarity
public import Erdos1017.Models.Selection.QuadraticEditDirections

/-!
# Singular quadratic comparison with finite edit mixtures

The singular quadratic comparison includes every finite collection of edits
dominated by the common feasible envelope, recorded by finite support, and one
multiplier controls every bounded vertex direction and every endpoint in an
arbitrary family of common-envelope edits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem singular_charge_firstVariation_zero (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0) :
    Variation.weightFirstVariation (chargeOperator W) = 0 := by
  apply (Variation.weightFirstVariation_eq_zero_iff _
    (KernelOperator.operator_range_bounded _ _ _ _ (Lp.const 2 μ (1 : ℝ)))).mpr
  apply Variation.stationary_of_singular_weight_comparison (adjacencyOperator W) (chargeOperator W)
    (adjacencyOperator_symmetric W) (chargeOperator_symmetric W)
    (KernelOperator.operator_range_bounded _ _ _ _ (Lp.const 2 μ (1 : ℝ))) hsingular 3 1 (by norm_num)
  intro f hf
  have h := weight_lipschitz_max W hW f hf
  change Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight f) -
      Variation.weightedPairIntegral (chargeKernel W) (Lp.const 2 μ (1 : ℝ)) ≤
    3 * |Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) -
      Variation.weightedPairIntegral (adjacencyKernel W) (Lp.const 2 μ (1 : ℝ))| at h
  simpa only [weighted_charge_eq, weighted_adjacency_eq] using h

variable [Fintype ι]

/-- The singular quadratic comparison includes every finite collection of
actual edits dominated by the common feasible envelope. The competitors
have edit mass `t^2 * sum a_i^2 <= 1` and vertex weight `1+t*f`. -/
theorem singular_finite_edit_bound (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0)
    (V : ι → Model Ω μ) (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p)
    (f : Variation.WeightDirections μ) (a : ι → ℝ) :
    Variation.weightSecondVariation (chargeOperator W) f f +
        ∑ i, (a i) ^ 2 * (2 * (objective (V i) - objective W)) ≤
      3 * |Variation.weightSecondVariation (adjacencyOperator W) f f +
        ∑ i, (a i) ^ 2 * (2 * (density (V i) - density W))| := by
  let TA := adjacencyOperator W
  let TY := chargeOperator W
  let A := fun i => adjacencyOperator (V i)
  let Y := fun i => chargeOperator (V i)
  let D := Variation.mixtureCurveQuotient TA A f a
  let C := Variation.mixtureCurveQuotient TY Y f a
  have hyzero := singular_charge_firstVariation_zero W hW hsingular
  have hD := Variation.mixtureCurveQuotient_continuous TA A f a
  have hC := Variation.mixtureCurveQuotient_continuous TY Y f a
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), ‖t • f‖ < 1 := by
    have hc : ContinuousAt (fun t : ℝ => ‖t • f‖) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by norm_num))
  have hmass : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 * ∑ i, (a i) ^ 2 < 1 := by
    have hc : ContinuousAt (fun t : ℝ => t ^ 2 * ∑ i, (a i) ^ 2) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by norm_num))
  have hlim : Tendsto (fun t => C t - 3 * |D t|) (𝓝[>] (0 : ℝ)) (𝓝 (C 0 - 3 * |D 0|)) :=
    (hC.continuousAt.sub (continuousAt_const.mul hD.continuousAt.abs)).tendsto.mono_left nhdsWithin_le_nhds
  have hle : C 0 - 3 * |D 0| ≤ 0 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      hmass.filter_mono nhdsWithin_le_nhds] with t ht hnorm hmass
    let E := squaredEditMixture W V a (t ^ 2) (sq_nonneg t) hmass.le
    have hfeas := feasible_squaredEditMixture W V a (t ^ 2) (sq_nonneg t) hmass.le hV hW.1
    have hcomp := weighted_competitor_lipschitz W hW E hfeas (t • f) hnorm
    have hc (i : ι) : (editAmplitudeWeights a (t ^ 2) (sq_nonneg t) i : ℝ) = t ^ 2 * (a i) ^ 2 := rfl
    have hAop : adjacencyOperator E =
        (1 - ∑ i, t ^ 2 * (a i) ^ 2) • TA + ∑ i, (t ^ 2 * (a i) ^ 2) • A i := by
      rw [show E = editMixture W V _ _ from rfl, adjacencyOperator_editMixture]
      simp only [hc]
      rfl
    have hYop : chargeOperator E =
        (1 - ∑ i, t ^ 2 * (a i) ^ 2) • TY + ∑ i, (t ^ 2 * (a i) ^ 2) • Y i := by
      rw [show E = editMixture W V _ _ from rfl, chargeOperator_editMixture]
      simp only [hc]
      rfl
    rw [hAop, hYop,
      Variation.mixture_weight_curve_expansion TY Y (chargeOperator_symmetric W)
        (fun i => chargeOperator_symmetric (V i)) hyzero,
      Variation.mixture_weight_curve_expansion TA A (adjacencyOperator_symmetric W)
        (fun i => adjacencyOperator_symmetric (V i)) hsingular] at hcomp
    change t ^ 2 * C t ≤ 3 * |t ^ 2 * D t| at hcomp
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)] at hcomp
    have hcancel : C t ≤ 3 * |D t| := (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp (by
      nlinarith [hcomp] : t ^ 2 * C t ≤ t ^ 2 * (3 * |D t|))
    linarith
  dsimp only [C, D, Variation.mixtureCurveQuotient, TA, TY, A, Y] at hle
  simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero,
    charge_constant_inner, adjacency_constant_inner] at hle
  simpa only [← mul_sub] using sub_nonpos.mp hle

omit [Fintype ι] in
/-- Finite support records exactly the finite mixtures constructed above;
the family of available actual edit endpoints may itself be arbitrary. -/
theorem singular_finsupp_edit_bound (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0)
    (V : ι → Model Ω μ) (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p)
    (f : Variation.WeightDirections μ) (a : ι →₀ ℝ) :
    Variation.weightSecondVariation (chargeOperator W) f f +
        a.sum (fun i t => (2 * (objective (V i) - objective W)) * t ^ 2) ≤
      3 * |Variation.weightSecondVariation (adjacencyOperator W) f f +
        a.sum (fun i t => (2 * (density (V i) - density W)) * t ^ 2)| := by
  classical
  have h := singular_finite_edit_bound W hW hsingular
    (fun i : a.support => V i) (fun i => hV i) f (fun i : a.support => a i)
  rw [Finset.sum_coe_sort a.support (fun i => (a i) ^ 2 * (2 * (objective (V i) - objective W))),
    Finset.sum_coe_sort a.support (fun i => (a i) ^ 2 * (2 * (density (V i) - density W)))] at h
  simpa only [Finsupp.sum, mul_comm] using h

omit [Fintype ι] in
/-- One multiplier controls every bounded vertex direction and every
endpoint in an arbitrary family of actual common-envelope edits. -/
theorem exists_singular_multiplier_with_edits (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0)
    (V : ι → Model Ω μ) (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p) :
    ∃ m : ℝ, -3 ≤ m ∧ m ≤ 3 ∧
      (∀ f : Variation.WeightDirections μ,
        Variation.weightSecondVariation (chargeOperator W) f f -
          m * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ 0) ∧
      (∀ i, objective (V i) - objective W - m * (density (V i) - density W) ≤ 0) := by
  obtain ⟨ell, hlo, hhi, hweight, hedit⟩ := Variation.exists_multiplier_with_edits
    (Variation.weightSecondVariation (adjacencyOperator W))
    (Variation.weightSecondVariation (chargeOperator W))
    (fun i => 2 * (density (V i) - density W))
    (fun i => 2 * (objective (V i) - objective W)) 3 (by norm_num)
    (singular_finsupp_edit_bound W hW hsingular V hV)
  refine ⟨-ell, by linarith, by linarith, ?_, ?_⟩
  · intro f
    have h := hweight f
    nlinarith
  · intro i
    have h := hedit i
    nlinarith

end Erdos1017.CappedModel

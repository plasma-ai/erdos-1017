module

public import Erdos1017.Models.Selection.FullModelEdits
public import Erdos1017.Models.Capped.CappedSingularMixedVariation
public import Erdos1017.Models.Capped.CappedEditMultiplier

/-!
# Edit comparisons for fully feasible models

Every affine edit of a fully feasible model obeys the same regular multiplier as
the vertex directions, and the singular quadratic comparison covers every finite
collection of edits dominated by a common feasible envelope, giving one
multiplier for all bounded vertex directions and all common-envelope edit
endpoints.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every affine edit of a fully feasible model obeys the same regular
multiplier as the vertex directions. The comparison uses actual feasible
edited models and exact quadratic vertex reweighting corrections. -/
theorem full_affine_edit_sign (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (E : AffineEdit W) (m : ℝ)
    (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0) :
    objective (E.model 1) - objective W - m * (density (E.model 1) - density W) ≤ 0 := by
  have hex : ∃ u, 0 < Variation.weightFirstVariation (adjacencyOperator W) u := by
    have hn : ∃ u, Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 := by
      by_contra h
      push Not at h
      exact hregular (LinearMap.ext h)
    obtain ⟨u, hu⟩ := hn
    rcases lt_or_gt_of_ne hu with hu | hu
    · exact ⟨-u, by simpa using neg_pos.mpr hu⟩
    · exact ⟨u, hu⟩
  obtain ⟨u, hu⟩ := hex
  let T₀ := adjacencyOperator W
  let T₁ := adjacencyOperator (E.model 1)
  let S₀ := chargeOperator W
  let S₁ := chargeOperator (E.model 1)
  let one := Lp.const 2 μ (1 : ℝ)
  let a := ⟪T₁ one, one⟫ - ⟪T₀ one, one⟫
  let b := Variation.weightFirstVariation T₀ u
  let c := Variation.weightFirstVariation T₁ u - Variation.weightFirstVariation T₀ u
  let d := Variation.weightSecondVariation T₀ u u
  let e := Variation.weightSecondVariation T₁ u u - Variation.weightSecondVariation T₀ u u
  let A := ⟪S₁ one, one⟫ - ⟪S₀ one, one⟫
  let B := Variation.weightFirstVariation S₀ u
  let C := Variation.weightFirstVariation S₁ u - Variation.weightFirstVariation S₀ u
  let D := Variation.weightSecondVariation S₀ u u
  let F := Variation.weightSecondVariation S₁ u u - Variation.weightSecondVariation S₀ u u
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεone : ε ≤ 1 := (div_le_one (by positivity : 0 < ‖u‖ + 1)).mpr (by linarith [norm_nonneg u])
  have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity : ‖u‖ + 1 ≠ 0)
  have hB : B = m * b := by
    have h := LinearMap.congr_fun hm u
    simpa only [LinearMap.smul_apply, smul_eq_mul] using h
  have hsign : A - m * a ≤ 0 := by
    apply Variation.edit_sign_of_local_max a b c d e A B C D F m hu hB ε hε
    intro τ s hτ hτε hs hroot
    let t : unitInterval := ⟨τ, hτ, (hτε.trans_le hεone).le⟩
    have hnorm : ‖s • u‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
      have hpos := mul_pos hε (by norm_num : (0 : ℝ) < 1)
      nlinarith
    have hden := Variation.affine_weight_curve_expansion T₀ T₁
      (adjacencyOperator_symmetric W) (adjacencyOperator_symmetric (E.model 1)) u τ s
    have hcost := Variation.affine_weight_curve_expansion S₀ S₁
      (chargeOperator_symmetric W) (chargeOperator_symmetric (E.model 1)) u τ s
    have hden0 : ⟪adjacencyOperator (E.model t) (Variation.vertexWeight (s • u)),
        Variation.vertexWeight (s • u)⟫ = ⟪T₀ one, one⟫ := by
      rw [adjacencyOperator_affine]
      change ⟪(T₀ + τ • (T₁ - T₀)) (Variation.vertexWeight (s • u)),
        Variation.vertexWeight (s • u)⟫ = _
      change a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 = 0 at hroot
      change _ = a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 at hden
      linarith
    have := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative (s • u) hnorm) (Variation.vertexWeight_integral (s • u))
    have hfeas := fullFeasible_reweight (E.model t)
      (fullFeasible_affineEdit W hW E t) (s • u) hnorm
    have hd : density (reweight (E.model t) (s • u) hnorm) = density W := by
      have h := density_reweight (E.model t) (s • u) hnorm
      change density (reweight (E.model t) (s • u) hnorm) =
        Variation.weightedPairIntegral (adjacencyKernel (E.model t)) (Variation.vertexWeight (s • u)) / 2 at h
      rw [weighted_adjacency_eq, hden0] at h
      change _ = ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ / 2 at h
      rw [adjacency_constant_inner] at h
      linarith
    have hmax := full_objective_le_of_density_eq W hopt
      (weightedMeasure (μ := μ) (Variation.vertexWeight (s • u)))
      (reweight (E.model t) (s • u) hnorm) hfeas hd
    have hc := objective_reweight (E.model t) (s • u) hnorm
    change objective (reweight (E.model t) (s • u) hnorm) =
      Variation.weightedPairIntegral (chargeKernel (E.model t)) (Variation.vertexWeight (s • u)) / 2 at hc
    rw [weighted_charge_eq, chargeOperator_affine] at hc
    change _ = ⟪(S₀ + τ • (S₁ - S₀)) (Variation.vertexWeight (s • u)),
      Variation.vertexWeight (s • u)⟫ / 2 at hc
    have hbase : ⟪S₀ one, one⟫ = 2 * objective W := charge_constant_inner W
    change _ = A * τ + (B + C * τ) * s + (D + F * τ) * s ^ 2 at hcost
    linarith
  change (⟪chargeOperator (E.model 1) (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ -
    ⟪chargeOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) -
      m * (⟪adjacencyOperator (E.model 1) (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ -
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫) ≤ 0 at hsign
  rw [charge_constant_inner, charge_constant_inner, adjacency_constant_inner, adjacency_constant_inner] at hsign
  nlinarith

variable [Fintype ι]

/-- The singular quadratic comparison includes every finite collection of
actual edits dominated by the common feasible envelope. The competitors
have edit mass `t^2 * sum a_i^2 <= 1` and vertex weight `1+t*f`. -/
theorem full_singular_finite_edit_bound (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
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
  have hyzero : Variation.weightFirstVariation (chargeOperator W) = 0 := by
    have hdegree := (Variation.kernel_weightFirstVariation_eq_zero_iff
      (adjacencyKernel W) (by norm_num) (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W)).mp hsingular
    exact full_singular_charge_firstVariation_zero W hW hopt hdegree
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
    have hfeas := fullFeasible_squaredEditMixture W V a (t ^ 2)
      (sq_nonneg t) hmass.le hV hW
    have hcomp := full_weighted_competitor_lipschitz W hopt E hfeas (t • f) hnorm
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
theorem full_singular_finsupp_edit_bound (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0)
    (V : ι → Model Ω μ) (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p)
    (f : Variation.WeightDirections μ) (a : ι →₀ ℝ) :
    Variation.weightSecondVariation (chargeOperator W) f f +
        a.sum (fun i t => (2 * (objective (V i) - objective W)) * t ^ 2) ≤
      3 * |Variation.weightSecondVariation (adjacencyOperator W) f f +
        a.sum (fun i t => (2 * (density (V i) - density W)) * t ^ 2)| := by
  classical
  have h := full_singular_finite_edit_bound W hW hopt hsingular
    (fun i : a.support => V i) (fun i => hV i) f (fun i : a.support => a i)
  rw [Finset.sum_coe_sort a.support (fun i => (a i) ^ 2 * (2 * (objective (V i) - objective W))),
    Finset.sum_coe_sort a.support (fun i => (a i) ^ 2 * (2 * (density (V i) - density W)))] at h
  simpa only [Finsupp.sum, mul_comm] using h

omit [Fintype ι] in
/-- One multiplier controls every bounded vertex direction and every
endpoint in an arbitrary family of actual common-envelope edits. -/
theorem exists_full_singular_multiplier_with_edits (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
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
    (full_singular_finsupp_edit_bound W hW hopt hsingular V hV)
  refine ⟨-ell, by linarith, by linarith, ?_, ?_⟩
  · intro f
    have h := hweight f
    nlinarith
  · intro i
    have h := hedit i
    nlinarith

end Erdos1017.CappedModel

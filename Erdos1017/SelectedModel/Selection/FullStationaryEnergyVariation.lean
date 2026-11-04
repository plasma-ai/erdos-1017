module

public import Erdos1017.SelectedModel.Selection.FullStationaryReweight
public import Erdos1017.SelectedModel.Selection.FullStationaryTransport
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Energy variation under reweighting

The squared shifted-kernel energy under a changed vertex law is the weighted
pair integral of the original squared kernel, with an exact quadratic expansion;
a bounded kernel-null tilt has nearby full optimizers at the same multiplier,
and bounded null vectors satisfy the selected energy first-variation identity
under a strict gap.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem squareKernel_measurable (W : Model Ω μ) (m : ℝ) :
    AEStronglyMeasurable (fun p : Ω × Ω => (shiftedKernel W m p.1 p.2) ^ 2) (μ.prod μ) :=
  (shiftedKernel_measurable W m).pow 2

omit [IsProbabilityMeasure μ] in
private theorem squareKernel_bound (W : Model Ω μ) (m : ℝ) :
    ∀ᵐ p ∂μ.prod μ, ‖(shiftedKernel W m p.1 p.2) ^ 2‖ ≤ (3 + ‖m‖) ^ 2 := by
  filter_upwards [shiftedKernel_bound W m] with p hp
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hp 2

/-- The actual squared shifted-kernel energy under a changed vertex law
is the weighted pair integral of the old squared kernel. -/
theorem stationaryEnergy_reweight (W : Model Ω μ) (m : ℝ)
    (h : Variation.WeightDirections μ) (hh : ‖h‖ < 1) :
    stationaryEnergy (reweight W h hh) m = Variation.weightedPairIntegral
      (fun x y => (shiftedKernel W m x y) ^ 2) (Variation.vertexWeight h) := by
  simpa only [stationaryEnergy, shiftedKernel, Variation.weightedPairIntegral,
    reweight, DecoratedKernel.changeMeasure, shiftedMoment, DecoratedKernel.moment] using
    integral_weightedMeasure_prod (Variation.vertexWeight h)
      (Lp.aestronglyMeasurable _).aemeasurable (Variation.vertexWeight_nonnegative h hh)
      (fun x y => (shiftedKernel W m x y) ^ 2)

/-- The exact quadratic change in the actual energy includes both vertex
weights. Symmetry identifies their two linear contributions. -/
theorem stationaryEnergy_reweight_smul (W : Model Ω μ) (m : ℝ)
    (h : Variation.WeightDirections μ) (t : ℝ) (ht : ‖t • h‖ < 1) :
    stationaryEnergy (reweight W (t • h) ht) m = stationaryEnergy W m +
      2 * t * (∫ p : Ω × Ω, (shiftedKernel W m p.1 p.2) ^ 2 *
        Variation.directionToL2 h p.1 ∂μ.prod μ) +
      t ^ 2 * (∫ p : Ω × Ω, (shiftedKernel W m p.1 p.2) ^ 2 *
        Variation.directionToL2 h p.2 * Variation.directionToL2 h p.1 ∂μ.prod μ) := by
  let K := fun x y => (shiftedKernel W m x y) ^ 2
  let T := KernelOperator.operator K (sq_nonneg _) (squareKernel_measurable W m)
    (squareKernel_bound W m)
  let one := Lp.const 2 μ (1 : ℝ)
  have hsym : T.toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact congrArg (fun z : ℝ => z ^ 2) hp.symm
  have hone : ⟪T one, one⟫ = stationaryEnergy W m := by
    rw [KernelOperator.operator_inner]
    exact weightedPairIntegral_one K
  have hlinear : ⟪T one, Variation.directionToL2 h⟫ =
      ∫ p : Ω × Ω, K p.1 p.2 * Variation.directionToL2 h p.1 ∂μ.prod μ := by
    rw [KernelOperator.operator_inner]
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_const 2 μ (1 : ℝ))]
      with p hp
    simp only [one, hp, Function.const_apply, mul_one]
  have hquad : ⟪T (Variation.directionToL2 h), Variation.directionToL2 h⟫ =
      ∫ p : Ω × Ω, K p.1 p.2 * Variation.directionToL2 h p.2 *
        Variation.directionToL2 h p.1 ∂μ.prod μ := by
    exact KernelOperator.operator_inner K (sq_nonneg _) (squareKernel_measurable W m)
      (squareKernel_bound W m) _ _
  rw [stationaryEnergy_reweight, Variation.weightedPairIntegral_eq K (sq_nonneg _)
    (squareKernel_measurable W m) (squareKernel_bound W m), Variation.vertexWeight,
    Variation.weighted_quadratic_expansion T hsym]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  change ⟪T one, one⟫ + t * (2 * ⟪T one, Variation.directionToL2 h⟫) +
    t * (t * ⟪T (Variation.directionToL2 h), Variation.directionToL2 h⟫) = _
  rw [hone, hlinear, hquad]
  ring

variable [MeasurableSpace.CountablyGenerated Ω]

/-- A bounded kernel-null tilt has nearby actual full optimizers at the
same original recorded multiplier. Exact density preservation and every
new class field are derived before the multipliers are identified. -/
theorem FullStationaryClass.eventually_reweight_null {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (h : Variation.WeightDirections μ)
    (hnull : shiftedOperator W m (Variation.directionToL2 h) = 0) :
    ∀ᶠ t : ℝ in nhds 0, ∃ ht : ‖t • h‖ < 1,
      letI : IsProbabilityMeasure
          (weightedMeasure (μ := μ) (Variation.vertexWeight (t • h))) :=
        weightedMeasure_probability
          ((Lp.memLp (Variation.vertexWeight (t • h))).integrable (by norm_num))
          (Variation.vertexWeight_nonnegative (t • h) ht)
          (Variation.vertexWeight_integral (t • h))
      FullStationaryClass d c (reweight W (t • h) ht) m := by
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hfirst := shiftedFirstVariation_zero_of_stationary W m _ hW.stationary
  obtain ⟨hAfirst, hA⟩ := full_null_direction_density_rigidity W hW.full hopt m
    hfirst hregular u hq h hnull
  have hu := full_positive_direction_transverse W hW.full hopt m hfirst hregular u hq
  have hM : Variation.weightSecondVariation (shiftedOperator W m) h h = 0 := by
    change ⟪shiftedOperator W m (Variation.directionToL2 h), Variation.directionToL2 h⟫ = 0
    rw [hnull, inner_zero_left]
  let one := Lp.const 2 μ (1 : ℝ)
  let z := Variation.directionToL2 u
  let D := fun t : ℝ => ⟪adjacencyOperator W (Variation.vertexWeight (t • h)), z⟫
  have hD : ContinuousAt D 0 := by
    dsimp only [D, Variation.vertexWeight]
    fun_prop
  have hD0 : D 0 ≠ 0 := by
    intro hz
    apply hu
    change 2 * ⟪adjacencyOperator W one, z⟫ = 0
    have hz' : ⟪adjacencyOperator W one, z⟫ = 0 := by simpa [D, Variation.vertexWeight] using hz
    rw [hz', mul_zero]
  have hnearD : ∀ᶠ t : ℝ in nhds 0, D t ≠ 0 := hD.eventually_ne hD0
  have hnear := hW.eventually_reweight hd h u hu hAfirst hA hM
  have hold : shiftedOperator W m one = (2 * (c - m * d)) • one :=
    KernelOperator.constant_one_eigenvector_of_stationary (shiftedKernel W m) (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m) _ hW.stationary
  filter_upwards [hnear, hnearD] with t ht hDt
  obtain ⟨htweight, n, hn, hrow⟩ := ht
  refine ⟨htweight, ?_⟩
  have hmrow : shiftedOperator W m (Variation.vertexWeight (t • h)) =
      (2 * (c - m * d)) • one := by
    simp only [Variation.vertexWeight, map_add, map_smul, hnull, smul_zero, add_zero]
    exact hold
  have hnscalar := congrArg (fun f : Lp ℝ 2 μ => ⟪f, z⟫) hrow
  have hmscalar := congrArg (fun f : Lp ℝ 2 μ => ⟪f, z⟫) hmrow
  simp only [one, z, shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left,
    KernelOperator.inner_constant_one, Variation.direction_integral_zero, mul_zero] at hnscalar hmscalar
  have hprod : (n - m) * D t = 0 := by
    dsimp only [D]
    linarith
  have hnm : n = m := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hDt)
  simpa only [hnm] using hn

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- Actual maximum-J selection forces the squared-kernel first variation
to vanish along every bounded null direction. Nearby class membership,
the same multiplier and fixed-law realization are all constructed. -/
theorem FullStationaryClass.selected_energy_null_first_variation
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hmax : ∀ V : Model Ω μ, FullStationaryClass d c V m →
      stationaryEnergy V m ≤ stationaryEnergy W m)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (h : Variation.WeightDirections μ)
    (hnull : shiftedOperator W m (Variation.directionToL2 h) = 0) :
    (∫ p : Ω × Ω, (shiftedKernel W m p.1 p.2) ^ 2 *
      Variation.directionToL2 h p.1 ∂μ.prod μ) = 0 := by
  let L := ∫ p : Ω × Ω, (shiftedKernel W m p.1 p.2) ^ 2 *
    Variation.directionToL2 h p.1 ∂μ.prod μ
  let Q := ∫ p : Ω × Ω, (shiftedKernel W m p.1 p.2) ^ 2 *
    Variation.directionToL2 h p.2 * Variation.directionToL2 h p.1 ∂μ.prod μ
  let J := fun t : ℝ => stationaryEnergy W m + 2 * t * L + t ^ 2 * Q
  have hnear := hW.eventually_reweight_null hd hregular u hq h hnull
  have hlocal : IsLocalMax J 0 := by
    filter_upwards [hnear] with t ht
    obtain ⟨htweight, hclass⟩ := ht
    let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (t • h))
    have : IsProbabilityMeasure ν := weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight (t • h))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative (t • h) htweight)
      (Variation.vertexWeight_integral (t • h))
    obtain ⟨V, hV, henergy⟩ := exists_fullStationary_transport_of_ac (μ := μ)
      (show ν ≪ μ from withDensity_absolutelyContinuous _ _) hclass
    have hle := hmax V hV
    rw [henergy, stationaryEnergy_reweight_smul] at hle
    simpa only [J, L, Q, mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hle
  have hderiv : HasDerivAt J (2 * L) 0 := by
    have hlinear := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const L).const_add
      (stationaryEnergy W m)
    have hquadratic := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const Q
    convert hlinear.add hquadratic using 1
    · rfl
    · simp
  have hz := hlocal.hasDerivAt_eq_zero hderiv
  linarith

/-- A bounded actual null vector has zero mean by positive stationarity,
so the selected energy identity applies without a supplied mean condition. -/
theorem FullStationaryClass.selected_energy_null_vector_first_variation
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hmax : ∀ V : Model Ω μ, FullStationaryClass d c V m →
      stationaryEnergy V m ≤ stationaryEnergy W m)
    (hν : 0 < 2 * (c - m * d))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hnull : shiftedOperator W m f = 0) :
    (∫ p : Ω × Ω, (shiftedKernel W m p.1 p.2) ^ 2 * f p.1 ∂μ.prod μ) = 0 := by
  have hmean := full_null_vector_mean_zero W m _ hν hW.stationary f hnull
  obtain ⟨h, hh⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
  simpa only [hh] using hW.selected_energy_null_first_variation hd hmax hregular u hq h
    (by rwa [hh])

variable [MeasurableEq Ω] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A genuine strict benchmark gap supplies positive stationarity,
regularity and the positive direction for every bounded null vector of
the original maximum-J model. No nearby competitor is a premise. -/
theorem FullStationaryClass.selected_energy_null_vector_first_variation_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ V : Model Ω μ, FullStationaryClass d c V m →
      stationaryEnergy V m ≤ stationaryEnergy W m)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hnull : shiftedOperator W m f = 0) :
    (∫ p : Ω × Ω, (shiftedKernel W m p.1 p.2) ^ 2 * f p.1 ∂μ.prod μ) = 0 := by
  have hstructure := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hstructure.positive_eigenvector
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hmean σ hσ heigen
  exact hW.selected_energy_null_vector_first_variation ⟨by linarith [hd.1], hd.2⟩ hmax
    hstructure.stationary_pos hstructure.regular u hq f hf hnull

end Erdos1017.CappedModel

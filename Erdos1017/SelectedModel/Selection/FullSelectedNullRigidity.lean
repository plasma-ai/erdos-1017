module

public import Erdos1017.SelectedModel.Selection.FullStationaryReweight
public import Erdos1017.SelectedModel.Selection.FullStationaryTransport
public import Erdos1017.SelectedModel.Selection.FullTangentNullDensity
public import Erdos1017.SelectedModel.LinearFractionalExtremum

/-!
# Tangent-null rigidity of the selected multiplier

Minimality of the recorded original multiplier turns a tangent tilt with zero
shifted energy into zero adjacency energy and a null row of the same kernel, for
every bounded mean-zero `L²` class tangent to the degree.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Minimality of the recorded original multiplier turns an exact tangent
zero-energy tilt into a null row. Nearby multipliers and class membership
are constructed from the actual reweighted kernel and transported laws. -/
theorem FullStationaryClass.selected_null_row_of_adjacency_null {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (h u : Variation.WeightDirections μ)
    (hu : Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0)
    (hfirst : Variation.weightFirstVariation (adjacencyOperator W) h = 0)
    (hA : Variation.weightSecondVariation (adjacencyOperator W) h h = 0)
    (hM : Variation.weightSecondVariation (shiftedOperator W m) h h = 0) :
    shiftedOperator W m (Variation.directionToL2 h) = 0 := by
  let one := Lp.const 2 μ (1 : ℝ)
  let v := Variation.directionToL2 h
  let z := Variation.directionToL2 u
  let a := ⟪chargeOperator W one, z⟫
  let b := ⟪chargeOperator W v, z⟫
  let e := ⟪adjacencyOperator W one, z⟫
  let k := ⟪adjacencyOperator W v, z⟫
  let R := Variation.linearFractional a b e k
  have he : e ≠ 0 := by
    intro hz
    apply hu
    change 2 * e = 0
    rw [hz, mul_zero]
  have hbase : a = m * e := by
    have hh := LinearMap.congr_fun
      (firstVariation_identity_of_shifted_zero W m
        (shiftedFirstVariation_zero_of_stationary W m _ hW.stationary)) u
    change 2 * a = m * (2 * e) at hh
    linarith
  have hR0 : R 0 = m := by
    change (a + b * 0) / (e + k * 0) = m
    simpa only [mul_zero, add_zero] using (div_eq_iff he).mpr hbase
  have hYpoly (t : ℝ) :
      ⟪chargeOperator W (Variation.vertexWeight (t • h)), z⟫ = a + b * t := by
    simp only [Variation.vertexWeight, map_add, map_smul, inner_add_left, real_inner_smul_left]
    change a + t * b = a + b * t
    ring
  have hApoly (t : ℝ) :
      ⟪adjacencyOperator W (Variation.vertexWeight (t • h)), z⟫ = e + k * t := by
    simp only [Variation.vertexWeight, map_add, map_smul, inner_add_left, real_inner_smul_left]
    change e + t * k = e + k * t
    ring
  have hnear := hW.eventually_reweight hd h u hu hfirst hA hM
  have hden := Variation.linearFractional_eventually_ne_zero_den e k he
  have hcomparison : ∀ᶠ t : ℝ in nhds 0, ∃ ht : ‖t • h‖ < 1,
      shiftedOperator W (R t) (Variation.vertexWeight (t • h)) =
        (2 * (c - R t * d)) • one ∧ m ≤ R t := by
    filter_upwards [hnear, hden] with t ht hden
    obtain ⟨htweight, hclass⟩ := ht
    let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (t • h))
    have : IsProbabilityMeasure ν := weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight (t • h))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative (t • h) htweight)
      (Variation.vertexWeight_integral (t • h))
    obtain ⟨n, hn, hrow⟩ := hclass
    have hscalar : n = R t := by
      have hh := congrArg (fun f : Lp ℝ 2 μ => ⟪f, z⟫) hrow
      rw [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left,
        real_inner_smul_left, KernelOperator.inner_constant_one,
        Variation.direction_integral_zero, mul_zero] at hh
      rw [hYpoly, hApoly] at hh
      change n = (a + b * t) / (e + k * t)
      apply (eq_div_iff hden).mpr
      linarith
    have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
    obtain ⟨V, hV, _⟩ := exists_fullStationary_transport_of_ac (μ := μ) hac hn
    refine ⟨htweight, ?_, ?_⟩
    · simpa only [hscalar] using hrow
    · simpa only [hscalar] using hmin V n hV
  have hlocal : IsLocalMin R 0 := by
    filter_upwards [hcomparison] with t ht
    rw [hR0]
    exact ht.choose_spec.2
  have hconstant := Variation.linearFractional_eventually_eq_of_local_min he hlocal
  have hconstant' : ∀ᶠ t : ℝ in nhds 0, R t = m := by
    filter_upwards [hconstant] with t ht
    exact ht.trans ((div_eq_iff he).mpr hbase)
  have hpositive : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ⟨hcomp, hconst⟩, htpos⟩ :=
    (((hcomparison.and hconstant').filter_mono nhdsWithin_le_nhds).and hpositive).exists
  obtain ⟨htweight, hrow, _⟩ := hcomp
  rw [hconst] at hrow
  have hold : shiftedOperator W m one = (2 * (c - m * d)) • one :=
    KernelOperator.constant_one_eigenvector_of_stationary (shiftedKernel W m) (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m) _ hW.stationary
  rw [Variation.vertexWeight, map_smul, map_add, map_smul, hold] at hrow
  have hz : t • shiftedOperator W m v = 0 :=
    add_left_cancel (hrow.trans (add_zero _).symm)
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt htpos)

/-- The selected original multiplier turns zero tangent shifted energy into
both zero adjacency energy and a null row of that same original kernel. -/
theorem FullStationaryClass.selected_tangent_null_rigidity {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (h : Variation.WeightDirections μ)
    (hdegree : Variation.weightFirstVariation (adjacencyOperator W) h = 0)
    (henergy : Variation.weightSecondVariation (shiftedOperator W m) h h = 0) :
    Variation.weightSecondVariation (adjacencyOperator W) h h = 0 ∧
      shiftedOperator W m (Variation.directionToL2 h) = 0 := by
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hfirst := shiftedFirstVariation_zero_of_stationary W m _ hW.stationary
  have hA := full_tangent_null_density W hW.full hopt m hfirst hregular u hq
    h hdegree henergy
  have hu := full_positive_direction_transverse W hW.full hopt m hfirst hregular u hq
  exact ⟨hA, hW.selected_null_row_of_adjacency_null hd hmin h u hu hdegree hA henergy⟩

/-- The selected model's rigidity holds for every bounded mean-zero L²
class tangent to its actual original degree, with zero shifted energy. -/
theorem FullStationaryClass.selected_tangent_null_vector_rigidity
    {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0)
    (henergy : ⟪shiftedOperator W m f, f⟫ = 0) :
    ⟪adjacencyOperator W f, f⟫ = 0 ∧ shiftedOperator W m f = 0 := by
  obtain ⟨h, hh⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
  have hdegree' : Variation.weightFirstVariation (adjacencyOperator W) h = 0 := by
    change 2 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 h⟫ = 0
    rw [hh, hdegree, mul_zero]
  have henergy' : Variation.weightSecondVariation (shiftedOperator W m) h h = 0 := by
    change ⟪shiftedOperator W m (Variation.directionToL2 h), Variation.directionToL2 h⟫ = 0
    rwa [hh]
  obtain ⟨hA, hM⟩ := hW.selected_tangent_null_rigidity hd hmin hregular u hq
    h hdegree' henergy'
  change ⟪adjacencyOperator W (Variation.directionToL2 h), Variation.directionToL2 h⟫ = 0 at hA
  rw [hh] at hA hM
  exact ⟨hA, hM⟩

/-- An actual positive mean-zero eigenvector supplies the required bounded
transverse direction internally; no nearby multiplier or model is supplied. -/
theorem FullStationaryClass.selected_tangent_null_vector_rigidity_of_positive_eigenvector
    {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hwmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : 0 < σ) (heigen : shiftedOperator W m w = σ • w)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0)
    (henergy : ⟪shiftedOperator W m f, f⟫ = 0) :
    ⟪adjacencyOperator W f, f⟫ = 0 ∧ shiftedOperator W m f = 0 := by
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hwmean σ hσ heigen
  exact hW.selected_tangent_null_vector_rigidity hd hmin hregular u hq
    f hf hmean hdegree henergy

end Erdos1017.CappedModel

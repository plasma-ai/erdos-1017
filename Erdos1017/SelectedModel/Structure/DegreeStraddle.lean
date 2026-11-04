module

public import Erdos1017.SelectedModel.Structure.NormalizedSetKernelEnergy
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Erdos1017.SelectedModel.Selection.FullPositiveEigenvector

/-!
# No degree straddle around an independent base

Nonnegative densities missing an independent base cannot straddle its degree
when their mutual kernel pairing is positive, by a convex-mixture tangent
direction against the full optimum's tangent inequality; the same holds for
positive missing sets at the strict-gap optimum.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A nonnegative actual kernel has nonnegative pairing on nonnegative
L² densities. This is not a positive-semidefinite operator assumption. -/
theorem operator_inner_nonneg_of_nonnegative
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hpos : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (f g : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hg : ∀ᵐ x ∂μ, 0 ≤ g x) :
    0 ≤ ⟪operator K hB0 hK hB f, g⟫ := by
  rw [operator_inner]
  apply integral_nonneg_of_ae
  filter_upwards [hpos, Measure.quasiMeasurePreserving_snd.ae hf,
    Measure.quasiMeasurePreserving_fst.ae hg] with p hp hf hg
  exact mul_nonneg (mul_nonneg hp hf) hg

/-- A positive convex mixture of lower and upper degree densities matches
the base degree. The difference is an actual bounded tangent direction with
strictly positive unhalved energy. -/
theorem exists_positive_tangent_of_degree_straddle
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hsym : T.toLinearMap.IsSymmetric)
    (g b l u : Lp ℝ 2 μ)
    (hb : b ∈ boundedL2Submodule μ) (hl : l ∈ boundedL2Submodule μ)
    (hu : u ∈ boundedL2Submodule μ)
    (hbm : (∫ x, b x ∂μ) = 1) (hlm : (∫ x, l x ∂μ) = 1)
    (hum : (∫ x, u x ∂μ) = 1)
    (hbb : ⟪T b, b⟫ = 0) (hbl : ⟪T b, l⟫ = 0) (hbu : ⟪T b, u⟫ = 0)
    (hll : 0 ≤ ⟪T l, l⟫) (huu : 0 ≤ ⟪T u, u⟫) (hlu : 0 < ⟪T l, u⟫)
    (hlower : ⟪g, l⟫ < ⟪g, b⟫) (hupper : ⟪g, b⟫ < ⟪g, u⟫) :
    ∃ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ ∧ (∫ x, f x ∂μ) = 0 ∧
      ⟪g, f⟫ = 0 ∧ 0 < ⟪T f, f⟫ := by
  let α := (⟪g, u⟫ - ⟪g, b⟫) / (⟪g, u⟫ - ⟪g, l⟫)
  let β := (⟪g, b⟫ - ⟪g, l⟫) / (⟪g, u⟫ - ⟪g, l⟫)
  have hden : 0 < ⟪g, u⟫ - ⟪g, l⟫ := by linarith
  have hα : 0 < α := div_pos (sub_pos.mpr hupper) hden
  have hβ : 0 < β := div_pos (sub_pos.mpr hlower) hden
  have hsum : α + β = 1 := by
    dsimp only [α, β]
    field_simp
    ring
  have hdegree : α * ⟪g, l⟫ + β * ⟪g, u⟫ = ⟪g, b⟫ := by
    dsimp only [α, β]
    field_simp
    ring
  have hswap (v w : Lp ℝ 2 μ) : ⟪T v, w⟫ = ⟪T w, v⟫ := by
    calc
      _ = ⟪v, T w⟫ := hsym v w
      _ = _ := real_inner_comm _ _
  have hlb : ⟪T l, b⟫ = 0 := (hswap l b).trans hbl
  have hub : ⟪T u, b⟫ = 0 := (hswap u b).trans hbu
  have hul : ⟪T u, l⟫ = ⟪T l, u⟫ := hswap u l
  let f := α • l + β • u - b
  refine ⟨f, (boundedL2Submodule μ).sub_mem ((boundedL2Submodule μ).add_mem
    ((boundedL2Submodule μ).smul_mem α hl) ((boundedL2Submodule μ).smul_mem β hu)) hb, ?_, ?_, ?_⟩
  · rw [← inner_constant_one]
    simp only [f, inner_sub_right, inner_add_right, real_inner_smul_right,
      inner_constant_one, hlm, hum, hbm, mul_one]
    linarith
  · simp only [f, inner_sub_right, inner_add_right, real_inner_smul_right]
    linarith
  · have hexp : ⟪T f, f⟫ = α ^ 2 * ⟪T l, l⟫ + β ^ 2 * ⟪T u, u⟫ +
        2 * α * β * ⟪T l, u⟫ := by
      simp only [f, map_sub, map_add, map_smul, inner_sub_left, inner_sub_right,
        inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hbb, hbl, hbu, hlb, hub, hul]
      ring
    rw [hexp]
    have hcross : 0 < 2 * α * β * ⟪T l, u⟫ := by positivity
    have hleft := mul_nonneg (sq_nonneg α) hll
    have hright := mul_nonneg (sq_nonneg β) huu
    linarith

/-- Actual nonnegative densities cannot straddle the degree of an
independent base if both miss it and their mutual kernel pairing is positive. -/
theorem not_degree_straddle
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hpos : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2) (g b l u : Lp ℝ 2 μ)
    (hnonpos : ∀ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ →
      (∫ x, f x ∂μ) = 0 → ⟪g, f⟫ = 0 → ⟪operator K hB0 hK hB f, f⟫ ≤ 0)
    (hb : b ∈ boundedL2Submodule μ) (hl : l ∈ boundedL2Submodule μ)
    (hu : u ∈ boundedL2Submodule μ)
    (hlpos : ∀ᵐ x ∂μ, 0 ≤ l x) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hbm : (∫ x, b x ∂μ) = 1) (hlm : (∫ x, l x ∂μ) = 1)
    (hum : (∫ x, u x ∂μ) = 1)
    (hbb : ⟪operator K hB0 hK hB b, b⟫ = 0)
    (hbl : ⟪operator K hB0 hK hB b, l⟫ = 0)
    (hbu : ⟪operator K hB0 hK hB b, u⟫ = 0)
    (hlu : 0 < ⟪operator K hB0 hK hB l, u⟫) :
    ¬(⟪g, l⟫ < ⟪g, b⟫ ∧ ⟪g, b⟫ < ⟪g, u⟫) := by
  rintro ⟨hlower, hupper⟩
  obtain ⟨f, hf, hm, hd, he⟩ := exists_positive_tangent_of_degree_straddle
    (operator K hB0 hK hB) (operator_symmetric K hB0 hK hB hsym)
    g b l u hb hl hu hbm hlm hum hbb hbl hbu
    (operator_inner_nonneg_of_nonnegative K hB0 hK hB hpos l l hlpos hlpos)
    (operator_inner_nonneg_of_nonnegative K hB0 hK hB hpos u u hupos hupos)
    hlu hlower hupper
  exact (not_le_of_gt he) (hnonpos f hf hm hd)

/-- A positive-energy density missing an independent base cannot have the
same original average degree under the actual tangent inequality. -/
theorem degree_ne_of_positive_energy
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hsym : T.toLinearMap.IsSymmetric)
    (g b e : Lp ℝ 2 μ)
    (hnonpos : ∀ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ →
      (∫ x, f x ∂μ) = 0 → ⟪g, f⟫ = 0 → ⟪T f, f⟫ ≤ 0)
    (hb : b ∈ boundedL2Submodule μ) (he : e ∈ boundedL2Submodule μ)
    (hbm : (∫ x, b x ∂μ) = 1) (hem : (∫ x, e x ∂μ) = 1)
    (hbb : ⟪T b, b⟫ = 0) (hbe : ⟪T b, e⟫ = 0) (hee : 0 < ⟪T e, e⟫) :
    ⟪g, e⟫ ≠ ⟪g, b⟫ := by
  intro hdegree
  have heb : ⟪T e, b⟫ = 0 := by
    calc
      _ = ⟪e, T b⟫ := hsym e b
      _ = ⟪T b, e⟫ := real_inner_comm _ _
      _ = 0 := hbe
  have hmean : (∫ x, (e - b) x ∂μ) = 0 := by
    rw [← inner_constant_one, inner_sub_right, inner_constant_one,
      inner_constant_one, hem, hbm, sub_self]
  have hd : ⟪g, e - b⟫ = 0 := by rw [inner_sub_right, hdegree, sub_self]
  have hn := hnonpos (e - b) ((boundedL2Submodule μ).sub_mem he hb) hmean hd
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hbe, heb, hbb] at hn
  linarith

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The full optimum's actual tangent inequality extends to every bounded
mean-zero L² direction. The energy is the unhalved form ⟪Mf,f⟫. -/
theorem FullStationaryClass.bounded_tangent_nonpositive
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0) :
    ⟪shiftedOperator W m f, f⟫ ≤ 0 := by
  obtain ⟨v, hv⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hd : Variation.weightFirstVariation (adjacencyOperator W) v = 0 := by
    change 2 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 v⟫ = 0
    rw [hv, hdegree, mul_zero]
  have h := full_regular_tangent_nonpositive W hW.full hopt m
    (shiftedFirstVariation_zero_of_stationary W m _ hW.stationary) hregular v hd
  change ⟪shiftedOperator W m (Variation.directionToL2 v), Variation.directionToL2 v⟫ ≤ 0 at h
  rwa [hv] at h

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- At the original strict-gap optimum, actual positive missing sets with
positive mutual shifted-kernel rectangle cannot straddle the independent
base's average original degree. No degree orientation is assumed. -/
theorem FullStationaryClass.not_degree_straddle_sets
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (b l u : Set Ω) (hb : MeasurableSet b) (hl : MeasurableSet l) (hu : MeasurableSet u)
    (hbpos : 0 < μ b) (hlpos : 0 < μ l) (hupos : 0 < μ u)
    (hbb : ∀ᵐ p ∂(μ.restrict b).prod (μ.restrict b), shiftedKernel W m p.1 p.2 = 0)
    (hbl : ∀ᵐ p ∂(μ.restrict b).prod (μ.restrict l), shiftedKernel W m p.1 p.2 = 0)
    (hbu : ∀ᵐ p ∂(μ.restrict b).prod (μ.restrict u), shiftedKernel W m p.1 p.2 = 0)
    (hlu : ∀ᵐ p ∂(μ.restrict l).prod (μ.restrict u), 0 < shiftedKernel W m p.1 p.2) :
    ¬(⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), KernelOperator.normalizedSetL2 l hl⟫ <
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), KernelOperator.normalizedSetL2 b hb⟫ ∧
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), KernelOperator.normalizedSetL2 b hb⟫ <
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), KernelOperator.normalizedSetL2 u hu⟫) := by
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hswap (v w : Lp ℝ 2 μ) : ⟪shiftedOperator W m v, w⟫ = ⟪shiftedOperator W m w, v⟫ := by
    calc
      _ = ⟪v, shiftedOperator W m w⟫ :=
        KernelOperator.operator_symmetric _ _ _ _ hsym v w
      _ = _ := real_inner_comm _ _
  apply KernelOperator.not_degree_straddle (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    (hW.moment_mem.mono (fun _ hp => hp.1))
    (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)))
    (KernelOperator.normalizedSetL2 b hb) (KernelOperator.normalizedSetL2 l hl)
    (KernelOperator.normalizedSetL2 u hu)
    (hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular)
    (KernelOperator.normalizedSetL2_bounded b hb) (KernelOperator.normalizedSetL2_bounded l hl)
    (KernelOperator.normalizedSetL2_bounded u hu)
    (KernelOperator.normalizedSetL2_nonnegative l hl) (KernelOperator.normalizedSetL2_nonnegative u hu)
    (KernelOperator.normalizedSetL2_integral b hb hbpos)
    (KernelOperator.normalizedSetL2_integral l hl hlpos)
    (KernelOperator.normalizedSetL2_integral u hu hupos)
  · exact KernelOperator.operator_inner_normalizedSetL2_eq_zero _ _ _ _ b b hb hb hbb
  · change ⟪shiftedOperator W m _, _⟫ = 0
    rw [hswap]
    exact KernelOperator.operator_inner_normalizedSetL2_eq_zero _ _ _ _ b l hb hl hbl
  · change ⟪shiftedOperator W m _, _⟫ = 0
    rw [hswap]
    exact KernelOperator.operator_inner_normalizedSetL2_eq_zero _ _ _ _ b u hb hu hbu
  · change 0 < ⟪shiftedOperator W m _, _⟫
    rw [hswap]
    exact KernelOperator.operator_inner_normalizedSetL2_pos _ _ _ _ l u hl hu hlpos hupos hlu

/-- A positive complete set missing an independent base cannot have its
same average original degree in the same strict-gap full optimum. -/
theorem FullStationaryClass.degree_ne_of_positive_missing_set
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (b e : Set Ω) (hb : MeasurableSet b) (he : MeasurableSet e)
    (hbpos : 0 < μ b) (hepos : 0 < μ e)
    (hbb : ∀ᵐ p ∂(μ.restrict b).prod (μ.restrict b), shiftedKernel W m p.1 p.2 = 0)
    (hbe : ∀ᵐ p ∂(μ.restrict e).prod (μ.restrict b), shiftedKernel W m p.1 p.2 = 0)
    (hee : ∀ᵐ p ∂(μ.restrict e).prod (μ.restrict e), 0 < shiftedKernel W m p.1 p.2) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), KernelOperator.normalizedSetL2 e he⟫ ≠
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), KernelOperator.normalizedSetL2 b hb⟫ := by
  have hsym : (shiftedOperator W m).toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  exact KernelOperator.degree_ne_of_positive_energy (shiftedOperator W m) hsym
    (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)))
    (KernelOperator.normalizedSetL2 b hb) (KernelOperator.normalizedSetL2 e he)
    (hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular)
    (KernelOperator.normalizedSetL2_bounded b hb) (KernelOperator.normalizedSetL2_bounded e he)
    (KernelOperator.normalizedSetL2_integral b hb hbpos)
    (KernelOperator.normalizedSetL2_integral e he hepos)
    (KernelOperator.operator_inner_normalizedSetL2_eq_zero _ _ _ _ b b hb hb hbb)
    (KernelOperator.operator_inner_normalizedSetL2_eq_zero _ _ _ _ e b he hb hbe)
    (KernelOperator.operator_inner_normalizedSetL2_pos _ _ _ _ e e he he hepos hepos hee)

end Erdos1017.CappedModel

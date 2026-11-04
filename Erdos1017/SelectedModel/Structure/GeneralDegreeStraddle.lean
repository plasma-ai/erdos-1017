module

public import Erdos1017.SelectedModel.Structure.DegreeStraddle

/-!
# Degree straddle with a nonnegative base

The convex tangent construction needs only nonnegative base energy, so three
nonnegative densities cannot exhibit the straddling configuration for a
nonnegative kernel with tangent nonpositivity, and a positive base set missing
two sets joined by a positive rectangle cannot have average degree strictly
between theirs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The convex tangent construction only needs nonnegative base energy.
Its unhalved energy includes the base self-energy with a positive sign. -/
theorem exists_positive_tangent_of_degree_straddle_nonnegative_base
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hsym : T.toLinearMap.IsSymmetric)
    (g b l u : Lp ℝ 2 μ)
    (hb : b ∈ boundedL2Submodule μ) (hl : l ∈ boundedL2Submodule μ)
    (hu : u ∈ boundedL2Submodule μ)
    (hbm : (∫ x, b x ∂μ) = 1) (hlm : (∫ x, l x ∂μ) = 1)
    (hum : (∫ x, u x ∂μ) = 1)
    (hbb : 0 ≤ ⟪T b, b⟫) (hbl : ⟪T b, l⟫ = 0) (hbu : ⟪T b, u⟫ = 0)
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
        2 * α * β * ⟪T l, u⟫ + ⟪T b, b⟫ := by
      simp only [f, map_sub, map_add, map_smul, inner_sub_left, inner_sub_right,
        inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hbl, hbu, hlb, hub, hul]
      ring
    rw [hexp]
    have hcross : 0 < 2 * α * β * ⟪T l, u⟫ + ⟪T b, b⟫ := by positivity
    have hleft := mul_nonneg (sq_nonneg α) hll
    have hright := mul_nonneg (sq_nonneg β) huu
    linarith

/-- Three actual nonnegative densities cannot exhibit the specified
straddling configuration for a nonnegative kernel with tangent nonpositivity.
All three self-energy bounds follow from pointwise nonnegativity. -/
theorem not_degree_straddle_nonnegative_base
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hpos : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2) (g b l u : Lp ℝ 2 μ)
    (hnonpos : ∀ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ →
      (∫ x, f x ∂μ) = 0 → ⟪g, f⟫ = 0 → ⟪operator K hB0 hK hB f, f⟫ ≤ 0)
    (hb : b ∈ boundedL2Submodule μ) (hl : l ∈ boundedL2Submodule μ)
    (hu : u ∈ boundedL2Submodule μ)
    (hbpos : ∀ᵐ x ∂μ, 0 ≤ b x) (hlpos : ∀ᵐ x ∂μ, 0 ≤ l x) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hbm : (∫ x, b x ∂μ) = 1) (hlm : (∫ x, l x ∂μ) = 1)
    (hum : (∫ x, u x ∂μ) = 1)
    (hbl : ⟪operator K hB0 hK hB b, l⟫ = 0)
    (hbu : ⟪operator K hB0 hK hB b, u⟫ = 0)
    (hlu : 0 < ⟪operator K hB0 hK hB l, u⟫) :
    ¬(⟪g, l⟫ < ⟪g, b⟫ ∧ ⟪g, b⟫ < ⟪g, u⟫) := by
  rintro ⟨hlower, hupper⟩
  obtain ⟨f, hf, hm, hd, he⟩ := exists_positive_tangent_of_degree_straddle_nonnegative_base
    (operator K hB0 hK hB) (operator_symmetric K hB0 hK hB hsym)
    g b l u hb hl hu hbm hlm hum
    (operator_inner_nonneg_of_nonnegative K hB0 hK hB hpos b b hbpos hbpos) hbl hbu
    (operator_inner_nonneg_of_nonnegative K hB0 hK hB hpos l l hlpos hlpos)
    (operator_inner_nonneg_of_nonnegative K hB0 hK hB hpos u u hupos hupos)
    hlu hlower hupper
  exact (not_le_of_gt he) (hnonpos f hf hm hd)

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A positive base set missing two sets joined by a positive rectangle
cannot have its original average degree strictly between theirs. The base
need not be independent, and no condition on its internal rectangle is used. -/
theorem FullStationaryClass.not_degree_straddle_sets_nonnegative_base
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (b l u : Set Ω) (hb : MeasurableSet b) (hl : MeasurableSet l) (hu : MeasurableSet u)
    (hbpos : 0 < μ b) (hlpos : 0 < μ l) (hupos : 0 < μ u)
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
  apply KernelOperator.not_degree_straddle_nonnegative_base (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    (hW.moment_mem.mono (fun _ hp => hp.1))
    (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)))
    (KernelOperator.normalizedSetL2 b hb) (KernelOperator.normalizedSetL2 l hl)
    (KernelOperator.normalizedSetL2 u hu)
    (hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular)
    (KernelOperator.normalizedSetL2_bounded b hb) (KernelOperator.normalizedSetL2_bounded l hl)
    (KernelOperator.normalizedSetL2_bounded u hu)
    (KernelOperator.normalizedSetL2_nonnegative b hb)
    (KernelOperator.normalizedSetL2_nonnegative l hl) (KernelOperator.normalizedSetL2_nonnegative u hu)
    (KernelOperator.normalizedSetL2_integral b hb hbpos)
    (KernelOperator.normalizedSetL2_integral l hl hlpos)
    (KernelOperator.normalizedSetL2_integral u hu hupos)
  · change ⟪shiftedOperator W m _, _⟫ = 0
    rw [hswap]
    exact KernelOperator.operator_inner_normalizedSetL2_eq_zero _ _ _ _ b l hb hl hbl
  · change ⟪shiftedOperator W m _, _⟫ = 0
    rw [hswap]
    exact KernelOperator.operator_inner_normalizedSetL2_eq_zero _ _ _ _ b u hb hu hbu
  · change 0 < ⟪shiftedOperator W m _, _⟫
    rw [hswap]
    exact KernelOperator.operator_inner_normalizedSetL2_pos _ _ _ _ l u hl hu hlpos hupos hlu

end Erdos1017.CappedModel

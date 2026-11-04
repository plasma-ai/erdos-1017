module

public import Erdos1017.Models.Kernel.StationaryKernel

/-!
# Normalized set indicators as L² classes

This module defines `normalizedSetL2`, the normalized indicator of a measurable
set as an `L²` class, and shows that the operator acts on a homogeneous positive
set by its whole row, so equal degrees on two positive homogeneous zero blocks
would give a bounded tangent-null direction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual normalized indicator of a measurable set, as an L² class.
Positive mass is required only by the normalization identities. -/
def normalizedSetL2 (s : Set Ω) (hs : MeasurableSet s) : Lp ℝ 2 μ :=
  (μ.real s)⁻¹ • indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)

/-- Normalized set indicators are bounded weight functions. -/
theorem normalizedSetL2_bounded (s : Set Ω) (hs : MeasurableSet s) :
    normalizedSetL2 (μ := μ) s hs ∈ boundedL2Submodule μ := by
  apply (boundedL2Submodule μ).smul_mem
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [show ⇑(indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) =ᵐ[μ]
    s.indicator (fun _ => 1) from indicatorConstLp_coeFn] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Pairing with the normalized indicator is the actual set average. -/
theorem normalizedSetL2_inner (s : Set Ω) (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    ⟪normalizedSetL2 (μ := μ) s hs, f⟫ = (μ.real s)⁻¹ * ∫ x in s, f x ∂μ := by
  rw [normalizedSetL2, real_inner_smul_left, L2.inner_indicatorConstLp_one]

/-- An almost-everywhere constant row has that same average on a positive set. -/
theorem normalizedSetL2_inner_of_constant (s : Set Ω) (hs : MeasurableSet s)
    (hspos : 0 < μ s) (f : Lp ℝ 2 μ) (c : ℝ)
    (hf : ∀ᵐ x ∂μ.restrict s, f x = c) :
    ⟪normalizedSetL2 (μ := μ) s hs, f⟫ = c := by
  have hmass : μ.real s ≠ 0 := (ENNReal.toReal_pos hspos.ne' (measure_ne_top μ s)).ne'
  rw [normalizedSetL2_inner, integral_congr_ae hf, setIntegral_const]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]

/-- A positive set's normalized indicator has mean one. -/
theorem normalizedSetL2_integral (s : Set Ω) (hs : MeasurableSet s) (hspos : 0 < μ s) :
    (∫ x, normalizedSetL2 (μ := μ) s hs x ∂μ) = 1 := by
  rw [← inner_constant_one, real_inner_comm]
  exact normalizedSetL2_inner_of_constant s hs hspos (Lp.const 2 μ (1 : ℝ)) 1
    (ae_restrict_of_ae (Lp.coeFn_const 2 μ (1 : ℝ)))

/-- Acting on a normalized positive homogeneous set gives its whole L² row.
The proof uses actual row integration and symmetry of the integral operator. -/
theorem operator_normalizedSetL2_of_homogeneous_rows
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (s : Set Ω) (hs : MeasurableSet s) (hspos : 0 < μ s) (r : Lp ℝ 2 μ)
    (hrows : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] (r : Ω → ℝ)) :
    operator K hB0 hK hB (normalizedSetL2 s hs) = r := by
  apply ext_inner_right ℝ
  intro f
  have hsymmetric := operator_symmetric K hB0 hK hB hsym (normalizedSetL2 s hs) f
  change ⟪operator K hB0 hK hB (normalizedSetL2 s hs), f⟫ =
    ⟪normalizedSetL2 s hs, operator K hB0 hK hB f⟫ at hsymmetric
  rw [hsymmetric]
  apply normalizedSetL2_inner_of_constant s hs hspos
  filter_upwards [hrows, ae_restrict_of_ae (onL2_coe K hK hB f)] with x hx hfx
  change onL2 K hK hB f x = _
  rw [hfx, applyKernel, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  rw [hy]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- A zero rectangle from a positive homogeneous row set forces its row
value to vanish on the second set. No arbitrary representative point is used. -/
theorem homogeneous_row_zero_of_zero_rectangle
    (K : Ω → Ω → ℝ) (s t : Set Ω) (hspos : 0 < μ s) (r : Lp ℝ 2 μ)
    (hrows : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] (r : Ω → ℝ))
    (hzero : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), K p.1 p.2 = 0) :
    ∀ᵐ y ∂μ.restrict t, r y = 0 := by
  have hsections := Measure.ae_ae_of_ae_prod hzero
  have hgood : ∀ᵐ x ∂μ.restrict s,
      (K x =ᵐ[μ] (r : Ω → ℝ)) ∧ ∀ᵐ y ∂μ.restrict t, K x y = 0 := hrows.and hsections
  obtain ⟨x, _, hx, hzx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne' hgood
  filter_upwards [ae_restrict_of_ae hx, hzx] with y hy hz
  exact hy.symm.trans hz

/-- Equal original degrees on two positive homogeneous zero blocks would
make their normalized indicator difference a bounded tangent-null direction.
Actual null rigidity therefore separates their distinct whole row values. -/
theorem degree_ne_of_homogeneous_zero_blocks
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (g : Lp ℝ 2 μ)
    (hrigid : ∀ f : Lp ℝ 2 μ, f ∈ boundedL2Submodule μ →
      (∫ x, f x ∂μ) = 0 → ⟪g, f⟫ = 0 →
        ⟪operator K hB0 hK hB f, f⟫ = 0 → operator K hB0 hK hB f = 0)
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hspos : 0 < μ s) (htpos : 0 < μ t) (r u : Lp ℝ 2 μ) (hru : r ≠ u)
    (hrows : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] (r : Ω → ℝ))
    (hrowt : ∀ᵐ x ∂μ.restrict t, K x =ᵐ[μ] (u : Ω → ℝ))
    (hss : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), K p.1 p.2 = 0)
    (htt : ∀ᵐ p ∂(μ.restrict t).prod (μ.restrict t), K p.1 p.2 = 0)
    (hst : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), K p.1 p.2 = 0)
    (a b : ℝ) (hgs : ∀ᵐ x ∂μ.restrict s, g x = a)
    (hgt : ∀ᵐ x ∂μ.restrict t, g x = b) : a ≠ b := by
  intro hab
  let v := normalizedSetL2 (μ := μ) s hs
  let w := normalizedSetL2 (μ := μ) t ht
  let T := operator K hB0 hK hB
  have hTv : T v = r :=
    operator_normalizedSetL2_of_homogeneous_rows K hB0 hK hB hsym s hs hspos r hrows
  have hTw : T w = u :=
    operator_normalizedSetL2_of_homogeneous_rows K hB0 hK hB hsym t ht htpos u hrowt
  have hrs : ⟪r, v⟫ = 0 := by
    rw [real_inner_comm]
    exact normalizedSetL2_inner_of_constant s hs hspos r 0
      (homogeneous_row_zero_of_zero_rectangle K s s hspos r hrows hss)
  have hrt : ⟪r, w⟫ = 0 := by
    rw [real_inner_comm]
    exact normalizedSetL2_inner_of_constant t ht htpos r 0
      (homogeneous_row_zero_of_zero_rectangle K s t hspos r hrows hst)
  have hut : ⟪u, w⟫ = 0 := by
    rw [real_inner_comm]
    exact normalizedSetL2_inner_of_constant t ht htpos u 0
      (homogeneous_row_zero_of_zero_rectangle K t t htpos u hrowt htt)
  have hus : ⟪u, v⟫ = 0 := by
    rw [← hTw]
    have h := operator_symmetric K hB0 hK hB hsym w v
    change ⟪T w, v⟫ = ⟪w, T v⟫ at h
    rw [h, hTv, real_inner_comm, hrt]
  have hf : v - w ∈ boundedL2Submodule μ := (boundedL2Submodule μ).sub_mem
    (normalizedSetL2_bounded s hs) (normalizedSetL2_bounded t ht)
  have hmean : (∫ x, (v - w) x ∂μ) = 0 := by
    rw [← inner_constant_one, inner_sub_right, inner_constant_one, inner_constant_one,
      normalizedSetL2_integral s hs hspos, normalizedSetL2_integral t ht htpos, sub_self]
  have hdegree : ⟪g, v - w⟫ = 0 := by
    rw [inner_sub_right, ← real_inner_comm g v, ← real_inner_comm g w,
      normalizedSetL2_inner_of_constant s hs hspos g a hgs,
      normalizedSetL2_inner_of_constant t ht htpos g b hgt, hab, sub_self]
  have henergy : ⟪T (v - w), v - w⟫ = 0 := by
    rw [map_sub, hTv, hTw, inner_sub_left, inner_sub_right, inner_sub_right,
      hrs, hrt, hus, hut]
    ring
  have hnull : T (v - w) = 0 := hrigid (v - w) hf hmean hdegree henergy
  rw [map_sub, hTv, hTw, sub_eq_zero] at hnull
  exact hru hnull

end Erdos1017.KernelOperator

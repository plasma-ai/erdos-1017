module

public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Localizing product functions by rectangle integrals

A bounded measurable function on a product whose integral over every measurable
rectangle is nonpositive, or bounded, is itself nonpositive, or bounded, almost
everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory symmDiff Filter ENNReal

namespace Erdos1017.ProductRectangleLocalization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Bounded integrals vary continuously with a set in measure. -/
private theorem norm_setIntegral_sub_le (f : Ω → ℝ) (hf : Integrable f μ)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (U V : Set Ω)
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    ‖(∫ x in U, f x ∂μ) - (∫ x in V, f x ∂μ)‖ ≤ C * μ.real (U ∆ V) := by
  have hUV : MeasurableSet (U ∆ V) := hU.symmDiff hV
  have hpoint (x : Ω) :
      ‖U.indicator f x - V.indicator f x‖ ≤ (U ∆ V).indicator (fun _ => C) x := by
    by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V
    · have hnot : x ∉ U ∆ V := by simp [Set.mem_symmDiff, hxU, hxV]
      simp [Set.indicator, hxU, hxV, hnot]
    · simpa [Set.indicator, Set.mem_symmDiff, hxU, hxV] using hC x
    · simpa [Set.indicator, Set.mem_symmDiff, hxU, hxV] using hC x
    · have hnot : x ∉ U ∆ V := by simp [Set.mem_symmDiff, hxU, hxV]
      simp [Set.indicator, hxU, hxV, hnot]
  calc
    ‖(∫ x in U, f x ∂μ) - (∫ x in V, f x ∂μ)‖ =
        ‖∫ x, U.indicator f x - V.indicator f x ∂μ‖ := by
      rw [integral_sub (hf.indicator hU) (hf.indicator hV),
        integral_indicator hU, integral_indicator hV]
    _ ≤ ∫ x, (U ∆ V).indicator (fun _ => C) x ∂μ :=
      norm_integral_le_of_norm_le ((integrable_const C).indicator hUV)
        (Eventually.of_forall hpoint)
    _ = C * μ.real (U ∆ V) := by
      rw [integral_indicator_const C hUV, smul_eq_mul, mul_comm]

/-- Inequalities on a measure-dense family extend to every measurable set. -/
private theorem setIntegral_nonpos_of_measureDense (f : Ω → ℝ) (hf : Integrable f μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C)
    {𝒜 : Set (Set Ω)} (hDense : μ.MeasureDense 𝒜)
    (hTest : ∀ U ∈ 𝒜, ∫ x in U, f x ∂μ ≤ 0)
    (U : Set Ω) (hU : MeasurableSet U) : ∫ x in U, f x ∂μ ≤ 0 := by
  by_contra hnot
  have hpos : 0 < ∫ x in U, f x ∂μ := lt_of_not_ge hnot
  let ε : ℝ := (∫ x in U, f x ∂μ) / (C + 1)
  have hε : 0 < ε := div_pos hpos (by linarith)
  obtain ⟨V, hVmem, hδ⟩ := hDense.approx U hU (measure_ne_top μ U) ε hε
  have hV : MeasurableSet V := hDense.measurable V hVmem
  have hδreal : μ.real (U ∆ V) < ε :=
    (lt_ofReal_iff_toReal_lt (measure_ne_top μ (U ∆ V))).1 hδ
  have hdiff := norm_setIntegral_sub_le f hf C hC U V hU hV
  have hstrict : C * ε < ∫ x in U, f x ∂μ := by
    dsimp [ε]
    rw [show C * ((∫ x in U, f x ∂μ) / (C + 1)) =
      C * (∫ x in U, f x ∂μ) / (C + 1) by ring]
    apply (div_lt_iff₀ (by linarith : 0 < C + 1)).2
    nlinarith
  have hbound : C * μ.real (U ∆ V) < ∫ x in U, f x ∂μ :=
    (mul_le_mul_of_nonneg_left hδreal.le hC0).trans_lt hstrict
  have hVnonpos := hTest V hVmem
  have hle : (∫ x in U, f x ∂μ) - (∫ x in V, f x ∂μ) ≤
      C * μ.real (U ∆ V) := le_trans (le_abs_self _) hdiff
  linarith

/-- Rectangle integral inequalities localize a bounded measurable function on a product. -/
theorem ae_nonpos_of_forall_rectangle_integral_nonpos [MeasurableSpace.CountablyGenerated Ω]
    (f : Ω × Ω → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ p, ‖f p‖ ≤ C)
    (hrect : ∀ U V, MeasurableSet U → MeasurableSet V →
      ∫ p in U ×ˢ V, f p ∂μ.prod μ ≤ 0) :
    ∀ᵐ p ∂μ.prod μ, f p ≤ 0 := by
  have hfInt : Integrable f (μ.prod μ) :=
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
  obtain ⟨𝒜, hcount, hDense⟩ := exists_countable_measureDense μ
  have hcols (U : Set Ω) (hUmem : U ∈ 𝒜) :
      ∀ᵐ y ∂μ, (∫ x in U, f (x, y) ∂μ) ≤ 0 := by
    have hU : MeasurableSet U := hDense.measurable U hUmem
    let F : Ω × Ω → ℝ := (Prod.fst ⁻¹' U).indicator f
    have hF : Integrable F (μ.prod μ) :=
      hfInt.indicator (hU.preimage measurable_fst)
    have hFeq (y : Ω) : (∫ x, F (x, y) ∂μ) = ∫ x in U, f (x, y) ∂μ := by
      change (∫ x, U.indicator (fun x => f (x, y)) x ∂μ) = _
      exact integral_indicator hU
    have hg : Integrable (fun y => ∫ x in U, f (x, y) ∂μ) μ := by
      simpa only [hFeq] using hF.integral_prod_right
    apply ae_le_of_forall_setIntegral_le hg (integrable_const (0 : ℝ))
    intro V hV _
    have hInt : IntegrableOn (fun p : Ω × Ω => f p.swap) (V ×ˢ U) (μ.prod μ) :=
      hfInt.swap.integrableOn
    have hFubini : (∫ y in V, ∫ x in U, f (x, y) ∂μ ∂μ) =
        ∫ p in U ×ˢ V, f p ∂μ.prod μ := by
      calc
        _ = ∫ p in V ×ˢ U, f p.swap ∂μ.prod μ :=
          (setIntegral_prod (fun p : Ω × Ω => f p.swap) hInt).symm
        _ = _ := setIntegral_prod_swap U V f
    simpa only [integral_zero] using hFubini.le.trans (hrect U V hU hV)
  have hcolsAll : ∀ᵐ y ∂μ, ∀ U ∈ 𝒜, (∫ x in U, f (x, y) ∂μ) ≤ 0 :=
    (ae_ball_iff hcount).2 hcols
  have hsec (y : Ω) : Integrable (fun x => f (x, y)) μ :=
    Integrable.of_bound (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      C (Eventually.of_forall (fun x => hC (x, y)))
  have hrectAE : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, f (x, y) ≤ 0 := by
    filter_upwards [hcolsAll] with y hy
    have hset (U : Set Ω) (hU : MeasurableSet U) :
        ∫ x in U, f (x, y) ∂μ ≤ 0 :=
      setIntegral_nonpos_of_measureDense (fun x => f (x, y)) (hsec y) C
        ((norm_nonneg _).trans (hC (y, y)))
        (fun x => hC (x, y)) hDense hy U hU
    apply ae_le_of_forall_setIntegral_le (hsec y) (integrable_const (0 : ℝ))
    intro U hU _
    simpa only [integral_zero] using hset U hU
  have hp : MeasurableSet {p : Ω × Ω | f p ≤ 0} :=
    measurableSet_le hf measurable_const
  exact (Measure.ae_prod_iff_ae_ae hp).2 ((Measure.ae_ae_comm hp).2 hrectAE)

/-- A bounded measurable function bounded in integral on every measurable rectangle is
bounded almost everywhere on the product. -/
theorem ae_le_of_forall_rectangle_integral_le [MeasurableSpace.CountablyGenerated Ω]
    (K : Ω × Ω → ℝ) (hK : Measurable K) (B : ℝ)
    (hB : ∀ p, ‖K p‖ ≤ B) (a : ℝ)
    (hrect : ∀ U V, MeasurableSet U → MeasurableSet V →
      ∫ p in U ×ˢ V, K p ∂μ.prod μ ≤ a * μ.real U * μ.real V) :
    ∀ᵐ p ∂μ.prod μ, K p ≤ a := by
  have hKInt : Integrable K (μ.prod μ) :=
    Integrable.of_bound hK.aestronglyMeasurable B (Eventually.of_forall hB)
  have hBound (p : Ω × Ω) : ‖K p - a‖ ≤ max B 0 + |a| := by
    calc
      ‖K p - a‖ ≤ ‖K p‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ B + |a| := by simpa only [Real.norm_eq_abs] using add_le_add_left (hB p) |a|
      _ ≤ max B 0 + |a| := add_le_add_left (le_max_left B 0) _
  have hrect0 (U V : Set Ω) (hU : MeasurableSet U) (hV : MeasurableSet V) :
      ∫ p in U ×ˢ V, K p - a ∂μ.prod μ ≤ 0 := by
    have hsub : (∫ p in U ×ˢ V, K p - a ∂μ.prod μ) =
        (∫ p in U ×ˢ V, K p ∂μ.prod μ) -
          (∫ _ in U ×ˢ V, a ∂μ.prod μ) :=
      integral_sub' hKInt.integrableOn (integrable_const (a : ℝ)).integrableOn
    rw [hsub, setIntegral_const, smul_eq_mul, measureReal_prod_prod]
    linarith [hrect U V hU hV]
  have h := ae_nonpos_of_forall_rectangle_integral_nonpos
    (fun p => K p - a) (hK.sub measurable_const) (max B 0 + |a|) hBound hrect0
  exact h.mono (fun p hp => by linarith)

end Erdos1017.ProductRectangleLocalization

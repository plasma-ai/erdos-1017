module

public import Erdos1017.Exclusions.Common.KernelOrthogonalCubic

/-!
# Two-stage Cauchy-Schwarz bound for the mixed source tax

Two pointwise disjoint bounded rows give a symmetrized rank-two kernel with
twice the product row mass, and each source row of the mixed pairing is bounded
by its rank-two square mass; integrating the row geometric means by
Cauchy-Schwarz then bounds the mixed source tax.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One source row of a mixed tax: two pointwise disjoint bounded rows give
a symmetrized rank-two kernel with exactly twice the product row mass. -/
theorem integral_rank_two_sq (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfB : ∀ x, ‖f x‖ ≤ 1) (hgB : ∀ x, ‖g x‖ ≤ 1) (horth : ∀ x, f x * g x = 0) :
    (∫ p : Ω × Ω, (f p.1 * g p.2 + g p.1 * f p.2) ^ 2 ∂μ.prod μ) =
      2 * ((∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ)) := by
  have hsq : ∀ (u w : Ω → ℝ), Measurable u → Measurable w → (∀ x, ‖u x‖ ≤ 1) →
      (∀ x, ‖w x‖ ≤ 1) →
      Integrable (fun p : Ω × Ω => (u p.1) ^ 2 * (w p.2) ^ 2) (μ.prod μ) :=
    fun u w hu hw huB hwB => Integrable.of_bound
      (((hu.comp measurable_fst).pow_const 2).mul
        ((hw.comp measurable_snd).pow_const 2)).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [norm_mul, norm_pow, norm_pow]
        simpa only [one_mul] using mul_le_mul (pow_le_one₀ (norm_nonneg _) (huB p.1))
          (pow_le_one₀ (norm_nonneg _) (hwB p.2)) (pow_nonneg (norm_nonneg _) 2) zero_le_one))
  calc
    _ = ∫ p : Ω × Ω, (f p.1) ^ 2 * (g p.2) ^ 2 + (g p.1) ^ 2 * (f p.2) ^ 2 ∂μ.prod μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        dsimp only
        linear_combination (2 * (f p.2 * g p.2)) * horth p.1)
    _ = (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) +
        (∫ x, (g x) ^ 2 ∂μ) * (∫ x, (f x) ^ 2 ∂μ) := by
      rw [integral_add (hsq f g hf hg hfB hgB) (hsq g f hg hf hgB hfB)]
      congr 1
      · exact integral_prod_mul (fun x => (f x) ^ 2) (fun x => (g x) ^ 2)
      · exact integral_prod_mul (fun x => (g x) ^ 2) (fun x => (f x) ^ 2)
    _ = _ := by ring

/-- Cauchy–Schwarz on the square bounds one source row of the mixed pairing
by the exact rank-two square mass of that row. -/
theorem rank_two_pairing_sq_le (T : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (hT : Measurable (Function.uncurry T)) (hf : Measurable f) (hg : Measurable g)
    (hTB : ∀ x y, ‖T x y‖ ≤ 1) (hfB : ∀ x, ‖f x‖ ≤ 1) (hgB : ∀ x, ‖g x‖ ≤ 1)
    (horth : ∀ x, f x * g x = 0) :
    (∫ p : Ω × Ω, T p.1 p.2 * (f p.1 * g p.2 + g p.1 * f p.2) ∂μ.prod μ) ^ 2 ≤
      2 * (∫ p : Ω × Ω, (T p.1 p.2) ^ 2 ∂μ.prod μ) *
        ((∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ)) := by
  have hTl : MemLp (fun p : Ω × Ω => T p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hT.aestronglyMeasurable 1 (Eventually.of_forall (fun p => hTB p.1 p.2))
  have hRl : MemLp (fun p : Ω × Ω => f p.1 * g p.2 + g p.1 * f p.2) 2 (μ.prod μ) :=
    MemLp.of_bound (((hf.comp measurable_fst).mul (hg.comp measurable_snd)).add
      ((hg.comp measurable_fst).mul (hf.comp measurable_snd))).aestronglyMeasurable 2
      (Eventually.of_forall (fun p => by
        calc
          _ ≤ ‖f p.1 * g p.2‖ + ‖g p.1 * f p.2‖ := norm_add_le _ _
          _ ≤ 1 + 1 := by
            rw [norm_mul, norm_mul]
            apply add_le_add
            · simpa only [one_mul] using
                mul_le_mul (hfB p.1) (hgB p.2) (norm_nonneg _) zero_le_one
            · simpa only [one_mul] using
                mul_le_mul (hgB p.1) (hfB p.2) (norm_nonneg _) zero_le_one
          _ = 2 := by norm_num))
  have hcauchy := integral_mul_sq_le (fun p : Ω × Ω => T p.1 p.2)
    (fun p => f p.1 * g p.2 + g p.1 * f p.2) hTl hRl
  rw [integral_rank_two_sq f g hf hg hfB hgB horth] at hcauchy
  exact hcauchy.trans_eq (by ring)

/-- Two-stage Cauchy–Schwarz for the mixed source tax. Each source row is
bounded by its exact rank-two mass; the row geometric means are then
integrated by Cauchy–Schwarz in the source. -/
theorem mixed_source_tax_sq_le (T b c : Ω → Ω → ℝ)
    (hT : Measurable (Function.uncurry T)) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c))
    (hTB : ∀ x y, ‖T x y‖ ≤ 1) (hbB : ∀ z x, ‖b z x‖ ≤ 1) (hcB : ∀ z x, ‖c z x‖ ≤ 1)
    (horth : ∀ z x, b z x * c z x = 0) :
    (∫ z, ∫ p : Ω × Ω, T p.1 p.2 * (b z p.1 * c z p.2 + c z p.1 * b z p.2)
        ∂μ.prod μ ∂μ) ^ 2 ≤
      2 * (∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ) *
        (∫ p : Ω × Ω, (c p.1 p.2) ^ 2 ∂μ.prod μ) *
          (∫ p : Ω × Ω, (T p.1 p.2) ^ 2 ∂μ.prod μ) := by
  set X := ∫ p : Ω × Ω, (T p.1 p.2) ^ 2 ∂μ.prod μ
  let B : Ω → ℝ := fun z => ∫ x, (b z x) ^ 2 ∂μ
  let C : Ω → ℝ := fun z => ∫ x, (c z x) ^ 2 ∂μ
  let I : Ω → ℝ := fun z =>
    ∫ p : Ω × Ω, T p.1 p.2 * (b z p.1 * c z p.2 + c z p.1 * b z p.2) ∂μ.prod μ
  let S := ∫ z, Real.sqrt (B z) * Real.sqrt (C z) ∂μ
  have hX0 : 0 ≤ 2 * X := mul_nonneg zero_le_two (integral_nonneg (fun _ => sq_nonneg _))
  have hB0 : ∀ z, 0 ≤ B z := fun z => integral_nonneg (fun _ => sq_nonneg _)
  have hC0 : ∀ z, 0 ≤ C z := fun z => integral_nonneg (fun _ => sq_nonneg _)
  have hB1 : ∀ z, B z ≤ 1 := fun z => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
      (f := fun x => (b z x) ^ 2) (Eventually.of_forall (fun x => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hbB z x)))
    rw [probReal_univ, mul_one] at h
    exact (Real.le_norm_self _).trans h
  have hC1 : ∀ z, C z ≤ 1 := fun z => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
      (f := fun x => (c z x) ^ 2) (Eventually.of_forall (fun x => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hcB z x)))
    rw [probReal_univ, mul_one] at h
    exact (Real.le_norm_self _).trans h
  have hbz : ∀ z, Measurable (b z) := fun z => hb.comp (measurable_prodMk_left (x := z))
  have hcz : ∀ z, Measurable (c z) := fun z => hc.comp (measurable_prodMk_left (x := z))
  have hBm : Measurable B :=
    (StronglyMeasurable.integral_prod_right' (ν := μ)
      (hb.pow_const 2).stronglyMeasurable).measurable
  have hCm : Measurable C :=
    (StronglyMeasurable.integral_prod_right' (ν := μ)
      (hc.pow_const 2).stronglyMeasurable).measurable
  have hsB : MemLp (fun z => Real.sqrt (B z)) 2 μ :=
    MemLp.of_bound (Real.continuous_sqrt.measurable.comp hBm).aestronglyMeasurable 1
      (Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact (Real.sqrt_le_sqrt (hB1 z)).trans_eq Real.sqrt_one))
  have hsC : MemLp (fun z => Real.sqrt (C z)) 2 μ :=
    MemLp.of_bound (Real.continuous_sqrt.measurable.comp hCm).aestronglyMeasurable 1
      (Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact (Real.sqrt_le_sqrt (hC1 z)).trans_eq Real.sqrt_one))
  -- Fixed source row: Cauchy on the square with the exact rank-two mass.
  have hrow : ∀ z, (I z) ^ 2 ≤ 2 * X * (B z * C z) := fun z =>
    rank_two_pairing_sq_le (μ := μ) T (b z) (c z) hT (hbz z) (hcz z) hTB (hbB z) (hcB z)
      (horth z)
  have habs : ∀ z, |I z| ≤ Real.sqrt (2 * X) * (Real.sqrt (B z) * Real.sqrt (C z)) :=
    fun z => by
      rw [← Real.sqrt_mul (hB0 z), ← Real.sqrt_mul hX0, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hrow z)
  -- Integration over the source.
  have hup : Integrable
      (fun z => Real.sqrt (2 * X) * (Real.sqrt (B z) * Real.sqrt (C z))) μ :=
    (hsB.integrable_mul hsC).const_mul _
  have hmono : (∫ z, |I z| ∂μ) ≤ Real.sqrt (2 * X) * S := by
    have h := integral_mono_of_nonneg (μ := μ) (f := fun z => |I z|)
      (g := fun z => Real.sqrt (2 * X) * (Real.sqrt (B z) * Real.sqrt (C z)))
      (Eventually.of_forall (fun z => abs_nonneg (I z))) hup (Eventually.of_forall habs)
    rwa [integral_const_mul] at h
  have htax : |∫ z, I z ∂μ| ≤ Real.sqrt (2 * X) * S :=
    (MeasureTheory.abs_integral_le_integral_abs (μ := μ) (f := I)).trans hmono
  have hsq : (∫ z, I z ∂μ) ^ 2 ≤ 2 * X * S ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) htax 2
    rwa [sq_abs, mul_pow, Real.sq_sqrt hX0] at h
  -- Cauchy in the source, with Fubini identifying the row masses.
  have hbl : Integrable (fun p : Ω × Ω => (b p.1 p.2) ^ 2) (μ.prod μ) :=
    (MemLp.of_bound hb.aestronglyMeasurable 1 (Eventually.of_forall (fun p => hbB p.1 p.2)) :
      MemLp (fun p : Ω × Ω => b p.1 p.2) 2 (μ.prod μ)).integrable_sq
  have hcl : Integrable (fun p : Ω × Ω => (c p.1 p.2) ^ 2) (μ.prod μ) :=
    (MemLp.of_bound hc.aestronglyMeasurable 1 (Eventually.of_forall (fun p => hcB p.1 p.2)) :
      MemLp (fun p : Ω × Ω => c p.1 p.2) 2 (μ.prod μ)).integrable_sq
  have hv : (∫ z, (Real.sqrt (B z)) ^ 2 ∂μ) = ∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ := by
    rw [integral_prod _ hbl]
    exact integral_congr_ae (Eventually.of_forall (fun z => Real.sq_sqrt (hB0 z)))
  have hV : (∫ z, (Real.sqrt (C z)) ^ 2 ∂μ) = ∫ p : Ω × Ω, (c p.1 p.2) ^ 2 ∂μ.prod μ := by
    rw [integral_prod _ hcl]
    exact integral_congr_ae (Eventually.of_forall (fun z => Real.sq_sqrt (hC0 z)))
  have hcs := integral_mul_sq_le (fun z => Real.sqrt (B z)) (fun z => Real.sqrt (C z)) hsB hsC
  rw [hv, hV] at hcs
  calc
    (∫ z, I z ∂μ) ^ 2 ≤ 2 * X * S ^ 2 := hsq
    _ ≤ 2 * X * ((∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ) *
        ∫ p : Ω × Ω, (c p.1 p.2) ^ 2 ∂μ.prod μ) := mul_le_mul_of_nonneg_left hcs hX0
    _ = _ := by ring

/-- The square-root form of the mixed source tax bound. -/
theorem mixed_source_tax_le_sqrt (T b c : Ω → Ω → ℝ)
    (hT : Measurable (Function.uncurry T)) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c))
    (hTB : ∀ x y, ‖T x y‖ ≤ 1) (hbB : ∀ z x, ‖b z x‖ ≤ 1) (hcB : ∀ z x, ‖c z x‖ ≤ 1)
    (horth : ∀ z x, b z x * c z x = 0) :
    (∫ z, ∫ p : Ω × Ω, T p.1 p.2 * (b z p.1 * c z p.2 + c z p.1 * b z p.2)
        ∂μ.prod μ ∂μ) ≤
      Real.sqrt (2 * (∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ) *
        (∫ p : Ω × Ω, (c p.1 p.2) ^ 2 ∂μ.prod μ) *
          (∫ p : Ω × Ω, (T p.1 p.2) ^ 2 ∂μ.prod μ)) :=
  (le_abs_self _).trans (Real.abs_le_sqrt
    (mixed_source_tax_sq_le T b c hT hb hc hTB hbB hcB horth))

end Erdos1017.KernelOperator

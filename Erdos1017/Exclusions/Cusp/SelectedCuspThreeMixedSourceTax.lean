module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeNeighborhoodTrace
public import Erdos1017.Exclusions.Cusp.KernelMixedSourceTax
public import Erdos1017.Exclusions.Cusp.CuspThreeDispersionScalar

/-!
# Mixed source tax at the low-slope third cusp

The two exterior source rows have disjoint supports carried by one
source-neighborhood rectangle, the copied-row inequality keeps an exact bounded
source row, and the neighborhood positive body pays its entire exterior
missing-region source row, giving the two-source tax bounds. With the remaining
global dispersion inputs, the dispersed low-slope case is impossible
(`cusp_three_dispersed_false`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
/-- One symmetrized mixed source row is bounded by two. -/
theorem mixed_source_row_norm_le (b c : Ω → Ω → ℝ)
    (hbB : ∀ z x, ‖b z x‖ ≤ 1) (hcB : ∀ z x, ‖c z x‖ ≤ 1) (z x y : Ω) :
    ‖b z x * c z y + c z x * b z y‖ ≤ 2 := by
  calc
    _ ≤ ‖b z x * c z y‖ + ‖c z x * b z y‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by
      rw [norm_mul, norm_mul]
      exact add_le_add
        ((mul_le_mul (hbB z x) (hcB z y) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
        ((mul_le_mul (hcB z x) (hbB z y) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
    _ = 2 := by norm_num

/-- The pairing of a bounded body with the integrated mixed source row may
be integrated over the source last. -/
theorem integral_mul_mixed_source_row (T b c : Ω → Ω → ℝ)
    (hT : Measurable (Function.uncurry T)) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c))
    (hTB : ∀ x y, ‖T x y‖ ≤ 1) (hbB : ∀ z x, ‖b z x‖ ≤ 1) (hcB : ∀ z x, ‖c z x‖ ≤ 1) :
    (∫ p : Ω × Ω, T p.1 p.2 * ∫ z, (b z p.1 * c z p.2 + c z p.1 * b z p.2) ∂μ
        ∂μ.prod μ) =
      ∫ z, ∫ p : Ω × Ω, T p.1 p.2 * (b z p.1 * c z p.2 + c z p.1 * b z p.2)
        ∂μ.prod μ ∂μ := by
  let f : Ω × Ω → Ω → ℝ := fun p z => T p.1 p.2 * (b z p.1 * c z p.2 + c z p.1 * b z p.2)
  have hbx : Measurable (fun q : (Ω × Ω) × Ω => b q.2 q.1.1) :=
    hb.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hby : Measurable (fun q : (Ω × Ω) × Ω => b q.2 q.1.2) :=
    hb.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hcx : Measurable (fun q : (Ω × Ω) × Ω => c q.2 q.1.1) :=
    hc.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hcy : Measurable (fun q : (Ω × Ω) × Ω => c q.2 q.1.2) :=
    hc.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hf : Integrable (Function.uncurry f) ((μ.prod μ).prod μ) :=
    Integrable.of_bound ((hT.comp measurable_fst).mul
      ((hbx.mul hcy).add (hcx.mul hby))).aestronglyMeasurable 2
      (Eventually.of_forall (fun q => by
        change ‖T q.1.1 q.1.2 * (b q.2 q.1.1 * c q.2 q.1.2 + c q.2 q.1.1 * b q.2 q.1.2)‖ ≤ 2
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul (hTB q.1.1 q.1.2)
          (mixed_source_row_norm_le b c hbB hcB q.2 q.1.1 q.1.2) (norm_nonneg _) zero_le_one))
  calc
    _ = ∫ p : Ω × Ω, ∫ z, f p z ∂μ ∂μ.prod μ := by
      congr 1
      funext p
      exact (integral_const_mul _ _).symm
    _ = _ := integral_integral_swap hf

/-- The copied-row inequality may retain an exact bounded source row. The
orthogonal cubic estimate pays the body moment and leaves that row paired
against the same positive body. -/
theorem copy_row_trace_le_source_pairing [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K J R : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hR : Measurable (Function.uncurry R))
    (hK01 : ∀ x y, K x y ∈ Set.Icc (0 : ℝ) 1)
    (hJB : ∀ x y, ‖J x y‖ ≤ 1) (hRB : ∀ x y, ‖R x y‖ ≤ 2) (hsym : ∀ x y, K x y = K y x)
    (a g : ℝ)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    (horthogonal : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1) + K p.1 p.2 * R p.1 p.2) :
    (a - Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      g * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤
      ∫ p : Ω × Ω, K p.1 p.2 * R p.1 p.2 ∂μ.prod μ := by
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK01 x y).1]
    exact (hK01 x y).2
  have hKl : MemLp (fun p : Ω × Ω => K p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hK.aestronglyMeasurable 1 (Eventually.of_forall (fun p => hKB p.1 p.2))
  have hJK := measurable_composedKernel (μ := μ) J K hJ hK
  have hpair : Integrable (fun p : Ω × Ω =>
      K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (hK.mul hJK).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hKB p.1 p.2)
          (composedKernel_bound (μ := μ) J K 1 1 (by norm_num) hJB hKB p.1 p.2)
          (norm_nonneg _) zero_le_one))
  have hpairSwap : Integrable (fun p : Ω × Ω =>
      K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1) (μ.prod μ) := by
    have hi := MeasurePreserving.integrable_comp_of_integrable
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)) hpair
    convert hi using 1
    funext p
    change K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1 =
      K p.2 p.1 * composedKernel (μ := μ) J K p.2 p.1
    rw [hsym p.2 p.1]
  have hsource : Integrable (fun p : Ω × Ω => K p.1 p.2 * R p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (hK.mul hR).aestronglyMeasurable 2
      (Eventually.of_forall (fun p => by
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul (hKB p.1 p.2) (hRB p.1 p.2)
          (norm_nonneg _) zero_le_one))
  have hiL : Integrable (fun p : Ω × Ω => a * (K p.1 p.2) ^ 2 + g * K p.1 p.2)
      (μ.prod μ) := (hKl.integrable_sq.const_mul a).add
        ((hKl.integrable (by norm_num)).const_mul g)
  have hiC : Integrable (fun p : Ω × Ω => K p.1 p.2 *
      (composedKernel (μ := μ) J K p.1 p.2 + composedKernel (μ := μ) J K p.2 p.1))
      (μ.prod μ) := by
    have hi : Integrable (fun p : Ω × Ω =>
        K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2 +
        K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1) (μ.prod μ) :=
      hpair.add hpairSwap
    simpa only [mul_add] using hi
  have hbound : (∫ p : Ω × Ω, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ∂μ.prod μ) ≤
      ∫ p : Ω × Ω, K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1) + K p.1 p.2 * R p.1 p.2 ∂μ.prod μ :=
    integral_mono_ae hiL (hiC.add hsource) hrow
  have hswap : (∫ p : Ω × Ω, K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1 ∂μ.prod μ) =
      ∫ p : Ω × Ω, K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2 ∂μ.prod μ := by
    calc
      _ = ∫ p : Ω × Ω, K p.2 p.1 * composedKernel (μ := μ) J K p.2 p.1 ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by dsimp only; rw [hsym p.1 p.2])
      _ = _ := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).integral_comp
        (MeasurableEquiv.prodComm (α := Ω) (β := Ω)).measurableEmbedding
        (fun p : Ω × Ω => K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2)
  have hcomposed : (∫ p : Ω × Ω, K p.1 p.2 *
      (composedKernel (μ := μ) J K p.1 p.2 + composedKernel (μ := μ) J K p.2 p.1) ∂μ.prod μ) =
      2 * (∫ p : Ω × Ω, J p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ) := by
    simp_rw [mul_add]
    rw [integral_add hpair hpairSwap, hswap, integral_mul_composed_swap K J hK hJ hKB hJB hsym]
    ring
  rw [integral_add (hKl.integrable_sq.const_mul a) ((hKl.integrable (by norm_num)).const_mul g),
    integral_const_mul, integral_const_mul, integral_add hiC hsource, hcomposed] at hbound
  -- The orthogonal cubic estimate pays the composed body term.
  have hsharp := orthogonal_composed_pairing_sq_le K J hK hJ 1 1 zero_le_one hKB hJB
    (Eventually.of_forall (fun p => hsym p.1 p.2)) hpositive horthogonal
  have hH : 0 ≤ ∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun p => sq_nonneg _)
  have hsqrt := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH)
  have hsharp' :
      (2 * (∫ p : Ω × Ω, J p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ)) ^ 2 ≤
      (Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ)) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)) ^ 2 := by
    simpa only [mul_pow, hsqrt] using hsharp
  have hupper := le_of_sq_le_sq hsharp' (mul_nonneg (Real.sqrt_nonneg _) hpositive.le)
  nlinarith only [hbound, hupper]

/-- The copied-row inequality with its entire mixed source row retained is
bounded by the actual two-source tax of the same positive body. -/
theorem copy_row_trace_le_mixed_source_tax [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K J b c : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (hK01 : ∀ x y, K x y ∈ Set.Icc (0 : ℝ) 1)
    (hJB : ∀ x y, ‖J x y‖ ≤ 1) (hbB : ∀ z x, ‖b z x‖ ≤ 1) (hcB : ∀ z x, ‖c z x‖ ≤ 1)
    (hsym : ∀ x y, K x y = K y x) (a g : ℝ)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    (horthogonal : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1) +
      K p.1 p.2 * ∫ z, (b z p.1 * c z p.2 + c z p.1 * b z p.2) ∂μ) :
    (a - Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      g * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤
      ∫ z, ∫ p : Ω × Ω, K p.1 p.2 * (b z p.1 * c z p.2 + c z p.1 * b z p.2)
        ∂μ.prod μ ∂μ := by
  let R : Ω → Ω → ℝ := fun x y => ∫ z, (b z x * c z y + c z x * b z y) ∂μ
  have hbx : Measurable (fun q : (Ω × Ω) × Ω => b q.2 q.1.1) :=
    hb.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hby : Measurable (fun q : (Ω × Ω) × Ω => b q.2 q.1.2) :=
    hb.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hcx : Measurable (fun q : (Ω × Ω) × Ω => c q.2 q.1.1) :=
    hc.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hcy : Measurable (fun q : (Ω × Ω) × Ω => c q.2 q.1.2) :=
    hc.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hR : Measurable (Function.uncurry R) :=
    (StronglyMeasurable.integral_prod_right' (ν := μ)
      ((hbx.mul hcy).add (hcx.mul hby)).stronglyMeasurable).measurable
  have hRB : ∀ x y, ‖R x y‖ ≤ 2 := fun x y => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := 2)
      (f := fun z => b z x * c z y + c z x * b z y)
      (Eventually.of_forall (fun z => mixed_source_row_norm_le b c hbB hcB z x y))
    rwa [probReal_univ, mul_one] at h
  have htrace := copy_row_trace_le_source_pairing K J R hK hJ hR hK01 hJB hRB hsym a g
    hpositive horthogonal hrow
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK01 x y).1]
    exact (hK01 x y).2
  rwa [integral_mul_mixed_source_row K b c hK hb hc hKB hbB hcB] at htrace

/-- With a nonnegative body margin and linear coefficient, the retained
source tax squares into the exact two-stage mixed source bound. -/
theorem copy_row_trace_sq_le_mixed_source [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K J b c : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (hK01 : ∀ x y, K x y ∈ Set.Icc (0 : ℝ) 1)
    (hJB : ∀ x y, ‖J x y‖ ≤ 1) (hbB : ∀ z x, ‖b z x‖ ≤ 1) (hcB : ∀ z x, ‖c z x‖ ≤ 1)
    (hsym : ∀ x y, K x y = K y x) (horth : ∀ z x, b z x * c z x = 0) (a g : ℝ)
    (hmargin : Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ)) ≤ a) (hg : 0 ≤ g)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    (horthogonal : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1) +
      K p.1 p.2 * ∫ z, (b z p.1 * c z p.2 + c z p.1 * b z p.2) ∂μ) :
    ((a - Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      g * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ)) ^ 2 ≤
      2 * (∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ) *
        (∫ p : Ω × Ω, (c p.1 p.2) ^ 2 ∂μ.prod μ) *
          (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) := by
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK01 x y).1]
    exact (hK01 x y).2
  have htax := copy_row_trace_le_mixed_source_tax K J b c hK hJ hb hc hK01 hJB hbB hcB hsym
    a g hpositive horthogonal hrow
  have hL : 0 ≤ ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ :=
    integral_nonneg (fun p => (hK01 p.1 p.2).1)
  have hleft : 0 ≤ (a - Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      g * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hmargin) hpositive.le) (mul_nonneg hg hL)
  exact (pow_le_pow_left₀ hleft htax 2).trans
    (mixed_source_tax_sq_le K b c hK hb hc hKB hbB hcB horth)

end Erdos1017.KernelOperator

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original missing incidence from a source region into a body. -/
def mixedSourceMissing (A : Ω → Ω → Bool) (J D : Set Ω) (z x : Ω) : ℝ :=
  if z ∈ J ∧ x ∈ D ∧ A z x = false then 1 else 0

/-- The original positive charge from a source region into a body. -/
def mixedSourceCharge (Y : Ω → Ω → ℝ) (J D : Set Ω) (z x : Ω) : ℝ :=
  if z ∈ J ∧ x ∈ D then max (Y z x) 0 else 0

theorem measurable_mixedSourceMissing (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (J D : Set Ω) (hJ : MeasurableSet J)
    (hD : MeasurableSet D) : Measurable (Function.uncurry (mixedSourceMissing A J D)) :=
  Measurable.ite ((hJ.preimage measurable_fst).inter
    ((hD.preimage measurable_snd).inter (hA (measurableSet_singleton false))))
    measurable_const measurable_const

theorem measurable_mixedSourceCharge (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (J D : Set Ω) (hJ : MeasurableSet J)
    (hD : MeasurableSet D) : Measurable (Function.uncurry (mixedSourceCharge Y J D)) :=
  Measurable.ite ((hJ.preimage measurable_fst).inter (hD.preimage measurable_snd))
    (hY.max measurable_const) measurable_const

omit [MeasurableSpace Ω] in
theorem mixedSourceMissing_mem (A : Ω → Ω → Bool) (J D : Set Ω) (z x : Ω) :
    mixedSourceMissing A J D z x ∈ Icc (0 : ℝ) 1 := by
  unfold mixedSourceMissing
  split_ifs <;> constructor <;> norm_num

omit [MeasurableSpace Ω] in
theorem mixedSourceCharge_mem (Y : Ω → Ω → ℝ) (J D : Set Ω)
    (hY : ∀ x y, Y x y ≤ 1) (z x : Ω) : mixedSourceCharge Y J D z x ∈ Icc (0 : ℝ) 1 := by
  unfold mixedSourceCharge
  split_ifs
  · exact ⟨le_max_right _ _, max_le (hY z x) zero_le_one⟩
  · exact ⟨le_rfl, zero_le_one⟩

omit [MeasurableSpace Ω] in
/-- The actual charge vanishes on every original nonedge, so the two source
rows have disjoint supports. -/
theorem mixedSourceMissing_mul_charge (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J D : Set Ω)
    (hzero : ∀ x y, A x y = false → Y x y = 0) (z x : Ω) :
    mixedSourceMissing A J D z x * mixedSourceCharge Y J D z x = 0 := by
  by_cases h : z ∈ J ∧ x ∈ D ∧ A z x = false
  · simp [mixedSourceMissing, mixedSourceCharge, h.1, h.2.1, h.2.2, hzero z x h.2.2]
  · simp [mixedSourceMissing, h]

omit [MeasurableSpace Ω] in
/-- The two source row squares are carried by disjoint parts of the
source-body rectangle. -/
theorem mixedSource_sq_add_le (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J D : Set Ω)
    (hzero : ∀ x y, A x y = false → Y x y = 0) (hY : ∀ x y, Y x y ≤ 1) (z x : Ω) :
    (mixedSourceMissing A J D z x) ^ 2 + (mixedSourceCharge Y J D z x) ^ 2 ≤
      (J ×ˢ D).indicator (fun _ => (1 : ℝ)) (z, x) := by
  by_cases h : z ∈ J ∧ x ∈ D
  · have hmem : (z, x) ∈ J ×ˢ D := h
    rw [indicator_of_mem hmem]
    cases hA : A z x
    · simp [mixedSourceMissing, mixedSourceCharge, h.1, h.2, hA, hzero z x hA]
    · have hc := mixedSourceCharge_mem Y J D hY z x
      have hsq : (mixedSourceCharge Y J D z x) ^ 2 ≤ 1 := by nlinarith only [hc.1, hc.2]
      simpa [mixedSourceMissing, h.1, h.2, hA] using hsq
  · have hmem : (z, x) ∉ J ×ˢ D := h
    rw [indicator_of_notMem hmem]
    have hJD : ¬(z ∈ J ∧ x ∈ D ∧ A z x = false) := fun h' => h ⟨h'.1, h'.2.1⟩
    simp [mixedSourceMissing, mixedSourceCharge, h, hJD]

/-- The two signed missing rows are paid by the original neighborhood body
and the retained mixed source row of the entire exterior missing region. -/
theorem missing_pair_integral_le_neighborhood_source (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I D : Set Ω)
    (hI : MeasurableSet I) (hD : MeasurableSet D) (hdisj : Disjoint I D)
    (hYB : ∀ x y, ‖Y x y‖ ≤ 3) (hY1 : ∀ x y, Y x y ≤ 1)
    (hGsym : ∀ x y, G x y = G y x)
    (hsym : ∀ x y, Y x y = Y y x) (x y : Ω) (hx : x ∈ D) (hy : y ∈ D)
    (hcommon : ∀ᵐ z ∂μ, z ∈ I → G x z = true ∧ G y z = true) :
    (∫ z in missingSection G x, Y y z ∂μ) +
      (∫ z in missingSection G y, Y x z ∂μ) ≤
      KernelOperator.composedKernel (μ := μ) (missingBody G Dᶜ) (positiveBody Y Dᶜ) x y +
      KernelOperator.composedKernel (μ := μ) (missingBody G Dᶜ) (positiveBody Y Dᶜ) y x +
      ∫ z, (mixedSourceMissing G (Iᶜ \ D) D z x * mixedSourceCharge Y (Iᶜ \ D) D z y +
        mixedSourceCharge Y (Iᶜ \ D) D z x * mixedSourceMissing G (Iᶜ \ D) D z y) ∂μ := by
  let K := positiveBody Y Dᶜ
  let J := missingBody G Dᶜ
  let b := mixedSourceMissing G (Iᶜ \ D) D
  let q := mixedSourceCharge Y (Iᶜ \ D) D
  have hK := measurable_positiveBody Y hY Dᶜ hD.compl
  have hJ := measurable_missingBody G hG Dᶜ hD.compl
  have hb := measurable_mixedSourceMissing G hG (Iᶜ \ D) D (hI.compl.diff hD) hD
  have hq := measurable_mixedSourceCharge Y hY (Iᶜ \ D) D (hI.compl.diff hD) hD
  have hbB : ∀ z u, ‖b z u‖ ≤ 1 := fun z u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mixedSourceMissing_mem G (Iᶜ \ D) D z u).1]
    exact (mixedSourceMissing_mem G (Iᶜ \ D) D z u).2
  have hqB : ∀ z u, ‖q z u‖ ≤ 1 := fun z u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mixedSourceCharge_mem Y (Iᶜ \ D) D hY1 z u).1]
    exact (mixedSourceCharge_mem Y (Iᶜ \ D) D hY1 z u).2
  have hrow (u : Ω) : Integrable (Y u) μ := Integrable.of_bound
    (hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (hYB u))
  have hprod (u v : Ω) : Integrable (fun z => J u z * K z v) μ :=
    Integrable.of_bound
      ((hJ.comp (measurable_const.prodMk measurable_id)).mul
        (hK.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable 1
      (Eventually.of_forall (fun z => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (missingBody_mem G Dᶜ u z).1,
          abs_of_nonneg (positiveBody_mem Y Dᶜ hY1 z v).1]
        exact (mul_le_mul (missingBody_mem G Dᶜ u z).2
          (positiveBody_mem Y Dᶜ hY1 z v).2
          (positiveBody_mem Y Dᶜ hY1 z v).1 zero_le_one).trans_eq (mul_one 1)))
  have hsource : Integrable (fun z => b z x * q z y + q z x * b z y) μ :=
    Integrable.of_bound
      (((hb.comp (measurable_id.prodMk measurable_const)).mul
        (hq.comp (measurable_id.prodMk measurable_const))).add
        ((hq.comp (measurable_id.prodMk measurable_const)).mul
          (hb.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable 2
      (Eventually.of_forall (fun z =>
        KernelOperator.mixed_source_row_norm_le b q hbB hqB z x y))
  have hmissingX := measurableSet_missingSection G hG x
  have hmissingY := measurableSet_missingSection G hG y
  have hprodAdd : Integrable (fun z => J x z * K z y + J y z * K z x) μ :=
    (hprod x y).add (hprod y x)
  have hbound : (∫ z, (missingSection G x).indicator (Y y) z +
      (missingSection G y).indicator (Y x) z ∂μ) ≤
      ∫ z, J x z * K z y + J y z * K z x +
        (b z x * q z y + q z x * b z y) ∂μ := by
    apply integral_mono_ae ((hrow y).indicator hmissingX |>.add ((hrow x).indicator hmissingY))
      (hprodAdd.add hsource)
    filter_upwards [hcommon] with z hz
    by_cases hzi : z ∈ I
    · have hzd : z ∉ D := fun h => Set.disjoint_left.mp hdisj hzi h
      obtain ⟨hGx, hGy⟩ := hz hzi
      simp [J, K, b, q, missingSection, missingBody, positiveBody, mixedSourceMissing,
        mixedSourceCharge, hzi, hzd, hGx, hGy]
    · by_cases hzd : z ∈ D
      · cases hGx : G x z <;> cases hGy : G y z <;>
          simp [J, K, b, q, missingSection, missingBody, positiveBody, mixedSourceMissing,
            mixedSourceCharge, hx, hy, hzi, hzd, hGx, hGy, hsym z x, hsym z y]
        exact add_le_add (le_max_left _ _) (le_max_left _ _)
      · -- An exterior missing-region source: each missing incidence pays the
        -- positive part of the opposite charge.
        cases hGx : G x z <;> cases hGy : G y z <;>
          simp [J, K, b, q, missingSection, missingBody, positiveBody, mixedSourceMissing,
            mixedSourceCharge, hx, hy, hzi, hzd, hGx, hGy, hGsym z x, hGsym z y,
            hsym z x, hsym z y]
        exact add_le_add (le_max_left _ _) (le_max_left _ _)
  rw [integral_add ((hrow y).indicator hmissingX) ((hrow x).indicator hmissingY),
    integral_indicator hmissingX, integral_indicator hmissingY,
    integral_add hprodAdd hsource, integral_add (hprod x y) (hprod y x)] at hbound
  exact hbound

end Erdos1017.IndependentAtomCopy

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original positive neighborhood body satisfies the copied-row bound
with the entire exterior missing-region source row retained exactly. -/
theorem ae_neighborhood_positive_body_source_row (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    let D := S.rootNeighborhood r
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) Dᶜ
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) Dᶜ
    let b := IndependentAtomCopy.mixedSourceMissing (PhysicalRepresentative.adjacency W m)
      (S.cuspThreeMissingRegion r) D
    let q := IndependentAtomCopy.mixedSourceCharge (PhysicalRepresentative.charge W m)
      (S.cuspThreeMissingRegion r) D
    ∀ᵐ p ∂μ.prod μ, S.originalAtomMass r * (K p.1 p.2) ^ 2 +
      (2 * (c - m * d) + m) * K p.1 p.2 ≤
      K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
        KernelOperator.composedKernel (μ := μ) J K p.2 p.1) +
      K p.1 p.2 * ∫ z, (b z p.1 * q z p.2 + q z p.1 * b z p.2) ∂μ := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let D := S.rootNeighborhood r
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  let J := IndependentAtomCopy.missingBody G Dᶜ
  let b := IndependentAtomCopy.mixedSourceMissing G (S.cuspThreeMissingRegion r) D
  let q := IndependentAtomCopy.mixedSourceCharge Y (S.cuspThreeMissingRegion r) D
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency r hW hd hgap)
  have hrows : ∀ᵐ x ∂μ, x ∈ D → ∀ᵐ z ∂μ, z ∈ I → G x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with x hx hxn
    filter_upwards [hx] with z hz hzi
    change PhysicalRepresentative.adjacency W m x z = true
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact (hz hzi).mpr hxn
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  filter_upwards [S.ae_common_neighborhood_copy_inequality r hW hd hgap,
    Measure.quasiMeasurePreserving_fst.ae hrows, Measure.quasiMeasurePreserving_snd.ae hrows]
    with p hp hx hy
  change μ.real I * (K p.1 p.2) ^ 2 + (2 * (c - m * d) + m) * K p.1 p.2 ≤
    K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
      KernelOperator.composedKernel (μ := μ) J K p.2 p.1) +
    K p.1 p.2 * ∫ z, (b z p.1 * q z p.2 + q z p.1 * b z p.2) ∂μ
  by_cases hpos : 0 < K p.1 p.2
  · have hout : p.1 ∈ D ∧ p.2 ∈ D := by
      by_contra h
      simp [K, IndependentAtomCopy.positiveBody, h] at hpos
    have hKeq : K p.1 p.2 = Y p.1 p.2 := by
      have hmax : 0 < max (Y p.1 p.2) 0 := by
        simpa [K, IndependentAtomCopy.positiveBody, hout] using hpos
      have hypos : 0 < Y p.1 p.2 := by
        simpa only [lt_max_iff, lt_self_iff_false, or_false] using hmax
      simp [K, IndependentAtomCopy.positiveBody, hout, max_eq_left hypos.le]
    have hypos : 0 < Y p.1 p.2 := by rwa [hKeq] at hpos
    have hc := hp hout.1 hout.2 hypos
    have hcommon : ∀ᵐ z ∂μ, z ∈ I → G p.1 z = true ∧ G p.2 z = true := by
      filter_upwards [hx hout.1, hy hout.2] with z hx hy hi
      exact ⟨hx hi, hy hi⟩
    have hpair : (∫ z in IndependentAtomCopy.missingSection G p.1, Y p.2 z ∂μ) +
        (∫ z in IndependentAtomCopy.missingSection G p.2, Y p.1 z ∂μ) ≤
        KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
          KernelOperator.composedKernel (μ := μ) J K p.2 p.1 +
          ∫ z, (b z p.1 * q z p.2 + q z p.1 * b z p.2) ∂μ :=
      IndependentAtomCopy.missing_pair_integral_le_neighborhood_source G
        (PhysicalRepresentative.measurable_adjacency W m) Y
        (PhysicalRepresentative.measurable_charge W m) I D (S.hfibers r.val r.property).1
        (S.measurableSet_rootNeighborhood r) (S.rootNeighborhood_disjoint r)
        (PhysicalRepresentative.charge_bound W m) hY1
        (PhysicalRepresentative.adjacency_symm W m)
        (PhysicalRepresentative.charge_symm W m) p.1 p.2 hout.1 hout.2 hcommon
    have hmass : 0 ≤ μ.real (IndependentAtomCopy.missingSection G p.1 ∩
        IndependentAtomCopy.missingSection G p.2) := measureReal_nonneg
    have hbound : μ.real I * K p.1 p.2 + (2 * (c - m * d) + m) ≤
        KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
          KernelOperator.composedKernel (μ := μ) J K p.2 p.1 +
          ∫ z, (b z p.1 * q z p.2 + q z p.1 * b z p.2) ∂μ := by
      change μ.real I * Y p.1 p.2 + _ - m * μ.real _ ≤ _ at hc
      rw [hKeq]
      dsimp only [J, K, b, q] at *
      nlinarith only [hc, hpair, mul_nonpos_of_nonpos_of_nonneg hm.le hmass]
    have h := mul_le_mul_of_nonneg_right hbound hpos.le
    nlinarith only [h]
  · have hzero : K p.1 p.2 = 0 := le_antisymm (le_of_not_gt hpos)
      (IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1 p.1 p.2).1
    rw [hzero]
    simp

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace ↥(Lp ℝ 2 μ)] in
/-- The two exterior source row squares are carried by the source-neighborhood
rectangle. Its neighborhood side is the exact complement of the atom and the
entire missing region, so the missing square is subtracted exactly. -/
theorem cusp_three_mixed_source_sq_le (S : SelectedHighLowStructure W m) (i : S.I) :
    let D := S.rootNeighborhood i
    let t := μ.real (S.cuspThreeMissingRegion i)
    let b := IndependentAtomCopy.mixedSourceMissing (PhysicalRepresentative.adjacency W m)
      (S.cuspThreeMissingRegion i) D
    let q := IndependentAtomCopy.mixedSourceCharge (PhysicalRepresentative.charge W m)
      (S.cuspThreeMissingRegion i) D
    (∫ p : Ω × Ω, (q p.1 p.2) ^ 2 ∂μ.prod μ) ≤
      t * (1 - S.originalAtomMass i - t) - ∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = i.val}
  let D := S.rootNeighborhood i
  let R := S.cuspThreeMissingRegion i
  let b := IndependentAtomCopy.mixedSourceMissing G R D
  let q := IndependentAtomCopy.mixedSourceCharge Y R D
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hD := S.measurableSet_rootNeighborhood i
  have hR := S.measurableSet_cuspThreeMissingRegion i
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hb := IndependentAtomCopy.measurable_mixedSourceMissing G
    (PhysicalRepresentative.measurable_adjacency W m) R D hR hD
  have hq := IndependentAtomCopy.measurable_mixedSourceCharge Y
    (PhysicalRepresentative.measurable_charge W m) R D hR hD
  have hbl : Integrable (fun p : Ω × Ω => (b p.1 p.2) ^ 2) (μ.prod μ) :=
    Integrable.of_bound (hb.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hmem := IndependentAtomCopy.mixedSourceMissing_mem G R D p.1 p.2
        nlinarith only [hmem.1, hmem.2]))
  have hql : Integrable (fun p : Ω × Ω => (q p.1 p.2) ^ 2) (μ.prod μ) :=
    Integrable.of_bound (hq.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hmem := IndependentAtomCopy.mixedSourceCharge_mem Y R D hY1 p.1 p.2
        nlinarith only [hmem.1, hmem.2]))
  have hrect := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hR.prod hD)
  have hbound : (∫ p : Ω × Ω, (b p.1 p.2) ^ 2 + (q p.1 p.2) ^ 2 ∂μ.prod μ) ≤
      ∫ p : Ω × Ω, (R ×ˢ D).indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ :=
    integral_mono (hbl.add hql) hrect (fun p =>
      IndependentAtomCopy.mixedSource_sq_add_le G Y R D
        (PhysicalRepresentative.charge_zero_of_nonedge W m) hY1 p.1 p.2)
  rw [integral_add hbl hql, integral_indicator (hR.prod hD), setIntegral_const,
    smul_eq_mul, mul_one, measureReal_prod_prod] at hbound
  -- The neighborhood is the complement of the atom and the missing region.
  have hDI : D ⊆ Iᶜ := fun x hx hxI => Set.disjoint_left.mp (S.rootNeighborhood_disjoint i) hxI hx
  have hsplit : μ.real R = μ.real Iᶜ - μ.real D := measureReal_sdiff hDI hD
  have hcompl : μ.real Iᶜ = 1 - μ.real I := probReal_compl_eq_one_sub hI
  have hDmass : μ.real D = 1 - S.originalAtomMass i - μ.real R := by
    change μ.real D = 1 - μ.real I - μ.real R
    linarith only [hsplit, hcompl]
  change (∫ p : Ω × Ω, (q p.1 p.2) ^ 2 ∂μ.prod μ) ≤
    μ.real R * (1 - S.originalAtomMass i - μ.real R) - ∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ
  rw [← hDmass]
  linarith only [hbound]

/-- At the low-slope third cusp, the actual original neighborhood positive
body pays its entire exterior missing-region source row. The retained
two-source tax gives the linear and the squared mixed bounds; the signed
trace and the source-neighborhood rectangle give the other scalar inputs.
All signs come from the actual peak floor and cusp contact margin. -/
theorem cusp_three_mixed_source_tax_bounds (S : SelectedHighLowStructure W m) (i : S.I)
    {d c : ℝ} (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) :
    let D := S.rootNeighborhood i
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) Dᶜ
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) Dᶜ
    let b := IndependentAtomCopy.mixedSourceMissing (PhysicalRepresentative.adjacency W m)
      (S.cuspThreeMissingRegion i) D
    let q := IndependentAtomCopy.mixedSourceCharge (PhysicalRepresentative.charge W m)
      (S.cuspThreeMissingRegion i) D
    let A := S.originalAtomMass i
    let t := μ.real (S.cuspThreeMissingRegion i)
    let gamma := 2 * (c - m * d) + m
    let H := ∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ
    let X := ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ
    let L := ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ
    let v := ∫ p : Ω × Ω, (b p.1 p.2) ^ 2 ∂μ.prod μ
    let V := ∫ p : Ω × Ω, (q p.1 p.2) ^ 2 ∂μ.prod μ
    let tax := ∫ z, ∫ p : Ω × Ω, K p.1 p.2 * (b z p.1 * q z p.2 + q z p.1 * b z p.2)
      ∂μ.prod μ ∂μ
    1 / 27 < gamma ∧ 11 / 39 < A ∧ 0 < A - Real.sqrt (2 * H) ∧
      (A - Real.sqrt (2 * H)) * X + gamma * L ≤ tax ∧
      ((A - Real.sqrt (2 * H)) * X + gamma * L) ^ 2 ≤ 2 * v * V * X ∧
      (A - Real.sqrt (2 * H)) * X + gamma * L ≤ t * L ∧
      V ≤ t * (1 - A - t) - v := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let D := S.rootNeighborhood i
  let R := S.cuspThreeMissingRegion i
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  let J := IndependentAtomCopy.missingBody G Dᶜ
  let b := IndependentAtomCopy.mixedSourceMissing G R D
  let q := IndependentAtomCopy.mixedSourceCharge Y R D
  let H := ∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  obtain ⟨_, hA, hfloor⟩ := S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
  -- The cusp contact margin and the slope below one make gamma exceed 1/27.
  obtain ⟨_, _, _, _, hcontact⟩ := hW.cusp_contact_parameters 3 (by norm_num)
    (show d = (1 - 1 / (3 : ℝ) ^ 2) / 2 by norm_num [hdk]) hgap hglobal
  have hgamma : 1 / 27 < 2 * (c - m * d) + m := by
    norm_num at hcontact
    linarith only [hcontact, hell]
  -- The original hole identity makes the body margin positive.
  have hH := S.neighborhood_missing_body_square_le i hW hd hgap
  have hH0 : 0 ≤ H := integral_nonneg (fun p => sq_nonneg _)
  have hsqrt := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH0)
  have hmargin : 0 < S.originalAtomMass i - Real.sqrt (2 * H) := by
    change H ≤ 1 - 2 * d - (S.originalAtomMass i) ^ 2 at hH
    rw [hdk] at hH
    nlinarith only [hH, hfloor, hA, hsqrt, Real.sqrt_nonneg (2 * H)]
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hD := S.measurableSet_rootNeighborhood i
  have hR := S.measurableSet_cuspThreeMissingRegion i
  have hK := IndependentAtomCopy.measurable_positiveBody Y
    (PhysicalRepresentative.measurable_charge W m) Dᶜ hD.compl
  have hJ := IndependentAtomCopy.measurable_missingBody G
    (PhysicalRepresentative.measurable_adjacency W m) Dᶜ hD.compl
  have hb := IndependentAtomCopy.measurable_mixedSourceMissing G
    (PhysicalRepresentative.measurable_adjacency W m) R D hR hD
  have hq := IndependentAtomCopy.measurable_mixedSourceCharge Y
    (PhysicalRepresentative.measurable_charge W m) R D hR hD
  have hJB : ∀ x y, ‖J x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem G Dᶜ x y).1]
    exact (IndependentAtomCopy.missingBody_mem G Dᶜ x y).2
  have hbB : ∀ z x, ‖b z x‖ ≤ 1 := fun z x => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (IndependentAtomCopy.mixedSourceMissing_mem G R D z x).1]
    exact (IndependentAtomCopy.mixedSourceMissing_mem G R D z x).2
  have hqB : ∀ z x, ‖q z x‖ ≤ 1 := fun z x => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (IndependentAtomCopy.mixedSourceCharge_mem Y R D hY1 z x).1]
    exact (IndependentAtomCopy.mixedSourceCharge_mem Y R D hY1 z x).2
  have hK01 := IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1
  have hsym := IndependentAtomCopy.positiveBody_symm Y Dᶜ (PhysicalRepresentative.charge_symm W m)
  have hzero := PhysicalRepresentative.charge_zero_of_nonedge W m
  have horth : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0 := by
    calc
      _ = ∫ _p : Ω × Ω, (0 : ℝ) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p =>
          IndependentAtomCopy.missingBody_positiveBody_mul G Y Dᶜ hzero p.1 p.2)
      _ = 0 := integral_zero _ _
  have hrow := S.ae_neighborhood_positive_body_source_row i hW hd hgap
  have htax := KernelOperator.copy_row_trace_le_mixed_source_tax K J b q hK hJ hb hq hK01 hJB
    hbB hqB hsym (S.originalAtomMass i) (2 * (c - m * d) + m) hpositive horth hrow
  have hsq := KernelOperator.copy_row_trace_sq_le_mixed_source K J b q hK hJ hb hq hK01 hJB
    hbB hqB hsym (IndependentAtomCopy.mixedSourceMissing_mul_charge G Y R D hzero)
    (S.originalAtomMass i) (2 * (c - m * d) + m) (sub_nonneg.mp hmargin.le)
    (by linarith only [hgamma]) hpositive horth hrow
  have htrace := S.neighborhood_positive_body_signed_trace i hW hd hgap hpositive
  have hcap := S.cusp_three_mixed_source_sq_le i
  refine ⟨hgamma, hA, hmargin, htax, hsq, ?_, hcap⟩
  change (S.originalAtomMass i - Real.sqrt (2 * H)) * (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
    (2 * (c - m * d) + m - μ.real R) * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤ 0 at htrace
  change (S.originalAtomMass i - Real.sqrt (2 * H)) * (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
    (2 * (c - m * d) + m) * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤
    μ.real R * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ)
  linarith only [htrace]

/-- The dispersed low-slope third-cusp case is impossible on the actual
original neighborhood body once the remaining global dispersion inputs are
supplied: the mass window, the gamma-to-missing-mass window, the original
hole cap, a positive missing rectangle and the edit lower ratio. The body
energy is positive because the edit ratio makes the body moment positive. -/
theorem cusp_three_dispersed_false (S : SelectedHighLowStructure W m) (i : S.I)
    {d c : ℝ} (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hmass : S.originalAtomMass i + μ.real (S.cuspThreeMissingRegion i) ≤ 1 / 3)
    (hgt : 2 * (c - m * d) + m < μ.real (S.cuspThreeMissingRegion i))
    (htg : μ.real (S.cuspThreeMissingRegion i) ≤ 2 * (2 * (c - m * d) + m))
    (hHcap : (∫ p : Ω × Ω, (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) ≤
      1 / 9 - (S.originalAtomMass i + μ.real (S.cuspThreeMissingRegion i)) ^ 2 -
        (S.originalAtomMass i + μ.real (S.cuspThreeMissingRegion i)) / 567)
    (hv : 0 < ∫ p : Ω × Ω, (IndependentAtomCopy.mixedSourceMissing
      (PhysicalRepresentative.adjacency W m) (S.cuspThreeMissingRegion i)
      (S.rootNeighborhood i) p.1 p.2) ^ 2 ∂μ.prod μ)
    (hL : (439 / 315) * (∫ p : Ω × Ω, (IndependentAtomCopy.mixedSourceMissing
      (PhysicalRepresentative.adjacency W m) (S.cuspThreeMissingRegion i)
      (S.rootNeighborhood i) p.1 p.2) ^ 2 ∂μ.prod μ) ≤
      ∫ p : Ω × Ω, IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        (S.rootNeighborhood i)ᶜ p.1 p.2 ∂μ.prod μ) :
    False := by
  let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
    (S.rootNeighborhood i)ᶜ
  -- The positive linear body moment forces positive body energy.
  have hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ := by
    have hY1 : ∀ x y, PhysicalRepresentative.charge W m x y ≤ 1 :=
      fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
    have hK01 := IndependentAtomCopy.positiveBody_mem (PhysicalRepresentative.charge W m)
      (S.rootNeighborhood i)ᶜ hY1
    have hK := IndependentAtomCopy.measurable_positiveBody (PhysicalRepresentative.charge W m)
      (PhysicalRepresentative.measurable_charge W m) (S.rootNeighborhood i)ᶜ
      (S.measurableSet_rootNeighborhood i).compl
    have hi : Integrable (fun p : Ω × Ω => (K p.1 p.2) ^ 2) (μ.prod μ) :=
      Integrable.of_bound (hK.pow_const 2).aestronglyMeasurable 1
        (Eventually.of_forall (fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith only [(hK01 p.1 p.2).1, (hK01 p.1 p.2).2]))
    apply lt_of_le_of_ne (integral_nonneg (fun p => sq_nonneg _))
    intro hzero
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun p : Ω × Ω => sq_nonneg (K p.1 p.2))) hi).mp hzero.symm
    have hL0 : (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) = 0 := by
      calc
        _ = ∫ _p : Ω × Ω, (0 : ℝ) ∂μ.prod μ := by
          apply integral_congr_ae
          filter_upwards [hae] with p hp
          exact sq_eq_zero_iff.mp hp
        _ = 0 := integral_zero _ _
    change (439 / 315) * _ ≤ ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ at hL
    linarith only [hL, hv, hL0]
  obtain ⟨hgamma, hA, _, _, hsq, hcopy, hcap⟩ :=
    S.cusp_three_mixed_source_tax_bounds i hdk hW hgap hglobal hell hpeak hpositive
  have hH0 : 0 ≤ ∫ p : Ω × Ω, (IndependentAtomCopy.missingBody
      (PhysicalRepresentative.adjacency W m) (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun p => sq_nonneg _)
  exact CuspThreeDispersionScalar.dispersed_contradiction hA.le
    (by linarith only [hgamma, hgt]) hmass hH0 hHcap hgamma.le hgt htg hv hpositive
    (by linarith only [hcap, hv]) hL hcopy hsq

end Erdos1017.CappedModel.SelectedHighLowStructure

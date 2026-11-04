module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassReplacementTests

/-!
# Measurable same-carrier patch of one class

This module defines `zeroClassPatchColor`, which replaces the colors of one
class by a finite label pattern on the same latent carrier, and proves the patch
is measurable, symmetric, has deterministic charge, and is fully feasible given
one positive original internal clique order.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open scoped Classical in
/-- Replace the colors of one class by the finite label pattern already
present on the same latent carrier. -/
def zeroClassPatchColor {k : ℕ} (s : Set Ω) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k)
    (z : (Ω × Ω) × CappedColor) : CappedColor :=
  if z.1.1 ∈ s ∧ z.1.2 ∈ s then
    if L z.1.1 = L z.1.2 then CappedColor.absent else CappedColor.present m hm
  else z.2

theorem measurable_zeroClassPatchColor {k : ℕ} (s : Set Ω)
    (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L) :
    Measurable (zeroClassPatchColor s m hm L) := by
  classical
  unfold zeroClassPatchColor
  have hfirst : Measurable (fun z : (Ω × Ω) × CappedColor => z.1.1) := by
    fun_prop
  have hsecond : Measurable (fun z : (Ω × Ω) × CappedColor => z.1.2) := by
    fun_prop
  exact (measurable_const.ite
    (measurableSet_eq_fun (hL.comp hfirst) (hL.comp hsecond)) measurable_const).ite
      ((hs.preimage hfirst).inter (hs.preimage hsecond)) measurable_snd

omit [MeasurableSpace Ω] in
theorem zeroClassPatchColor_symm {k : ℕ} (s : Set Ω) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k)
    (p : Ω × Ω) (c : CappedColor) :
    zeroClassPatchColor s m hm L (p.swap, c) =
      zeroClassPatchColor s m hm L (p, c) := by
  classical
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · simp [zeroClassPatchColor, hclass, eq_comm]
  · have hswap : ¬(p.2 ∈ s ∧ p.1 ∈ s) := by simpa [and_comm] using hclass
    simp [zeroClassPatchColor, hclass, hswap]

/-- An actual decorated model patched on one selected class, without
changing the latent probability space. -/
def patchZeroClass {k : ℕ} (W : Model Ω μ) (s : Set Ω)
    (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L) : Model Ω μ :=
  W.edit (zeroClassPatchColor s m hm L)
    (measurable_zeroClassPatchColor s hs m hm L hL)
    (Filter.Eventually.of_forall fun p c => zeroClassPatchColor_symm s m hm L p c)

open scoped Classical in
omit [IsProbabilityMeasure μ] in
/-- The patched kernel is deterministic within the class and literally
the original conditional color kernel on every other pair. -/
theorem patchZeroClass_kernel {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (p : Ω × Ω) :
    (patchZeroClass W s hs m hm L hL).kernel p =
      if p.1 ∈ s ∧ p.2 ∈ s then
        Measure.dirac (if L p.1 = L p.2 then CappedColor.absent
          else CappedColor.present m hm)
      else W.kernel p := by
  classical
  change W.editKernel (zeroClassPatchColor s m hm L) p = _
  rw [DecoratedKernel.editKernel_apply _ _
    (measurable_zeroClassPatchColor s hs m hm L hL)]
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · by_cases hlabel : L p.1 = L p.2
    · simp [zeroClassPatchColor, hclass, hlabel, Measure.map_const]
    · simp [zeroClassPatchColor, hclass, hlabel, Measure.map_const]
  · simp [zeroClassPatchColor, hclass]

open scoped Classical in
omit [IsProbabilityMeasure μ] in
/-- Every patched color moment has its exact internal deterministic value
and its unchanged old external value. -/
theorem patchZeroClass_moment {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (f : CappedColor → ℝ) (p : Ω × Ω) :
    (patchZeroClass W s hs m hm L hL).moment f p =
      if p.1 ∈ s ∧ p.2 ∈ s then
        f (if L p.1 = L p.2 then CappedColor.absent else CappedColor.present m hm)
      else W.moment f p := by
  rw [DecoratedKernel.moment, patchZeroClass_kernel]
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · simp [hclass]
  · simp [hclass, DecoratedKernel.moment]

open scoped Classical in
omit [IsProbabilityMeasure μ] in
theorem replacementPresence_eq_patchMoment {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (p : Ω × Ω) :
    replacementPresence W s ((p.1, L p.1), (p.2, L p.2)) =
      (patchZeroClass W s hs m hm L hL).moment CappedColor.adjacency p := by
  rw [replacementPresence, patchZeroClass_moment]
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · by_cases hlabel : L p.1 = L p.2
    · simp [hclass, hlabel]
    · simp [hclass, hlabel, CappedColor.present, CappedColor.adjacency]
  · simp [hclass]

open scoped Classical in
omit [IsProbabilityMeasure μ] in
/-- The actual patched pair-color charge is the selected deterministic
coefficient times its sampled adjacency. -/
theorem patch_charge_deterministic {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (p : Ω × Ω)
    (hcomp : (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ c ∂(patchZeroClass W s hs m hm L hL).kernel p,
      CappedColor.charge c =
        replacementChargeCoefficient W s m ((p.1, L p.1), (p.2, L p.2)) *
          CappedColor.adjacency c := by
  rw [patchZeroClass_kernel]
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · by_cases hlabel : L p.1 = L p.2
    · simp [hclass, hlabel, replacementChargeCoefficient]
    · simp [hclass, hlabel, replacementChargeCoefficient,
        CappedColor.present, CappedColor.charge, CappedColor.adjacency]
  · simpa only [hclass, ↓reduceIte, replacementChargeCoefficient] using
      charge_eq_shifted_plus_multiplier W m p hcomp hdet

/-- The conditional clique violation of the same-carrier patch has the
same scalar form for its actual old latent tuple and its measurable labels. -/
theorem ae_integral_patch_violation_eq {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (n : ℕ)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      (∫ c, violation c ∂cliqueLaw (patchZeroClass W s hs m hm L hL) x) =
        max ((∑ e : CliquePair n,
          replacementChargeCoefficient W s m
            ((x e.val.1, L (x e.val.1)),
              (x e.val.2, L (x e.val.2)))) - 1) 0 *
          ∏ e : CliquePair n,
            replacementPresence W s
              ((x e.val.1, L (x e.val.1)),
                (x e.val.2, L (x e.val.2))) := by
  let V := patchZeroClass W s hs m hm L hL
  have hp : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ e : CliquePair n,
        (1 - W.moment CappedColor.adjacency (x e.val.1, x e.val.2)) *
          shiftedMoment W m (x e.val.1, x e.val.2) = 0 ∧
        (∀ᵐ c ∂W.kernel (x e.val.1, x e.val.2),
          shiftedColor m c = shiftedMoment W m (x e.val.1, x e.val.2)) := by
    apply ae_all_iff.mpr
    intro e
    exact (DecoratedCounting.measurePreserving_pairProjection (μ := μ)
      e.val.1 e.val.2 e.property.ne).quasiMeasurePreserving.ae (hcomp.and hdet)
  filter_upwards [hp] with x hx
  change (∫ c, colorViolation c ∂Measure.pi
    (fun e : CliquePair n => V.kernel (x e.val.1, x e.val.2))) = _
  rw [integral_colorViolation_of_deterministic_charge
    (fun e : CliquePair n => V.kernel (x e.val.1, x e.val.2))
    (fun e => replacementChargeCoefficient W s m
      ((x e.val.1, L (x e.val.1)), (x e.val.2, L (x e.val.2))))
    (fun e => patch_charge_deterministic W s hs m hm L hL _ (hx e).1 (hx e).2)]
  change max ((∑ e : CliquePair n,
      replacementChargeCoefficient W s m
        ((x e.val.1, L (x e.val.1)), (x e.val.2, L (x e.val.2)))) - 1) 0 *
      ∏ e : CliquePair n,
        (patchZeroClass W s hs m hm L hL).moment CappedColor.adjacency
          (x e.val.1, x e.val.2) = _
  simp_rw [← replacementPresence_eq_patchMoment W s hs m hm L hL]

/-- The common old latent-tuple event for all label patterns proves full
feasibility of an arbitrary measurable same-carrier label patch. -/
theorem fullFeasible_patchZeroClass {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L)
    (hsupport : ∀ j ≤ k, 0 < restrictedCliquePresence W {y | F y = v} j)
    (hrep : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔
        ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ r, Feasible r (patchZeroClass W {y | F y = v}
      (hF (measurableSet_singleton v)) m hm L hL) := by
  let s : Set Ω := {y | F y = v}
  have hs : MeasurableSet s := hF (measurableSet_singleton v)
  intro r n hn _
  filter_upwards [ae_integral_patch_violation_eq W s hs m hm L hL n hcomp hdet,
    ae_replace_scalar_zero_all_labels W hW F hF v ν m hν hv hn
      hsupport hrep hzero hnonneg hcomp hdet]
    with x hformula hscalar
  have hintegral : (∫ c, violation c ∂cliqueLaw
      (patchZeroClass W s hs m hm L hL) x) = 0 :=
    hformula.trans (hscalar (fun i => L (x i)))
  have hint : Integrable (violation : (CliquePair n → CappedColor) → ℝ)
      (cliqueLaw (patchZeroClass W s hs m hm L hL) x) := by
    apply integrableOn_univ.mp
    exact (continuous_violation n).continuousOn.integrableOn_compact isCompact_univ
  exact (integral_eq_zero_iff_of_nonneg (fun c => violation_nonneg c) hint).mp hintegral

/-- One genuinely positive old internal clique order supplies all
smaller support tests for the same-carrier measurable patch. -/
theorem fullFeasible_patchZeroClass_of_positive_clique {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hpos : 0 < μ {y | F y = v})
    (hclique : 0 < restrictedCliquePresence W {y | F y = v} k)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L)
    (hrep : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔
        ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ r, Feasible r (patchZeroClass W {y | F y = v}
      (hF (measurableSet_singleton v)) m hm L hL) := by
  have hsupport : ∀ j ≤ k,
      0 < restrictedCliquePresence W {y | F y = v} j := by
    intro j hjk
    by_cases hj : j = 0
    · subst j
      rw [restrictedCliquePresence_zero]
      norm_num
    · exact restrictedCliquePresence_pos_of_le W {y | F y = v} hpos j k
        (Nat.one_le_iff_ne_zero.mpr hj) hjk hclique
  exact fullFeasible_patchZeroClass W hW F hF v ν m hν hv hm L hL hsupport
    hrep hzero hnonneg hcomp hdet

end Erdos1017.CappedModel

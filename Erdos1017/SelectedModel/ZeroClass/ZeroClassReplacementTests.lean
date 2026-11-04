module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassInternalTuran
public import Erdos1017.Models.Decorated.DecoratedPullback
public import Erdos1017.Models.Capped.CappedPairEdits
public import Erdos1017.Models.Capped.CappedShiftedSelection
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassPatternSupport
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassCoordinateTransfer

/-!
# Feasibility tests for a single-class replacement

This module defines `zeroClassReplacementColor`, replacing pairs within one
class by the edge law of independent finite part labels, and shows that every
sampled clique feasibility test survives the replacement, since label collisions
kill the new clique product and the scalar violation vanishes for every
membership pattern.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open scoped Classical in
/-- Replace only pairs of vertices from one class by the edge law of their
independent finite part labels; every other old color is retained. -/
def zeroClassReplacementColor {k : ℕ} (s : Set Ω) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (z : ((Ω × Fin k) × (Ω × Fin k)) × CappedColor) : CappedColor :=
  if z.1.1.1 ∈ s ∧ z.1.2.1 ∈ s then
    if z.1.1.2 = z.1.2.2 then CappedColor.absent else CappedColor.present m hm
  else z.2

theorem measurable_zeroClassReplacementColor {k : ℕ} (s : Set Ω) (hs : MeasurableSet s)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) :
    Measurable (zeroClassReplacementColor (k := k) s m hm) := by
  classical
  unfold zeroClassReplacementColor
  have hfirst : Measurable (fun z : ((Ω × Fin k) × (Ω × Fin k)) × CappedColor =>
      z.1.1.1) := by fun_prop
  have hsecond : Measurable (fun z : ((Ω × Fin k) × (Ω × Fin k)) × CappedColor =>
      z.1.2.1) := by fun_prop
  have hlabel1 : Measurable (fun z : ((Ω × Fin k) × (Ω × Fin k)) × CappedColor =>
      z.1.1.2) := by fun_prop
  have hlabel2 : Measurable (fun z : ((Ω × Fin k) × (Ω × Fin k)) × CappedColor =>
      z.1.2.2) := by fun_prop
  exact (measurable_const.ite (measurableSet_eq_fun hlabel1 hlabel2) measurable_const).ite
    ((hs.preimage hfirst).inter (hs.preimage hsecond)) measurable_snd

omit [MeasurableSpace Ω] in
theorem zeroClassReplacementColor_symm {k : ℕ} (s : Set Ω) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (p : (Ω × Fin k) × (Ω × Fin k)) (c : CappedColor) :
    zeroClassReplacementColor s m hm (p.swap, c) =
      zeroClassReplacementColor s m hm (p, c) := by
  classical
  by_cases hclass : p.1.1 ∈ s ∧ p.2.1 ∈ s
  · simp [zeroClassReplacementColor, hclass, eq_comm]
  · have hswap : ¬(p.2.1 ∈ s ∧ p.1.1 ∈ s) := by simpa [and_comm] using hclass
    simp [zeroClassReplacementColor, hclass, hswap]

/-- A genuine decorated model on a product latent law, with independent
finite part labels and only one selected zero class replaced. -/
def replaceZeroClass {k : ℕ} (W : Model Ω μ) (s : Set Ω) (hs : MeasurableSet s)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ] : Model (Ω × Fin k) (μ.prod ρ) := by
  let U : Model (Ω × Fin k) (μ.prod ρ) :=
    W.pullback Prod.fst measurePreserving_fst
  exact U.edit (zeroClassReplacementColor s m hm)
    (measurable_zeroClassReplacementColor s hs m hm)
    (Filter.Eventually.of_forall fun p c => zeroClassReplacementColor_symm s m hm p c)

open scoped Classical in
/-- The replacement law is deterministic inside the chosen class and is
literally the old pair-color law everywhere else. -/
theorem replaceZeroClass_kernel {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ]
    (p : (Ω × Fin k) × (Ω × Fin k)) :
    (replaceZeroClass W s hs m hm ρ).kernel p =
      if p.1.1 ∈ s ∧ p.2.1 ∈ s then
        Measure.dirac (if p.1.2 = p.2.2 then CappedColor.absent else CappedColor.present m hm)
      else W.kernel (p.1.1, p.2.1) := by
  classical
  change (W.pullback Prod.fst (measurePreserving_fst (μ := μ) (ν := ρ))).editKernel
    (zeroClassReplacementColor s m hm) p = _
  rw [DecoratedKernel.editKernel_apply _ _ (measurable_zeroClassReplacementColor s hs m hm)]
  rw [DecoratedKernel.pullback_kernel]
  by_cases hclass : p.1.1 ∈ s ∧ p.2.1 ∈ s
  · by_cases hlabel : p.1.2 = p.2.2
    · simp [zeroClassReplacementColor, hclass, hlabel, Measure.map_const]
    · simp [zeroClassReplacementColor, hclass, hlabel, Measure.map_const]
  · simp [zeroClassReplacementColor, hclass]

open scoped Classical in
/-- Every bounded color moment of the replacement has its literal
deterministic internal value and its unchanged old external value. -/
theorem replaceZeroClass_moment {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ]
    (f : CappedColor → ℝ) (p : (Ω × Fin k) × (Ω × Fin k)) :
    (replaceZeroClass W s hs m hm ρ).moment f p =
      if p.1.1 ∈ s ∧ p.2.1 ∈ s then
        f (if p.1.2 = p.2.2 then CappedColor.absent else CappedColor.present m hm)
      else W.moment f (p.1.1, p.2.1) := by
  rw [DecoratedKernel.moment, replaceZeroClass_kernel]
  by_cases hclass : p.1.1 ∈ s ∧ p.2.1 ∈ s
  · simp [hclass]
  · simp [hclass, DecoratedKernel.moment]

open scoped Classical in
def replacementPresence {k : ℕ} (W : Model Ω μ) (s : Set Ω)
    (p : (Ω × Fin k) × (Ω × Fin k)) : ℝ :=
  if p.1.1 ∈ s ∧ p.2.1 ∈ s then
    if p.1.2 = p.2.2 then 0 else 1
  else W.moment CappedColor.adjacency (p.1.1, p.2.1)

open scoped Classical in
def replacementChargeCoefficient {k : ℕ} (W : Model Ω μ) (s : Set Ω)
    (m : ℝ) (p : (Ω × Fin k) × (Ω × Fin k)) : ℝ :=
  if p.1.1 ∈ s ∧ p.2.1 ∈ s then m
  else shiftedMoment W m (p.1.1, p.2.1) + m

omit [IsProbabilityMeasure μ] in
theorem measurable_replacementPresence {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) :
    Measurable (replacementPresence (k := k) W s) := by
  classical
  have hA : Measurable (W.moment CappedColor.adjacency) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable
  have hfirst : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) => p.1.1) := by
    fun_prop
  have hsecond : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) => p.2.1) := by
    fun_prop
  have hlabel1 : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) => p.1.2) := by
    fun_prop
  have hlabel2 : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) => p.2.2) := by
    fun_prop
  have hclass : MeasurableSet {p : (Ω × Fin k) × (Ω × Fin k) |
      p.1.1 ∈ s ∧ p.2.1 ∈ s} :=
    (hs.preimage hfirst).inter (hs.preimage hsecond)
  have hlabels : MeasurableSet {p : (Ω × Fin k) × (Ω × Fin k) |
      p.1.2 = p.2.2} := measurableSet_eq_fun hlabel1 hlabel2
  have hexternal : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) =>
      W.moment CappedColor.adjacency (p.1.1, p.2.1)) := by
    change Measurable (W.moment CappedColor.adjacency ∘
      fun p : (Ω × Fin k) × (Ω × Fin k) => (p.1.1, p.2.1))
    exact hA.comp (hfirst.prodMk hsecond)
  unfold replacementPresence
  exact (measurable_const.ite hlabels measurable_const).ite hclass hexternal

omit [IsProbabilityMeasure μ] in
theorem measurable_replacementChargeCoefficient {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) :
    Measurable (replacementChargeCoefficient (k := k) W s m) := by
  classical
  have hM : Measurable (shiftedMoment W m) :=
    (W.stronglyMeasurable_moment
      (continuous_shiftedColor m).measurable.stronglyMeasurable).measurable
  have hfirst : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) => p.1.1) := by
    fun_prop
  have hsecond : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) => p.2.1) := by
    fun_prop
  have hclass : MeasurableSet {p : (Ω × Fin k) × (Ω × Fin k) |
      p.1.1 ∈ s ∧ p.2.1 ∈ s} :=
    (hs.preimage hfirst).inter (hs.preimage hsecond)
  have hexternal : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) =>
      shiftedMoment W m (p.1.1, p.2.1) + m) := by
    have hp : Measurable (fun p : (Ω × Fin k) × (Ω × Fin k) =>
        shiftedMoment W m (p.1.1, p.2.1)) := by
      change Measurable (shiftedMoment W m ∘
        fun p : (Ω × Fin k) × (Ω × Fin k) => (p.1.1, p.2.1))
      exact hM.comp (hfirst.prodMk hsecond)
    exact hp.add measurable_const
  unfold replacementChargeCoefficient
  exact measurable_const.ite hclass hexternal

omit [IsProbabilityMeasure μ] in
theorem measurable_replacementScalar_sep {n k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) :
    Measurable (fun z : (Fin n → Ω) × (Fin n → Fin k) =>
      max ((∑ e : CliquePair n,
        replacementChargeCoefficient W s m
          ((z.1 e.val.1, z.2 e.val.1), (z.1 e.val.2, z.2 e.val.2))) - 1) 0 *
        ∏ e : CliquePair n,
          replacementPresence W s
            ((z.1 e.val.1, z.2 e.val.1), (z.1 e.val.2, z.2 e.val.2))) := by
  classical
  have hpair (e : CliquePair n) :
      Measurable (fun z : (Fin n → Ω) × (Fin n → Fin k) =>
        ((z.1 e.val.1, z.2 e.val.1), (z.1 e.val.2, z.2 e.val.2))) := by
    fun_prop
  have hsum : Measurable (fun z : (Fin n → Ω) × (Fin n → Fin k) =>
      ∑ e : CliquePair n,
        replacementChargeCoefficient W s m
          ((z.1 e.val.1, z.2 e.val.1), (z.1 e.val.2, z.2 e.val.2))) := by
    apply Finset.measurable_sum
    intro e _
    change Measurable (replacementChargeCoefficient W s m ∘
      fun z : (Fin n → Ω) × (Fin n → Fin k) =>
        ((z.1 e.val.1, z.2 e.val.1), (z.1 e.val.2, z.2 e.val.2)))
    exact (measurable_replacementChargeCoefficient W s hs m).comp (hpair e)
  have hprod : Measurable (fun z : (Fin n → Ω) × (Fin n → Fin k) =>
      ∏ e : CliquePair n,
        replacementPresence W s
          ((z.1 e.val.1, z.2 e.val.1), (z.1 e.val.2, z.2 e.val.2))) := by
    apply Finset.measurable_prod
    intro e _
    change Measurable (replacementPresence W s ∘
      fun z : (Fin n → Ω) × (Fin n → Fin k) =>
        ((z.1 e.val.1, z.2 e.val.1), (z.1 e.val.2, z.2 e.val.2)))
    exact (measurable_replacementPresence W s hs).comp (hpair e)
  exact ((hsum.sub measurable_const).max measurable_const).mul hprod

open scoped Classical in
theorem replacementPresence_eq_moment {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ]
    (p : (Ω × Fin k) × (Ω × Fin k)) :
    replacementPresence W s p =
      (replaceZeroClass W s hs m hm ρ).moment CappedColor.adjacency p := by
  rw [replacementPresence, replaceZeroClass_moment]
  by_cases hclass : p.1.1 ∈ s ∧ p.2.1 ∈ s
  · by_cases hlabel : p.1.2 = p.2.2
    · simp [hclass, hlabel]
    · simp [hclass, hlabel, CappedColor.present, CappedColor.adjacency]
  · simp [hclass]

omit [IsProbabilityMeasure μ] in
/-- Deterministic shifted colors on a zero shifted pair force the old
present charge to equal the selected multiplier. -/
theorem charge_eq_multiplier_of_zero_shifted (W : Model Ω μ) (m : ℝ) (p : Ω × Ω)
    (hzero : shiftedMoment W m p = 0)
    (hdet : ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ c ∂W.kernel p,
      CappedColor.charge c = m * CappedColor.adjacency c := by
  filter_upwards [hdet] with c hc
  rw [shiftedColor, hzero] at hc
  linarith

omit [IsProbabilityMeasure μ] in
/-- Complementarity makes a positive shifted pair present; deterministic
shifted color then fixes its actual color charge. -/
theorem cross_color_of_positive_shifted (W : Model Ω μ) (m : ℝ) (p : Ω × Ω)
    (hpositive : 0 < shiftedMoment W m p)
    (hcomp : (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ c ∂W.kernel p,
      CappedColor.adjacency c = 1 ∧
        CappedColor.charge c = shiftedMoment W m p + m := by
  have hAone : W.moment CappedColor.adjacency p = 1 := by
    nlinarith
  filter_upwards [ae_adjacency_one_of_moment_one W p hAone, hdet] with c ha hc
  refine ⟨ha, ?_⟩
  rw [shiftedColor, ha] at hc
  linarith

omit [IsProbabilityMeasure μ] in
/-- Complementarity and actual shifted-color determinism make the charge
on every present sampled color equal to the shifted mean plus multiplier. -/
theorem charge_eq_shifted_plus_multiplier (W : Model Ω μ) (m : ℝ) (p : Ω × Ω)
    (hcomp : (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ c ∂W.kernel p,
      CappedColor.charge c =
        (shiftedMoment W m p + m) * CappedColor.adjacency c := by
  by_cases hz : shiftedMoment W m p = 0
  · simpa only [hz, zero_add] using charge_eq_multiplier_of_zero_shifted W m p hz hdet
  · have hAone : W.moment CappedColor.adjacency p = 1 := by
      have h := (mul_eq_zero.mp hcomp).resolve_right hz
      linarith
    filter_upwards [hdet, ae_adjacency_one_of_moment_one W p hAone] with c hc ha
    rw [shiftedColor, ha] at hc
    rw [ha]
    linarith

open scoped Classical in
theorem replacement_charge_deterministic {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ]
    (p : (Ω × Fin k) × (Ω × Fin k))
    (hcomp : (1 - W.moment CappedColor.adjacency (p.1.1, p.2.1)) *
      shiftedMoment W m (p.1.1, p.2.1) = 0)
    (hdet : ∀ᵐ c ∂W.kernel (p.1.1, p.2.1),
      shiftedColor m c = shiftedMoment W m (p.1.1, p.2.1)) :
    ∀ᵐ c ∂(replaceZeroClass W s hs m hm ρ).kernel p,
      CappedColor.charge c =
        replacementChargeCoefficient W s m p * CappedColor.adjacency c := by
  rw [replaceZeroClass_kernel]
  by_cases hclass : p.1.1 ∈ s ∧ p.2.1 ∈ s
  · by_cases hlabel : p.1.2 = p.2.2
    · simp [hclass, hlabel, replacementChargeCoefficient]
    · simp [hclass, hlabel, replacementChargeCoefficient,
        CappedColor.present, CappedColor.charge, CappedColor.adjacency]
  · simpa only [hclass, ↓reduceIte, replacementChargeCoefficient] using
      charge_eq_shifted_plus_multiplier W m (p.1.1, p.2.1) hcomp hdet

/-- The actual conditional clique violation integrates to one scalar
adjacency product times the shifted charge sum for almost every latent tuple. -/
theorem ae_integral_cliqueLaw_violation_eq (W : Model Ω μ) (m : ℝ) (n : ℕ)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      (∫ c, violation c ∂cliqueLaw W x) =
        max ((∑ e : CliquePair n,
          (shiftedMoment W m (x e.val.1, x e.val.2) + m)) - 1) 0 *
          ∏ e : CliquePair n,
            W.moment CappedColor.adjacency (x e.val.1, x e.val.2) := by
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
      (fun e : CliquePair n => W.kernel (x e.val.1, x e.val.2))) = _
  rw [integral_colorViolation_of_deterministic_charge
    (fun e : CliquePair n => W.kernel (x e.val.1, x e.val.2))
    (fun e => shiftedMoment W m (x e.val.1, x e.val.2) + m)
    (fun e => charge_eq_shifted_plus_multiplier W m _ (hx e).1 (hx e).2)]
  rfl

/-- Every full feasible sampled clique obeys the deterministic scalar
charge inequality wherever its actual adjacency product is positive. -/
theorem ae_shifted_clique_test_zero (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (m : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      max ((∑ e : CliquePair n,
        (shiftedMoment W m (x e.val.1, x e.val.2) + m)) - 1) 0 *
        ∏ e : CliquePair n,
          W.moment CappedColor.adjacency (x e.val.1, x e.val.2) = 0 := by
  filter_upwards [ae_integral_cliqueLaw_violation_eq W m n hcomp hdet,
    hW n n hn le_rfl] with x hformula htest
  have hzero : (∫ c, violation c ∂cliqueLaw W x) = 0 :=
    integral_eq_zero_of_ae htest
  exact hformula.symm.trans hzero

/-- The replacement's actual conditional violation has the same scalar
form, with deterministic internal adjacency from the independent labels. -/
theorem ae_integral_replace_violation_eq {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ] (n : ℕ)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ.prod ρ),
      (∫ c, violation c ∂cliqueLaw (replaceZeroClass W s hs m hm ρ) z) =
        max ((∑ e : CliquePair n,
          replacementChargeCoefficient W s m (z e.val.1, z e.val.2)) - 1) 0 *
          ∏ e : CliquePair n,
            replacementPresence W s (z e.val.1, z e.val.2) := by
  let V := replaceZeroClass W s hs m hm ρ
  have hfst : MeasurePreserving (fun z : Ω × Fin k => z.1) (μ.prod ρ) μ :=
    measurePreserving_fst
  have hpairs := (hfst.prod hfst).quasiMeasurePreserving.ae (hcomp.and hdet)
  have htuple : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ.prod ρ),
      ∀ e : CliquePair n,
        (1 - W.moment CappedColor.adjacency ((z e.val.1).1, (z e.val.2).1)) *
          shiftedMoment W m ((z e.val.1).1, (z e.val.2).1) = 0 ∧
        (∀ᵐ c ∂W.kernel ((z e.val.1).1, (z e.val.2).1),
          shiftedColor m c = shiftedMoment W m ((z e.val.1).1, (z e.val.2).1)) := by
    apply ae_all_iff.mpr
    intro e
    exact (DecoratedCounting.measurePreserving_pairProjection (μ := μ.prod ρ)
      e.val.1 e.val.2 e.property.ne).quasiMeasurePreserving.ae hpairs
  filter_upwards [htuple] with z hz
  change (∫ c, colorViolation c ∂Measure.pi
    (fun e : CliquePair n => V.kernel (z e.val.1, z e.val.2))) = _
  rw [integral_colorViolation_of_deterministic_charge
    (fun e : CliquePair n => V.kernel (z e.val.1, z e.val.2))
    (fun e => replacementChargeCoefficient W s m (z e.val.1, z e.val.2))
    (fun e => replacement_charge_deterministic W s hs m hm ρ _ (hz e).1 (hz e).2)]
  change max ((∑ e : CliquePair n,
      replacementChargeCoefficient W s m (z e.val.1, z e.val.2)) - 1) 0 *
      (∏ e : CliquePair n,
        (replaceZeroClass W s hs m hm ρ).moment CappedColor.adjacency
          (z e.val.1, z e.val.2)) = _
  simp_rw [← replacementPresence_eq_moment W s hs m hm ρ]

/-- A positive boundary feature fiber has the selected multiplier as the
charge of every actually sampled present color on almost every class pair. -/
theorem ae_charge_eq_multiplier_conditioned_featureFiber {H : Type*}
    [NormedAddCommGroup H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (W : Model Ω μ) (F : Ω → H) (hF : Measurable F) (v : H)
    (hpos : 0 < μ {x | F x = v}) (m R : ℝ) (hv : ‖v‖ = R)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ p ∂(ProbabilityTheory.cond μ {x | F x = v}).prod
      (ProbabilityTheory.cond μ {x | F x = v}),
      ∀ᵐ c ∂(conditionOn W {x | F x = v} hpos).kernel p,
        CappedColor.charge c = m * CappedColor.adjacency c := by
  have hz := ae_zero_conditioned_featureFiber F hF v hpos
    (fun x y => shiftedMoment W m (x, y)) R hv hzero
  have hac : ProbabilityTheory.cond μ {x | F x = v} ≪ μ :=
    cond_absolutelyContinuous
  have hd := (hac.prod hac).ae_le hdet
  filter_upwards [hz, hd] with p hp hdp
  exact charge_eq_multiplier_of_zero_shifted W m p hp hdp

/-- Across a positive boundary feature fiber and its complement, the old
sampled color is present and its charge depends on the class only through
its single feature value. -/
theorem ae_cross_color_constant_on_featureFiber {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (W : Model Ω μ) (F : Ω → H) (hF : Measurable F) (v : H)
    (m ν R : ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ p ∂(ProbabilityTheory.cond μ {x | F x = v}).prod
      (μ.restrict {x | F x ≠ v}),
      ∀ᵐ c ∂W.kernel p,
        CappedColor.adjacency c = 1 ∧
          CappedColor.charge c = ν - ⟪v, F p.2⟫ + m := by
  let s : Set Ω := {x | F x = v}
  have hs : MeasurableSet s := hF (measurableSet_singleton v)
  have hcond : ProbabilityTheory.cond μ s ≪ μ := cond_absolutelyContinuous
  have hrest : μ.restrict sᶜ ≪ μ := Measure.absolutelyContinuous_restrict
  have hbase := (hcond.prod hrest).ae_le
    (Filter.Eventually.and (Filter.Eventually.and (Filter.Eventually.and hrep hzero) hnonneg)
      (Filter.Eventually.and hcomp hdet))
  have hx := (Measure.quasiMeasurePreserving_fst
    (μ := ProbabilityTheory.cond μ s) (ν := μ.restrict sᶜ)).ae
    (ae_feature_eq_conditioned (μ := μ) F hF v)
  have hy := (Measure.quasiMeasurePreserving_snd
    (μ := ProbabilityTheory.cond μ s) (ν := μ.restrict sᶜ)).ae
    (ae_restrict_mem hs.compl)
  filter_upwards [hbase, hx, hy] with p hp hxp hyp
  obtain ⟨⟨⟨hrep', hzero'⟩, hnonneg'⟩, hcomp', hdet'⟩ := hp
  have hneq : shiftedMoment W m p ≠ 0 := by
    intro hz
    have heq := (hzero'.mp hz).2
    exact hyp (show p.2 ∈ s from heq.symm.trans hxp)
  have hpositive : 0 < shiftedMoment W m p := lt_of_le_of_ne hnonneg' (Ne.symm hneq)
  filter_upwards [cross_color_of_positive_shifted W m p hpositive hcomp' hdet']
    with c hc
  refine ⟨hc.1, ?_⟩
  rw [hrep', hxp] at hc
  exact hc.2

open scoped Classical in
/-- In one fixed membership pattern, all internal feature values are
replaced by the feature value of the selected class. -/
def patternFeature {H : Type*} {n : ℕ} (F : Ω → H) (v : H)
    (S : Finset (Fin n)) (x : Fin n → Ω) (i : Fin n) : H :=
  if i ∈ S then v else F (x i)

open scoped Classical in
/-- The scalar outside factor of a clique test on a fixed class pattern. -/
def patternOutsideScalar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (W : Model Ω μ) (F : Ω → H) (v : H) (ν m : ℝ)
    (S : Finset (Fin n)) (x : Fin n → Ω) : ℝ :=
  max ((∑ e : CliquePair n,
      (ν - ⟪patternFeature F v S x e.val.1,
        patternFeature F v S x e.val.2⟫ + m)) - 1) 0 *
    ∏ e : CliquePair n,
      if e.val.1 ∈ S ∨ e.val.2 ∈ S then 1
      else W.moment CappedColor.adjacency (x e.val.1, x e.val.2)

open scoped Classical in
/-- The internal adjacency factor of an old clique on one class pattern. -/
def patternInternalPresence {n : ℕ} (W : Model Ω μ)
    (S : Finset (Fin n)) (x : Fin n → Ω) : ℝ :=
  ∏ e : CliquePair n,
    if e.val.1 ∈ S ∧ e.val.2 ∈ S then
      W.moment CappedColor.adjacency (x e.val.1, x e.val.2)
    else 1

omit [IsProbabilityMeasure μ] in
/-- The outside scalar is unchanged by replacing any internal vertex. -/
theorem patternOutsideScalar_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (W : Model Ω μ)
    (F : Ω → H) (v : H) (ν m : ℝ) (S : Finset (Fin n))
    (x y : Fin n → Ω) (hxy : ∀ i ∉ S, x i = y i) :
    patternOutsideScalar W F v ν m S x =
      patternOutsideScalar W F v ν m S y := by
  classical
  have hF (i : Fin n) :
      patternFeature F v S x i = patternFeature F v S y i := by
    by_cases hi : i ∈ S
    · simp [patternFeature, hi]
    · simp [patternFeature, hi, hxy i hi]
  have hsum :
      (∑ e : CliquePair n,
        (ν - ⟪patternFeature F v S x e.val.1,
          patternFeature F v S x e.val.2⟫ + m)) =
      ∑ e : CliquePair n,
        (ν - ⟪patternFeature F v S y e.val.1,
          patternFeature F v S y e.val.2⟫ + m) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [hF e.val.1, hF e.val.2]
  have hprod :
      (∏ e : CliquePair n,
        if e.val.1 ∈ S ∨ e.val.2 ∈ S then 1
        else W.moment CappedColor.adjacency (x e.val.1, x e.val.2)) =
      ∏ e : CliquePair n,
        if e.val.1 ∈ S ∨ e.val.2 ∈ S then 1
        else W.moment CappedColor.adjacency (y e.val.1, y e.val.2) := by
    apply Finset.prod_congr rfl
    intro e _
    by_cases heither : e.val.1 ∈ S ∨ e.val.2 ∈ S
    · simp [heither]
    · have hi : e.val.1 ∉ S := fun h => heither (Or.inl h)
      have hj : e.val.2 ∉ S := fun h => heither (Or.inr h)
      simp [heither, hxy _ hi, hxy _ hj]
  simp only [patternOutsideScalar, hsum, hprod]

open scoped Classical in
/-- Fill the internal positions of a membership pattern by a dummy point;
the outside scalar does not depend on that point. -/
def patternFill {n : ℕ} (x₀ : Ω) (S : Finset (Fin n))
    (y : {i : Fin n // i ∉ S} → Ω) (i : Fin n) : Ω :=
  if hi : i ∈ S then x₀ else y ⟨i, hi⟩

omit [IsProbabilityMeasure μ] in
/-- The internal adjacency factor is the clique product on the ordered
internal vertices of the membership pattern. -/
theorem patternInternalPresence_eq_ordered {n : ℕ} (W : Model Ω μ)
    (S : Finset (Fin n)) (x : Fin n → Ω) :
    let e : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
    patternInternalPresence W S x =
      ∏ p : CliquePair S.card,
        W.moment CappedColor.adjacency (x (e p.val.1), x (e p.val.2)) := by
  classical
  let e : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  change patternInternalPresence W S x =
    ∏ p : CliquePair S.card,
      W.moment CappedColor.adjacency (x (e p.val.1), x (e p.val.2))
  rw [patternInternalPresence, ← Finset.prod_filter]
  symm
  refine Finset.prod_bij (fun p _ => pairEmbedding e p) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨S.orderEmbOfFin_mem rfl p.val.1, S.orderEmbOfFin_mem rfl p.val.2⟩
  · intro p _ q _ hpq
    exact (pairEmbedding e).injective hpq
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    let es : Fin S.card ≃o {i : Fin n // i ∈ S} := S.orderIsoOfFin rfl
    let i : Fin S.card := es.symm ⟨p.val.1, hp'.1⟩
    let j : Fin S.card := es.symm ⟨p.val.2, hp'.2⟩
    have hij : i < j := es.symm.strictMono p.property
    let q : CliquePair S.card := ⟨(i, j), hij⟩
    refine ⟨q, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change e i = p.val.1
      change ((S.orderIsoOfFin rfl) i : Fin n) = p.val.1
      rw [show (S.orderIsoOfFin rfl) i = ⟨p.val.1, hp'.1⟩ from
        (S.orderIsoOfFin rfl).apply_symm_apply _]
    · change e j = p.val.2
      change ((S.orderIsoOfFin rfl) j : Fin n) = p.val.2
      rw [show (S.orderIsoOfFin rfl) j = ⟨p.val.2, hp'.2⟩ from
        (S.orderIsoOfFin rfl).apply_symm_apply _]
  · intro p _
    rfl

omit [IsProbabilityMeasure μ] in
theorem measurable_patternOutsideScalar {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [OpensMeasurableSpace H] [SecondCountableTopology H]
    {n : ℕ} (W : Model Ω μ) (F : Ω → H) (hF : Measurable F)
    (v : H) (ν m : ℝ) (S : Finset (Fin n)) :
    Measurable (patternOutsideScalar W F v ν m S) := by
  classical
  have hA : Measurable (W.moment CappedColor.adjacency) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable
  have hfeature (i : Fin n) :
      Measurable (fun x : Fin n → Ω => patternFeature F v S x i) := by
    by_cases hi : i ∈ S
    · simp [patternFeature, hi]
    · simp only [patternFeature, hi, ↓reduceIte]
      change Measurable (F ∘ fun x : Fin n → Ω => x i)
      exact hF.comp (measurable_pi_apply i)
  unfold patternOutsideScalar
  have hsum : Measurable (fun x : Fin n → Ω =>
      ∑ e : CliquePair n,
        (ν - ⟪patternFeature F v S x e.val.1,
          patternFeature F v S x e.val.2⟫ + m)) := by
    apply Finset.measurable_sum
    intro e _
    have hinner : Measurable (fun x : Fin n → Ω =>
        ⟪patternFeature F v S x e.val.1,
          patternFeature F v S x e.val.2⟫) :=
      continuous_inner.measurable.comp
        ((hfeature e.val.1).prodMk (hfeature e.val.2))
    exact (measurable_const.sub hinner).add measurable_const
  have hprod : Measurable (fun x : Fin n → Ω =>
      ∏ e : CliquePair n,
        if e.val.1 ∈ S ∨ e.val.2 ∈ S then 1
        else W.moment CappedColor.adjacency (x e.val.1, x e.val.2)) := by
    apply Finset.measurable_prod
    intro e _
    by_cases heither : e.val.1 ∈ S ∨ e.val.2 ∈ S
    · simp [heither]
    · simp only [heither, ↓reduceIte]
      change Measurable (W.moment CappedColor.adjacency ∘
        fun x : Fin n → Ω => (x e.val.1, x e.val.2))
      exact hA.comp (by fun_prop)
  exact ((hsum.sub measurable_const).max measurable_const).mul hprod

omit [IsProbabilityMeasure μ] in
theorem measurable_patternFill {n : ℕ} (x₀ : Ω) (S : Finset (Fin n)) :
    Measurable (patternFill x₀ S) := by
  classical
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ S
  · simp [patternFill, hi]
  · simpa [patternFill, hi] using
      (measurable_pi_apply (⟨i, hi⟩ : {i : Fin n // i ∉ S}))

omit [IsProbabilityMeasure μ] in
/-- On a fixed membership pattern the old scalar clique test factors
into its internal adjacency product and a factor using only outside data. -/
theorem old_scalar_eq_pattern_factors {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (W : Model Ω μ)
    (F : Ω → H) (v : H) (ν m : ℝ) (S : Finset (Fin n)) (x : Fin n → Ω)
    (hclass : ∀ i ∈ S, F (x i) = v)
    (hrep : ∀ e : CliquePair n,
      shiftedMoment W m (x e.val.1, x e.val.2) =
        ν - ⟪F (x e.val.1), F (x e.val.2)⟫)
    (hcross : ∀ e : CliquePair n,
      e.val.1 ∈ S ∨ e.val.2 ∈ S →
      ¬(e.val.1 ∈ S ∧ e.val.2 ∈ S) →
      W.moment CappedColor.adjacency (x e.val.1, x e.val.2) = 1) :
    max ((∑ e : CliquePair n,
      (shiftedMoment W m (x e.val.1, x e.val.2) + m)) - 1) 0 *
      ∏ e : CliquePair n,
        W.moment CappedColor.adjacency (x e.val.1, x e.val.2) =
      patternInternalPresence W S x * patternOutsideScalar W F v ν m S x := by
  classical
  have hF (i : Fin n) : patternFeature F v S x i = F (x i) := by
    by_cases hi : i ∈ S
    · simp [patternFeature, hi, hclass i hi]
    · simp [patternFeature, hi]
  have hsum :
      (∑ e : CliquePair n,
        (shiftedMoment W m (x e.val.1, x e.val.2) + m)) =
      ∑ e : CliquePair n,
        (ν - ⟪patternFeature F v S x e.val.1,
          patternFeature F v S x e.val.2⟫ + m) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [hrep e, hF e.val.1, hF e.val.2]
  have hprod :
      (∏ e : CliquePair n,
        W.moment CappedColor.adjacency (x e.val.1, x e.val.2)) =
      patternInternalPresence W S x *
        ∏ e : CliquePair n,
          if e.val.1 ∈ S ∨ e.val.2 ∈ S then 1
          else W.moment CappedColor.adjacency (x e.val.1, x e.val.2) := by
    rw [patternInternalPresence, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    by_cases hboth : e.val.1 ∈ S ∧ e.val.2 ∈ S
    · simp [hboth]
    · by_cases heither : e.val.1 ∈ S ∨ e.val.2 ∈ S
      · simp [hboth, heither, hcross e heither hboth]
      · simp [hboth, heither]
  rw [hsum, hprod]
  unfold patternOutsideScalar
  ring

omit [IsProbabilityMeasure μ] in
/-- An injective internal label pattern has exactly the outside scalar
factor of the old clique, with all internal adjacencies set to one. -/
theorem replace_scalar_eq_pattern_outside {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n k : ℕ} (W : Model Ω μ)
    (F : Ω → H) (v : H) (ν m : ℝ) (s : Set Ω) (S : Finset (Fin n))
    (x : Fin n → Ω) (b : Fin n → Fin k)
    (hpattern : ∀ i : Fin n, i ∈ S ↔ x i ∈ s)
    (hclass : ∀ i ∈ S, F (x i) = v)
    (hvv : ν - ⟪v, v⟫ = 0)
    (hrep : ∀ e : CliquePair n,
      shiftedMoment W m (x e.val.1, x e.val.2) =
        ν - ⟪F (x e.val.1), F (x e.val.2)⟫)
    (hcross : ∀ e : CliquePair n,
      e.val.1 ∈ S ∨ e.val.2 ∈ S →
      ¬(e.val.1 ∈ S ∧ e.val.2 ∈ S) →
      W.moment CappedColor.adjacency (x e.val.1, x e.val.2) = 1)
    (hinj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → b i ≠ b j) :
    max ((∑ e : CliquePair n,
      replacementChargeCoefficient W s m ((x e.val.1, b e.val.1),
        (x e.val.2, b e.val.2))) - 1) 0 *
      ∏ e : CliquePair n,
        replacementPresence W s ((x e.val.1, b e.val.1),
          (x e.val.2, b e.val.2)) =
      patternOutsideScalar W F v ν m S x := by
  classical
  have hvv' : ν - ‖v‖ ^ 2 = 0 := by simpa [real_inner_self_eq_norm_sq] using hvv
  have hF (i : Fin n) : patternFeature F v S x i = F (x i) := by
    by_cases hi : i ∈ S
    · simp [patternFeature, hi, hclass i hi]
    · simp [patternFeature, hi]
  have hsum :
      (∑ e : CliquePair n,
        replacementChargeCoefficient W s m ((x e.val.1, b e.val.1),
          (x e.val.2, b e.val.2))) =
      ∑ e : CliquePair n,
        (ν - ⟪patternFeature F v S x e.val.1,
          patternFeature F v S x e.val.2⟫ + m) := by
    apply Finset.sum_congr rfl
    intro e _
    have hmem : (x e.val.1 ∈ s ∧ x e.val.2 ∈ s) ↔
        (e.val.1 ∈ S ∧ e.val.2 ∈ S) := by simp [← hpattern]
    by_cases hboth : e.val.1 ∈ S ∧ e.val.2 ∈ S
    · have hclassPair : x e.val.1 ∈ s ∧ x e.val.2 ∈ s := hmem.mpr hboth
      simp [replacementChargeCoefficient, hclassPair, patternFeature,
        hboth.1, hboth.2, hvv']
    · have hnot : ¬(x e.val.1 ∈ s ∧ x e.val.2 ∈ s) := by simpa [hmem] using hboth
      simp [replacementChargeCoefficient, hnot, hrep e, hF]
  have hprod :
      (∏ e : CliquePair n,
        replacementPresence W s ((x e.val.1, b e.val.1),
          (x e.val.2, b e.val.2))) =
      ∏ e : CliquePair n,
        if e.val.1 ∈ S ∨ e.val.2 ∈ S then 1
        else W.moment CappedColor.adjacency (x e.val.1, x e.val.2) := by
    apply Finset.prod_congr rfl
    intro e _
    have hmem : (x e.val.1 ∈ s ∧ x e.val.2 ∈ s) ↔
        (e.val.1 ∈ S ∧ e.val.2 ∈ S) := by simp [← hpattern]
    by_cases hboth : e.val.1 ∈ S ∧ e.val.2 ∈ S
    · have hclassPair : x e.val.1 ∈ s ∧ x e.val.2 ∈ s := hmem.mpr hboth
      have hne : b e.val.1 ≠ b e.val.2 :=
        hinj _ hboth.1 _ hboth.2 e.property.ne
      simp [replacementPresence, hclassPair, hne, hboth.1, hboth.2]
    · have hnot : ¬(x e.val.1 ∈ s ∧ x e.val.2 ∈ s) := by simpa [hmem] using hboth
      by_cases heither : e.val.1 ∈ S ∨ e.val.2 ∈ S
      · simp [replacementPresence, hnot, heither, hcross e heither hboth]
      · simp [replacementPresence, hnot, heither]
  rw [hsum, hprod]
  rfl

omit [IsProbabilityMeasure μ] in
/-- The zero-set characterization makes every cross-pattern adjacency one
and fixes all internal feature values at the selected boundary value. -/
theorem pattern_structural {H : Type*} [NormedAddCommGroup H]
    {n : ℕ} (W : Model Ω μ) (F : Ω → H) (v : H) (m R : ℝ)
    (s : Set Ω) (S : Finset (Fin n)) (x : Fin n → Ω)
    (hpattern : ∀ i : Fin n, i ∈ S ↔ x i ∈ s)
    (hs : s = {y | F y = v})
    (hzero : ∀ e : CliquePair n,
      shiftedMoment W m (x e.val.1, x e.val.2) = 0 ↔
        ‖F (x e.val.1)‖ = R ∧ F (x e.val.1) = F (x e.val.2))
    (hnonneg : ∀ e : CliquePair n,
      0 ≤ shiftedMoment W m (x e.val.1, x e.val.2))
    (hcomp : ∀ e : CliquePair n,
      (1 - W.moment CappedColor.adjacency (x e.val.1, x e.val.2)) *
        shiftedMoment W m (x e.val.1, x e.val.2) = 0) :
    (∀ i ∈ S, F (x i) = v) ∧
      ∀ e : CliquePair n,
        e.val.1 ∈ S ∨ e.val.2 ∈ S →
        ¬(e.val.1 ∈ S ∧ e.val.2 ∈ S) →
        W.moment CappedColor.adjacency (x e.val.1, x e.val.2) = 1 := by
  constructor
  · intro i hi
    simpa [hs] using (hpattern i).mp hi
  intro e heither hnotboth
  have hdiff : F (x e.val.1) ≠ F (x e.val.2) := by
    rcases heither with hi | hj
    · have hj : e.val.2 ∉ S := by
        intro hj
        exact hnotboth ⟨hi, hj⟩
      have hfirst : F (x e.val.1) = v := by
        simpa [hs] using (hpattern e.val.1).mp hi
      have hsecond : F (x e.val.2) ≠ v := by
        intro h
        exact hj ((hpattern e.val.2).mpr (by simpa [hs] using h))
      exact hfirst ▸ Ne.symm hsecond
    · have hi : e.val.1 ∉ S := by
        intro hi
        exact hnotboth ⟨hi, hj⟩
      have hfirst : F (x e.val.1) ≠ v := by
        intro h
        exact hi ((hpattern e.val.1).mpr (by simpa [hs] using h))
      have hsecond : F (x e.val.2) = v := by
        simpa [hs] using (hpattern e.val.2).mp hj
      exact hsecond ▸ hfirst
  have hMne : shiftedMoment W m (x e.val.1, x e.val.2) ≠ 0 := by
    intro hM
    exact hdiff ((hzero e).mp hM).2
  have hMpos : 0 < shiftedMoment W m (x e.val.1, x e.val.2) :=
    lt_of_le_of_ne (hnonneg e) (Ne.symm hMne)
  nlinarith [hcomp e]

/-- Actual pairwise spectral and complementarity identities hold on each
fixed membership pattern after restricting the sampled vertex law. -/
theorem ae_pattern_structural {H : Type*} [NormedAddCommGroup H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    {n : ℕ} (W : Model Ω μ) (F : Ω → H) (hF : Measurable F)
    (v : H) (m R : ℝ) (S : Finset (Fin n))
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => μ)).restrict
      (patternSet {y | F y = v} S),
      (∀ i : Fin n, i ∈ S ↔ F (x i) = v) ∧
      (∀ i ∈ S, F (x i) = v) ∧
      ∀ e : CliquePair n,
        e.val.1 ∈ S ∨ e.val.2 ∈ S →
        ¬(e.val.1 ∈ S ∧ e.val.2 ∈ S) →
        W.moment CappedColor.adjacency (x e.val.1, x e.val.2) = 1 := by
  classical
  let s : Set Ω := {y | F y = v}
  have hs : MeasurableSet s := hF (measurableSet_singleton v)
  have hpatternMeas : MeasurableSet (patternSet s S) := by
    unfold patternSet
    exact MeasurableSet.pi countable_univ (fun i _ => by
      split_ifs <;> [exact hs; exact hs.compl])
  have hpair : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ e : CliquePair n,
        (shiftedMoment W m (x e.val.1, x e.val.2) = 0 ↔
          ‖F (x e.val.1)‖ = R ∧ F (x e.val.1) = F (x e.val.2)) ∧
        0 ≤ shiftedMoment W m (x e.val.1, x e.val.2) ∧
        (1 - W.moment CappedColor.adjacency (x e.val.1, x e.val.2)) *
          shiftedMoment W m (x e.val.1, x e.val.2) = 0 := by
    apply ae_all_iff.mpr
    intro e
    exact (DecoratedCounting.measurePreserving_pairProjection (μ := μ)
      e.val.1 e.val.2 e.property.ne).quasiMeasurePreserving.ae
        (hzero.and (hnonneg.and hcomp))
  filter_upwards [ae_restrict_of_ae hpair, ae_restrict_mem hpatternMeas]
    with x hx hpat
  have hpattern : ∀ i : Fin n, i ∈ S ↔ x i ∈ s := by
    intro i
    have hi := Set.mem_pi.mp hpat i (Set.mem_univ i)
    by_cases his : i ∈ S <;> simp [his] at hi ⊢
    · exact hi
    · exact hi
  have hstruct := pattern_structural W F v m R s S x hpattern rfl
    (fun e => (hx e).1) (fun e => (hx e).2.1) (fun e => (hx e).2.2)
  exact ⟨fun i => by simpa [s] using hpattern i, hstruct.1, hstruct.2⟩

/-- Full old feasibility gives a zero product of the actual internal
adjacency factor and the outside scalar on each class membership pattern. -/
theorem ae_old_pattern_product_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    {n : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m R : ℝ)
    (S : Finset (Fin n)) (hn : 2 ≤ n)
    (hrep : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => μ)).restrict
      (patternSet {y | F y = v} S),
      patternInternalPresence W S x *
        patternOutsideScalar W F v ν m S x = 0 := by
  have hrepTuple : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ e : CliquePair n,
        shiftedMoment W m (x e.val.1, x e.val.2) =
          ν - ⟪F (x e.val.1), F (x e.val.2)⟫ := by
    apply ae_all_iff.mpr
    intro e
    exact (DecoratedCounting.measurePreserving_pairProjection (μ := μ)
      e.val.1 e.val.2 e.property.ne).quasiMeasurePreserving.ae hrep
  filter_upwards [ae_restrict_of_ae (ae_shifted_clique_test_zero W hW m n hn hcomp hdet),
    ae_restrict_of_ae hrepTuple,
    ae_pattern_structural W F hF v m R S hzero hnonneg hcomp]
    with x htest hrepX hstruct
  rw [← old_scalar_eq_pattern_factors W F v ν m S x hstruct.2.1 hrepX
    hstruct.2.2]
  exact htest

/-- A positive actual internal clique test lets the old zero test cancel
its internal factor, leaving the outside scalar zero almost everywhere. -/
theorem ae_pattern_outside_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {n : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m R : ℝ)
    (S : Finset (Fin n)) (hn : 2 ≤ n) (x₀ : Ω)
    (hpositive : 0 < restrictedCliquePresence W {y | F y = v} S.card)
    (hrep : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ y ∂Measure.pi (fun _ : {i : Fin n // i ∉ S} =>
      μ.restrict {z | F z ≠ v}),
      patternOutsideScalar W F v ν m S (patternFill x₀ S y) = 0 := by
  classical
  let s : Set Ω := {y | F y = v}
  let ξ := Measure.pi (fun _ : {i : Fin n // i ∈ S} => μ.restrict s)
  let η := Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict sᶜ)
  let e : (Fin n → Ω) ≃ᵐ
      ({i : Fin n // i ∈ S} → Ω) × ({i : Fin n // i ∉ S} → Ω) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)
  let oe : Fin S.card ≃ {i : Fin n // i ∈ S} := (S.orderIsoOfFin rfl).toEquiv
  let f : ({i : Fin n // i ∈ S} → Ω) → ℝ := fun z =>
    ∏ p : CliquePair S.card,
      W.moment CappedColor.adjacency (z (oe p.val.1), z (oe p.val.2))
  let g : ({i : Fin n // i ∉ S} → Ω) → ℝ := fun y =>
    patternOutsideScalar W F v ν m S (patternFill x₀ S y)
  have hf : Measurable f := by
    have hA : Measurable (W.moment CappedColor.adjacency) :=
      (W.stronglyMeasurable_moment
        CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable
    apply Finset.measurable_prod
    intro p _
    change Measurable (W.moment CappedColor.adjacency ∘
      fun z : ({i : Fin n // i ∈ S} → Ω) =>
        (z (oe p.val.1), z (oe p.val.2)))
    exact hA.comp (by fun_prop)
  have hg : Measurable g :=
    (measurable_patternOutsideScalar W F hF v ν m S).comp
      (measurable_patternFill x₀ S)
  have hfpos : 0 < ∫ z, f z ∂ξ := by
    change 0 < ∫ z : ({i : Fin n // i ∈ S} → Ω),
      ∏ p : CliquePair S.card,
        W.moment CappedColor.adjacency (z (oe p.val.1), z (oe p.val.2)) ∂ξ
    rw [integral_internal_product_eq_restrictedCliquePresence W s S]
    exact hpositive
  have hsplit : MeasurePreserving e.symm (ξ.prod η)
      ((Measure.pi (fun _ : Fin n => μ)).restrict (patternSet s S)) :=
    (measurePreserving_patternSplit (μ := μ) s S).symm
  have hprod := hsplit.quasiMeasurePreserving.ae
    (ae_old_pattern_product_zero W hW F hF v ν m R S hn
      hrep hzero hnonneg hcomp hdet)
  have hfactor (z : ({i : Fin n // i ∈ S} → Ω) ×
      ({i : Fin n // i ∉ S} → Ω)) :
      patternInternalPresence W S (e.symm z) *
        patternOutsideScalar W F v ν m S (e.symm z) = f z.1 * g z.2 := by
    have heval (i : Fin S.card) :
        (e.symm z) (S.orderEmbOfFin rfl i) = z.1 (oe i) := by
      have hmem : S.orderEmbOfFin rfl i ∈ S := S.orderEmbOfFin_mem rfl i
      have hindex :
          (⟨S.orderEmbOfFin rfl i, hmem⟩ : {i : Fin n // i ∈ S}) = oe i := by
        apply Subtype.ext
        exact (S.coe_orderIsoOfFin_apply rfl i).symm
      change (if h : S.orderEmbOfFin rfl i ∈ S then z.1 ⟨_, h⟩
        else z.2 ⟨_, h⟩) = z.1 (oe i)
      simp [hmem, hindex]
    have hi : patternInternalPresence W S (e.symm z) = f z.1 := by
      rw [patternInternalPresence_eq_ordered]
      apply Finset.prod_congr rfl
      intro p _
      rw [heval p.val.1, heval p.val.2]
    have ho : patternOutsideScalar W F v ν m S (e.symm z) = g z.2 := by
      apply patternOutsideScalar_congr W F v ν m S
      intro i hi
      simp [e, patternFill, hi]
    rw [hi, ho]
  have hzeroProd : ∀ᵐ z ∂ξ.prod η, f z.1 * g z.2 = 0 := by
    filter_upwards [hprod] with z hz
    rw [← hfactor z]
    exact hz
  exact ae_zero_right_of_positive_factor ξ η f g hf hg hfpos hzeroProd

omit [IsProbabilityMeasure μ] in
/-- Repeated part labels inside the replaced class make the new clique
adjacency product vanish, regardless of the old color kernels. -/
theorem replacement_product_zero_of_label_collision {n k : ℕ}
    (W : Model Ω μ) (s : Set Ω) (S : Finset (Fin n))
    (x : Fin n → Ω) (b : Fin n → Fin k)
    (hpattern : ∀ i : Fin n, i ∈ S ↔ x i ∈ s)
    (hcollision : ¬∀ i ∈ S, ∀ j ∈ S, i ≠ j → b i ≠ b j) :
    (∏ e : CliquePair n,
      replacementPresence W s ((x e.val.1, b e.val.1),
        (x e.val.2, b e.val.2))) = 0 := by
  classical
  push Not at hcollision
  obtain ⟨i, hi, j, hj, hij, hb⟩ := hcollision
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · let e : CliquePair n := ⟨(i, j), hlt⟩
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [replacementPresence, (hpattern i).mp hi, (hpattern j).mp hj, hb, e]
  · let e : CliquePair n := ⟨(j, i), hlt⟩
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [replacementPresence, (hpattern j).mp hj, (hpattern i).mp hi, hb.symm, e]

/-- For any fixed part labels and class membership pattern, the new
conditional scalar violation vanishes under the restricted old vertex law. -/
theorem ae_replace_pattern_scalar_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {n k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (S : Finset (Fin n)) (b : Fin n → Fin k) (hn : 2 ≤ n)
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
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => μ)).restrict
      (patternSet {y | F y = v} S),
      max ((∑ e : CliquePair n,
        replacementChargeCoefficient W {y | F y = v} m
          ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2))) - 1) 0 *
        ∏ e : CliquePair n,
          replacementPresence W {y | F y = v}
            ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2)) = 0 := by
  classical
  let s : Set Ω := {y | F y = v}
  have hvv : ν - ⟪v, v⟫ = 0 := by
    rw [real_inner_self_eq_norm_sq, hv, Real.sq_sqrt hν]
    ring
  have hrepTuple : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ e : CliquePair n,
        shiftedMoment W m (x e.val.1, x e.val.2) =
          ν - ⟪F (x e.val.1), F (x e.val.2)⟫ := by
    apply ae_all_iff.mpr
    intro e
    exact (DecoratedCounting.measurePreserving_pairProjection (μ := μ)
      e.val.1 e.val.2 e.property.ne).quasiMeasurePreserving.ae hrep
  have hstruct := ae_pattern_structural W F hF v m (Real.sqrt ν) S
    hzero hnonneg hcomp
  by_cases hinj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → b i ≠ b j
  · have hcard : S.card ≤ k := by
      have hinj' : Function.Injective (fun i : S => b i.val) := by
        intro i j hij
        apply Subtype.ext
        by_contra hne
        exact (hinj i.val i.property j.val j.property hne) hij
      simpa using Fintype.card_le_of_injective _ hinj'
    let x₀ : Ω := Classical.choice (nonempty_of_isProbabilityMeasure μ)
    have hη := ae_pattern_outside_zero W hW F hF v ν m (Real.sqrt ν)
      S hn x₀ (hsupport S.card hcard) hrep hzero hnonneg hcomp hdet
    let ξ := Measure.pi (fun _ : {i : Fin n // i ∈ S} => μ.restrict s)
    let η := Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict sᶜ)
    let e : (Fin n → Ω) ≃ᵐ
        ({i : Fin n // i ∈ S} → Ω) × ({i : Fin n // i ∉ S} → Ω) :=
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)
    have hηprod : ∀ᵐ z ∂ξ.prod η,
        patternOutsideScalar W F v ν m S (patternFill x₀ S z.2) = 0 :=
      (Measure.quasiMeasurePreserving_snd (μ := ξ) (ν := η)).ae hη
    have hηold := (measurePreserving_patternSplit (μ := μ) s S).quasiMeasurePreserving.ae
      hηprod
    filter_upwards [hηold, ae_restrict_of_ae hrepTuple, hstruct]
      with x hg hrepX hsX
    have houtside : patternOutsideScalar W F v ν m S x = 0 := by
      have hcongr := patternOutsideScalar_congr W F v ν m S x
        (patternFill x₀ S (e x).2) (by
          intro i hi
          simp [e, patternFill, hi])
      exact hcongr.trans hg
    rw [replace_scalar_eq_pattern_outside W F v ν m s S x b hsX.1
      hsX.2.1 hvv hrepX hsX.2.2 hinj]
    exact houtside
  · filter_upwards [ae_restrict_mem (show MeasurableSet (patternSet s S) by
      unfold patternSet
      exact MeasurableSet.pi countable_univ (fun i _ => by
        split_ifs <;> [exact hF (measurableSet_singleton v);
          exact (hF (measurableSet_singleton v)).compl]))]
      with x hx
    have hpattern : ∀ i : Fin n, i ∈ S ↔ x i ∈ s := by
      intro i
      have hi := Set.mem_pi.mp hx i (Set.mem_univ i)
      by_cases his : i ∈ S <;> simp [his] at hi ⊢
      · exact hi
      · exact hi
    have hprod := replacement_product_zero_of_label_collision W s S x b hpattern hinj
    rw [hprod, mul_zero]

/-- The finite class-membership patterns cover every latent tuple, so the
replacement scalar test vanishes for each fixed tuple of part labels. -/
theorem ae_replace_scalar_zero_fixed_labels {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {n k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (b : Fin n → Fin k) (hn : 2 ≤ n)
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
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      max ((∑ e : CliquePair n,
        replacementChargeCoefficient W {y | F y = v} m
          ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2))) - 1) 0 *
        ∏ e : CliquePair n,
          replacementPresence W {y | F y = v}
            ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2)) = 0 := by
  classical
  let s : Set Ω := {y | F y = v}
  have hcover : (⋃ S : Finset (Fin n), patternSet s S) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨Finset.univ.filter (fun i => x i ∈ s), ?_⟩
    rw [patternSet, Set.mem_pi]
    intro i _
    by_cases hi : x i ∈ s <;> simp [hi]
  have hpattern : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => μ)).restrict
      (⋃ S : Finset (Fin n), patternSet s S),
      max ((∑ e : CliquePair n,
        replacementChargeCoefficient W s m
          ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2))) - 1) 0 *
        ∏ e : CliquePair n,
          replacementPresence W s
            ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2)) = 0 := by
    rw [ae_restrict_iUnion_iff]
    intro S
    exact ae_replace_pattern_scalar_zero W hW F hF v ν m hν hv S b hn
      hsupport hrep hzero hnonneg hcomp hdet
  simpa only [hcover, Measure.restrict_univ] using hpattern

/-- One common old latent-tuple event works for every finite part-label
tuple, including deterministic measurable assignments of labels. -/
theorem ae_replace_scalar_zero_all_labels {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {n k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hn : 2 ≤ n)
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
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ b : Fin n → Fin k,
        max ((∑ e : CliquePair n,
          replacementChargeCoefficient W {y | F y = v} m
            ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2))) - 1) 0 *
          ∏ e : CliquePair n,
            replacementPresence W {y | F y = v}
              ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2)) = 0 := by
  apply ae_all_iff.mpr
  intro b
  exact ae_replace_scalar_zero_fixed_labels W hW F hF v ν m hν hv b hn
    hsupport hrep hzero hnonneg hcomp hdet

/-- The product of old latent coordinates and independent finite part labels
has zero replacement scalar clique violation at every sampled order. -/
theorem ae_replace_scalar_zero_augmented {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {n k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ]
    (hn : 2 ≤ n)
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
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ.prod ρ),
      max ((∑ e : CliquePair n,
        replacementChargeCoefficient W {y | F y = v} m
          (z e.val.1, z e.val.2)) - 1) 0 *
        ∏ e : CliquePair n,
          replacementPresence W {y | F y = v}
            (z e.val.1, z e.val.2) = 0 := by
  classical
  let s : Set Ω := {y | F y = v}
  have hs : MeasurableSet s := hF (measurableSet_singleton v)
  let P : (Fin n → Ω) → (Fin n → Fin k) → Prop := fun x b =>
    max ((∑ e : CliquePair n,
      replacementChargeCoefficient W s m
        ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2))) - 1) 0 *
      ∏ e : CliquePair n,
        replacementPresence W s
          ((x e.val.1, b e.val.1), (x e.val.2, b e.val.2)) = 0
  have hP : MeasurableSet {z : (Fin n → Ω) × (Fin n → Fin k) | P z.1 z.2} := by
    exact measurableSet_eq_fun (measurable_replacementScalar_sep W s hs m)
      measurable_const
  have hlabels : ∀ᵐ b ∂Measure.pi (fun _ : Fin n => ρ),
      ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), P x b :=
    Filter.Eventually.of_forall fun b =>
      ae_replace_scalar_zero_fixed_labels W hW F hF v ν m hν hv b hn
        hsupport hrep hzero hnonneg hcomp hdet
  have hprod : ∀ᵐ z ∂(Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => ρ)), P z.1 z.2 :=
    (Measure.ae_prod_iff_ae_ae hP).mpr ((Measure.ae_ae_comm hP).mpr hlabels)
  have hmap := (measurePreserving_arrowProdEquivProdArrow Ω (Fin k) (Fin n)
    (fun _ => μ) (fun _ => ρ)).quasiMeasurePreserving.ae hprod
  filter_upwards [hmap] with z hz
  exact hz

/-- The empty restricted clique has the actual empty-product probability
one, independently of the selected measurable class. -/
theorem restrictedCliquePresence_zero (W : Model Ω μ) (s : Set Ω) :
    restrictedCliquePresence W s 0 = 1 := by
  have hset : Set.univ.pi (fun _ : Fin 0 => s) = Set.univ := by
    ext x
    simp [Set.mem_pi]
  simp [restrictedCliquePresence, cliquePresence, cliqueLaw, hset]

/-- Replacing one positive zero class by an independently labeled finite
multipartite law preserves every actual sampled clique feasibility test. -/
theorem fullFeasible_replaceZeroClass {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ]
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
    ∀ r, Feasible r (replaceZeroClass W {y | F y = v}
      (hF (measurableSet_singleton v)) m hm ρ) := by
  let s : Set Ω := {y | F y = v}
  have hs : MeasurableSet s := hF (measurableSet_singleton v)
  intro r n hn _
  filter_upwards [ae_integral_replace_violation_eq W s hs m hm ρ n hcomp hdet,
    ae_replace_scalar_zero_augmented W hW F hF v ν m hν hv ρ hn
      hsupport hrep hzero hnonneg hcomp hdet]
    with z hformula hscalar
  have hintegral : (∫ c, violation c ∂cliqueLaw
      (replaceZeroClass W s hs m hm ρ) z) = 0 := hformula.trans hscalar
  have hint : Integrable (violation : (CliquePair n → CappedColor) → ℝ)
      (cliqueLaw (replaceZeroClass W s hs m hm ρ) z) := by
    apply integrableOn_univ.mp
    exact (continuous_violation n).continuousOn.integrableOn_compact isCompact_univ
  exact (integral_eq_zero_iff_of_nonneg (fun c => violation_nonneg c)
    hint).mp hintegral

/-- One genuinely positive old internal clique order supplies every
internal order used by the finite part labels, including the empty order. -/
theorem fullFeasible_replaceZeroClass_of_positive_clique {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [BorelSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    {k : ℕ} (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (F : Ω → H) (hF : Measurable F) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hpos : 0 < μ {y | F y = v})
    (hclique : 0 < restrictedCliquePresence W {y | F y = v} k)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ]
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
    ∀ r, Feasible r (replaceZeroClass W {y | F y = v}
      (hF (measurableSet_singleton v)) m hm ρ) := by
  have hsupport : ∀ j ≤ k,
      0 < restrictedCliquePresence W {y | F y = v} j := by
    intro j hjk
    by_cases hj : j = 0
    · subst j
      rw [restrictedCliquePresence_zero]
      norm_num
    · exact restrictedCliquePresence_pos_of_le W {y | F y = v} hpos j k
        (Nat.one_le_iff_ne_zero.mpr hj) hjk hclique
  exact fullFeasible_replaceZeroClass W hW F hF v ν m hν hv hm ρ hsupport
    hrep hzero hnonneg hcomp hdet

end Erdos1017.CappedModel

module

public import Erdos1017.Models.Kernel.KernelPositiveIndexStability
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Schur complement of the indefinite head plane

This module defines a finite positive-index bound on a subspace and the residual
after removing the indefinite head plane, shows the residual is orthogonal to
both isotropic heads with a nonnegative Schur pairing on an index-two form, and
bounds the positive index of a compact operator form.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Erdos1017.SchurHeadPlane

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A finite positive index bound on a specified original subspace. -/
def PositiveIndexOn (B : LinearMap.BilinForm ℝ V) (H : Submodule ℝ V) (n : ℕ) : Prop :=
  ∀ W : Submodule ℝ V, W ≤ H → ∀ (_ : FiniteDimensional ℝ W),
    (∀ x ∈ W, x ≠ 0 → 0 < B x x) → Module.finrank ℝ W ≤ n

/-- Adjoining a positive direction orthogonal for the original form pays
one actual positive dimension. -/
theorem positive_orthogonal_dimension (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (H : Submodule ℝ V) (n : ℕ)
    (hindex : PositiveIndexOn B H n) (a : V) (ha : a ∈ H) (hqa : 0 < B a a)
    (W : Submodule ℝ V) [FiniteDimensional ℝ W] (hW : W ≤ H)
    (horth : ∀ x ∈ W, B a x = 0) (hpositive : ∀ x ∈ W, x ≠ 0 → 0 < B x x) :
    Module.finrank ℝ W + 1 ≤ n := by
  have ha0 : a ≠ 0 := by intro h; simp only [h, map_zero] at hqa; linarith
  let A : Submodule ℝ V := Submodule.span ℝ {a}
  have hA : A ≤ H := by
    apply Submodule.span_le.mpr
    intro x hx
    have he : x = a := Set.mem_singleton_iff.mp hx
    exact he ▸ ha
  have hdisj : Disjoint W A := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx.2
    have hxW := hx.1
    have he := horth (t • a) hxW
    simp only [map_smul, smul_eq_mul] at he
    have ht : t = 0 := (mul_eq_zero.mp he).resolve_right hqa.ne'
    simp only [ht, zero_smul]
  have hpos : ∀ x ∈ W ⊔ A, x ≠ 0 → 0 < B x x := by
    intro x hx hx0
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have haw := horth w hw
    have hwa : B w a = 0 := (hsym w a).trans haw
    have he : B (w + t • a) (w + t • a) = B w w + t ^ 2 * B a a := by
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, haw, hwa, mul_zero, zero_add, add_zero]
      ring
    rw [he]
    by_cases hw0 : w = 0
    · have ht : t ≠ 0 := by intro ht; simp only [hw0, ht, zero_smul, add_zero] at hx0; exact hx0 rfl
      simpa only [hw0, map_zero, LinearMap.zero_apply, zero_add] using
        mul_pos (sq_pos_of_ne_zero ht) hqa
    · exact add_pos_of_pos_of_nonneg (hpositive w hw hw0) (mul_nonneg (sq_nonneg t) hqa.le)
  have hdim := hindex (W ⊔ A) (sup_le hW hA) inferInstance hpos
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W A
  rw [hdisj.eq_bot, finrank_bot, add_zero] at hsum
  have hdimA : Module.finrank ℝ A = 1 := finrank_span_singleton ha0
  omega

/-- On a positive-index-one form, the orthogonal complement of every
positive vector is nonpositive. -/
theorem nonpositive_on_positive_orthogonal (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (H : Submodule ℝ V)
    (hindex : PositiveIndexOn B H 1) (w : V) (hw : w ∈ H) (hqw : 0 < B w w)
    (x : V) (hx : x ∈ H) (horth : B w x = 0) : B x x ≤ 0 := by
  by_contra hneg
  have hqx : 0 < B x x := lt_of_not_ge hneg
  have hx0 : x ≠ 0 := by intro h; simp only [h, map_zero] at hqx; linarith
  let X : Submodule ℝ V := Submodule.span ℝ {x}
  have hX : X ≤ H := by
    apply Submodule.span_le.mpr
    intro y hy
    have he : y = x := Set.mem_singleton_iff.mp hy
    exact he ▸ hx
  have horthX : ∀ y ∈ X, B w y = 0 := by
    intro y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [map_smul, smul_eq_mul, horth, mul_zero]
  have hpositive : ∀ y ∈ X, y ≠ 0 → 0 < B y y := by
    intro y hy hy0
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have ht : t ≠ 0 := by intro ht; exact hy0 (by rw [ht, zero_smul])
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_two] using
      mul_pos (sq_pos_of_ne_zero ht) hqx
  have hdim := positive_orthogonal_dimension B hsym H 1 hindex w hw hqw X hX horthX hpositive
  have hxDim : Module.finrank ℝ X = 1 := finrank_span_singleton hx0
  omega

/-- A positive reference and positive reference pairings orient all
nonnegative vectors in one cone of an actual index-one form. -/
theorem pairing_nonnegative_of_positive_reference (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (H : Submodule ℝ V)
    (hindex : PositiveIndexOn B H 1) (w x y : V)
    (hw : w ∈ H) (hx : x ∈ H) (hy : y ∈ H)
    (hqw : 0 < B w w) (hqx : 0 ≤ B x x) (hqy : 0 ≤ B y y)
    (hwx : 0 < B w x) (hwy : 0 < B w y) : 0 ≤ B x y := by
  let t := B w x / B w y
  have ht : 0 < t := div_pos hwx hwy
  have hcancel : t * B w y = B w x := div_mul_cancel₀ _ hwy.ne'
  have horth : B w (x - t • y) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hcancel, sub_self]
  have hn := nonpositive_on_positive_orthogonal B hsym H hindex w hw hqw
    (x - t • y) (H.sub_mem hx (H.smul_mem t hy)) horth
  have hyx := hsym y x
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hyx] at hn
  have hty : 0 ≤ t ^ 2 * B y y := mul_nonneg (sq_nonneg t) hqy
  nlinarith

/-- A nonnegative reference can be null. A genuine positive perturbation
makes its strict positive pairings sufficient for the same cone sign. -/
theorem pairing_nonnegative_of_common_reference (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (H : Submodule ℝ V)
    (hindex : PositiveIndexOn B H 1) (z x y : V)
    (hz : z ∈ H) (hx : x ∈ H) (hy : y ∈ H)
    (hqz : 0 ≤ B z z) (hqx : 0 ≤ B x x) (hqy : 0 ≤ B y y)
    (hzx : 0 < B z x) (hzy : 0 < B z y) : 0 ≤ B x y := by
  by_cases hxy : 0 ≤ B x y
  · exact hxy
  have hn : B x y < 0 := lt_of_not_ge hxy
  let ε := B z y / (-2 * B x y)
  have hε : 0 < ε := div_pos hzy (by linarith)
  have hεxy : ε * B x y = -(B z y) / 2 := by
    dsimp only [ε]
    field_simp [ne_of_lt hn]
  let w := z + ε • x
  have hw : w ∈ H := H.add_mem hz (H.smul_mem ε hx)
  have hwx : 0 < B w x := by
    have he : B w x = B z x + ε * B x x := by simp only [w, map_add, LinearMap.add_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [he]
    exact add_pos_of_pos_of_nonneg hzx (mul_nonneg hε.le hqx)
  have hwy : 0 < B w y := by
    have he : B w y = B z y + ε * B x y := by simp only [w, map_add, LinearMap.add_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [he, hεxy]
    linarith
  have hqw : 0 < B w w := by
    have hxz := hsym x z
    have he : B w w = B z z + 2 * ε * B z x + ε ^ 2 * B x x := by
      simp only [w, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hxz]
      ring
    rw [he]
    have h1 := mul_pos hε hzx
    have h2 := mul_nonneg (sq_nonneg ε) hqx
    nlinarith
  exact pairing_nonnegative_of_positive_reference B hsym H hindex w x y hw hx hy hqw hqx hqy hwx hwy

/-- The original bilinear orthogonal complement of both isotropic heads. -/
def headComplement (B : LinearMap.BilinForm ℝ V) (a b : V) : Submodule ℝ V :=
  (B a).ker ⊓ (B b).ker

/-- Removing the actual indefinite two-head plane leaves positive index at
most one. No restricted spectral operator or cone certificate is supplied. -/
theorem headComplement_index_le_one (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (hindex : PositiveIndexOn B ⊤ 2)
    (a b : V) (haa : B a a = 0) (hbb : B b b = 0) (hab : 0 < B a b) :
    PositiveIndexOn B (headComplement B a b) 1 := by
  intro W hW hfinite hpositive
  let := hfinite
  have hsum : 0 < B (a + b) (a + b) := by
    simp only [map_add, LinearMap.add_apply, haa, hbb, hsym b a]
    linarith
  have horth : ∀ x ∈ W, B (a + b) x = 0 := by
    intro x hx
    have hm := hW hx
    change B a x = 0 ∧ B b x = 0 at hm
    simp only [map_add, LinearMap.add_apply, hm.1, hm.2, add_zero]
  have hdim := positive_orthogonal_dimension B hsym ⊤ 2 hindex (a + b)
    (Submodule.mem_top) hsum W le_top horth hpositive
  omega

/-- The actual algebraic residual after removing the indefinite head plane. -/
def headResidual (B : LinearMap.BilinForm ℝ V) (a b x : V) : V :=
  x - (B b x / B a b) • a - (B a x / B a b) • b

/-- The residual of the zero vector is zero, including null patterns. -/
theorem headResidual_zero (B : LinearMap.BilinForm ℝ V) (a b : V) :
    headResidual B a b 0 = 0 := by simp only [headResidual, map_zero, zero_div, zero_smul, sub_zero]

/-- The actual residual preserves sums of the original source means. -/
theorem headResidual_add (B : LinearMap.BilinForm ℝ V) (a b x y : V) :
    headResidual B a b (x + y) = headResidual B a b x + headResidual B a b y := by
  simp only [headResidual, map_add, add_div, add_smul]
  abel

/-- Every residual is orthogonal to both original isotropic heads. -/
theorem headResidual_mem (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (a b x : V)
    (haa : B a a = 0) (hbb : B b b = 0) (hab : B a b ≠ 0) :
    headResidual B a b x ∈ headComplement B a b := by
  change B a (headResidual B a b x) = 0 ∧ B b (headResidual B a b x) = 0
  constructor
  · simp only [headResidual, map_sub, map_smul, smul_eq_mul, haa, mul_zero, sub_zero]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hab).symm
  · simp only [headResidual, map_sub, map_smul, smul_eq_mul, hbb, mul_zero,
      hsym b a, div_mul_cancel₀ _ hab, sub_self]

/-- The exact Schur pairing retains the original cross-head coefficient. -/
theorem pairing_headResidual (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (a b x y : V)
    (haa : B a a = 0) (hbb : B b b = 0) (hab : B a b ≠ 0) :
    B (headResidual B a b x) (headResidual B a b y) =
      B x y - (B a x * B b y + B b x * B a y) / B a b := by
  simp only [headResidual, map_sub, LinearMap.sub_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, haa, hbb, hsym b a, hsym x a, hsym x b]
  field_simp [hab]
  ring

/-- Null shared-source means are allowed as the common reference in the
actual Schur complement of an index-two original form. -/
theorem residual_pairing_nonnegative_of_common_reference (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (hindex : PositiveIndexOn B ⊤ 2)
    (a b z x y : V) (haa : B a a = 0) (hbb : B b b = 0) (hab : 0 < B a b)
    (hqz : 0 ≤ B (headResidual B a b z) (headResidual B a b z))
    (hqx : 0 ≤ B (headResidual B a b x) (headResidual B a b x))
    (hqy : 0 ≤ B (headResidual B a b y) (headResidual B a b y))
    (hzx : 0 < B (headResidual B a b z) (headResidual B a b x))
    (hzy : 0 < B (headResidual B a b z) (headResidual B a b y)) :
    0 ≤ B (headResidual B a b x) (headResidual B a b y) :=
  pairing_nonnegative_of_common_reference B hsym (headComplement B a b)
    (headComplement_index_le_one B hsym hindex a b haa hbb hab)
    _ _ _ (headResidual_mem B hsym a b z haa hbb hab.ne')
    (headResidual_mem B hsym a b x haa hbb hab.ne')
    (headResidual_mem B hsym a b y haa hbb hab.ne') hqz hqx hqy hzx hzy

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual symmetric operator pairing as a bilinear form. -/
def operatorForm (T : E →L[ℝ] E) : LinearMap.BilinForm ℝ E := (innerₗ E).comp T.toLinearMap

/-- The actual compact spectral positive index bounds all finite positive
Gram subspaces of the original operator form. -/
theorem operator_positiveIndexOn (T : E →L[ℝ] E) (hc : IsCompactOperator T)
    (hsym : T.toLinearMap.IsSymmetric) [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace T)]
    (n : ℕ) (hi : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace T) ≤ n) :
    PositiveIndexOn (operatorForm T) ⊤ n := by
  intro W _ hfinite hpositive
  let := hfinite
  exact (KernelOperator.positive_subspace_finrank_le_index T hc hsym W hpositive).trans hi

end Operator

end Erdos1017.SchurHeadPlane

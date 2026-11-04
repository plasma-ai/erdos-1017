module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Convexity of the joint range of two quadratic forms

The joint range of two real quadratic forms is convex (Dines's theorem), with no
finite-dimensional or closed-range assumption; the algebraic core is closure of
the joint range under addition, obtained from a rotation parameter making one
quadratic image parallel to the sum of two.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Variation

/-- A real rotation parameter making one quadratic image parallel to the
sum of two images. The discriminant is always nonnegative. -/
theorem exists_quadratic_rotation (d e : ℝ) :
    ∃ t : ℝ, d * (1 - t ^ 2) + e * t = 0 := by
  by_cases hd : d = 0
  · exact ⟨0, by simp [hd]⟩
  let r := Real.sqrt (e ^ 2 + 4 * d ^ 2)
  have hr : r ^ 2 = e ^ 2 + 4 * d ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨(e + r) / (2 * d), ?_⟩
  field_simp
  nlinarith

private theorem positive_parallel_component_fst
    (a b s : ℝ × ℝ) (k : ℝ) (hk : 0 < k) (hs : s.1 ≠ 0)
    (hadd : a + b = k • s) (hdet : a.1 * s.2 = a.2 * s.1) :
    ∃ r : ℝ, 0 < r ∧ (a = r • s ∨ b = r • s) := by
  let r := a.1 / s.1
  have ha : a = r • s := by
    apply Prod.ext
    · change a.1 = a.1 / s.1 * s.1
      rw [div_mul_cancel₀ _ hs]
    · change a.2 = a.1 / s.1 * s.2
      field_simp
      nlinarith [hdet]
  have hb : b = (k - r) • s := by
    rw [ha] at hadd
    apply Prod.ext
    · have h := congrArg Prod.fst hadd
      change r * s.1 + b.1 = k * s.1 at h
      change b.1 = (k - r) * s.1
      linarith
    · have h := congrArg Prod.snd hadd
      change r * s.2 + b.2 = k * s.2 at h
      change b.2 = (k - r) * s.2
      linarith
  by_cases hr : 0 < r
  · exact ⟨r, hr, Or.inl ha⟩
  · exact ⟨k - r, by linarith, Or.inr hb⟩

/-- Two parallel vectors adding to a positive multiple of a nonzero vector
have a component which is itself a positive multiple. -/
theorem positive_parallel_component
    (a b s : ℝ × ℝ) (k : ℝ) (hk : 0 < k) (hs : s ≠ 0)
    (hadd : a + b = k • s) (hdet : a.1 * s.2 = a.2 * s.1) :
    ∃ r : ℝ, 0 < r ∧ (a = r • s ∨ b = r • s) := by
  by_cases hfirst : s.1 ≠ 0
  · exact positive_parallel_component_fst a b s k hk hfirst hadd hdet
  have hzero : s.1 = 0 := not_ne_iff.mp hfirst
  have hsecond : s.2 ≠ 0 := by
    intro h
    apply hs
    exact Prod.ext hzero h
  have hadd' : a.swap + b.swap = k • s.swap := by
    exact congrArg Prod.swap hadd
  have hdet' : a.swap.1 * s.swap.2 = a.swap.2 * s.swap.1 := hdet.symm
  obtain ⟨r, hr, ha | hb⟩ := positive_parallel_component_fst
    a.swap b.swap s.swap k hk hsecond hadd' hdet'
  · exact ⟨r, hr, Or.inl (congrArg Prod.swap ha)⟩
  · exact ⟨r, hr, Or.inr (congrArg Prod.swap hb)⟩

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The joint diagonal image of two bilinear forms. Symmetry is unnecessary
because only their quadratic diagonal evaluations are used. -/
def jointQuadratic (A B : LinearMap.BilinForm ℝ E) (x : E) : ℝ × ℝ :=
  (A x x, B x x)

theorem jointQuadratic_smul (A B : LinearMap.BilinForm ℝ E) (c : ℝ) (x : E) :
    jointQuadratic A B (c • x) = c ^ 2 • jointQuadratic A B x := by
  apply Prod.ext <;> simp only [jointQuadratic, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Prod.smul_fst, Prod.smul_snd] <;> ring

/-- The joint range of two real quadratic forms is closed under addition.
This is the algebraic core of Dines's convexity theorem. -/
theorem jointQuadratic_add_mem_range (A B : LinearMap.BilinForm ℝ E) (u v : E) :
    jointQuadratic A B u + jointQuadratic A B v ∈ Set.range (jointQuadratic A B) := by
  let s := jointQuadratic A B u + jointQuadratic A B v
  by_cases hs : s = 0
  · refine ⟨0, ?_⟩
    change jointQuadratic A B 0 = s
    rw [hs]
    simp [jointQuadratic]
  let d := A u u * B v v - B u u * A v v
  let e := (A u v + A v u) * (B u u + B v v) - (B u v + B v u) * (A u u + A v v)
  obtain ⟨t, ht⟩ := exists_quadratic_rotation d e
  let w := u + t • v
  let z := t • u - v
  have hadd : jointQuadratic A B w + jointQuadratic A B z = (1 + t ^ 2) • s := by
    apply Prod.ext <;>
      simp only [jointQuadratic, w, z, s, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, map_add, map_sub, map_smul,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] <;> ring
  have hdet : (jointQuadratic A B w).1 * s.2 = (jointQuadratic A B w).2 * s.1 := by
    have heq : (jointQuadratic A B w).1 * s.2 - (jointQuadratic A B w).2 * s.1 =
        d * (1 - t ^ 2) + e * t := by
      simp only [jointQuadratic, w, s, d, e, Prod.fst_add, Prod.snd_add,
        map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    exact sub_eq_zero.mp (heq.trans ht)
  obtain ⟨r, hr, hw | hz⟩ := positive_parallel_component
    (jointQuadratic A B w) (jointQuadratic A B z) s (1 + t ^ 2) (by positivity) hs hadd hdet
  · refine ⟨Real.sqrt r⁻¹ • w, ?_⟩
    rw [jointQuadratic_smul, Real.sq_sqrt (inv_nonneg.mpr hr.le), hw, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  · refine ⟨Real.sqrt r⁻¹ • z, ?_⟩
    rw [jointQuadratic_smul, Real.sq_sqrt (inv_nonneg.mpr hr.le), hz, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]

theorem jointQuadratic_nonneg_smul_mem_range (A B : LinearMap.BilinForm ℝ E)
    (c : ℝ) (hc : 0 ≤ c) {x : ℝ × ℝ} (hx : x ∈ Set.range (jointQuadratic A B)) :
    c • x ∈ Set.range (jointQuadratic A B) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨Real.sqrt c • u, ?_⟩
  rw [jointQuadratic_smul, Real.sq_sqrt hc]

/-- Dines's theorem: the joint range of two real quadratic forms is convex,
without a finite-dimensional or closed-range assumption. -/
theorem jointQuadratic_range_convex (A B : LinearMap.BilinForm ℝ E) :
    Convex ℝ (Set.range (jointQuadratic A B)) := by
  intro x hx y hy a b ha hb _
  obtain ⟨u, hu⟩ := jointQuadratic_nonneg_smul_mem_range A B a ha hx
  obtain ⟨v, hv⟩ := jointQuadratic_nonneg_smul_mem_range A B b hb hy
  rw [← hu, ← hv]
  exact jointQuadratic_add_mem_range A B u v

end Erdos1017.Variation

module

public import Erdos1017.Models.Selection.QuadraticConstraint
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Lagrange multiplier at a quadratic local maximum

A regular quadratic equality constraint has a Lagrange multiplier and a
nonpositive tangent Lagrangian quadratic form at any local maximum, obtained by
restricting the local optimum to a tangent/transverse plane for first- and
second-order conditions.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restricting an actual local quadratic optimum to a tangent/transverse
plane gives both first- and second-order necessary conditions. -/
theorem tangent_conditions_on_plane
    (D C : E →ₗ[ℝ] ℝ) (A B : LinearMap.BilinForm ℝ E)
    (hA : ∀ x y, A x y = A y x) (hB : ∀ x y, B x y = B y x)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ x : E, ‖x‖ < ε → D x + A x x = 0 → C x + B x x ≤ 0)
    (u v : E) (hu : 0 < D u) (hv : D v = 0) :
    C v = 0 ∧ B v v - C u * A v v / D u ≤ 0 := by
  let η := ε / (‖v‖ + ‖u‖ + 1)
  have hden : 0 < ‖v‖ + ‖u‖ + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  have hηeq : η * (‖v‖ + ‖u‖ + 1) = ε := div_mul_cancel₀ _ hden.ne'
  apply lagrange_tangent_conditions_of_local_max (A v v) (D u) (A v u) (A u u)
    (C v) (C u) (B v v) (B v u) (B u u) hu η hη
  intro t s ht hs hroot
  have hnorm : ‖t • v + s • u‖ < ε := by
    have hn := norm_add_le (t • v) (s • u)
    simp only [norm_smul, Real.norm_eq_abs] at hn
    have hvbound := mul_le_mul_of_nonneg_right ht.le (norm_nonneg v)
    have hubound := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
    nlinarith
  have hconstraint : D (t • v + s • u) + A (t • v + s • u) (t • v + s • u) =
      A v v * t ^ 2 + (D u + 2 * A v u * t) * s + A u u * s ^ 2 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv]
    rw [hA u v]
    ring
  have h := hmax (t • v + s • u) hnorm (hconstraint.trans hroot)
  have hcost : C (t • v + s • u) + B (t • v + s • u) (t • v + s • u) =
      C v * t + C u * s + B v v * t ^ 2 + 2 * B v u * t * s + B u u * s ^ 2 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hB u v]
    ring
  rwa [hcost] at h

/-- A regular quadratic equality constraint has a genuine Lagrange
multiplier and a nonpositive tangent Lagrangian quadratic form at any local
maximum. Only the actual local maximum and bilinear algebra are assumed. -/
theorem exists_multiplier_of_quadratic_local_max
    (D C : E →ₗ[ℝ] ℝ) (A B : LinearMap.BilinForm ℝ E)
    (hA : ∀ x y, A x y = A y x) (hB : ∀ x y, B x y = B y x)
    (hregular : D ≠ 0) (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ x : E, ‖x‖ < ε → D x + A x x = 0 → C x + B x x ≤ 0) :
    ∃ m : ℝ, C = m • D ∧ ∀ v, D v = 0 → B v v - m * A v v ≤ 0 := by
  have hex : ∃ u, D u ≠ 0 := by
    by_contra h
    push Not at h
    exact hregular (LinearMap.ext h)
  obtain ⟨w, hw⟩ := hex
  have hexpos : ∃ u, 0 < D u := by
    rcases lt_or_gt_of_ne hw with hn | hp
    · exact ⟨-w, by simpa using neg_pos.mpr hn⟩
    · exact ⟨w, hp⟩
  obtain ⟨u, hu⟩ := hexpos
  let m := C u / D u
  have htangent (v : E) (hv : D v = 0) :
      C v = 0 ∧ B v v - C u * A v v / D u ≤ 0 :=
    tangent_conditions_on_plane D C A B hA hB ε hε hmax u v hu hv
  refine ⟨m, ?_, ?_⟩
  · ext v
    have hv : D (v - (D v / D u) • u) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hu.ne', sub_self]
    have hc := (htangent _ hv).1
    simp only [map_sub, map_smul, smul_eq_mul] at hc
    change C v = m * D v
    calc
      C v = (D v / D u) * C u := sub_eq_zero.mp hc
      _ = m * D v := by dsimp [m]; ring
  · intro v hv
    convert (htangent v hv).2 using 1
    dsimp [m]
    ring

end Erdos1017.Variation

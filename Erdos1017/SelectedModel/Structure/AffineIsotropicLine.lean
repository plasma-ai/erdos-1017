module

public import Erdos1017.SelectedModel.Structure.OrderedZeroTripleGeometry

/-!
# Affine feature lines and isotropic pairs

This module defines the affine line through two scalar-labeled endpoints, the
plane of physical points whose coordinates lie on it, and `IsotropicPair`, and
shows that compatible endpoint Gram data determine the Gram identity on the
whole line and plane, independently of the chosen anchors.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Erdos1017.OrderedZeroTripleGeometry

variable {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The affine feature line through two scalar-labelled endpoints. -/
def affineLine (x z : ℝ) (Vx Vz : H) (t : ℝ) : H :=
  ((z - t) / (z - x)) • Vx + ((t - x) / (z - x)) • Vz

/-- Physical points whose scalar and Hilbert coordinates lie on the
affine line determined by the two endpoints. -/
def affinePlane (φ : Ω → ℝ) (V : Ω → H) (x z : Ω) : Set Ω :=
  {w | V w = affineLine (φ x) (φ z) (V x) (V z) (φ w)}

/-- Two distinct scalar-labelled endpoints with matching canonical Gram
data. These are pointwise identities, with no measure assumptions. -/
structure IsotropicPair (ν σ : ℝ) (φ : Ω → ℝ) (V : Ω → H) (x z : Ω) : Prop where
  scalar_ne : φ x ≠ φ z
  left_norm : ‖V x‖ ^ 2 = ν + σ * (φ x) ^ 2
  right_norm : ‖V z‖ ^ 2 = ν + σ * (φ z) ^ 2
  inner_eq : ⟪V x, V z⟫ = ν + σ * φ x * φ z

theorem affineLine_apply_left (x z : ℝ) (Vx Vz : H) (hxz : x ≠ z) :
    affineLine x z Vx Vz x = Vx := by
  simp [affineLine, sub_ne_zero.mpr hxz.symm]

theorem affineLine_apply_right (x z : ℝ) (Vx Vz : H) (hxz : x ≠ z) :
    affineLine x z Vx Vz z = Vz := by
  simp [affineLine, sub_ne_zero.mpr hxz.symm]

/-- Reinterpolating any two distinct scalar positions recovers the same
affine line at every scalar position. -/
theorem affineLine_reanchor (x z u v : ℝ) (Vx Vz : H) (huv : u ≠ v) (t : ℝ) :
    affineLine u v (affineLine x z Vx Vz u) (affineLine x z Vx Vz v) t =
      affineLine x z Vx Vz t := by
  by_cases hxz : x = z
  · subst z
    simp [affineLine]
  · have hleft : ((v - t) / (v - u)) * ((z - u) / (z - x)) +
        ((t - u) / (v - u)) * ((z - v) / (z - x)) = (z - t) / (z - x) := by
      field_simp
      ring
    have hright : ((v - t) / (v - u)) * ((u - x) / (z - x)) +
        ((t - u) / (v - u)) * ((v - x) / (z - x)) = (t - x) / (z - x) := by
      field_simp
      ring
    unfold affineLine
    calc
      _ = (((v - t) / (v - u)) * ((z - u) / (z - x)) +
          ((t - u) / (v - u)) * ((z - v) / (z - x))) • Vx +
          (((v - t) / (v - u)) * ((u - x) / (z - x)) +
          ((t - u) / (v - u)) * ((v - x) / (z - x))) • Vz := by module
      _ = _ := by rw [hleft, hright]

/-- A middle interpolation relation can be solved for the left endpoint
using the line anchored at the middle and right endpoints. -/
theorem affineLine_left_of_middle {x y z : ℝ} {Vx Vy Vz : H}
    (hxz : x ≠ z) (hyz : y ≠ z) (hmid : Vy = affineLine x z Vx Vz y) :
    Vx = affineLine y z Vy Vz x := by
  have h := affineLine_reanchor x z y z Vx Vz hyz x
  rw [affineLine_apply_right x z Vx Vz hxz, ← hmid,
    affineLine_apply_left x z Vx Vz hxz] at h
  exact h.symm

/-- The analogous rearrangement solves for the right endpoint using the
line anchored at the left and middle endpoints. -/
theorem affineLine_right_of_middle {x y z : ℝ} {Vx Vy Vz : H}
    (hxz : x ≠ z) (hxy : x ≠ y) (hmid : Vy = affineLine x z Vx Vz y) :
    Vz = affineLine x y Vx Vy z := by
  have h := affineLine_reanchor x z x y Vx Vz hxy z
  rw [affineLine_apply_left x z Vx Vz hxz, ← hmid,
    affineLine_apply_right x z Vx Vz hxz] at h
  exact h.symm

theorem left_mem_affinePlane (φ : Ω → ℝ) (V : Ω → H) (x z : Ω)
    (hxz : φ x ≠ φ z) : x ∈ affinePlane φ V x z :=
  (affineLine_apply_left (φ x) (φ z) (V x) (V z) hxz).symm

theorem right_mem_affinePlane (φ : Ω → ℝ) (V : Ω → H) (x z : Ω)
    (hxz : φ x ≠ φ z) : z ∈ affinePlane φ V x z :=
  (affineLine_apply_right (φ x) (φ z) (V x) (V z) hxz).symm

/-- Two distinct scalar coordinates on one feature line determine the
same set of physical points, regardless of the chosen anchors. -/
theorem affinePlane_reanchor {φ : Ω → ℝ} {V : Ω → H} {x z u v : Ω}
    (hu : u ∈ affinePlane φ V x z) (hv : v ∈ affinePlane φ V x z)
    (huv : φ u ≠ φ v) : affinePlane φ V u v = affinePlane φ V x z := by
  ext w
  change (V w = affineLine (φ u) (φ v) (V u) (V v) (φ w)) ↔
    V w = affineLine (φ x) (φ z) (V x) (V z) (φ w)
  change V u = affineLine (φ x) (φ z) (V x) (V z) (φ u) at hu
  change V v = affineLine (φ x) (φ z) (V x) (V z) (φ v) at hv
  rw [hu, hv, affineLine_reanchor _ _ _ _ _ _ huv]

/-- The plane depends only on the two endpoint coordinate pairs. -/
theorem affinePlane_eq_of_endpoint_coordinates
    {φ : Ω → ℝ} {V : Ω → H} {x z x' z' : Ω}
    (hx : φ x = φ x') (hVx : V x = V x')
    (hz : φ z = φ z') (hVz : V z = V z') :
    affinePlane φ V x z = affinePlane φ V x' z' := by
  simp only [affinePlane, hx, hVx, hz, hVz]

/-- Membership also depends only on the tested point's coordinate pair. -/
theorem mem_affinePlane_iff_of_coordinates
    {φ : Ω → ℝ} {V : Ω → H} {x z u v : Ω}
    (hφ : φ u = φ v) (hV : V u = V v) :
    u ∈ affinePlane φ V x z ↔ v ∈ affinePlane φ V x z := by
  simp only [affinePlane, Set.mem_ofPred_eq, hφ, hV]

/-- Compatible diagonal and cross Gram identities at two distinct scalar
endpoints determine the Gram identity on their entire affine line. -/
theorem affineLine_gram (ν σ x z : ℝ) (Vx Vz : H) (hxz : x ≠ z)
    (hx : ‖Vx‖ ^ 2 = ν + σ * x ^ 2)
    (hz : ‖Vz‖ ^ 2 = ν + σ * z ^ 2)
    (hcross : ⟪Vx, Vz⟫ = ν + σ * x * z) (s t : ℝ) :
    ⟪affineLine x z Vx Vz s, affineLine x z Vx Vz t⟫ = ν + σ * s * t := by
  have hreverse : ⟪Vz, Vx⟫ = ν + σ * x * z :=
    (real_inner_comm Vx Vz).trans hcross
  simp only [affineLine, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hx, hz, hcross, hreverse]
  field_simp
  ring

/-- Every two members of a line with compatible endpoint Gram data have
zero canonical pair defect. No measure or pointwise-kernel premise is used. -/
theorem affinePlane_gram {φ : Ω → ℝ} {V : Ω → H} {x z u v : Ω}
    (ν σ : ℝ) (hxz : φ x ≠ φ z)
    (hx : ‖V x‖ ^ 2 = ν + σ * (φ x) ^ 2)
    (hz : ‖V z‖ ^ 2 = ν + σ * (φ z) ^ 2)
    (hcross : ⟪V x, V z⟫ = ν + σ * φ x * φ z)
    (hu : u ∈ affinePlane φ V x z) (hv : v ∈ affinePlane φ V x z) :
    ⟪V u, V v⟫ = ν + σ * φ u * φ v := by
  change V u = affineLine (φ x) (φ z) (V x) (V z) (φ u) at hu
  change V v = affineLine (φ x) (φ z) (V x) (V z) (φ v) at hv
  rw [hu, hv]
  exact affineLine_gram ν σ _ _ _ _ hxz hx hz hcross _ _

/-- The bundled compatible endpoint identities give the whole-plane Gram
identity without any further pointwise geometric premise. -/
theorem IsotropicPair.gram {ν σ : ℝ} {φ : Ω → ℝ} {V : Ω → H} {x z u v : Ω}
    (h : IsotropicPair ν σ φ V x z)
    (hu : u ∈ affinePlane φ V x z) (hv : v ∈ affinePlane φ V x z) :
    ⟪V u, V v⟫ = ν + σ * φ u * φ v :=
  affinePlane_gram ν σ h.scalar_ne h.left_norm h.right_norm h.inner_eq hu hv

/-- Any two distinct scalar coordinates on the compatible line form a
new compatible pair. The diagonal identities follow from the proved Gram form. -/
theorem IsotropicPair.reanchor {ν σ : ℝ} {φ : Ω → ℝ} {V : Ω → H} {x z u v : Ω}
    (h : IsotropicPair ν σ φ V x z)
    (hu : u ∈ affinePlane φ V x z) (hv : v ∈ affinePlane φ V x z)
    (huv : φ u ≠ φ v) : IsotropicPair ν σ φ V u v := by
  refine ⟨huv, ?_, ?_, h.gram hu hv⟩
  · simpa only [real_inner_self_eq_norm_sq, pow_two, mul_assoc] using h.gram hu hu
  · simpa only [real_inner_self_eq_norm_sq, pow_two, mul_assoc] using h.gram hv hv

end Erdos1017.OrderedZeroTripleGeometry

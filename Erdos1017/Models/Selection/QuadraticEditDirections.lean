module

public import Erdos1017.Models.Selection.QuadraticSeparation
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# One multiplier for vertex directions and edits

Vertex directions and arbitrary finite collections of squared edit amplitudes
are represented by one bilinear form (`withEditDirections`), and a single
bounded multiplier controls every vertex direction and every edit, even for an
infinite edit index set.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Variation

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- A diagonal bilinear form on finitely supported edit amplitudes. -/
def editDiagonal (a : ι → ℝ) : LinearMap.BilinForm ℝ (ι →₀ ℝ) :=
  Finsupp.lsum ℝ (fun i => LinearMap.toSpanSingleton ℝ ((ι →₀ ℝ) →ₗ[ℝ] ℝ)
    (a i • (Finsupp.lapply i : (ι →₀ ℝ) →ₗ[ℝ] ℝ)))

theorem editDiagonal_apply (a : ι → ℝ) (r s : ι →₀ ℝ) :
    editDiagonal a r s = r.sum (fun i t => a i * t * s i) := by
  classical
  simp only [editDiagonal, Finsupp.lsum_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Vertex directions and arbitrary finite collections of squared edit
amplitudes are represented by one genuine bilinear form. -/
def withEditDirections (A : LinearMap.BilinForm ℝ E) (a : ι → ℝ) :
    LinearMap.BilinForm ℝ (E × (ι →₀ ℝ)) :=
  A.compl₁₂ (LinearMap.fst ℝ E (ι →₀ ℝ)) (LinearMap.fst ℝ E (ι →₀ ℝ)) +
    (editDiagonal a).compl₁₂ (LinearMap.snd ℝ E (ι →₀ ℝ)) (LinearMap.snd ℝ E (ι →₀ ℝ))

theorem withEditDirections_self (A : LinearMap.BilinForm ℝ E) (a : ι → ℝ)
    (x : E) (r : ι →₀ ℝ) :
    withEditDirections A a (x, r) (x, r) = A x x + r.sum (fun i t => a i * t ^ 2) := by
  change A x x + editDiagonal a r r = _
  rw [editDiagonal_apply]
  congr 1
  apply Finsupp.sum_congr
  intro i _
  ring

/-- A single bounded multiplier simultaneously controls every vertex
direction and every edit, even for an infinite edit index set. The finite
support in the hypothesis records exactly the finite combinations used. -/
theorem exists_multiplier_with_edits
    (A B : LinearMap.BilinForm ℝ E) (a b : ι → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ (x : E) (r : ι →₀ ℝ),
      B x x + r.sum (fun i t => b i * t ^ 2) ≤
        L * |A x x + r.sum (fun i t => a i * t ^ 2)|) :
    ∃ m : ℝ, -L ≤ m ∧ m ≤ L ∧
      (∀ x, B x x + m * A x x ≤ 0) ∧ (∀ i, b i + m * a i ≤ 0) := by
  have h : ∀ z : E × (ι →₀ ℝ),
      withEditDirections B b z z ≤ L * |withEditDirections A a z z| := by
    rintro ⟨x, r⟩
    simpa only [withEditDirections_self] using hbound x r
  obtain ⟨m, hmlo, hmhi, hm⟩ := exists_bounded_quadratic_multiplier
    (withEditDirections A a) (withEditDirections B b) L hL h
  refine ⟨m, hmlo, hmhi, ?_, ?_⟩
  · intro x
    have h := hm (x, 0)
    simpa [withEditDirections_self] using h
  · intro i
    have h := hm (0, Finsupp.single i 1)
    simpa [withEditDirections_self, Finsupp.sum_single_index] using h

end Erdos1017.Variation

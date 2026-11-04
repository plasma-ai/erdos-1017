module

public import Erdos1017.Models.Kernel.KernelPositiveIndexStability

/-!
# Positive eigenvalue gaps from a coercive plane

The quadratic form of a compact symmetric operator is bounded by that of its
positive projection, and a quantitative positive plane with positive index at
most two gives the same coercive constant on the whole positive subspace and
every positive eigenvalue, uniformly along norm-convergent sequences.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual algebraic sum of positive eigenspaces is invariant under
the original operator, without a supplied eigenbasis. -/
theorem map_mem_positiveSpectralSubspace (S : E →L[ℝ] E) (x : E)
    (hx : x ∈ positiveSpectralSubspace S) : S x ∈ positiveSpectralSubspace S := by
  have hle : positiveSpectralSubspace S ≤ (positiveSpectralSubspace S).comap S.toLinearMap := by
    apply iSup_le
    intro σ
    apply iSup_le
    intro hσ y hy
    change S y ∈ positiveSpectralSubspace S
    have hSy : S y = σ • y := Module.End.mem_eigenspace_iff.mp hy
    have hsub : Module.End.eigenspace S.toLinearMap σ ≤ positiveSpectralSubspace S :=
      le_iSup_of_le σ (le_iSup_of_le hσ le_rfl)
    rw [hSy]
    exact (positiveSpectralSubspace S).smul_mem σ (hsub hy)
  exact hle hx

variable [CompleteSpace E]

/-- The original quadratic form is bounded above by that of the actual
positive orthogonal projection. Its complement is proved nonpositive from
the actual compact symmetric operator's constructed eigenbasis. -/
theorem quadratic_le_positive_projection (S : E →L[ℝ] E) (hcompact : IsCompactOperator S)
    (hsym : S.toLinearMap.IsSymmetric) [FiniteDimensional ℝ (positiveSpectralSubspace S)]
    (x : E) :
    ⟪S x, x⟫ ≤ ⟪S ((positiveSpectralSubspace S).orthogonalProjectionOnto x : E),
      ((positiveSpectralSubspace S).orthogonalProjectionOnto x : E)⟫ := by
  let P := positiveSpectralSubspace S
  let y := P.starProjection x
  let z := x - y
  have hy : y ∈ P := P.starProjection_apply_mem x
  have hz : z ∈ Pᗮ := P.sub_starProjection_mem_orthogonal x
  have hcross : ⟪S y, z⟫ = 0 :=
    (Submodule.mem_orthogonal P z).mp hz (S y) (map_mem_positiveSpectralSubspace S y hy)
  have hcross' : ⟪S z, y⟫ = 0 := by
    calc
      _ = ⟪z, S y⟫ := hsym z y
      _ = ⟪S y, z⟫ := real_inner_comm _ _
      _ = 0 := hcross
  have hx : x = y + z := by dsimp [z]; abel
  have hform : ⟪S x, x⟫ = ⟪S y, y⟫ + ⟪S z, z⟫ := by
    calc
      _ = ⟪S (y + z), y + z⟫ := congrArg (fun w => ⟪S w, w⟫) hx
      _ = _ := by simp only [map_add, inner_add_left, inner_add_right, hcross, hcross']; ring
  have hnonpos := quadratic_nonpos_on_positive_orthogonal S hcompact hsym z hz
  change ⟪S x, x⟫ ≤ ⟪S y, y⟫
  linarith

/-- A quantitative positive plane and actual positive index at most two
force the same coercive constant on the entire actual positive subspace.
The actual projection is injective on the plane and hence surjective. -/
theorem positive_subspace_coercive_of_coercive_plane
    (S : E →L[ℝ] E) (hcompact : IsCompactOperator S) (hsym : S.toLinearMap.IsSymmetric)
    [FiniteDimensional ℝ (positiveSpectralSubspace S)]
    (hindex : Module.finrank ℝ (positiveSpectralSubspace S) ≤ 2)
    (W : Submodule ℝ E) [FiniteDimensional ℝ W] (hdim : Module.finrank ℝ W = 2)
    (η : ℝ) (hη : 0 < η) (hcoercive : ∀ x ∈ W, η * ‖x‖ ^ 2 ≤ ⟪S x, x⟫) :
    ∀ y ∈ positiveSpectralSubspace S, η * ‖y‖ ^ 2 ≤ ⟪S y, y⟫ := by
  let P := positiveSpectralSubspace S
  let C : W →ₗ[ℝ] P := P.orthogonalProjectionOnto.toLinearMap.comp W.subtype
  have hzero (x : W) (hx : C x = 0) : x = 0 := by
    by_contra hx0
    have hxE : (x : E) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hpositive : 0 < ⟪S (x : E), (x : E)⟫ :=
      (mul_pos hη (sq_pos_of_pos (norm_pos_iff.mpr hxE))).trans_le (hcoercive x x.property)
    change P.orthogonalProjectionOnto (x : E) = 0 at hx
    have hq := quadratic_le_positive_projection S hcompact hsym (x : E)
    change ⟪S (x : E), (x : E)⟫ ≤ ⟪S (P.orthogonalProjectionOnto (x : E) : E),
      (P.orthogonalProjectionOnto (x : E) : E)⟫ at hq
    rw [hx] at hq
    have hnonpos : ⟪S (x : E), (x : E)⟫ ≤ 0 := by
      simpa only [Submodule.coe_zero, map_zero, inner_zero_left] using hq
    exact (not_le_of_gt hpositive) hnonpos
  have hinj : Function.Injective C := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  change Module.finrank ℝ P ≤ 2 at hindex
  have heqdim : Module.finrank ℝ W = Module.finrank ℝ P := by omega
  have hsurj : Function.Surjective C :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heqdim).mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have hproj : (P.orthogonalProjectionOnto (x : E) : E) = y := congrArg Subtype.val hx
  have hnorm : ‖y‖ ≤ ‖(x : E)‖ := by
    have h := P.norm_orthogonalProjectionOnto_apply_le (x : E)
    change ‖(P.orthogonalProjectionOnto (x : E) : E)‖ ≤ ‖(x : E)‖ at h
    rwa [hproj] at h
  have hnormsq : ‖y‖ ^ 2 ≤ ‖(x : E)‖ ^ 2 := by nlinarith [norm_nonneg y, norm_nonneg (x : E)]
  have hq := quadratic_le_positive_projection S hcompact hsym (x : E)
  change ⟪S (x : E), (x : E)⟫ ≤ ⟪S (P.orthogonalProjectionOnto (x : E) : E),
    (P.orthogonalProjectionOnto (x : E) : E)⟫ at hq
  rw [hproj] at hq
  exact (mul_le_mul_of_nonneg_left hnormsq hη.le).trans ((hcoercive x x.property).trans hq)

/-- Every actual positive eigenvalue inherits the coercive plane's gap
when the actual finite positive spectral index is at most two. -/
theorem positive_eigenvalue_ge_of_coercive_plane
    (S : E →L[ℝ] E) (hcompact : IsCompactOperator S) (hsym : S.toLinearMap.IsSymmetric)
    [FiniteDimensional ℝ (positiveSpectralSubspace S)]
    (hindex : Module.finrank ℝ (positiveSpectralSubspace S) ≤ 2)
    (W : Submodule ℝ E) [FiniteDimensional ℝ W] (hdim : Module.finrank ℝ W = 2)
    (η : ℝ) (hη : 0 < η) (hcoercive : ∀ x ∈ W, η * ‖x‖ ^ 2 ≤ ⟪S x, x⟫)
    (σ : ℝ) (hσ : 0 < σ) (w : E) (hw : w ≠ 0) (heigen : S w = σ • w) : η ≤ σ := by
  have hsub : Module.End.eigenspace S.toLinearMap σ ≤ positiveSpectralSubspace S :=
    le_iSup_of_le σ (le_iSup_of_le hσ le_rfl)
  have hmem : w ∈ positiveSpectralSubspace S := hsub (Module.End.mem_eigenspace_iff.mpr heigen)
  have hq := positive_subspace_coercive_of_coercive_plane S hcompact hsym hindex W hdim η hη hcoercive w hmem
  rw [heigen, real_inner_smul_left, real_inner_self_eq_norm_sq] at hq
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hw))).mp hq

/-- Actual norm convergence, positive index at most two along the compact
symmetric sequence and index greater than one at the limit give a uniform
eventual lower bound on every positive eigenvalue. No plane, gap or
eigenbasis is supplied to this limit application. -/
theorem eventually_positive_eigenvalue_gap_of_tendsto
    {T : E →L[ℝ] E} {S : ℕ → E →L[ℝ] E}
    (hlim : Filter.Tendsto S Filter.atTop (nhds T))
    (hcompact : ∀ n, IsCompactOperator (S n)) (hsym : ∀ n, (S n).toLinearMap.IsSymmetric)
    (hfinite : ∀ n, FiniteDimensional ℝ (positiveSpectralSubspace (S n)))
    (hindex : ∀ n, Module.finrank ℝ (positiveSpectralSubspace (S n)) ≤ 2)
    (hlimit : ¬(FiniteDimensional ℝ (positiveSpectralSubspace T) ∧
      Module.finrank ℝ (positiveSpectralSubspace T) ≤ 1)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in Filter.atTop,
      ∀ (σ : ℝ), 0 < σ → ∀ w : E, w ≠ 0 → S n w = σ • w → η ≤ σ := by
  have hcompactT := isCompactOperator_of_tendsto hlim (Filter.Eventually.of_forall hcompact)
  have hsymT := symmetric_of_tendsto hlim hsym
  obtain ⟨W, hfiniteW, hdim, η, hη, hpersist⟩ :=
    two_dimensional_positive_subspace_persists hlim hcompactT hsymT hlimit
  let := hfiniteW
  refine ⟨η, hη, hpersist.mono ?_⟩
  intro n hn σ hσ w hw heigen
  let := hfinite n
  exact positive_eigenvalue_ge_of_coercive_plane (S n) (hcompact n) (hsym n) (hindex n)
    W hdim η hη hn σ hσ w hw heigen

end Erdos1017.KernelOperator

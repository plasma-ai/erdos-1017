module

public import Erdos1017.Models.Kernel.PositiveSpectralSubspace

/-!
# Bounding positive index by constraints

If the quadratic form of a compact symmetric operator is nonpositive on the
kernel of a constraint map, positive orthonormal eigendirections have linearly
independent constraint images, so a finite-dimensional constraint space bounds
the positive spectral index.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

/-- If the quadratic form is nonpositive on the kernel of a constraint map,
positive orthonormal eigendirections have linearly independent constraint
images. This is the algebraic positive-index step in the capped variation
argument. -/
theorem positive_eigen_constraint_independent_on_submodule
    {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (T : E →L[ℝ] E) (C : E →ₗ[ℝ] F)
    (D : Submodule ℝ E) (hquadratic : ∀ x ∈ D, C x = 0 → ⟪T x, x⟫ ≤ 0)
    (v : ι → E) (hv : Orthonormal ℝ v) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (heigen : ∀ i, T (v i) = t i • v i) (hmem : ∀ i, v i ∈ D) :
    LinearIndependent ℝ (fun i => C (v i)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s g hsum i hi
  have hc : C (∑ j ∈ s, g j • v j) = 0 := by simpa only [map_sum, map_smul] using hsum
  have hq := hquadratic (∑ j ∈ s, g j • v j)
    (D.sum_mem (fun j _ => D.smul_mem _ (hmem j))) hc
  have heq : ⟪T (∑ j ∈ s, g j • v j), ∑ j ∈ s, g j • v j⟫ =
      ∑ j ∈ s, t j * (g j) ^ 2 := by
    simp only [map_sum, map_smul, heigen, smul_smul]
    rw [hv.inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [conj_trivial]
    ring
  rw [heq] at hq
  have hn (j : ι) (_ : j ∈ s) : 0 ≤ t j * (g j) ^ 2 := mul_nonneg (ht j).le (sq_nonneg _)
  have hz : (∑ j ∈ s, t j * (g j) ^ 2) = 0 := le_antisymm hq (Finset.sum_nonneg hn)
  have hzi := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz i hi
  have hsq : (g i) ^ 2 = 0 := (mul_eq_zero.mp hzi).resolve_left (ht i).ne'
  exact sq_eq_zero_iff.mp hsq

theorem positive_eigen_constraint_independent
    {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (T : E →L[ℝ] E) (C : E →ₗ[ℝ] F)
    (hquadratic : ∀ x, C x = 0 → ⟪T x, x⟫ ≤ 0)
    (v : ι → E) (hv : Orthonormal ℝ v) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (heigen : ∀ i, T (v i) = t i • v i) :
    LinearIndependent ℝ (fun i => C (v i)) :=
  positive_eigen_constraint_independent_on_submodule T C ⊤ (fun x _ => hquadratic x)
    v hv t ht heigen (fun _ => Submodule.mem_top)

theorem finite_positive_indices_of_constraints_on_submodule
    {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] E) (C : E →ₗ[ℝ] F)
    (D : Submodule ℝ E) (hquadratic : ∀ x ∈ D, C x = 0 → ⟪T x, x⟫ ≤ 0)
    (b : HilbertBasis ι ℝ E) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) (hmem : ∀ i, 0 < t i → b i ∈ D) :
    ∃ s : Finset ι, (∀ i, i ∈ s ↔ 0 < t i) ∧ s.card ≤ Module.finrank ℝ F := by
  classical
  have hind := positive_eigen_constraint_independent_on_submodule T C D hquadratic
    (fun i : {i // 0 < t i} => b i)
    (b.orthonormal.comp _ Subtype.val_injective) (fun i => t i)
    (fun i => i.property) (fun i => heigen i) (fun i => hmem i i.property)
  have hf : Finite {i // 0 < t i} := hind.finite
  have hs : {i | 0 < t i}.Finite := Set.finite_coe_iff.mp hf
  let : Fintype {i // 0 < t i} := @Fintype.ofFinite _ hf
  let : Fintype {i | 0 < t i} := hs.fintype
  refine ⟨hs.toFinset, fun i => hs.mem_toFinset, ?_⟩
  have hcard : hs.toFinset.card = Fintype.card {i // 0 < t i} :=
    (Fintype.card_of_finset' hs.toFinset (fun i => hs.mem_toFinset)).symm
  rw [hcard]
  exact hind.fintype_card_le_finrank

theorem finite_positive_indices_of_constraints
    {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] E) (C : E →ₗ[ℝ] F)
    (hquadratic : ∀ x, C x = 0 → ⟪T x, x⟫ ≤ 0)
    (b : HilbertBasis ι ℝ E) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) :
    ∃ s : Finset ι, (∀ i, i ∈ s ↔ 0 < t i) ∧ s.card ≤ Module.finrank ℝ F :=
  finite_positive_indices_of_constraints_on_submodule T C ⊤ (fun x _ => hquadratic x)
    b t heigen (fun _ _ => Submodule.mem_top)

/-- Every positive eigenspace lies in the span of the positive members of
any complete orthonormal eigenbasis. Finiteness here is a conclusion supplied
by the constraint argument, rather than an assumed spectral theorem. -/
theorem positiveSpectralSubspace_le_finite_span
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hsym : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℝ E) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i)
    (s : Finset ι) (houtside : ∀ i ∉ s, t i ≤ 0) :
    positiveSpectralSubspace T ≤ Submodule.span ℝ (b '' (s : Set ι)) := by
  classical
  apply iSup_le
  intro r
  apply iSup_le
  intro hr x hx
  have hx' : T x = r • x := Module.End.mem_eigenspace_iff.mp hx
  have hz (i : ι) (hi : i ∉ s) : b.repr x i • b i = 0 := by
    have hinner := hsym (b i) x
    change ⟪T (b i), x⟫ = ⟪b i, T x⟫ at hinner
    rw [heigen i, hx', real_inner_smul_left, real_inner_smul_right] at hinner
    have hzero : ⟪b i, x⟫ = 0 := by
      have hne : t i ≠ r := ne_of_lt ((houtside i hi).trans_lt hr)
      exact (mul_eq_mul_right_iff.mp hinner).resolve_left hne
    simp [b.repr_apply_apply, hzero]
  have hsum : x = ∑ i ∈ s, b.repr x i • b i :=
    (b.hasSum_repr x).tsum_eq.symm.trans (tsum_eq_sum hz)
  rw [hsum]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- A finite-dimensional constraint space bounds the positive spectral
index of a compact symmetric operator whenever the quadratic form is
nonpositive on the constraint kernel. -/
theorem positive_subspace_dimension_le_constraints
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] E) (hcompact : IsCompactOperator T)
    (hsym : T.toLinearMap.IsSymmetric) (C : E →ₗ[ℝ] F)
    (hquadratic : ∀ x, C x = 0 → ⟪T x, x⟫ ≤ 0) :
    FiniteDimensional ℝ (positiveSpectralSubspace T) ∧
      Module.finrank ℝ (positiveSpectralSubspace T) ≤ Module.finrank ℝ F := by
  classical
  obtain ⟨ι, b, t, heigen⟩ := exists_eigen_hilbertBasis T hcompact hsym
  obtain ⟨s, hs, hcard⟩ := finite_positive_indices_of_constraints T C hquadratic b t heigen
  have hout (i : ι) (hi : i ∉ s) : t i ≤ 0 := le_of_not_gt (fun hp => hi ((hs i).mpr hp))
  have hsub : positiveSpectralSubspace T ≤ Submodule.span ℝ (↑(s.image b) : Set E) := by
    simpa only [Finset.coe_image] using positiveSpectralSubspace_le_finite_span T hsym b t heigen s hout
  have hfinite := Submodule.finiteDimensional_of_le hsub
  refine ⟨hfinite, ?_⟩
  exact (Submodule.finrank_mono hsub).trans
    ((finrank_span_finset_le_card (R := ℝ) (s.image b)).trans ((Finset.card_image_le).trans hcard))

end Erdos1017.KernelOperator

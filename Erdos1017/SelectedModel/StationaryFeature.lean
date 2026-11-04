module

public import Erdos1017.SelectedModel.AnchoredEigenbasis
public import Erdos1017.Models.Kernel.StationaryKernel
public import Erdos1017.SelectedModel.UniformSpectralFeature

/-!
# Uniform feature bound at positive index two

Stationarity, positive rank at most two and a second positive eigenvector with a
gap give the explicit feature bound, using that positive orthonormal
eigenvectors cannot exceed the positive spectral dimension.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- A finite family of positive orthonormal eigenvectors cannot exceed the
positive spectral dimension. -/
theorem positive_basis_finset_card_le
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) [FiniteDimensional ℝ (positiveSpectralSubspace T)]
    (b : HilbertBasis ι ℝ E) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) (s : Finset ι) (ht : ∀ i ∈ s, 0 < t i) :
    s.card ≤ Module.finrank ℝ (positiveSpectralSubspace T) := by
  have hmem (i : s) : b i ∈ positiveSpectralSubspace T := by
    have hle : Module.End.eigenspace T.toLinearMap (t i) ≤ positiveSpectralSubspace T :=
      le_iSup_of_le (t i) (le_iSup_of_le (ht i i.property) le_rfl)
    exact hle (Module.End.mem_eigenspace_iff.mpr (heigen i))
  let v : s → positiveSpectralSubspace T := fun i => ⟨b i, hmem i⟩
  have hind : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (positiveSpectralSubspace T).subtype
    exact b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  simpa using hind.fintype_card_le_finrank

/-- A nonzero eigenvector orthogonal to one basis vector has a nonzero
coordinate at a different basis vector with the same eigenvalue. -/
theorem exists_eigenbasis_index_of_orthogonal_eigenvector
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hsym : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℝ E) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) (j : ι)
    (w : E) (hw : w ≠ 0) (horth : ⟪b j, w⟫ = 0) (σ : ℝ) (hweigen : T w = σ • w) :
    ∃ i, i ≠ j ∧ t i = σ := by
  have hcoord : ∃ i, b.repr w i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    apply b.repr.injective
    apply lp.ext
    funext i
    simpa using h i
  obtain ⟨i, hi⟩ := hcoord
  have hinner : ⟪b i, w⟫ ≠ 0 := by simpa only [b.repr_apply_apply] using hi
  have hne : i ≠ j := by
    rintro rfl
    exact hinner horth
  have heq := hsym (b i) w
  change ⟪T (b i), w⟫ = ⟪b i, T w⟫ at heq
  rw [heigen i, hweigen, real_inner_smul_left, real_inner_smul_right] at heq
  exact ⟨i, hne, (mul_eq_mul_right_iff.mp heq).resolve_right hinner⟩

universe u

/-- Stationarity, positive rank at most two, and an actual second positive
eigenvector with a gap suffice for the explicit feature bound. The complete
eigenbasis containing the constant direction is constructed. -/
theorem exists_uniform_feature_of_stationary_positive_index_two
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ 4)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (ν : ℝ) (hν : 0 < ν) (hstationary : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν)
    (hfinite : FiniteDimensional ℝ
      (positiveSpectralSubspace (operator K (by norm_num) hK hB)))
    (hindex : Module.finrank ℝ
      (positiveSpectralSubspace (operator K (by norm_num) hK hB)) ≤ 2)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hmean : (∫ x, w x ∂μ) = 0)
    (σ s₀ : ℝ) (hs₀ : 0 < s₀) (hσ : s₀ ≤ σ)
    (hweigen : operator K (by norm_num) hK hB w = σ • w) :
    ∃ (ι : Type u) (_ : Countable ι) (F : Ω → lp (fun _ : ι => ℝ) 2)
      (J : lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] lp (fun _ : ι => ℝ) 2),
      AEStronglyMeasurable F μ ∧ (∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt (8 + 32 / s₀)) ∧
      (∀ f g, ⟪J f, g⟫ = ⟪f, J g⟫) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ⟪J (F z.1), F z.2⟫ := by
  classical
  let T := operator K (by norm_num) hK hB
  let := hfinite
  have hsymmetric := operator_symmetric K (by norm_num) hK hB hsym
  obtain ⟨ι, b, t, i₀, heigen, hb₀, ht₀⟩ := exists_eigen_hilbertBasis_containing T
    (operator_isCompact K (by norm_num) hK hB) hsymmetric (Lp.const 2 μ (1 : ℝ))
    constant_one_norm ν (constant_one_eigenvector_of_stationary K (by norm_num) hK hB ν hstationary)
  have hcount := orthonormal_countable b.orthonormal
  let := hcount
  have horth : ⟪b i₀, w⟫ = 0 := by rw [hb₀, inner_constant_one, hmean]
  obtain ⟨i₁, hne, ht₁⟩ := exists_eigenbasis_index_of_orthogonal_eigenvector
    T hsymmetric b t heigen i₀ w hw horth σ hweigen
  have hpositive₀ : 0 < t i₀ := ht₀.symm ▸ hν
  have hpositive₁ : 0 < t i₁ := ht₁.symm ▸ hs₀.trans_le hσ
  have hout (i : ι) (hi₀ : i ≠ i₀) (hi₁ : i ≠ i₁) : t i ≤ 0 := by
    by_contra hi
    have hpos : 0 < t i := lt_of_not_ge hi
    have hcard := positive_basis_finset_card_le T b t heigen {i₀, i₁, i} (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact hpositive₀
      · exact hpositive₁
      · exact hpos)
    have hthree : ({i₀, i₁, i} : Finset ι).card = 3 := by
      simp [hne.symm, hi₀.symm, hi₁.symm]
    change Module.finrank ℝ (positiveSpectralSubspace T) ≤ 2 at hindex
    omega
  have hconst : ∀ᵐ x ∂μ, b i₀ x = 1 := by
    rw [hb₀]
    exact Lp.coeFn_const 2 μ (1 : ℝ)
  have hνbound : t i₀ ≤ 4 := by
    rw [ht₀]
    exact (le_abs_self ν).trans (stationary_value_abs_le K (by norm_num) hK hB ν hstationary)
  obtain ⟨F, hF, hbound, hrep⟩ := exists_bounded_two_positive_feature
    K hK hB hK0 hsym b t heigen i₀ i₁ hne.symm hconst ⟨hpositive₀.le, hνbound⟩
    hs₀ (ht₁.symm ▸ hσ) hout
  exact ⟨ι, hcount, F, spectralSign t, hF, hbound, spectralSign_self_adjoint t, hrep⟩

end Erdos1017.KernelOperator

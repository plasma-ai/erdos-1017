module

public import Erdos1017.Models.Kernel.PositiveIndexBound
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Stability of the positive spectral index

Strict positivity of a quadratic form on a finite-dimensional subspace has a
uniform gap that persists under small operator norm perturbations, every
strictly positive subspace injects into the positive spectral subspace, and the
positive index bound is closed under operator norm limits.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Operator norm controls the quadratic form uniformly in the vector. -/
theorem quadratic_sub_abs_le (S T : E →L[ℝ] E) (x : E) :
    |⟪S x, x⟫ - ⟪T x, x⟫| ≤ ‖S - T‖ * ‖x‖ ^ 2 := by
  calc
    _ = ‖⟪(S - T) x, x⟫‖ := by rw [sub_apply, inner_sub_left, Real.norm_eq_abs]
    _ ≤ ‖(S - T) x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖S - T‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right ((S - T).le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

/-- Strict positivity on a finite-dimensional subspace gives an actual
uniform positive quadratic gap, obtained from its compact unit sphere. -/
theorem positive_quadratic_subspace_coercive (T : E →L[ℝ] E) (W : Submodule ℝ E)
    [FiniteDimensional ℝ W]
    (hpositive : ∀ x ∈ W, x ≠ 0 → 0 < ⟪T x, x⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫ := by
  rcases subsingleton_or_nontrivial W with htrivial | hnontrivial
  · let := htrivial
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    have hx0 : x = 0 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : W) 0)
    simp [hx0]
  · let := hnontrivial
    have hne : (Metric.sphere (0 : W) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
    have hcont : Continuous (fun x : W => ⟪T (x : E), (x : E)⟫) := by fun_prop
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : W) 1).exists_isMinOn hne hcont.continuousOn
    have hunorm : ‖(u : E)‖ = 1 := by
      change ‖u‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using hu
    have hu0 : (u : E) ≠ 0 := by intro hz; rw [hz, norm_zero] at hunorm; norm_num at hunorm
    refine ⟨⟪T (u : E), (u : E)⟫, hpositive u u.property hu0, ?_⟩
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let v : W := ‖x‖⁻¹ • (⟨x, hx⟩ : W)
    have hvnorm : ‖v‖ = 1 := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hnorm.ne'
    have hv : v ∈ Metric.sphere (0 : W) 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hvnorm
    have h := hmin hv
    change ⟪T (u : E), (u : E)⟫ ≤ ⟪T (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫ at h
    rw [map_smul, real_inner_smul_left, real_inner_smul_right] at h
    have hscaled := mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
    field_simp [hnorm.ne'] at hscaled
    nlinarith

/-- Finite-dimensional strict positivity persists under a sufficiently
small operator norm perturbation, with a derived quantitative gap. -/
theorem positive_quadratic_subspace_persists (T : E →L[ℝ] E) (W : Submodule ℝ E)
    [FiniteDimensional ℝ W]
    (hpositive : ∀ x ∈ W, x ≠ 0 → 0 < ⟪T x, x⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : E →L[ℝ] E, ‖S - T‖ < c →
      ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ ⟪S x, x⟫ := by
  obtain ⟨c, hc, hcoercive⟩ := positive_quadratic_subspace_coercive T W hpositive
  refine ⟨c / 2, by positivity, ?_⟩
  intro S hS x hx
  have hdiff := (abs_le.mp (quadratic_sub_abs_le S T x)).1
  have hbound := mul_le_mul_of_nonneg_right hS.le (sq_nonneg ‖x‖)
  have hq := hcoercive x hx
  nlinarith

/-- The actual quadratic form is nonpositive on the orthogonal complement
of its finite positive spectral subspace. The eigenbasis is constructed. -/
theorem quadratic_nonpos_on_positive_orthogonal [CompleteSpace E]
    (T : E →L[ℝ] E) (hcompact : IsCompactOperator T)
    (hsym : T.toLinearMap.IsSymmetric)
    [FiniteDimensional ℝ (positiveSpectralSubspace T)]
    (x : E) (hx : x ∈ (positiveSpectralSubspace T)ᗮ) : ⟪T x, x⟫ ≤ 0 := by
  classical
  obtain ⟨ι, b, t, heigen⟩ := exists_eigen_hilbertBasis T hcompact hsym
  have hpositive := finite_positive_basis_indices T b t heigen
  let s := hpositive.toFinset
  have houtside (i : ι) (hi : i ∉ s) : t i ≤ 0 :=
    le_of_not_gt (fun hp => hi (hpositive.mem_toFinset.mpr hp))
  have hzero (i : ι) (hi : i ∈ s) : ⟪b i, x⟫ = 0 := by
    have ht : 0 < t i := hpositive.mem_toFinset.mp hi
    have hle : Module.End.eigenspace T.toLinearMap (t i) ≤ positiveSpectralSubspace T :=
      le_iSup_of_le (t i) (le_iSup_of_le ht le_rfl)
    exact (Submodule.mem_orthogonal _ _).mp hx (b i)
      (hle (Module.End.mem_eigenspace_iff.mpr (heigen i)))
  have h := eigen_quadratic_le_finite_sum b T hsym t heigen s houtside x
  have hsum : (∑ i ∈ s, t i * ⟪b i, x⟫ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i hi]
    ring
  rwa [hsum] at h

/-- Every strictly positive quadratic subspace injects into the actual
positive spectral subspace. No eigenbasis or complement premise is supplied. -/
theorem positive_subspace_finrank_le_index [CompleteSpace E]
    (T : E →L[ℝ] E) (hcompact : IsCompactOperator T)
    (hsym : T.toLinearMap.IsSymmetric)
    [FiniteDimensional ℝ (positiveSpectralSubspace T)]
    (W : Submodule ℝ E) [FiniteDimensional ℝ W]
    (hpositive : ∀ x ∈ W, x ≠ 0 → 0 < ⟪T x, x⟫) :
    Module.finrank ℝ W ≤ Module.finrank ℝ (positiveSpectralSubspace T) := by
  let C : W →ₗ[ℝ] positiveSpectralSubspace T :=
    (positiveSpectralSubspace T).orthogonalProjectionOnto.toLinearMap.comp W.subtype
  have hzero (x : W) (hx : C x = 0) : x = 0 := by
    by_contra hx0
    have hxE : (x : E) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hq := hpositive x x.property hxE
    change (positiveSpectralSubspace T).orthogonalProjectionOnto (x : E) = 0 at hx
    have horth := (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hx
    have hn := quadratic_nonpos_on_positive_orthogonal T hcompact hsym (x : E) horth
    linarith
  have hinj : Function.Injective C := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- A finite orthonormal family of actual positive eigenvectors spans a
strictly positive quadratic subspace. No uniform eigenvalue gap is assumed. -/
theorem quadratic_pos_on_eigen_span {ι : Type*} [Fintype ι]
    (T : E →L[ℝ] E) (v : ι → E) (hv : Orthonormal ℝ v)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) (heigen : ∀ i, T (v i) = t i • v i)
    (x : E) (hx : x ∈ Submodule.span ℝ (Set.range v)) (hx0 : x ≠ 0) :
    0 < ⟪T x, x⟫ := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hnonzero : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    rw [← hc]
    simp only [h, zero_smul, Finset.sum_const_zero]
  have heq : ⟪T (∑ i, c i • v i), ∑ i, c i • v i⟫ = ∑ i, t i * (c i) ^ 2 := by
    simp only [map_sum, map_smul, heigen, smul_smul]
    rw [hv.inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [conj_trivial]
    ring
  rw [← hc, heq]
  apply Finset.sum_pos' (fun i _ => mul_nonneg (ht i).le (sq_nonneg _))
  obtain ⟨i, hi⟩ := hnonzero
  exact ⟨i, Finset.mem_univ _, mul_pos (ht i) (sq_pos_of_ne_zero hi)⟩

/-- Compact symmetric operators retain their symmetry under an actual
operator norm limit. -/
theorem symmetric_of_tendsto {T : E →L[ℝ] E} {S : ℕ → E →L[ℝ] E}
    (hlim : Filter.Tendsto S Filter.atTop (nhds T))
    (hsym : ∀ n, (S n).toLinearMap.IsSymmetric) : T.toLinearMap.IsSymmetric := by
  intro x y
  have hleft : Filter.Tendsto (fun n => ⟪S n x, y⟫) Filter.atTop (nhds ⟪T x, y⟫) :=
    (show Continuous (fun A : E →L[ℝ] E => ⟪A x, y⟫) by fun_prop).continuousAt.tendsto.comp hlim
  have hright : Filter.Tendsto (fun n => ⟪x, S n y⟫) Filter.atTop (nhds ⟪x, T y⟫) :=
    (show Continuous (fun A : E →L[ℝ] E => ⟪x, A y⟫) by fun_prop).continuousAt.tendsto.comp hlim
  exact tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall (fun n => (hsym n x y).symm)))

/-- The positive spectral index bound is closed under operator norm limits.
Compactness and symmetry of the limit, its finite positive index set, and
its finite positive spectral dimension are all derived. -/
theorem positive_index_le_of_tendsto [CompleteSpace E]
    {T : E →L[ℝ] E} {S : ℕ → E →L[ℝ] E}
    (hlim : Filter.Tendsto S Filter.atTop (nhds T))
    (hcompact : ∀ n, IsCompactOperator (S n))
    (hsym : ∀ n, (S n).toLinearMap.IsSymmetric)
    (hfinite : ∀ n, FiniteDimensional ℝ (positiveSpectralSubspace (S n)))
    (k : ℕ) (hindex : ∀ n, Module.finrank ℝ (positiveSpectralSubspace (S n)) ≤ k) :
    FiniteDimensional ℝ (positiveSpectralSubspace T) ∧
      Module.finrank ℝ (positiveSpectralSubspace T) ≤ k := by
  classical
  have hcompactT := isCompactOperator_of_tendsto hlim (Filter.Eventually.of_forall hcompact)
  have hsymT := symmetric_of_tendsto hlim hsym
  obtain ⟨ι, b, t, heigen⟩ := exists_eigen_hilbertBasis T hcompactT hsymT
  have hcard (s : Finset ι) (hinside : ∀ i ∈ s, 0 < t i) : s.card ≤ k := by
    let v : s → E := fun i => b i
    have hv : Orthonormal ℝ v := b.orthonormal.comp _ Subtype.val_injective
    let W := Submodule.span ℝ (Set.range v)
    let _ : FiniteDimensional ℝ W := Module.Finite.span_of_finite ℝ (Set.finite_range v)
    have hpos : ∀ x ∈ W, x ≠ 0 → 0 < ⟪T x, x⟫ :=
      quadratic_pos_on_eigen_span T v hv (fun i => t i) (fun i => hinside i i.property) (fun i => heigen i)
    obtain ⟨c, hc, hpersist⟩ := positive_quadratic_subspace_persists T W hpos
    have hnear : ∀ᶠ n in Filter.atTop, ‖S n - T‖ < c := by
      simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hlim) c hc
    obtain ⟨n, hn⟩ := hnear.exists
    let _ := hfinite n
    have hpositive : ∀ x ∈ W, x ≠ 0 → 0 < ⟪S n x, x⟫ := by
      intro x hx hx0
      exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hx0))).trans_le (hpersist (S n) hn x hx)
    have hdim := (positive_subspace_finrank_le_index (S n) (hcompact n) (hsym n) W hpositive).trans (hindex n)
    have hdimW : Module.finrank ℝ W = s.card := by
      simpa only [W, Fintype.card_coe] using finrank_span_eq_card hv.linearIndependent
    rwa [hdimW] at hdim
  have hpositive : {i | 0 < t i}.Finite := by
    by_contra hinfinite
    obtain ⟨s, hs, hsize⟩ := Set.Infinite.exists_subset_card_eq hinfinite (k + 1)
    have hle := hcard s (fun i hi => hs hi)
    omega
  let s := hpositive.toFinset
  have houtside (i : ι) (hi : i ∉ s) : t i ≤ 0 :=
    le_of_not_gt (fun hp => hi (hpositive.mem_toFinset.mpr hp))
  have hsub : positiveSpectralSubspace T ≤ Submodule.span ℝ (↑(s.image b) : Set E) := by
    simpa only [Finset.coe_image] using positiveSpectralSubspace_le_finite_span T hsymT b t heigen s houtside
  have hfiniteT := Submodule.finiteDimensional_of_le hsub
  refine ⟨hfiniteT, ?_⟩
  exact (Submodule.finrank_mono hsub).trans
    ((finrank_span_finset_le_card (R := ℝ) (s.image b)).trans
      ((Finset.card_image_le).trans (hcard s (fun i hi => hpositive.mem_toFinset.mp hi))))

/-- Actual positive index greater than one gives a two-dimensional positive
witness with a uniform perturbation gap. Infinite positive dimension is
included by the explicit negation of the finite index-at-most-one condition. -/
theorem exists_two_dimensional_positive_subspace [CompleteSpace E]
    (T : E →L[ℝ] E) (hcompact : IsCompactOperator T)
    (hsym : T.toLinearMap.IsSymmetric)
    (hindex : ¬(FiniteDimensional ℝ (positiveSpectralSubspace T) ∧
      Module.finrank ℝ (positiveSpectralSubspace T) ≤ 1)) :
    ∃ W : Submodule ℝ E, FiniteDimensional ℝ W ∧ Module.finrank ℝ W = 2 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ S : E →L[ℝ] E, ‖S - T‖ < c →
        ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ ⟪S x, x⟫ := by
  classical
  obtain ⟨ι, b, t, heigen⟩ := exists_eigen_hilbertBasis T hcompact hsym
  have hexists : ∃ s : Finset ι, s.card = 2 ∧ ∀ i ∈ s, 0 < t i := by
    by_cases hfinite : {i | 0 < t i}.Finite
    · let s := hfinite.toFinset
      have houtside (i : ι) (hi : i ∉ s) : t i ≤ 0 :=
        le_of_not_gt (fun hp => hi (hfinite.mem_toFinset.mpr hp))
      have hsub : positiveSpectralSubspace T ≤ Submodule.span ℝ (↑(s.image b) : Set E) := by
        simpa only [Finset.coe_image] using positiveSpectralSubspace_le_finite_span T hsym b t heigen s houtside
      have hdim : 2 ≤ s.card := by
        by_contra hsmall
        apply hindex
        refine ⟨Submodule.finiteDimensional_of_le hsub, ?_⟩
        exact (Submodule.finrank_mono hsub).trans
          ((finrank_span_finset_le_card (R := ℝ) (s.image b)).trans
            ((Finset.card_image_le).trans (by omega)))
      obtain ⟨u, hus, hucard⟩ := Finset.exists_subset_card_eq hdim
      exact ⟨u, hucard, fun i hi => hfinite.mem_toFinset.mp (hus hi)⟩
    · obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hfinite 2
      exact ⟨s, hcard, fun i hi => hs hi⟩
  obtain ⟨s, hcard, hinside⟩ := hexists
  let v : s → E := fun i => b i
  have hv : Orthonormal ℝ v := b.orthonormal.comp _ Subtype.val_injective
  let W := Submodule.span ℝ (Set.range v)
  let hfiniteW : FiniteDimensional ℝ W := Module.Finite.span_of_finite ℝ (Set.finite_range v)
  have hdimW : Module.finrank ℝ W = 2 := by
    have h := finrank_span_eq_card hv.linearIndependent
    simpa only [W, Fintype.card_coe, hcard] using h
  have hpos : ∀ x ∈ W, x ≠ 0 → 0 < ⟪T x, x⟫ :=
    quadratic_pos_on_eigen_span T v hv (fun i => t i) (fun i => hinside i i.property) (fun i => heigen i)
  exact ⟨W, hfiniteW, hdimW, positive_quadratic_subspace_persists T W hpos⟩

/-- A genuine two-dimensional positive spectral index at the limit yields
one fixed quantitative positive plane for all sufficiently late operators. -/
theorem two_dimensional_positive_subspace_persists [CompleteSpace E]
    {T : E →L[ℝ] E} {S : ℕ → E →L[ℝ] E}
    (hlim : Filter.Tendsto S Filter.atTop (nhds T))
    (hcompact : IsCompactOperator T) (hsym : T.toLinearMap.IsSymmetric)
    (hindex : ¬(FiniteDimensional ℝ (positiveSpectralSubspace T) ∧
      Module.finrank ℝ (positiveSpectralSubspace T) ≤ 1)) :
    ∃ W : Submodule ℝ E, FiniteDimensional ℝ W ∧ Module.finrank ℝ W = 2 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
        ∀ x ∈ W, c * ‖x‖ ^ 2 ≤ ⟪S n x, x⟫ := by
  obtain ⟨W, hfinite, hdim, c, hc, hpersist⟩ := exists_two_dimensional_positive_subspace T hcompact hsym hindex
  refine ⟨W, hfinite, hdim, c, hc, ?_⟩
  have hnear : ∀ᶠ n in Filter.atTop, ‖S n - T‖ < c := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hlim) c hc
  exact hnear.mono fun n hn => hpersist (S n) hn

end Erdos1017.KernelOperator

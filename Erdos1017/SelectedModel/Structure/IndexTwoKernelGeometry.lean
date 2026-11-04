module

public import Erdos1017.SelectedModel.ZeroClass.IndexOneKernelGeometry

/-!
# Canonical index-two kernel geometry

This module defines `CanonicalIndexTwoFeature`, canonical index-two data for the
original kernel with a normalized scalar positive coordinate and a negative
feature, and constructs it from stationarity and positive index at most two by
removing both positive coordinates from the spectral feature.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- Removing the two positive coordinates leaves a negative Hilbert Gram
pairing, with the constant and scalar positive coordinates explicit. -/
theorem spectralSign_inner_eq_two_positive_sub
    {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (j k : ι) (hne : k ≠ j)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (htj : t j = ν) (htk : t k = σ)
    (hout : ∀ i, i ≠ j → i ≠ k → t i ≤ 0)
    (F G : lp (fun _ : ι => ℝ) 2) (a b : ℝ)
    (hFj : F j = Real.sqrt ν) (hGj : G j = Real.sqrt ν)
    (hFk : F k = Real.sqrt σ * a) (hGk : G k = Real.sqrt σ * b)
    (hFzero : ∀ i, t i = 0 → F i = 0) :
    ⟪spectralSign t F, G⟫ = ν + σ * a * b -
      ⟪F - lp.single 2 j (Real.sqrt ν) - lp.single 2 k (Real.sqrt σ * a),
        G - lp.single 2 j (Real.sqrt ν) - lp.single 2 k (Real.sqrt σ * b)⟫ := by
  classical
  let c : lp (fun _ : ι => ℝ) 2 := lp.single 2 j (Real.sqrt ν)
  let d (a : ℝ) : lp (fun _ : ι => ℝ) 2 := lp.single 2 k (Real.sqrt σ * a)
  let V := F - c - d a
  let W := G - c - d b
  have hVj : V j = 0 := by simp [V, c, d, hFj, hne.symm]
  have hVk : V k = 0 := by simp [V, c, d, hFk, hne]
  have hWj : W j = 0 := by simp [W, c, d, hGj, hne.symm]
  have hWk : W k = 0 := by simp [W, c, d, hGk, hne]
  have hSV : spectralSign t V = -V := by
    apply lp.ext
    funext i
    by_cases hij : i = j
    · subst i
      simp [spectralSign, signChange, hVj, htj, hν.not_gt]
    by_cases hik : i = k
    · subst i
      simp [spectralSign, signChange, hVk, htk, hσ.not_gt]
    have hti := hout i hij hik
    by_cases hi : t i < 0
    · simp [spectralSign, signChange, hi]
    have hz : t i = 0 := le_antisymm hti (le_of_not_gt hi)
    have hVi : V i = 0 := by simp [V, c, d, lp.single_apply, hij, hik, hFzero i hz]
    simp [spectralSign, signChange, hi, hVi]
  have hSc : spectralSign t c = c := by
    apply lp.ext
    funext i
    by_cases hij : i = j
    · subst i
      simp [spectralSign, signChange, c, htj, hν.not_gt]
    · simp [spectralSign, signChange, c, lp.single_apply, hij]
  have hSd : spectralSign t (d a) = d a := by
    apply lp.ext
    funext i
    by_cases hik : i = k
    · subst i
      simp [spectralSign, signChange, d, htk, hσ.not_gt]
    · simp [spectralSign, signChange, d, lp.single_apply, hik]
  have hVc : ⟪V, c⟫ = 0 := by
    rw [lp.inner_single_right, RCLike.inner_apply, hVj]; simp
  have hVd : ⟪V, d b⟫ = 0 := by
    rw [lp.inner_single_right, RCLike.inner_apply, hVk]; simp
  have hcW : ⟪c, W⟫ = 0 := by
    rw [lp.inner_single_left, RCLike.inner_apply, hWj]; simp
  have hdW : ⟪d a, W⟫ = 0 := by
    rw [lp.inner_single_left, RCLike.inner_apply, hWk]; simp
  have hcd : ⟪c, d b⟫ = 0 := by
    simp [c, d, lp.inner_single_left, RCLike.inner_apply, lp.single_apply, hne.symm]
  have hdc : ⟪d a, c⟫ = 0 := by
    simp [c, d, lp.inner_single_left, RCLike.inner_apply, lp.single_apply, hne]
  have hcc : ⟪c, c⟫ = ν := by
    simp only [c, lp.inner_single_left, RCLike.inner_apply, lp.single_apply,
      Pi.single_eq_same, conj_trivial]
    nlinarith [Real.sq_sqrt hν.le]
  have hdd : ⟪d a, d b⟫ = σ * a * b := by
    simp only [d, lp.inner_single_left, RCLike.inner_apply, lp.single_apply,
      Pi.single_eq_same, conj_trivial]
    calc
      Real.sqrt σ * b * (Real.sqrt σ * a) = (Real.sqrt σ) ^ 2 * a * b := by ring
      _ = σ * a * b := by rw [Real.sq_sqrt hσ.le]
  have hF : F = V + c + d a := by dsimp [V]; abel
  have hG : G = W + c + d b := by dsimp [W]; abel
  calc
    ⟪spectralSign t F, G⟫ = ⟪-V + c + d a, W + c + d b⟫ := by
      rw [hF, hG, map_add, map_add, hSV, hSc, hSd]
    _ = ν + σ * a * b - ⟪V, W⟫ := by
      simp only [inner_add_left, inner_add_right, inner_neg_left, hVc, hVd,
        hcW, hdW, hcd, hdc, hcc, hdd]
      ring
    _ = _ := rfl

universe u

/-- Canonical index-two data for the original kernel. The scalar positive
coordinate is normalized in L² and the negative feature obeys the same
pointwise diagonal inequality as the representation. -/
structure CanonicalIndexTwoFeature
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) {ι : Type u}
    (K : Ω → Ω → ℝ) (B ν σ : ℝ) (φ : Ω → ℝ)
    (V : Ω → lp (fun _ : ι => ℝ) 2) : Prop where
  scalar_measurable : StronglyMeasurable φ
  feature_measurable : StronglyMeasurable V
  scalar_bound : ∀ x, |φ x| ≤ B / σ
  feature_bound : ∀ x, ‖V x‖ ≤ Real.sqrt (ν + B ^ 2 / σ)
  mean_zero : (∫ x, φ x ∂μ) = 0
  square_integral : (∫ x, (φ x) ^ 2 ∂μ) = 1
  eigen_equation : ∀ᵐ x ∂μ, (∫ y, K x y * φ y ∂μ) = σ * φ x
  representation : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    K z.1 z.2 = ν + σ * φ z.1 * φ z.2 - ⟪V z.1, V z.2⟫
  diagonal : ∀ᵐ x ∂μ, ‖V x‖ ^ 2 ≤ ν + σ * (φ x) ^ 2

/-- Actual stationarity and positive index at most two yield canonical
geometry, with both positive coordinates removed from the constructed
spectral feature. No eigenbasis or diagonal bound is an input. -/
theorem exists_index_two_feature
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (ν : ℝ) (hν : 0 < ν) (hstationary : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν)
    (hfinite : FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hB)))
    (hindex : Module.finrank ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ≤ 2)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : 0 < σ) (hweigen : operator K hB0 hK hB w = σ • w) :
    ∃ (ι : Type u) (_ : Countable ι) (φ : Ω → ℝ) (V : Ω → lp (fun _ : ι => ℝ) 2),
      CanonicalIndexTwoFeature μ K B ν σ φ V := by
  classical
  let T := operator K hB0 hK hB
  let := hfinite
  have hsymmetric := operator_symmetric K hB0 hK hB hsym
  obtain ⟨ι, b, t, j, heigen, hb₀, ht₀⟩ := exists_eigen_hilbertBasis_containing T
    (operator_isCompact K hB0 hK hB) hsymmetric (Lp.const 2 μ (1 : ℝ))
    constant_one_norm ν (constant_one_eigenvector_of_stationary K hB0 hK hB ν hstationary)
  have hcount := orthonormal_countable b.orthonormal
  let := hcount
  have horth : ⟪b j, w⟫ = 0 := by rw [hb₀, inner_constant_one, hmean]
  obtain ⟨k, hne, htk⟩ := exists_eigenbasis_index_of_orthogonal_eigenvector
    T hsymmetric b t heigen j w hw horth σ hweigen
  have hout (i : ι) (hij : i ≠ j) (hik : i ≠ k) : t i ≤ 0 := by
    by_contra hi
    have hcard := positive_basis_finset_card_le T b t heigen {j, k, i} (by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · simpa [ht₀] using hν
      · simpa [htk] using hσ
      · exact lt_of_not_ge hi)
    have hthree : ({j, k, i} : Finset ι).card = 3 := by simp [hne.symm, hij.symm, hik.symm]
    change Module.finrank ℝ (positiveSpectralSubspace T) ≤ 2 at hindex
    omega
  obtain ⟨F, hF, _, hcoord, hrep⟩ := exists_bounded_spectral_feature
    K hB0 hK hB hK0 hsym b t heigen {j, k} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simpa [ht₀] using hν
      · simpa [htk] using hσ) (by
      intro i hi
      exact hout i (by aesop) (by aesop))
  have hconstant : ∀ᵐ x ∂μ, b j x = 1 := by
    rw [hb₀]
    exact Lp.coeFn_const 2 μ (1 : ℝ)
  let φ₀ : Ω → ℝ := b k
  have hφ₀ : AEStronglyMeasurable φ₀ μ := (Lp.memLp (b k)).aestronglyMeasurable
  let V₀ : Ω → lp (fun _ : ι => ℝ) 2 := fun x =>
    F x - lp.single 2 j (Real.sqrt ν) - lp.single 2 k (Real.sqrt σ * φ₀ x)
  have hV₀ : AEStronglyMeasurable V₀ μ :=
    (hF.sub aestronglyMeasurable_const).sub
      ((lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : ι => ℝ) 2 k).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_const.mul hφ₀))
  have hsign (x y : Ω) (hx : (∀ i, F x i = Real.sqrt |t i| * b i x) ∧ b j x = 1)
      (hy : (∀ i, F y i = Real.sqrt |t i| * b i y) ∧ b j y = 1) :
      ⟪spectralSign t (F x), F y⟫ = ν + σ * φ₀ x * φ₀ y - ⟪V₀ x, V₀ y⟫ := by
    apply spectralSign_inner_eq_two_positive_sub t j k hne ν σ hν hσ ht₀ htk hout
    · simp [hx.1 j, hx.2, ht₀, hν.le]
    · simp [hy.1 j, hy.2, ht₀, hν.le]
    · simp [hx.1 k, htk, hσ.le, φ₀]
    · simp [hy.1 k, htk, hσ.le, φ₀]
    · intro i hi
      simp [hx.1 i, hi]
  have hrep₀ : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      K z.1 z.2 = ν + σ * φ₀ z.1 * φ₀ z.2 - ⟪V₀ z.1, V₀ z.2⟫ := by
    filter_upwards [hrep,
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hcoord.and hconstant),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hcoord.and hconstant)]
      with z hz hx hy
    exact hz.trans (hsign _ _ hx hy)
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  have hpair : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      0 ≤ ⟪spectralSign t (F z.1), F z.2⟫ ∧ ⟪spectralSign t (F z.1), F z.2⟫ ≤ B := by
    filter_upwards [hrep, hB, hK0] with z hz hb hk
    rw [← hz]
    exact ⟨hk, (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)⟩
  have hdiag := feature_diagonal_bounds F hF (spectralSign t) 0 B hpair
  have hdiag₀ : ∀ᵐ x ∂μ, ‖V₀ x‖ ^ 2 ≤ ν + σ * (φ₀ x) ^ 2 := by
    filter_upwards [hdiag, hcoord.and hconstant] with x hx hc
    rw [hsign x x hc hc, real_inner_self_eq_norm_sq] at hx
    nlinarith [hx.1]
  have hφbound₀ : ∀ᵐ x ∂μ, |φ₀ x| ≤ B / σ := by
    simpa [φ₀, b.orthonormal.norm_eq_one k, htk, Real.norm_of_nonneg hσ.le] using
      eigenfunction_bound K hB0 hK hB (b k) (t k) (by rw [htk]; exact hσ.ne') (heigen k)
  have hbound₀ : ∀ᵐ x ∂μ, ‖V₀ x‖ ≤ Real.sqrt (ν + B ^ 2 / σ) := by
    filter_upwards [hdiag₀, hφbound₀] with x hx hb
    have hs : (φ₀ x) ^ 2 ≤ (B / σ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    have he : σ * (B / σ) ^ 2 = B ^ 2 / σ := by field_simp
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hσ.le]
  let φ₁ := hφ₀.mk φ₀
  let V₁ := hV₀.mk V₀
  have hφ₁ : StronglyMeasurable φ₁ := hφ₀.stronglyMeasurable_mk
  have hV₁ : StronglyMeasurable V₁ := hV₀.stronglyMeasurable_mk
  let good : Set Ω := {x | ‖φ₁ x‖ ≤ B / σ ∧ ‖V₁ x‖ ≤ Real.sqrt (ν + B ^ 2 / σ)}
  have hgood : MeasurableSet good :=
    (measurableSet_le hφ₁.measurable.norm measurable_const).inter
      (measurableSet_le hV₁.measurable.norm measurable_const)
  have hgood_ae : ∀ᵐ x ∂μ, x ∈ good := by
    filter_upwards [hφ₀.ae_eq_mk, hV₀.ae_eq_mk, hφbound₀, hbound₀] with x hp hv hb hc
    exact ⟨by simpa [good, φ₁, ← hp, Real.norm_eq_abs] using hb, by simpa [good, V₁, ← hv] using hc⟩
  let φ := good.indicator φ₁
  let V := good.indicator V₁
  have hφe : φ₀ =ᵐ[μ] φ := by
    filter_upwards [hφ₀.ae_eq_mk, hgood_ae] with x hx hg
    simpa [φ, Set.indicator_of_mem hg] using hx
  have hVe : V₀ =ᵐ[μ] V := by
    filter_upwards [hV₀.ae_eq_mk, hgood_ae] with x hx hg
    simpa [V, Set.indicator_of_mem hg] using hx
  refine ⟨ι, hcount, φ, V, hφ₁.indicator hgood, hV₁.indicator hgood,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ good
    · simpa [φ, Set.indicator_of_mem hx, Real.norm_eq_abs] using hx.1
    · simp [φ, Set.indicator_of_notMem hx, div_nonneg hB0 hσ.le]
  · intro x
    by_cases hx : x ∈ good
    · simpa [V, Set.indicator_of_mem hx] using hx.2
    · simp [V, Set.indicator_of_notMem hx, Real.sqrt_nonneg]
  · rw [← integral_congr_ae hφe, ← inner_constant_one, ← hb₀]
    exact b.orthonormal.inner_eq_zero hne.symm
  · have hsq : (∫ x, (φ x) ^ 2 ∂μ) = ∫ x, (φ₀ x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hφe] with x hx
      rw [hx]
    rw [hsq]
    have hi : ⟪b k, b k⟫ = (1 : ℝ) := by simp [b.orthonormal.norm_eq_one]
    rw [L2.inner_def] at hi
    simpa [φ₀, RCLike.inner_apply, pow_two] using hi
  · have he : T (b k) = σ • b k := by simpa [htk] using heigen k
    have hcoe : ⇑(onL2 K hK hB (b k)) =ᵐ[μ] σ • ⇑(b k) := by
      change ⇑(T (b k)) =ᵐ[μ] _
      rw [he]
      exact Lp.coeFn_smul σ (b k)
    have hrow : applyKernel K φ₀ = applyKernel K φ := applyKernel_congr hφe
    filter_upwards [onL2_coe K hK hB (b k), hcoe, hφe] with x hx hy hz
    change applyKernel K φ x = σ * φ x
    rw [← hrow, ← hx, hy]
    simp [φ₀, hz]
  · filter_upwards [hrep₀,
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hφe.and hVe),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hφe.and hVe)] with z hz hx hy
    simpa [← hx.1, ← hx.2, ← hy.1, ← hy.2] using hz
  · filter_upwards [hdiag₀, hφe, hVe] with x hx hp hv
    simpa [← hp, ← hv] using hx

end Erdos1017.KernelOperator

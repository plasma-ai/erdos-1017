module

public import Erdos1017.SelectedModel.StationaryFeature
public import Erdos1017.Models.Kernel.FeatureDiagonal

/-!
# Index-one kernels as constant minus Gram

Removing the sole positive constant coordinate turns the signed spectral pairing
into a constant minus a Hilbert Gram pairing, so a nonnegative stationary kernel
of positive index at most one is a constant minus a Hilbert Gram kernel with a
strongly measurable feature.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {ι : Type*} [DecidableEq ι]

/-- Removing the sole positive constant coordinate turns the signed spectral
pairing into the difference of a constant and a Hilbert Gram pairing. -/
theorem spectralSign_inner_eq_constant_sub
    (t : ι → ℝ) (j : ι) (ν : ℝ) (hν : 0 < ν) (htj : t j = ν)
    (hout : ∀ i, i ≠ j → t i ≤ 0)
    (F G : lp (fun _ : ι => ℝ) 2)
    (hFj : F j = Real.sqrt ν) (hGj : G j = Real.sqrt ν)
    (hFzero : ∀ i, t i = 0 → F i = 0) :
    ⟪spectralSign t F, G⟫ =
      ν - ⟪F - lp.single (E := fun _ : ι => ℝ) 2 j (Real.sqrt ν),
        G - lp.single (E := fun _ : ι => ℝ) 2 j (Real.sqrt ν)⟫ := by
  classical
  let c : lp (fun _ : ι => ℝ) 2 := lp.single 2 j (Real.sqrt ν)
  let V := F - c
  let W := G - c
  have hVj : V j = 0 := by simp [V, c, hFj]
  have hWj : W j = 0 := by simp [W, c, hGj]
  have hSV : spectralSign t V = -V := by
    apply lp.ext
    funext i
    by_cases hij : i = j
    · subst i
      simp [spectralSign, signChange, hVj, htj, hν.not_gt]
    · have hti := hout i hij
      by_cases hi : t i < 0
      · simp [spectralSign, signChange, hi]
      · have hz : t i = 0 := le_antisymm hti (le_of_not_gt hi)
        have hVi : V i = 0 := by simp [V, c, lp.single_apply, hij, hFzero i hz]
        simp [spectralSign, signChange, hi, hVi]
  have hSc : spectralSign t c = c := by
    apply lp.ext
    funext i
    by_cases hij : i = j
    · subst i
      simp [spectralSign, signChange, c, htj, hν.not_gt]
    · simp [spectralSign, signChange, c, lp.single_apply, hij]
  have hVc : ⟪V, c⟫ = 0 := by
    rw [lp.inner_single_right, RCLike.inner_apply, hVj]
    simp
  have hcW : ⟪c, W⟫ = 0 := by
    rw [lp.inner_single_left, RCLike.inner_apply, hWj]
    simp
  have hcc : ⟪c, c⟫ = ν := by
    rw [lp.inner_single_left, RCLike.inner_apply]
    simp only [c, lp.single_apply, Pi.single_eq_same, conj_trivial]
    calc
      Real.sqrt ν * Real.sqrt ν = (Real.sqrt ν) ^ 2 := by ring
      _ = ν := Real.sq_sqrt hν.le
  have hF : F = V + c := by simp [V]
  have hG : G = W + c := by simp [W]
  calc
    ⟪spectralSign t F, G⟫ = ⟪-V + c, W + c⟫ := by rw [hF, hG, map_add, hSV, hSc]
    _ = ν - ⟪V, W⟫ := by
      simp [inner_add_left, inner_add_right, hVc, hcW]
      rw [← real_inner_self_eq_norm_sq, hcc]
      ring
    _ = ν - ⟪F - lp.single 2 j (Real.sqrt ν),
        G - lp.single 2 j (Real.sqrt ν)⟫ := rfl

universe u

/-- A nonnegative stationary kernel of positive index at most one is a
constant minus a Hilbert Gram kernel. The feature law uses an actual strongly
measurable representative, and zero pairs coincide with equal boundary
features. -/
theorem exists_index_one_feature
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (ν : ℝ) (hν : 0 < ν) (hstationary : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν)
    (hfinite : FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hB)))
    (hindex : Module.finrank ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ≤ 1) :
    ∃ (ι : Type u) (_ : Countable ι) (V : Ω → lp (fun _ : ι => ℝ) 2),
      StronglyMeasurable V ∧
      (∀ᵐ x ∂μ, ‖V x‖ ≤ Real.sqrt ν) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ν - ⟪V z.1, V z.2⟫) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ,
        K z.1 z.2 = 0 ↔ ‖V z.1‖ = Real.sqrt ν ∧ V z.1 = V z.2) := by
  classical
  let T := operator K hB0 hK hB
  let := hfinite
  have hsymmetric := operator_symmetric K hB0 hK hB hsym
  obtain ⟨ι, b, t, j, heigen, hb₀, ht₀⟩ := exists_eigen_hilbertBasis_containing T
    (operator_isCompact K hB0 hK hB) hsymmetric (Lp.const 2 μ (1 : ℝ))
    constant_one_norm ν (constant_one_eigenvector_of_stationary K hB0 hK hB ν hstationary)
  have hcount := orthonormal_countable b.orthonormal
  let := hcount
  have hpositive : 0 < t j := ht₀.symm ▸ hν
  have hout (i : ι) (hi : i ≠ j) : t i ≤ 0 := by
    by_contra hn
    have hp : 0 < t i := lt_of_not_ge hn
    have hcard := positive_basis_finset_card_le T b t heigen {j, i} (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hpositive
      · exact hp)
    have htwo : ({j, i} : Finset ι).card = 2 := by simp [hi.symm]
    change Module.finrank ℝ (positiveSpectralSubspace T) ≤ 1 at hindex
    omega
  have houtside (i : ι) (hi : i ∉ ({j} : Finset ι)) : t i ≤ 0 :=
    hout i (by simpa using hi)
  obtain ⟨F, hF, _, hcoord, hrep⟩ := exists_bounded_spectral_feature
    K hB0 hK hB hK0 hsym b t heigen {j} (by simpa using hpositive) houtside
  have hconstant : ∀ᵐ x ∂μ, b j x = 1 := by
    rw [hb₀]
    exact Lp.coeFn_const 2 μ (1 : ℝ)
  let V₀ : Ω → lp (fun _ : ι => ℝ) 2 :=
    fun x => F x - lp.single 2 j (Real.sqrt ν)
  have hV₀ : AEStronglyMeasurable V₀ μ := hF.sub aestronglyMeasurable_const
  have hrep₀ : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      K z.1 z.2 = ν - ⟪V₀ z.1, V₀ z.2⟫ := by
    filter_upwards [hrep,
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hcoord.and hconstant),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hcoord.and hconstant)]
      with z hz hx hy
    rw [hz]
    have hFj : F z.1 j = Real.sqrt ν := by simp [hx.1 j, hx.2, ht₀, hν.le]
    have hGj : F z.2 j = Real.sqrt ν := by simp [hy.1 j, hy.2, ht₀, hν.le]
    have hFzero (i : ι) (hi : t i = 0) : F z.1 i = 0 := by simp [hx.1 i, hi]
    exact spectralSign_inner_eq_constant_sub t j ν hν ht₀ hout
      (F z.1) (F z.2) hFj hGj hFzero
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  have hpair : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      ν - B ≤ ⟪V₀ z.1, V₀ z.2⟫ ∧ ⟪V₀ z.1, V₀ z.2⟫ ≤ ν := by
    filter_upwards [hrep₀, hB, hK0] with z hz hb hk
    rw [Real.norm_eq_abs] at hb
    constructor <;> linarith [le_abs_self (K z.1 z.2)]
  have hdiag := feature_diagonal_bounds V₀ hV₀
    (LinearIsometry.id : lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] lp (fun _ : ι => ℝ) 2)
      (ν - B) ν hpair
  have hbound₀ : ∀ᵐ x ∂μ, ‖V₀ x‖ ≤ Real.sqrt ν := by
    filter_upwards [hdiag] with x hx
    simp only [LinearIsometry.id_apply] at hx
    rw [real_inner_self_eq_norm_sq] at hx
    exact (Real.le_sqrt (norm_nonneg _) hν.le).mpr hx.2
  let V := hV₀.mk V₀
  have hVm : StronglyMeasurable V := hV₀.stronglyMeasurable_mk
  have hVe : V₀ =ᵐ[μ] V := hV₀.ae_eq_mk
  have hbound : ∀ᵐ x ∂μ, ‖V x‖ ≤ Real.sqrt ν := by
    filter_upwards [hbound₀, hVe] with x hx he
    rwa [← he]
  have hrepV : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      K z.1 z.2 = ν - ⟪V z.1, V z.2⟫ := by
    filter_upwards [hrep₀,
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hVe,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hVe] with z hz hx hy
    simpa [← hx, ← hy] using hz
  refine ⟨ι, hcount, V, hVm, hbound, hrepV, ?_⟩
  filter_upwards [hrepV,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hbound,
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hbound] with z hz hx hy
  constructor
  · intro hzero
    have hinner : ⟪V z.1, V z.2⟫ = ν := by linarith
    have hsqx : ‖V z.1‖ ^ 2 ≤ ν := (Real.le_sqrt (norm_nonneg _) hν.le).mp hx
    have hsqy : ‖V z.2‖ ^ 2 ≤ ν := (Real.le_sqrt (norm_nonneg _) hν.le).mp hy
    have hdiff : ‖V z.1 - V z.2‖ ^ 2 =
        ‖V z.1‖ ^ 2 + ‖V z.2‖ ^ 2 - 2 * ⟪V z.1, V z.2⟫ := by
      rw [norm_sub_sq_real]
      ring
    have heq : V z.1 = V z.2 := by
      have hn : ‖V z.1 - V z.2‖ ^ 2 = 0 := by
        rw [hdiff, hinner]
        nlinarith [sq_nonneg ‖V z.1 - V z.2‖]
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
    refine ⟨?_, heq⟩
    have hne : ‖V z.1‖ ^ 2 = ν := by
      rw [← heq] at hinner
      simpa only [real_inner_self_eq_norm_sq] using hinner
    nlinarith [norm_nonneg (V z.1), Real.sqrt_nonneg ν, Real.sq_sqrt hν.le]
  · rintro ⟨hboundary, heq⟩
    rw [hz, ← heq, real_inner_self_eq_norm_sq, hboundary, Real.sq_sqrt hν.le]
    ring

end Erdos1017.KernelOperator

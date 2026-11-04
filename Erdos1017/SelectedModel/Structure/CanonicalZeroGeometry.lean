module

public import Erdos1017.SelectedModel.Structure.CanonicalFeatureRows
public import Erdos1017.SelectedModel.Structure.OrderedZeroTripleGeometry

/-!
# Canonical zero geometry of the shifted kernel

This module defines the canonical continuous-feature representative
`canonicalPairing` and the structure `CanonicalZeroGeometry` holding at every
pair of a set, with endpoint closure, strict-triple interpolation and
equal-scalar identities, and constructs it on a measurable conull set together
with the row factorization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

universe u

variable {Ω : Type u} {ι : Type u}

/-- The canonical continuous-feature representative of the shifted kernel. -/
def canonicalPairing (ν σ : ℝ) (φ : Ω → ℝ)
    (V : Ω → lp (fun _ : ι => ℝ) 2) (x y : Ω) : ℝ :=
  ν + σ * φ x * φ y - ⟪V x, V y⟫

/-- Canonical geometry on a set of actual points, including every pair in
that set rather than only almost every pair. -/
structure CanonicalZeroGeometry (ν σ : ℝ) (φ : Ω → ℝ)
    (V : Ω → lp (fun _ : ι => ℝ) 2) (S : Set Ω) : Prop where
  constant_nonneg : 0 ≤ ν
  eigenvalue_pos : 0 < σ
  diagonal : ∀ x ∈ S, ‖V x‖ ^ 2 ≤ ν + σ * (φ x) ^ 2
  nonnegative : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ canonicalPairing ν σ φ V x y

variable {ν σ : ℝ} {φ : Ω → ℝ} {V : Ω → lp (fun _ : ι => ℝ) 2} {S : Set Ω}

/-- Weakly ordered consecutive zero pairs close at their endpoints. -/
theorem CanonicalZeroGeometry.ordered_zero_endpoint
    (h : CanonicalZeroGeometry ν σ φ V S) {x y z : Ω}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxyOrder : φ x ≤ φ y) (hyzOrder : φ y ≤ φ z)
    (hxy : canonicalPairing ν σ φ V x y = 0)
    (hyz : canonicalPairing ν σ φ V y z = 0) :
    canonicalPairing ν σ φ V x z = 0 := by
  have hs : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt h.eigenvalue_pos.le
  have hν : (Real.sqrt ν) ^ 2 = ν := Real.sq_sqrt h.constant_nonneg
  have hscale (a b : ℝ) : (Real.sqrt ν) ^ 2 +
      (Real.sqrt σ * a) * (Real.sqrt σ * b) = ν + σ * a * b := by
    calc
      _ = (Real.sqrt ν) ^ 2 + (Real.sqrt σ) ^ 2 * a * b := by ring
      _ = _ := by rw [hν, hs]
  have hxz := h.nonnegative x hx z hz
  have he := OrderedZeroTripleGeometry.scalar_ordered_zero_endpoint
    (Real.sqrt ν) (Real.sqrt σ * φ x) (Real.sqrt σ * φ y) (Real.sqrt σ * φ z)
    (V x) (V y) (V z)
    (mul_le_mul_of_nonneg_left hxyOrder (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_left hyzOrder (Real.sqrt_nonneg _))
    (by simpa only [mul_pow, hs, hν] using h.diagonal x hx)
    (by simpa only [mul_pow, hs, hν] using h.diagonal y hy)
    (by simpa only [mul_pow, hs, hν] using h.diagonal z hz)
    (by rw [hscale]; dsimp [canonicalPairing] at hxy; linarith)
    (by rw [hscale]; dsimp [canonicalPairing] at hyz; linarith)
    (by rw [hscale]; dsimp [canonicalPairing] at hxz; linarith)
  rw [hscale] at he
  dsimp [canonicalPairing]
  linarith

/-- Strictly ordered consecutive zero pairs force all diagonal defects to
vanish and give the explicit interpolation of the negative feature. -/
theorem CanonicalZeroGeometry.strict_zero_triple
    (h : CanonicalZeroGeometry ν σ φ V S) {x y z : Ω}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxyOrder : φ x < φ y) (hyzOrder : φ y < φ z)
    (hxy : canonicalPairing ν σ φ V x y = 0)
    (hyz : canonicalPairing ν σ φ V y z = 0) :
    canonicalPairing ν σ φ V x z = 0 ∧
      ‖V x‖ ^ 2 = ν + σ * (φ x) ^ 2 ∧
      ‖V y‖ ^ 2 = ν + σ * (φ y) ^ 2 ∧
      ‖V z‖ ^ 2 = ν + σ * (φ z) ^ 2 ∧
      V y = ((φ z - φ y) / (φ z - φ x)) • V x +
        ((φ y - φ x) / (φ z - φ x)) • V z := by
  have hs : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt h.eigenvalue_pos.le
  have hsp : 0 < Real.sqrt σ := Real.sqrt_pos.mpr h.eigenvalue_pos
  have hν : (Real.sqrt ν) ^ 2 = ν := Real.sq_sqrt h.constant_nonneg
  have hscale (a b : ℝ) : (Real.sqrt ν) ^ 2 +
      (Real.sqrt σ * a) * (Real.sqrt σ * b) = ν + σ * a * b := by
    calc
      _ = (Real.sqrt ν) ^ 2 + (Real.sqrt σ) ^ 2 * a * b := by ring
      _ = _ := by rw [hν, hs]
  have hxz := h.nonnegative x hx z hz
  obtain ⟨he, hdx, hdy, hdz, hv⟩ := OrderedZeroTripleGeometry.scalar_strict_zero_triple
    (Real.sqrt ν) (Real.sqrt σ * φ x) (Real.sqrt σ * φ y) (Real.sqrt σ * φ z)
    (V x) (V y) (V z)
    (mul_lt_mul_of_pos_left hxyOrder hsp) (mul_lt_mul_of_pos_left hyzOrder hsp)
    (by simpa only [mul_pow, hs, hν] using h.diagonal x hx)
    (by simpa only [mul_pow, hs, hν] using h.diagonal y hy)
    (by simpa only [mul_pow, hs, hν] using h.diagonal z hz)
    (by rw [hscale]; dsimp [canonicalPairing] at hxy; linarith)
    (by rw [hscale]; dsimp [canonicalPairing] at hyz; linarith)
    (by rw [hscale]; dsimp [canonicalPairing] at hxz; linarith)
  refine ⟨h.ordered_zero_endpoint hx hy hz hxyOrder.le hyzOrder.le hxy hyz,
    by simpa only [mul_pow, hs, hν] using hdx,
    by simpa only [mul_pow, hs, hν] using hdy,
    by simpa only [mul_pow, hs, hν] using hdz, ?_⟩
  have hratio (a b c d : ℝ) :
      (Real.sqrt σ * a - Real.sqrt σ * b) / (Real.sqrt σ * c - Real.sqrt σ * d) =
        (a - b) / (c - d) := by
    rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hsp.ne']
  simpa only [hratio] using hv

/-- Equal scalar coordinates joined by a canonical zero pair have equal
negative features and zero diagonal defects at both endpoints. -/
theorem CanonicalZeroGeometry.equal_scalar_zero_pair
    (h : CanonicalZeroGeometry ν σ φ V S) {x y : Ω}
    (hx : x ∈ S) (hy : y ∈ S) (heq : φ x = φ y)
    (hxy : canonicalPairing ν σ φ V x y = 0) :
    V x = V y ∧ ‖V x‖ ^ 2 = ν + σ * (φ x) ^ 2 ∧
      ‖V y‖ ^ 2 = ν + σ * (φ y) ^ 2 := by
  let U : ℝ := Real.sqrt (ν + σ * (φ x) ^ 2)
  have hnonneg : 0 ≤ ν + σ * (φ x) ^ 2 :=
    add_nonneg h.constant_nonneg (mul_nonneg h.eigenvalue_pos.le (sq_nonneg _))
  have hUx : ‖U‖ ^ 2 = ν + σ * (φ x) ^ 2 := by
    dsimp [U]
    rw [sq_abs, Real.sq_sqrt hnonneg]
  have hUy : ‖U‖ ^ 2 = ν + σ * (φ y) ^ 2 := by rw [hUx, heq]
  have hinner : ⟪U, U⟫ = ⟪V x, V y⟫ := by
    rw [real_inner_self_eq_norm_sq, hUx]
    dsimp [canonicalPairing] at hxy
    rw [← heq] at hxy
    nlinarith
  obtain ⟨hV, hdx, hdy⟩ := OrderedZeroTripleGeometry.equal_positive_zero_pair
    U U (V x) (V y) rfl (by rw [hUx]; exact h.diagonal x hx)
    (by rw [hUy]; exact h.diagonal y hy) hinner
  exact ⟨hV, hdx.trans hUx, hdy.trans hUy⟩

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Countable ι] {K : Ω → Ω → ℝ} {B : ℝ}

/-- The actual joint feature law makes the canonical pairing nonnegative
at every pair in one measurable conull set. The original kernel is retained
almost everywhere, without a pointwise claim about its null-set values. -/
theorem CanonicalIndexTwoFeature.exists_conull_zero_geometry
    (h : CanonicalIndexTwoFeature μ K B ν σ φ V) (hν : 0 ≤ ν) (hσ : 0 < σ)
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧
      CanonicalZeroGeometry ν σ φ V S ∧
      (∀ᵐ p ∂μ.prod μ, canonicalPairing ν σ φ V p.1 p.2 = K p.1 p.2) := by
  classical
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  let Ψ : Ω → ℝ × lp (fun _ : ι => ℝ) 2 := fun x => (φ x, V x)
  have hΨ : StronglyMeasurable Ψ := h.scalar_measurable.prodMk h.feature_measurable
  let law := μ.map Ψ
  let q (a b : ℝ × lp (fun _ : ι => ℝ) 2) : ℝ :=
    ν + σ * a.1 * b.1 - ⟪a.2, b.2⟫
  have hqc (a : ℝ × lp (fun _ : ι => ℝ) 2) : Continuous (q a) := by
    exact (continuous_const.add ((continuous_const.mul continuous_fst))).sub
      (continuous_const.inner continuous_snd)
  have hqc' (b : ℝ × lp (fun _ : ι => ℝ) 2) : Continuous (fun a => q a b) := by
    exact (continuous_const.add ((continuous_const.mul continuous_fst).mul continuous_const)).sub
      (continuous_snd.inner continuous_const)
  have hpair : ∀ᵐ p ∂μ.prod μ, 0 ≤ q (Ψ p.1) (Ψ p.2) := by
    filter_upwards [h.representation, hK0] with p hp hk
    change 0 ≤ ν + σ * φ p.1 * φ p.2 - ⟪V p.1, V p.2⟫
    rwa [← hp]
  have hrow : ∀ᵐ x ∂μ, ∀ b ∈ law.support, 0 ≤ q (Ψ x) b := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpair] with x hx
    have hc : IsClosed {b | 0 ≤ q (Ψ x) b} := isClosed_le continuous_const (hqc _)
    have ha : {b | 0 ≤ q (Ψ x) b} ∈ ae law :=
      (ae_map_iff hΨ.aemeasurable hc.measurableSet).mpr hx
    exact fun _ hb => Measure.support_subset_of_isClosed hc ha hb
  have hsupport_pair (a b : ℝ × lp (fun _ : ι => ℝ) 2)
      (ha : a ∈ law.support) (hb : b ∈ law.support) : 0 ≤ q a b := by
    have hc : IsClosed {a | 0 ≤ q a b} := isClosed_le continuous_const (hqc' b)
    have hz : ∀ᵐ x ∂μ, 0 ≤ q (Ψ x) b := hrow.mono fun _ hx => hx b hb
    have hmap : {a | 0 ≤ q a b} ∈ ae law :=
      (ae_map_iff hΨ.aemeasurable hc.measurableSet).mpr hz
    exact Measure.support_subset_of_isClosed hc hmap ha
  have hsupport : ∀ᵐ x ∂μ, Ψ x ∈ law.support :=
    ae_of_ae_map hΨ.aemeasurable Measure.support_mem_ae
  let T := {x | Ψ x ∈ law.support ∧ ‖V x‖ ^ 2 ≤ ν + σ * (φ x) ^ 2}
  have hTae : ∀ᵐ x ∂μ, x ∈ T := hsupport.and h.diagonal
  let S := (toMeasurable μ Tᶜ)ᶜ
  have hS : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    change μ Sᶜ = 0
    simp only [S, compl_compl, measure_toMeasurable]
    exact hTae
  have hST : S ⊆ T := by
    intro x hx
    by_contra hn
    exact hx (subset_toMeasurable μ Tᶜ hn)
  refine ⟨S, hS, hSae, ⟨hν, hσ, fun x hx => (hST hx).2, ?_⟩, ?_⟩
  · intro x hx y hy
    exact hsupport_pair (Ψ x) (Ψ y) (hST hx).1 (hST hy).1
  · exact h.representation.mono (fun _ hp => hp.symm)

/-- The all-pair zero geometry and the actual row factorization can be
chosen on the same measurable conull set. -/
theorem CanonicalIndexTwoFeature.exists_conull_zero_geometry_and_rows
    (h : CanonicalIndexTwoFeature μ K B ν σ φ V) (hν : 0 ≤ ν) (hσ : 0 < σ)
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (R : Ω → Lp ℝ 2 μ) (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧
      CanonicalZeroGeometry ν σ φ V S ∧
      (∀ᵐ p ∂μ.prod μ, canonicalPairing ν σ φ V p.1 p.2 = K p.1 p.2) ∧
      (∀ x ∈ S, (R x : Ω → ℝ) =ᵐ[μ] K x) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        (K x =ᵐ[μ] K y) ↔ φ x = φ y ∧ V x = V y) ∧
      (∀ x ∈ S, ∀ y ∈ S, R x = R y ↔ φ x = φ y ∧ V x = V y) := by
  obtain ⟨S₀, hS₀, hS₀ae, hgeometry, hidentity⟩ := h.exists_conull_zero_geometry hν hσ hK0
  obtain ⟨T, hT, hTae, hrows, hiff, hmap⟩ := h.exists_conull_rowMap_feature_iff hσ R hrow
  refine ⟨S₀ ∩ T, hS₀.inter hT, hS₀ae.and hTae,
    ⟨hν, hσ, fun x hx => hgeometry.diagonal x hx.1,
      fun x hx y hy => hgeometry.nonnegative x hx.1 y hy.1⟩,
    hidentity, fun x hx => hrows x hx.2,
    fun x hx y hy => hiff x hx.2 y hy.2, fun x hx y hy => hmap x hx.2 y hy.2⟩

end Erdos1017.KernelOperator

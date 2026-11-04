module

public import Erdos1017.SelectedModel.Structure.IndexTwoKernelGeometry
public import Erdos1017.SelectedModel.Structure.KernelRowMap

/-!
# Kernel rows through canonical coordinates

On one measurable conull set, equality of the original kernel rows is exactly
equality of both canonical coordinates, and any `L²` row map factors through the
canonical coordinates there.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type u} [Countable ι] {K : Ω → Ω → ℝ} {B ν σ : ℝ}
  {φ : Ω → ℝ} {V : Ω → lp (fun _ : ι => ℝ) 2}

/-- On one measurable conull set, equality of the original kernel rows is
exactly equality of both canonical coordinates. Support membership removes
negative feature directions invisible to almost every other feature. -/
theorem CanonicalIndexTwoFeature.exists_conull_row_feature_iff
    (h : CanonicalIndexTwoFeature μ K B ν σ φ V) (hσ : 0 < σ) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧
      ∀ x ∈ S, ∀ y ∈ S,
        (K x =ᵐ[μ] K y) ↔ φ x = φ y ∧ V x = V y := by
  classical
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  have hsupport : ∀ᵐ x ∂μ, V x ∈ (μ.map V).support :=
    ae_of_ae_map h.feature_measurable.aemeasurable Measure.support_mem_ae
  let P (x : Ω) : Prop :=
    (∫ z, K x z * φ z ∂μ) = σ * φ x ∧
    (∀ᵐ z ∂μ, K x z = ν + σ * φ x * φ z - ⟪V x, V z⟫) ∧
    V x ∈ (μ.map V).support
  have hP : ∀ᵐ x ∂μ, P x := by
    filter_upwards [h.eigen_equation, Measure.ae_ae_of_ae_prod h.representation,
      hsupport] with x he hr hs
    exact ⟨he, hr, hs⟩
  let S := (toMeasurable μ {x | ¬P x})ᶜ
  have hS : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    change μ Sᶜ = 0
    simp only [S, compl_compl, measure_toMeasurable]
    exact hP
  have hSP (x : Ω) (hx : x ∈ S) : P x := by
    by_contra hn
    exact hx (subset_toMeasurable μ {x | ¬P x} hn)
  refine ⟨S, hS, hSae, ?_⟩
  intro x hx y hy
  have hpx := hSP x hx
  have hpy := hSP y hy
  constructor
  · intro hrows
    have hscalar : φ x = φ y := by
      have hi : (∫ z, K x z * φ z ∂μ) = ∫ z, K y z * φ z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hrows] with z hz
        rw [hz]
      rw [hpx.1, hpy.1] at hi
      exact (mul_left_cancel₀ hσ.ne') hi
    have hzero : ∀ᵐ z ∂μ, ⟪V x - V y, V z⟫ = 0 := by
      filter_upwards [hrows, hpx.2.1, hpy.2.1] with z hz hxz hyz
      rw [hxz, hyz, hscalar] at hz
      rw [inner_sub_left]
      linarith
    have hc : IsClosed {v : lp (fun _ : ι => ℝ) 2 | ⟪V x - V y, v⟫ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hmap : {v : lp (fun _ : ι => ℝ) 2 | ⟪V x - V y, v⟫ = 0} ∈ ae (μ.map V) :=
      (ae_map_iff h.feature_measurable.aemeasurable hc.measurableSet).mpr hzero
    have hzx : ⟪V x - V y, V x⟫ = 0 :=
      Measure.support_subset_of_isClosed hc hmap hpx.2.2
    have hzy : ⟪V x - V y, V y⟫ = 0 :=
      Measure.support_subset_of_isClosed hc hmap hpy.2.2
    refine ⟨hscalar, sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp ?_)⟩
    rw [inner_sub_right, hzx, hzy, sub_self]
  · rintro ⟨hscalar, hfeature⟩
    filter_upwards [hpx.2.1, hpy.2.1] with z hxz hyz
    rw [hxz, hyz, hscalar, hfeature]

/-- Any actual L² row map factors through the canonical coordinates on a
single common measurable conull set, with both original row identities
and the pointwise equivalence retained. -/
theorem CanonicalIndexTwoFeature.exists_conull_rowMap_feature_iff
    (h : CanonicalIndexTwoFeature μ K B ν σ φ V) (hσ : 0 < σ)
    (R : Ω → Lp ℝ 2 μ) (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧
      (∀ x ∈ S, (R x : Ω → ℝ) =ᵐ[μ] K x) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        (K x =ᵐ[μ] K y) ↔ φ x = φ y ∧ V x = V y) ∧
      (∀ x ∈ S, ∀ y ∈ S, R x = R y ↔ φ x = φ y ∧ V x = V y) := by
  obtain ⟨S₀, hS₀, hS₀ae, hiff⟩ := h.exists_conull_row_feature_iff hσ
  let T := (toMeasurable μ {x | ¬((R x : Ω → ℝ) =ᵐ[μ] K x)})ᶜ
  have hT : MeasurableSet T := (measurableSet_toMeasurable _ _).compl
  have hTae : ∀ᵐ x ∂μ, x ∈ T := by
    change μ Tᶜ = 0
    simp only [T, compl_compl, measure_toMeasurable]
    exact hrow
  have hTrow (x : Ω) (hx : x ∈ T) : (R x : Ω → ℝ) =ᵐ[μ] K x := by
    by_contra hn
    exact hx (subset_toMeasurable μ {x | ¬((R x : Ω → ℝ) =ᵐ[μ] K x)} hn)
  refine ⟨S₀ ∩ T, hS₀.inter hT, hS₀ae.and hTae,
    fun x hx => hTrow x hx.2, fun x hx y hy => hiff x hx.1 y hy.1, ?_⟩
  intro x hx y hy
  rw [← hiff x hx.1 y hy.1]
  constructor
  · intro heq
    have hr : (R x : Ω → ℝ) =ᵐ[μ] (R y : Ω → ℝ) := by rw [heq]
    exact (hTrow x hx.2).symm.trans (hr.trans (hTrow y hy.2))
  · intro heq
    exact Lp.ext ((hTrow x hx.2).trans (heq.trans (hTrow y hy.2).symm))

end Erdos1017.KernelOperator

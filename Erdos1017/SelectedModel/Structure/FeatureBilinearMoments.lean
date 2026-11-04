module

public import Erdos1017.SelectedModel.Structure.IntegrableDegreeCone
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bilinear feature moments and barycenters

A continuous bilinear form on two independent integrable vector inputs has an
integrable product whose integral is the form at the two Bochner barycenters,
which identifies the mixed kernel integral, the kernel energy and the degree
coordinate with weighted feature barycenters.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.KernelOperator

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [CompleteSpace E] in
/-- A continuous bilinear form on two independent integrable vector
inputs has an integrable scalar product. -/
theorem integrable_bilinear_feature_product (B : E →L[ℝ] E →L[ℝ] ℝ)
    (U V : Ω → E) (hU : Integrable U μ) (hV : Integrable V μ) :
    Integrable (fun p : Ω × Ω => B (U p.1) (V p.2)) (μ.prod μ) := by
  apply ((hU.norm.mul_prod hV.norm).const_mul ‖B‖).mono'
    (B.aestronglyMeasurable_comp₂ hU.aestronglyMeasurable.comp_fst
      hV.aestronglyMeasurable.comp_snd)
  exact Eventually.of_forall (fun p => (B.le_opNorm₂ (U p.1) (V p.2)).trans_eq (by ring))

/-- The actual independent bilinear integral is the bilinear form of
the two Bochner barycenters. Integrability licenses both Fubini and
commuting the continuous linear maps with the integrals. -/
theorem bilinear_feature_product_integral (B : E →L[ℝ] E →L[ℝ] ℝ)
    (U V : Ω → E) (hU : Integrable U μ) (hV : Integrable V μ) :
    (∫ p : Ω × Ω, B (U p.1) (V p.2) ∂μ.prod μ) =
      B (∫ x, U x ∂μ) (∫ x, V x ∂μ) := by
  rw [integral_prod _ (integrable_bilinear_feature_product B U V hU hV)]
  simp_rw [(B _).integral_comp_comm hV]
  exact (B.flip (∫ x, V x ∂μ)).integral_comp_comm hU

/-- An actual bilinear feature representation identifies the original
physical mixed kernel integral with the weighted feature barycenters.
The first kernelPairing input occupies the second physical coordinate. -/
theorem kernelPairing_eq_bilinear_barycenters
    (K : Ω → Ω → ℝ) (F : Ω → E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (f g : Ω → ℝ)
    (hf : Integrable (fun x => f x • F x) μ)
    (hg : Integrable (fun x => g x • F x) μ) :
    kernelPairing (μ := μ) K f g =
      B (∫ x, g x • F x ∂μ) (∫ x, f x • F x ∂μ) := by
  calc
    _ = ∫ p : Ω × Ω, B (g p.1 • F p.1) (f p.2 • F p.2) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [hrep] with p hp
      rw [hp]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    _ = _ := bilinear_feature_product_integral B _ _ hg hf

/-- The quadratic form is evaluated at the Bochner barycenter of the
signed feature density; no expectation of pointwise quadratic values appears. -/
theorem kernelEnergy_eq_bilinear_barycenter
    (K : Ω → Ω → ℝ) (F : Ω → E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (f : Ω → ℝ) (hf : Integrable (fun x => f x • F x) μ) :
    kernelEnergy (μ := μ) K f = B (∫ x, f x • F x ∂μ) (∫ x, f x • F x ∂μ) :=
  kernelPairing_eq_bilinear_barycenters K F B hrep f f hf hf

omit [IsProbabilityMeasure μ] in
/-- The original degree coordinate is the continuous linear coordinate
of the same actual weighted feature barycenter. -/
theorem integral_feature_degree (F : Ω → E) (ℓ : E →L[ℝ] ℝ)
    (f : Ω → ℝ) (hf : Integrable (fun x => f x • F x) μ) :
    (∫ x, ℓ (F x) * f x ∂μ) = ℓ (∫ x, f x • F x ∂μ) := by
  rw [← ℓ.integral_comp_comm hf]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [map_smul, smul_eq_mul]; ring)

end Erdos1017.KernelOperator

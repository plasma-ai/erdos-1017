module

public import Erdos1017.SelectedModel.Structure.FeatureBilinearMoments
public import Erdos1017.SelectedModel.Flows.MissingFlowDensity

/-!
# Feature moments of flow directions

The feature barycenter of a flow direction is the integral of feature
displacements against the flow density, the kernel pairing of two directions is
the bilinear integral of their pair displacements, and the energy of a sum
expands with the exact mixed term.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.MissingFlow

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original oriented feature displacement of a physical pair. -/
def featureDifference (F : Ω → E) (p : Ω × Ω) : E := F p.1 - F p.2

omit [CompleteSpace E] in
/-- Bounded physical features make the feature-weighted density of any
integrable actual flow Bochner integrable. -/
theorem integrable_weighted_featureDifference
    (F : Ω → E) (hF : AEStronglyMeasurable F μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) :
    Integrable (fun p => q p • featureDifference F p) (μ.prod μ) := by
  have h₁ : Integrable (fun p : Ω × Ω => q p • F p.1) (μ.prod μ) :=
    hq.smul_bdd C hF.comp_fst (Measure.quasiMeasurePreserving_fst.ae hC)
  have h₂ : Integrable (fun p : Ω × Ω => q p • F p.2) (μ.prod μ) :=
    hq.smul_bdd C hF.comp_snd (Measure.quasiMeasurePreserving_snd.ae hC)
  convert h₁.sub h₂ using 1
  funext p
  simp only [featureDifference, smul_sub, Pi.sub_apply]

/-- The feature barycenter of the actual receipt-minus-supply direction
is exactly the integral of original feature displacements against q.
Both marginal identities are proved by vector-valued Fubini. -/
theorem integral_direction_smul_feature
    (F : Ω → E) (hF : AEStronglyMeasurable F μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) :
    (∫ x, direction μ q x • F x ∂μ) =
      ∫ p, q p • featureDifference F p ∂μ.prod μ := by
  have h₁ : Integrable (fun p : Ω × Ω => q p • F p.1) (μ.prod μ) :=
    hq.smul_bdd C hF.comp_fst (Measure.quasiMeasurePreserving_fst.ae hC)
  have h₂ : Integrable (fun p : Ω × Ω => q p • F p.2) (μ.prod μ) :=
    hq.smul_bdd C hF.comp_snd (Measure.quasiMeasurePreserving_snd.ae hC)
  have hreceipt : (∫ x, receipt μ q x • F x ∂μ) = ∫ p, q p • F p.1 ∂μ.prod μ := by
    rw [integral_prod _ h₁]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (integral_smul_const (fun y => q (x, y)) (F x)).symm)
  have hsupply : (∫ x, supply μ q x • F x ∂μ) = ∫ p, q p • F p.2 ∂μ.prod μ := by
    rw [integral_prod_symm _ h₂]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (integral_smul_const (fun y => q (y, x)) (F x)).symm)
  have hrF : Integrable (fun x => receipt μ q x • F x) μ :=
    (integrable_marginals hq).1.smul_bdd C hF hC
  have hsF : Integrable (fun x => supply μ q x • F x) μ :=
    (integrable_marginals hq).2.smul_bdd C hF hC
  simp only [direction, featureDifference, sub_smul, smul_sub]
  rw [integral_sub hrF hsF, integral_sub h₁ h₂, hreceipt, hsupply]

/-- Actual original kernel pairing between two flow directions is the
bilinear product integral of their original pair displacements. The
second direction occupies the first product coordinate, as in kernelPairing. -/
theorem kernelPairing_directions_eq_feature_integral
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : AEStronglyMeasurable F μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ)) :
    KernelOperator.kernelPairing (μ := μ) K (direction μ q) (direction μ r) =
      ∫ p : (Ω × Ω) × (Ω × Ω),
        B (r p.1 • featureDifference F p.1) (q p.2 • featureDifference F p.2)
          ∂(μ.prod μ).prod (μ.prod μ) := by
  rw [KernelOperator.kernelPairing_eq_bilinear_barycenters K F B hrep _ _
    ((integrable_direction hq).smul_bdd C hF hC) ((integrable_direction hr).smul_bdd C hF hC),
    integral_direction_smul_feature F hF hC r hr, integral_direction_smul_feature F hF hC q hq]
  exact (KernelOperator.bilinear_feature_product_integral B _ _
    (integrable_weighted_featureDifference F hF hC r hr)
    (integrable_weighted_featureDifference F hF hC q hq)).symm

/-- Adding two actual product densities expands the original direction's
quadratic energy with the exact mixed term. The input densities may be signed. -/
theorem kernelEnergy_direction_add_eq
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : AEStronglyMeasurable F μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ)) :
    KernelOperator.kernelEnergy (μ := μ) K (direction μ (q + r)) =
      KernelOperator.kernelEnergy (μ := μ) K (direction μ q) +
        2 * KernelOperator.kernelPairing (μ := μ) K (direction μ q) (direction μ r) +
          KernelOperator.kernelEnergy (μ := μ) K (direction μ r) := by
  have hqF : Integrable (fun x => direction μ q x • F x) μ :=
    (integrable_direction hq).smul_bdd C hF hC
  have hrF : Integrable (fun x => direction μ r x • F x) μ :=
    (integrable_direction hr).smul_bdd C hF hC
  have hsumF : Integrable (fun x => direction μ (q + r) x • F x) μ :=
    (integrable_direction (hq.add hr)).smul_bdd C hF hC
  have hadd : (∫ x, direction μ (q + r) x • F x ∂μ) =
      (∫ x, direction μ q x • F x ∂μ) + ∫ x, direction μ r x • F x ∂μ := by
    calc
      _ = ∫ x, direction μ q x • F x + direction μ r x • F x ∂μ := by
        apply integral_congr_ae
        filter_upwards [direction_add hq hr] with x hx
        rw [hx, Pi.add_apply, add_smul]
      _ = _ := integral_add hqF hrF
  rw [KernelOperator.kernelEnergy_eq_bilinear_barycenter K F B hrep _ hsumF, hadd,
    KernelOperator.kernelEnergy_eq_bilinear_barycenter K F B hrep _ hqF,
    KernelOperator.kernelEnergy_eq_bilinear_barycenter K F B hrep _ hrF,
    KernelOperator.kernelPairing_eq_bilinear_barycenters K F B hrep _ _ hqF hrF]
  simp only [map_add, add_apply]
  rw [hsym (∫ x, direction μ q x • F x ∂μ) (∫ x, direction μ r x • F x ∂μ)]
  ring

end Erdos1017.MissingFlow

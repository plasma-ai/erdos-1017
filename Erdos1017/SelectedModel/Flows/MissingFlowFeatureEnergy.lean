module

public import Erdos1017.SelectedModel.Flows.MissingFlowFeatureMoments
public import Erdos1017.SelectedModel.Structure.FeatureTangentTransfer

/-!
# Nonnegative kernel energy of oriented flows

Nonnegative oriented zero-pair flow densities have nonnegative mutual kernel
energy, every integrable oriented missing flow has nonnegative shifted
self-energy, and restricting to a nonnegative subdensity cannot increase the
energy (`kernelEnergy_direction_mono`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.MissingFlow

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual nonnegative oriented zero-pair flow densities have nonnegative
mutual original kernel energy. Feature support membership is licensed
under the original physical product measure before integrating. -/
theorem kernelPairing_directions_nonnegative
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : StronglyMeasurable F) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (ℓ : E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (hdiag : ∀ᵐ x ∂μ, 0 ≤ B (F x) (F x))
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      (∫ x, ℓ (F x) * f x ∂μ) = 0 → KernelOperator.kernelEnergy (μ := μ) K f ≤ 0)
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hr0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ r p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2))
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2)) :
    0 ≤ KernelOperator.kernelPairing (μ := μ) K (direction μ q) (direction μ r) := by
  have hsupport : ∀ᵐ x ∂μ, F x ∈ (μ.map F).support :=
    ae_of_ae_map hF.aemeasurable Measure.support_mem_ae
  have hgood : ∀ᵐ p ∂μ.prod μ,
      (F p.1 ∈ (μ.map F).support ∧ F p.2 ∈ (μ.map F).support) ∧
      (0 ≤ B (F p.1) (F p.1) ∧ 0 ≤ B (F p.2) (F p.2)) ∧
      K p.1 p.2 = B (F p.1) (F p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsupport,
      Measure.quasiMeasurePreserving_snd.ae hsupport,
      Measure.quasiMeasurePreserving_fst.ae hdiag,
      Measure.quasiMeasurePreserving_snd.ae hdiag, hrep] with p h₁ h₂ h₃ h₄ h₅
    exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅⟩
  rw [kernelPairing_directions_eq_feature_integral K F hF.aestronglyMeasurable hC B hrep q r hq hr]
  apply integral_nonneg_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hgood.and (hr0.and hrs)),
    Measure.quasiMeasurePreserving_snd.ae (hgood.and (hq0.and hqs))] with p hp hp'
  by_cases hrzero : r p.1 = 0
  · simp only [hrzero, zero_smul, map_zero, zero_apply, Pi.zero_apply, le_refl]
  by_cases hqzero : q p.2 = 0
  · simp only [hqzero, zero_smul, map_zero, Pi.zero_apply, le_refl]
  have hrpair := hp.2.2 hrzero
  have hqpair := hp'.2.2 hqzero
  let a : Fin 4 → E := ![F p.1.1, F p.1.2, F p.2.1, F p.2.2]
  have ha : ∀ i, a i ∈ (μ.map F).support := by
    intro i
    fin_cases i
    · exact hp.1.1.1
    · exact hp.1.1.2
    · exact hp'.1.1.1
    · exact hp'.1.1.2
  have hd : ∀ i, 0 ≤ B (a i) (a i) := by
    intro i
    fin_cases i
    · exact hp.1.2.1.1
    · exact hp.1.2.1.2
    · exact hp'.1.2.1.1
    · exact hp'.1.2.1.2
  have hcross : 0 ≤ B (featureDifference F p.1) (featureDifference F p.2) :=
    KernelOperator.bilinear_missing_pair_cross_nonnegative_on_support K F hF B hsym ℓ hrep hnonpos
      a ha hd (hp.1.2.2.symm.trans hrpair.1) (hp'.1.2.2.symm.trans hqpair.1) hrpair.2 hqpair.2
  simp only [map_smul, smul_apply, smul_eq_mul]
  exact mul_nonneg hp'.2.1 (mul_nonneg hp.2.1 hcross)

/-- Every actual integrable oriented missing flow has nonnegative original
shifted self-energy, including unbounded marginal densities. -/
theorem kernelEnergy_direction_nonnegative
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : StronglyMeasurable F) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (ℓ : E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (hdiag : ∀ᵐ x ∂μ, 0 ≤ B (F x) (F x))
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      (∫ x, ℓ (F x) * f x ∂μ) = 0 → KernelOperator.kernelEnergy (μ := μ) K f ≤ 0)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2)) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) K (direction μ q) :=
  kernelPairing_directions_nonnegative K F hF hC B hsym ℓ hrep hdiag hnonpos q q hq hq hq0 hq0 hqs hqs

/-- Adding an oriented nonnegative subflow cannot decrease the original
quadratic energy: both the added self-energy and the mixed term are nonnegative. -/
theorem kernelEnergy_direction_le_add
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : StronglyMeasurable F) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (ℓ : E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (hdiag : ∀ᵐ x ∂μ, 0 ≤ B (F x) (F x))
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      (∫ x, ℓ (F x) * f x ∂μ) = 0 → KernelOperator.kernelEnergy (μ := μ) K f ≤ 0)
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hr0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ r p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2))
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2)) :
    KernelOperator.kernelEnergy (μ := μ) K (direction μ q) ≤
      KernelOperator.kernelEnergy (μ := μ) K (direction μ (q + r)) := by
  have hcross := kernelPairing_directions_nonnegative K F hF hC B hsym ℓ hrep hdiag hnonpos
    q r hq hr hq0 hr0 hqs hrs
  have hself := kernelEnergy_direction_nonnegative K F hF hC B hsym ℓ hrep hdiag hnonpos r hr hr0 hrs
  rw [kernelEnergy_direction_add_eq K F hF.aestronglyMeasurable hC B hsym hrep q r hq hr]
  linarith

/-- Restricting any actual oriented flow density to a nonnegative subdensity
cannot increase its original energy. This applies to arbitrary measurable
subflows, without requiring a rectangular or atomic decomposition. -/
theorem kernelEnergy_direction_mono
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : StronglyMeasurable F) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (ℓ : E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (hdiag : ∀ᵐ x ∂μ, 0 ≤ B (F x) (F x))
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      (∫ x, ℓ (F x) * f x ∂μ) = 0 → KernelOperator.kernelEnergy (μ := μ) K f ≤ 0)
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hqr : ∀ᵐ p ∂μ.prod μ, q p ≤ r p)
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2)) :
    KernelOperator.kernelEnergy (μ := μ) K (direction μ q) ≤
      KernelOperator.kernelEnergy (μ := μ) K (direction μ r) := by
  have hres : ∀ᵐ p ∂μ.prod μ, 0 ≤ (r - q) p := by
    filter_upwards [hqr] with p hp
    exact sub_nonneg.mpr hp
  have hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2) := by
    filter_upwards [hq0, hqr, hrs] with p hp hle hs hne
    apply hs
    have hpos : 0 < q p := lt_of_le_of_ne hp (Ne.symm hne)
    exact (hpos.trans_le hle).ne'
  have hress : ∀ᵐ p ∂μ.prod μ, (r - q) p ≠ 0 →
      K p.1 p.2 = 0 ∧ 0 < ℓ (F p.1 - F p.2) := by
    filter_upwards [hq0, hqr, hrs] with p hp hle hs hne
    apply hs
    intro hz
    apply hne
    change r p - q p = 0
    rw [hz]
    have : q p = 0 := le_antisymm (by simpa only [hz] using hle) hp
    rw [this, sub_self]
  have h := kernelEnergy_direction_le_add K F hF hC B hsym ℓ hrep hdiag hnonpos
    q (r - q) hq (hr.sub hq) hq0 hres hqs hress
  have heq : q + (r - q) = r := by funext p; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rwa [heq] at h

end Erdos1017.MissingFlow

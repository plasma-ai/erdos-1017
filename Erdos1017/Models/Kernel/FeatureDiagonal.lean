module

public import Erdos1017.Models.Kernel.SignedHilbertFeature
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Diagonal bounds for feature pairings

Product-almost-everywhere bounds on a continuous feature pairing also bound its
canonical diagonal, using the support of the feature law, so the canonical
spectral diagonal lies in the kernel's essential range.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- Product-almost-everywhere bounds on a continuous feature pairing also
bound its canonical diagonal. This uses the support of the feature law,
without assigning values to the original kernel on its diagonal. -/
theorem feature_diagonal_bounds
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (F : Ω → E) (hF : AEStronglyMeasurable F μ) (J : E →ₗᵢ[ℝ] E)
    (a b : ℝ)
    (hpair : ∀ᵐ z ∂μ.prod μ,
      a ≤ ⟪J (F z.1), F z.2⟫ ∧ ⟪J (F z.1), F z.2⟫ ≤ b) :
    ∀ᵐ x ∂μ, a ≤ ⟪J (F x), F x⟫ ∧ ⟪J (F x), F x⟫ ≤ b := by
  have hsupport : ∀ᵐ x ∂μ, F x ∈ (μ.map F).support :=
    ae_of_ae_map hF.aemeasurable Measure.support_mem_ae
  filter_upwards [hsupport, Measure.ae_ae_of_ae_prod hpair] with x hx hrow
  have hcontinuous : Continuous (fun v : E => ⟪J (F x), v⟫) :=
    continuous_const.inner continuous_id
  have hc : IsClosed {v : E | a ≤ ⟪J (F x), v⟫ ∧ ⟪J (F x), v⟫ ≤ b} :=
    (isClosed_le continuous_const hcontinuous).inter
      (isClosed_le hcontinuous continuous_const)
  have hmap : {v : E | a ≤ ⟪J (F x), v⟫ ∧ ⟪J (F x), v⟫ ≤ b} ∈ ae (μ.map F) :=
    (ae_map_iff hF.aemeasurable hc.measurableSet).mpr hrow
  exact Measure.support_subset_of_isClosed hc hmap hx

/-- The canonical spectral diagonal lies in the kernel's essential range.
The series is the signed feature energy, not the original kernel evaluated
at the repeated physical point. -/
theorem spectral_diagonal_bounds
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Countable ι] (K : Ω → Ω → ℝ) (t : ι → ℝ) (b : ι → Ω → ℝ)
    (F : Ω → lp (fun _ : ι => ℝ) 2) (hF : AEStronglyMeasurable F μ)
    (hcoord : ∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x)
    (hrepresentation : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = ⟪spectralSign t (F z.1), F z.2⟫)
    (B : ℝ) (hK : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z.1 z.2 ∧ K z.1 z.2 ≤ B) :
    ∀ᵐ x ∂μ, 0 ≤ (∑' i, t i * (b i x) ^ 2) ∧ (∑' i, t i * (b i x) ^ 2) ≤ B := by
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  have hpair : ∀ᵐ z ∂μ.prod μ,
      0 ≤ ⟪spectralSign t (F z.1), F z.2⟫ ∧ ⟪spectralSign t (F z.1), F z.2⟫ ≤ B := by
    filter_upwards [hrepresentation, hK] with z hz hbound
    rwa [← hz]
  filter_upwards [feature_diagonal_bounds F hF (spectralSign t) 0 B hpair,
    hcoord] with x hx hc
  have heq : ⟪spectralSign t (F x), F x⟫ = ∑' i, t i * (b i x) ^ 2 := by
    rw [spectralSign_inner_eq_tsum t (fun i => b i x) (fun i => b i x) (F x) (F x) hc hc]
    apply tsum_congr
    intro i
    ring
  rwa [heq] at hx

end Erdos1017.KernelOperator

module

public import Erdos1017.Models.Capped.CappedShiftedSelection
public import Erdos1017.Models.Kernel.SpectralTrace

/-!
# Spectral sums of selected shifted operators

A nonnegative shifted kernel with positive spectral rank at most two has a
countable eigenbasis and absolute spectral sum at most sixteen, and every
interior-density capped optimizer has an equally good selected optimizer whose
compact shifted operator has absolutely summable eigenvalues.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

/-- A finite set of positive eigenbasis indices has cardinality bounded by
the actual positive spectral dimension. -/
theorem positive_basis_card_le_finrank {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    [FiniteDimensional ℝ (positiveSpectralSubspace T)]
    (b : HilbertBasis ι ℝ E) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i)
    (s : Finset ι) (hinside : ∀ i ∈ s, 0 < t i) :
    s.card ≤ Module.finrank ℝ (positiveSpectralSubspace T) := by
  have hmem (i : s) : b i ∈ positiveSpectralSubspace T := by
    have hle : Module.End.eigenspace T.toLinearMap (t i) ≤ positiveSpectralSubspace T :=
      le_iSup_of_le (t i) (le_iSup_of_le (hinside i i.property) le_rfl)
    exact hle (Module.End.mem_eigenspace_iff.mpr (heigen i))
  let v : s → positiveSpectralSubspace T := fun i => ⟨b i, hmem i⟩
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (positiveSpectralSubspace T).subtype
    exact b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  simpa only [Fintype.card_coe] using hv.fintype_card_le_finrank

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual shifted integral operator does not depend on which proved
kernel bound is used in its continuous-linear construction. -/
theorem shiftedOperator_eq_of_bound (W : Model Ω μ) (m : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ B) :
    shiftedOperator W m = KernelOperator.operator (shiftedKernel W m) hB
      (shiftedKernel_measurable W m) hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp only [shiftedOperator, KernelOperator.operator_inner]

/-- An actual nonnegative shifted kernel with positive spectral rank at
most two has an actual countable eigenbasis and absolute spectral sum at
most sixteen. The eigenbasis and finite positive index set are derived. -/
theorem exists_shifted_spectral_sum [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (m : ℝ)
    (hmem : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4)
    (hfinite : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)))
    (hindex : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 2) :
    ∃ (ι : Type u) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ),
      (∀ i, shiftedOperator W m (b i) = t i • b i) ∧
      Summable (fun i => |t i|) ∧ (∑' i, |t i|) ≤ 16 := by
  classical
  let := hfinite
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hcompact : IsCompactOperator (shiftedOperator W m) :=
    KernelOperator.operator_isCompact _ _ _ _
  have hsymmetric : (shiftedOperator W m).toLinearMap.IsSymmetric :=
    KernelOperator.operator_symmetric _ _ _ _ hsym
  obtain ⟨ι, hcount, b, t, heigen⟩ := KernelOperator.exists_countable_eigen_hilbertBasis
    (shiftedOperator W m) hcompact hsymmetric
  let := hcount
  have hpositive := KernelOperator.finite_positive_basis_indices (shiftedOperator W m) b t heigen
  let s := hpositive.toFinset
  have hinside (i : ι) (hi : i ∈ s) : 0 < t i := hpositive.mem_toFinset.mp hi
  have houtside (i : ι) (hi : i ∉ s) : t i ≤ 0 :=
    le_of_not_gt (fun hp => hi (hpositive.mem_toFinset.mpr hp))
  have hcard : s.card ≤ 2 :=
    (KernelOperator.positive_basis_card_le_finrank (shiftedOperator W m) b t heigen s hinside).trans hindex
  have hbound : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hmem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedKernel W m p.1 p.2 := hmem.mono fun _ hp => hp.1
  have hfour := shiftedOperator_eq_of_bound W m (by norm_num : (0 : ℝ) ≤ 4) hbound
  have heigenFour (i : ι) : KernelOperator.operator (shiftedKernel W m) (by norm_num : (0 : ℝ) ≤ 4)
      (shiftedKernel_measurable W m) hbound (b i) = t i • b i := by
    rw [← hfour]
    exact heigen i
  obtain ⟨habs, hsum⟩ := KernelOperator.summable_spectral_abs_and_bound (shiftedKernel W m)
    (by norm_num : (0 : ℝ) ≤ 4) (shiftedKernel_measurable W m) hbound hnonneg hsym
    b t heigenFour s hinside houtside
  have hcardReal : (s.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  exact ⟨ι, hcount, b, t, heigen, habs, hsum.trans (by nlinarith)⟩

/-- Every actual interior-density capped optimizer has an equally good
selected optimizer whose actual compact shifted integral operator has
absolutely summable eigenvalues of total absolute sum at most sixteen.
This is a numerical spectral sum; no trace-class premise is used. -/
theorem exists_selected_capped_spectral_sum [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ (V : Model Ω μ) (m ν : ℝ), IsMaximizer r V ∧ density V = density W ∧
      objective V = objective W ∧ m ∈ Set.Icc (-3) 1 ∧
      (∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂V.kernel p, shiftedColor m c = shiftedMoment V m p) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment V m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - V.moment CappedColor.adjacency p) * shiftedMoment V m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel V m x y ∂μ) = ν) ∧
      ν = 2 * (objective V - m * density V) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ≤ 2 ∧
      ∃ (ι : Type u) (_ : Countable ι) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ),
        (∀ i, shiftedOperator V m (b i) = t i • b i) ∧
        Summable (fun i => |t i|) ∧ (∑' i, |t i|) ≤ 16 := by
  obtain ⟨V, m, ν, hV, hd, hc, hm, hdet, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
    exists_selected_capped_kernel W hW hd0 hdhalf
  exact ⟨V, m, ν, hV, hd, hc, hm, hdet, hmem, hcomp, hrow, hν, hfinite, hindex,
    exists_shifted_spectral_sum V m hmem hfinite hindex⟩

end Erdos1017.CappedModel

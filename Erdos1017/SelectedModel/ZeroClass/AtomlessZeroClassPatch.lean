module

public import Erdos1017.SelectedModel.ZeroClass.AtomlessClassLabels
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassMeasurablePatch
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassPatchMoments
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassPatchStructure
public import Erdos1017.Models.Capped.CappedGrowingLimit

/-!
# Patch of a zero class on an atomless carrier

A positive zero class with finite-`k` density capacity admits an exact patch on
the original atomless carrier, with its fixed labels and conditional law
(`exists_atomless_zeroClass_patch_of_density_bound`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- A positive actual zero class with finite-k density capacity admits an
exact patch on the original atomless carrier. Its fixed labels, actual
conditional law and raw matching identity are exposed for later reuse. -/
theorem exists_atomless_zeroClass_patch_of_density_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [BorelSpace H]
    [OpensMeasurableSpace H] [SecondCountableTopology H]
    (W : Model Ω μ) (hW : FullFeasible W) (F : Ω → H) (hF : Measurable F)
    (v : H) (ν m : ℝ) (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hm : m ∈ Icc (-3 : ℝ) 1) (k : ℕ) (hk : 0 < k)
    (hpos : 0 < μ {x | F x = v})
    (hclique : 0 < restrictedCliquePresence W {x | F x = v} k)
    (hbound : (∫ p in {x | F x = v} ×ˢ {x | F x = v},
      W.moment CappedColor.adjacency p ∂μ.prod μ) /
      (μ.real {x | F x = v}) ^ 2 ≤ 1 - 1 / (k : ℝ))
    (hrep : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∃ (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1)
      (L : Ω → Fin k) (hL : Measurable L),
      MeasurePreserving L (ProbabilityTheory.cond μ {x | F x = v})
        (MultipartiteDensityRealization.labelLaw a ha hsum) ∧
      (∀ i, patchLabelMass (μ := μ) {x | F x = v} L i = μ.real {x | F x = v} * a i) ∧
      ((μ.real {x | F x = v}) ^ 2 -
        ∑ i, (patchLabelMass (μ := μ) {x | F x = v} L i) ^ 2 =
          ∫ p in {x | F x = v} ×ˢ {x | F x = v}, W.moment CappedColor.adjacency p ∂μ.prod μ) ∧
      FullFeasible (patchZeroClass W {x | F x = v} (hF (measurableSet_singleton v)) m hm L hL) ∧
      density (patchZeroClass W {x | F x = v} (hF (measurableSet_singleton v)) m hm L hL) = density W ∧
      objective (patchZeroClass W {x | F x = v} (hF (measurableSet_singleton v)) m hm L hL) = objective W := by
  let s : Set Ω := {x | F x = v}
  have hs : MeasurableSet s := hF (measurableSet_singleton v)
  let A := ∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ
  let q := A / (μ.real s) ^ 2
  have hmass : 0 < μ.real s := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ s)
  have hden : (μ.real s) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hmass)
  have hq0 : 0 ≤ q := by
    dsimp [q, A]
    apply div_nonneg
    · exact integral_nonneg (fun p => (adjacency_moment_mem W p).1)
    · exact sq_nonneg _
  obtain ⟨a, ha, hsum, hsquare, _⟩ :=
    MultipartiteDensityRealization.exists_part_masses k hk q hq0 hbound
  obtain ⟨L, hLmap, hlabelmass⟩ := exists_atomless_class_labels_of_masses s hs hpos hk a ha hsum
  have hL : Measurable L := hLmap.measurable
  have hlabelmass (i : Fin k) : patchLabelMass (μ := μ) s L i = μ.real s * a i := hlabelmass i
  have hsumsq : (∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) =
      (μ.real s) ^ 2 * ∑ i, (a i) ^ 2 := by
    simp_rw [hlabelmass, mul_pow]
    rw [Finset.mul_sum]
  have hAeq : A = (μ.real s) ^ 2 * q := by
    dsimp [q]
    exact (div_mul_cancel₀ A hden).symm.trans (mul_comm _ _)
  have hmatch : (μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2 = A := by
    rw [hsumsq, hsquare]
    nlinarith [hAeq]
  have hzeroClass := ae_shiftedMoment_zero_on_featureFiber W F v ν m hν hv hrep
  have hcharge : ∀ᵐ p ∂(μ.prod μ).restrict (s ×ˢ s),
      W.moment CappedColor.charge p = m * W.moment CappedColor.adjacency p := by
    filter_upwards [ae_restrict_mem (hs.prod hs), ae_restrict_of_ae hzeroClass] with p hp hz
    have hM : shiftedMoment W m p = 0 := hz hp
    rw [shiftedMoment_eq] at hM
    linarith
  have hfull := fullFeasible_patchZeroClass_of_positive_clique W hW F hF v ν m hν hv hpos hclique
    hm L hL hrep hzero hnonneg hcomp hdet
  have hmean := density_objective_patchZeroClass_eq W s hs m hm L hL hmatch hcharge
  exact ⟨a, ha, hsum, L, hL, hLmap, hlabelmass, hmatch, hfull, hmean.1, hmean.2⟩

end Erdos1017.CappedModel

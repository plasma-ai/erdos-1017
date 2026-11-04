module

public import Erdos1017.SelectedModel.SelectedMiddleExclusion
public import Erdos1017.SelectedModel.Structure.CanonicalCutFibers

/-!
# Homogeneous zero cut of the selected model

The selected original model has the explicit canonical left-side cut, which
crosses distinct-row raw zero pairs and is compatible with every positive whole
fiber of the same constructed row.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The selected original model has the explicit canonical left-side cut.
It crosses distinct-row raw zero pairs, and every positive whole fiber of
the same constructed row map lies almost everywhere on one side. -/
theorem FullStationaryClass.exists_homogeneous_zero_cut
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    ∃ (σ : ℝ), 0 < σ ∧ ∃ (ι : Type u) (_ : Countable ι)
      (φ : Ω → ℝ) (V : Ω → lp (fun _ : ι => ℝ) 2)
      (ρ : Ω → Lp ℝ 2 μ) (S B : Set Ω),
      KernelOperator.CanonicalIndexTwoFeature μ (shiftedKernel W m) 4
        (2 * (c - m * d)) σ φ V ∧
      StronglyMeasurable ρ ∧ MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧
      KernelOperator.CanonicalZeroGeometry (2 * (c - m * d)) σ φ V S ∧
      (∀ x ∈ S, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x) ∧
      (∀ x ∈ S, ∀ y ∈ S, ρ x = ρ y ↔ φ x = φ y ∧ V x = V y) ∧
      B = OrderedZeroRelation.leftSide μ
        (KernelOperator.canonicalZeroRelation (2 * (c - m * d)) σ φ V S) φ ∧
      MeasurableSet B ∧
      (∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
        (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B)) ∧
      (∀ r : Lp ℝ 2 μ, 0 < μ {x | ρ x = r} →
        (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ B) ∨
        (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∉ B)) := by
  obtain ⟨σ, hσ, ι, hcount, φ, V, ρ, S, hfeature, hρ, hS, hSae,
    hgeometry, hrowS, hcoords, hnone⟩ := hW.exists_canonical_middle_exclusion hd hgap hmax
  let ν := 2 * (c - m * d)
  let Z := KernelOperator.canonicalZeroRelation ν σ φ V S
  let B := OrderedZeroRelation.leftSide μ Z φ
  have hZ := KernelOperator.measurableSet_canonicalZeroRelation ν σ φ V S hS
    hfeature.scalar_measurable hfeature.feature_measurable
  have hB : MeasurableSet B := OrderedZeroRelation.measurableSet_leftSide Z hZ φ
    hfeature.scalar_measurable.measurable
  have hnoMiddle : ∀ᵐ y ∂μ, OrderedZeroRelation.leftNeighborMass μ Z φ y = 0 ∨
      OrderedZeroRelation.rightNeighborMass μ Z φ y = 0 := by
    filter_upwards [hSae, hnone] with y hy hn
    change OrderedZeroRelation.leftNeighborMass μ
      (KernelOperator.canonicalZeroRelation ν σ φ V S) φ y = 0 ∨
      OrderedZeroRelation.rightNeighborMass μ
        (KernelOperator.canonicalZeroRelation ν σ φ V S) φ y = 0
    rw [KernelOperator.leftNeighborMass_canonicalZeroRelation ν σ φ V S μ hy,
      KernelOperator.rightNeighborMass_canonicalZeroRelation ν σ φ V S μ hy]
    exact hn
  have hequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → φ p.1 = φ p.2 → ρ p.1 = ρ p.2 := by
    filter_upwards with p hp hφeq
    exact (hcoords p.1 hp.1.1 p.2 hp.1.2).mpr
      ⟨hφeq, (hgeometry.equal_scalar_zero_pair hp.1.1 hp.1.2 hφeq hp.2).1⟩
  have hcross := KernelOperator.ae_distinct_row_zero_crosses_leftSide ν σ φ V S μ hS
    hfeature.scalar_measurable hfeature.feature_measurable ρ hnoMiddle hequal
  refine ⟨σ, hσ, ι, hcount, φ, V, ρ, S, B, hfeature, hρ, hS, hSae,
    hgeometry, hrowS, hcoords, rfl, hB, ?_, ?_⟩
  · filter_upwards [hcross, hfeature.representation,
      Measure.quasiMeasurePreserving_fst.ae hSae,
      Measure.quasiMeasurePreserving_snd.ae hSae] with p hp hrep hx hy hzero hne
    apply hp ?_ hne
    exact ⟨⟨hx, hy⟩, hrep.symm.trans hzero⟩
  · intro r hr
    let : MeasurableSpace (Lp ℝ 2 μ) := borel _
    have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
    exact KernelOperator.positive_fiber_one_side ν σ φ V S μ hSae ρ
      (fun x hx y hy heq => (hcoords x hx y hy).mp heq) r
      (hρ.measurable (measurableSet_singleton r)) hr

end Erdos1017.CappedModel

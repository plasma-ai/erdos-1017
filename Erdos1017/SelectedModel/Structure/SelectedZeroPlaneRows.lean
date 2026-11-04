module

public import Erdos1017.SelectedModel.Structure.SelectedZeroBlockRigidity
public import Erdos1017.SelectedModel.Structure.AffineIsotropicLine

/-!
# Row map values on zero blocks and feature planes

The row map of the selected model takes at most two values on each measurable
zero block, including null blocks, and compatible canonical endpoint data make
their feature plane a zero block with the same two-value conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual row map of the selected model takes at most two values on
each measurable zero block, including a block of measure zero. -/
theorem FullStationaryClass.zero_block_two_rowMap_values_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ V : Model Ω μ, FullStationaryClass d c V m →
      stationaryEnergy V m ≤ stationaryEnergy W m)
    (ρ : Ω → Lp ℝ 2 μ)
    (hrow : ∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x)
    (E : Set Ω) (hE : MeasurableSet E)
    (hzero : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict E),
      shiftedKernel W m p.1 p.2 = 0) :
    ∃ Q₁ Q₂ : Lp ℝ 2 μ, ∀ᵐ x ∂μ, x ∈ E → ρ x = Q₁ ∨ ρ x = Q₂ := by
  by_cases hEzero : μ E = 0
  · have hnot : ∀ᵐ x ∂μ, x ∉ E := measure_eq_zero_iff_ae_notMem.mp hEzero
    refine ⟨0, 0, ?_⟩
    filter_upwards [hnot] with x hx hxe
    exact False.elim (hx hxe)
  · obtain ⟨Q₁, Q₂, htwo⟩ := hW.zero_block_two_rows_of_strict_gap hd hgap hmax E hE hEzero hzero
    refine ⟨Q₁, Q₂, ?_⟩
    filter_upwards [htwo, hrow] with x hx hr hxe
    rcases hx hxe with h₁ | h₂
    · exact Or.inl (Lp.ext (hr.trans h₁))
    · exact Or.inr (Lp.ext (hr.trans h₂))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Compatible canonical endpoint data make their actual feature plane
a zero block. The selected model's row map therefore has at most two
values there, with the raw-kernel identity used only almost everywhere. -/
theorem FullStationaryClass.isotropic_plane_two_rowMap_values_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m)
    (ρ : Ω → Lp ℝ 2 μ)
    (hrow : ∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x)
    (φ : Ω → ℝ) (V : Ω → H) (ν σ : ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = ν + σ * φ p.1 * φ p.2 - ⟪V p.1, V p.2⟫)
    (x z : Ω) (hpair : OrderedZeroTripleGeometry.IsotropicPair ν σ φ V x z)
    (hE : MeasurableSet (OrderedZeroTripleGeometry.affinePlane φ V x z)) :
    ∃ Q₁ Q₂ : Lp ℝ 2 μ, ∀ᵐ w ∂μ,
      w ∈ OrderedZeroTripleGeometry.affinePlane φ V x z → ρ w = Q₁ ∨ ρ w = Q₂ := by
  let E := OrderedZeroTripleGeometry.affinePlane φ V x z
  have hac : μ.restrict E ≪ μ := Measure.restrict_le_self.absolutelyContinuous
  have hzero : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict E),
      shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [(hac.prod hac).ae_le hrep,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hE),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hE)] with p hp hx hz
    have hgram := hpair.gram hx hz
    rw [hp, hgram]
    ring
  exact hW.zero_block_two_rowMap_values_of_strict_gap hd hgap hmax ρ hrow E hE hzero

end Erdos1017.CappedModel

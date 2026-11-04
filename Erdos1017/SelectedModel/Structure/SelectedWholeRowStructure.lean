module

public import Erdos1017.SelectedModel.Structure.SelectedCliqueSides
public import Erdos1017.SelectedModel.Structure.SelectedHomogeneousZeroCut

/-!
# Whole-row structure of the selected model

The selected original model has whole independent row fibers, a complete exact
remainder and a measurable zero-relation cut that assigns each positive whole
row fiber to one side (`exists_whole_row_structure`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The selected original model has whole independent row fibers, a
complete exact remainder and a measurable zero-relation cut that assigns
every positive whole row fiber almost everywhere to one side. -/
theorem FullStationaryClass.exists_whole_row_structure
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    ∃ (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D B : Set Ω),
      StronglyMeasurable ρ ∧
      (∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x) ∧ I.Countable ∧
      (∀ r ∈ I, MeasurableSet {x | ρ x = r} ∧ 0 < μ {x | ρ x = r} ∧
        (∀ᵐ p ∂(μ.restrict {x | ρ x = r}).prod (μ.restrict {x | ρ x = r}),
          adjacencyKernel W p.1 p.2 = 0) ∧
        KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
          (adjacencyKernel W) (chargeKernel W) 4 m ρ r) ∧
      I.Pairwise (fun r t => Disjoint {x | ρ x = r} {x | ρ x = t}) ∧
      D = (⋃ r ∈ I, {x | ρ x = r})ᶜ ∧ MeasurableSet D ∧
      (∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → W.moment CappedColor.adjacency p = 1) ∧
      MeasurableSet B ∧
      (∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
        (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B)) ∧
      ∀ r : Lp ℝ 2 μ, 0 < μ {x | ρ x = r} →
        (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ B) ∨
        (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∉ B) := by
  obtain ⟨ρ, I, D, hρ, hrow, hI, hfibers, hdisjoint, hDeq, hD, hcomplete⟩ :=
    hW.exists_independent_rows_complete_remainder hd hgap hmax
  obtain ⟨σ, _, ι, _, φ, V, τ, S, B, _, hτ, _, hSae, _, hτrowS, _, _, hB,
    hcross, hside⟩ := hW.exists_homogeneous_zero_cut hd hgap hmax
  have hτrow : ∀ᵐ x ∂μ, (τ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x :=
    hSae.mono fun x hx => hτrowS x hx
  have heq : ρ =ᵐ[μ] τ := by
    filter_upwards [hrow, hτrow] with x hx hy
    exact Lp.ext (hx.trans hy.symm)
  have hcrossρ : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B) := by
    filter_upwards [hcross, Measure.quasiMeasurePreserving_fst.ae heq,
      Measure.quasiMeasurePreserving_snd.ae heq] with p hp hx hy hzero hne
    apply hp hzero
    rwa [← hx, ← hy]
  refine ⟨ρ, I, D, B, hρ, hrow, hI, hfibers, hdisjoint, hDeq, hD, hcomplete,
    hB, hcrossρ, ?_⟩
  intro r hr
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hρfiber : MeasurableSet {x | ρ x = r} := hρ.measurable (measurableSet_singleton r)
  have hτfiber : MeasurableSet {x | τ x = r} := hτ.measurable (measurableSet_singleton r)
  have hmeasure : μ {x | ρ x = r} = μ {x | τ x = r} := by
    apply measure_congr
    filter_upwards [heq] with x hx
    simp only [hx]
  have hrτ : 0 < μ {x | τ x = r} := hmeasure ▸ hr
  rcases hside r hrτ with hinside | houtside
  · left
    apply (ae_restrict_iff' hρfiber).mpr
    filter_upwards [heq, (ae_restrict_iff' hτfiber).mp hinside] with x hx hcut hxr
    exact hcut (hx.symm.trans hxr)
  · right
    apply (ae_restrict_iff' hρfiber).mpr
    filter_upwards [heq, (ae_restrict_iff' hτfiber).mp houtside] with x hx hcut hxr
    exact hcut (hx.symm.trans hxr)

end Erdos1017.CappedModel

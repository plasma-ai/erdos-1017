module

public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence
public import Erdos1017.Exclusions.Common.Flows.DiffuseFlowEndpointRemainder

/-!
# Small diffuse rerouting of the selected flow

Finite atomic incidence yields measurable source and recipient regions with the
geometric hypotheses needed for diffuse rerouting, and a positive diffuse high
excess set constructs all incidence, small-recipient and full-flow interpolation
data internally.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Actual finite atomic incidence yields measurable source and recipient
regions with all geometric hypotheses needed for actual diffuse rerouting.
The source union has its true original mass. -/
theorem exists_measurable_diffuse_incidence_regions (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : ℝ)
    (hpositive : 0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x})) :
    ∃ (C₀ J : Set Ω), MeasurableSet C₀ ∧ 0 < μ C₀ ∧ C₀ ⊆ S.D ∧ C₀ ⊆ S.H ∧
      MeasurableSet J ∧ b < μ.real J ∧
      (∀ᵐ y ∂μ, y ∈ J → y ∈ S.L) ∧
      (∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I) ∧
      (∀ᵐ p ∂μ.prod μ, p.1 ∈ C₀ → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0) := by
  let : Countable S.I := S.hI.to_subtype
  obtain ⟨F, C₀, hC₀, hpos, hsubset, hmass, hlow, hrect⟩ :=
    S.exists_finite_low_atoms_common_diffuse_high_set hW hd hgap b hpositive
  let J := ⋃ r ∈ F, {x | S.ρ x = r.val}
  have hJ : MeasurableSet J := MeasurableSet.iUnion (fun r =>
    MeasurableSet.iUnion (fun _ => (S.hfibers r r.property).1))
  have hJmass : μ.real J = ∑ r ∈ F, S.originalAtomMass r := by
    apply measureReal_biUnion_finset
    · intro r _ u _ hne
      exact Set.disjoint_left.mpr (fun x hx hy => hne (Subtype.ext (hx.symm.trans hy)))
    · intro r _
      exact (S.hfibers r r.property).1
    · intro r _
      exact measure_ne_top _ _
  have hlowAll : ∀ᵐ y ∂μ, ∀ r : S.I, r ∈ F → S.ρ y = r → y ∈ S.L := by
    apply ae_all_iff.mpr
    intro r
    by_cases hr : r ∈ F
    · exact ((ae_restrict_iff' (S.hfibers r r.property).1).mp (hlow r hr)).mono
        (fun _ hy _ => hy)
    · exact Eventually.of_forall (fun _ h => False.elim (hr h))
  have hrectangle : ∀ᵐ p ∂μ.prod μ, ∀ r : S.I, r ∈ F →
      S.ρ p.1 = r → p.2 ∈ C₀ → shiftedKernel W m p.1 p.2 = 0 := by
    apply ae_all_iff.mpr
    intro r
    by_cases hr : r ∈ F
    · have hh := (hrect r hr).mono (fun _ hp => hp.1)
      rw [Measure.prod_restrict] at hh
      have hg := (ae_restrict_iff' ((S.hfibers r r.property).1.prod hC₀)).mp hh
      exact hg.mono (fun _ hp _ hx hy => hp ⟨hx, hy⟩)
    · exact Eventually.of_forall (fun _ h => False.elim (hr h))
  refine ⟨C₀, J, hC₀, hpos, (fun _ hx => (hsubset hx).1.1),
    (fun _ hx => (hsubset hx).1.2), hJ, ?_, ?_, ?_, ?_⟩
  · rw [hJmass]
    exact hmass
  · filter_upwards [hlowAll] with y hy hJy
    obtain ⟨r, hrow⟩ := mem_iUnion.mp hJy
    obtain ⟨hr, hrow⟩ := mem_iUnion.mp hrow
    exact hy r hr hrow
  · apply Eventually.of_forall
    intro y hJy
    obtain ⟨r, hrow⟩ := mem_iUnion.mp hJy
    obtain ⟨hr, hrow⟩ := mem_iUnion.mp hrow
    exact hrow ▸ r.property
  · have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hrectangle
    filter_upwards [hswap, shiftedMoment_symm W m] with p hp hs hx hy
    obtain ⟨r, hrow⟩ := mem_iUnion.mp hy
    obtain ⟨hr, hrow⟩ := mem_iUnion.mp hrow
    exact hs.symm.trans (hp r hr hrow hx)

/-- A positive actual diffuse HIGH excess set constructs all incidence,
small-recipient and full-flow interpolation data internally. Every original
atom avoided by the starting flow remains avoided. -/
theorem IsFullForwardFlow.exists_selected_small_diffuse_rerouting
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hpositive : 0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x})) :
    ∃ (C J : Set Ω) (θ : ℝ), MeasurableSet C ∧ MeasurableSet J ∧ 0 < μ.real C ∧
      C ⊆ S.D ∧ C ⊆ S.H ∧
      (∀ᵐ y ∂μ, y ∈ J → y ∈ S.L) ∧
      (∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I) ∧
      (∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0) ∧
      μ.real C + (∫ x in C, MissingFlow.receipt μ q x ∂μ) < ε ∧
      θ ∈ Ioo (0 : ℝ) 1 ∧
      S.IsFullForwardFlow (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p) ∧
      (missingFlowEndpointLaw μ
        (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)).real C = b ∧
      ∀ i : S.I, (∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) →
        ∀ᵐ p ∂μ.prod μ,
          (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p ≠ 0 → S.ρ p.1 ≠ i := by
  obtain ⟨C₀, J, hC₀, hpos, hCD, hCH, hJ, hJmass, hJL, hJI, hzero⟩ :=
    S.exists_measurable_diffuse_incidence_regions hW hd hgap b hpositive
  obtain ⟨C, hCC, hC, hCp, hsmall, θ, hθ, ht, hmass, havoid⟩ :=
    hq.exists_small_diffuse_redirect_interpolation C₀ J hC₀ hJ hpos hCD hCH hJL hJI hzero
      b ε hb hε hJmass
  exact ⟨C, J, θ, hC, hJ, hCp, hCC.trans hCD, hCC.trans hCH, hJL, hJI,
    hzero.mono (fun _ hp hx hy => hp (hCC hx) hy), hsmall, hθ, ht, hmass, havoid⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

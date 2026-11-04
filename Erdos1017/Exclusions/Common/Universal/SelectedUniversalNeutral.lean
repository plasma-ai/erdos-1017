module

public import Erdos1017.SelectedModel.Structure.SelectedHighLowClassification

/-!
# Neutrality of universal atoms

A universal independent atom of the original model is neutral, since strict
support rules out every distinct-row zero pair from its whole fiber.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

attribute [local instance] Classical.propDecidable

/-- An actual universal original independent atom is neutral. Strict
support rules out every distinct-row zero pair from that whole fiber;
both strict degree-neighbor section masses therefore vanish. -/
theorem universal_atom_neutral (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (huniv : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N := by
  let F := {x | S.ρ x = r.val}
  let Z := actualZeroRelation W m S.ρ
  let g := fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x
  have hF : MeasurableSet F := (S.hfibers r.val r.property).1
  have hnone : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p ∉ Z := by
    filter_upwards [huniv, (hW.strict_gap_structure hd hgap).strict_support]
      with p hu hs hpr hZ
    have hne : S.ρ p.2 ≠ r.val := fun h => hZ.2 (hpr.trans h.symm)
    have hG : adjacencyKernel W p.1 p.2 = 1 := by
      simpa only [hne, ite_false] using hu hpr
    change adjacencyKernel W p.1 p.2 =
      if 0 < shiftedKernel W m p.1 p.2 then 1 else 0 at hs
    have hzero : adjacencyKernel W p.1 p.2 = 0 := by
      simpa only [hZ.1, lt_self_iff_false, ite_false] using hs
    linarith
  have hrows := ae_restrict_of_ae (s := F) (Measure.ae_ae_of_ae_prod hnone)
  have hsym := ae_restrict_of_ae (s := F)
    (Measure.ae_ae_of_ae_prod (actualZeroRelation_symm W m S.ρ))
  filter_upwards [hrows, hsym, ae_restrict_mem hF] with x hx hs hFx
  have hout : ∀ᵐ y ∂μ, (x, y) ∉ Z := hx.mono (fun _ hy => hy hFx)
  have hin : ∀ᵐ y ∂μ, (y, x) ∉ Z := by
    filter_upwards [hout, hs] with y hy hsym hyx
    exact hy (hsym.mpr hyx)
  have houtzero : μ {y | (x, y) ∈ Z} = 0 := by
    simpa only [not_not] using ae_iff.mp hout
  have hinzero : μ {y | (y, x) ∈ Z} = 0 := by
    simpa only [not_not] using ae_iff.mp hin
  have hleft : OrderedZeroRelation.leftNeighborMass μ Z g x = 0 :=
    measure_mono_null (fun _ h => h.1) hinzero
  have hright : OrderedZeroRelation.rightNeighborMass μ Z g x = 0 :=
    measure_mono_null (fun _ h => h.1) houtzero
  rw [S.hN]
  change x ∉ OrderedZeroRelation.highClass μ Z g ∪ OrderedZeroRelation.lowClass μ Z g
  rintro (hH | hL)
  · change 0 < OrderedZeroRelation.leftNeighborMass μ Z g x at hH
    rw [hleft] at hH
    exact (lt_irrefl _ hH)
  · have hpos := hL.1
    change 0 < OrderedZeroRelation.rightNeighborMass μ Z g x at hpos
    rw [hright] at hpos
    exact (lt_irrefl _ hpos)

end Erdos1017.CappedModel.SelectedHighLowStructure

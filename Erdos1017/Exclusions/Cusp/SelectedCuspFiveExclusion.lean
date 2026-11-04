module

public import Erdos1017.Exclusions.Cusp.SelectedCuspFiveSourcePeak
public import Erdos1017.Exclusions.Cusp.SelectedCuspFiveOutsidePeak
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns

/-!
# Exclusion of the fifth reciprocal cusp

Every selected positive global excess at the fifth reciprocal cusp is excluded:
the reverse recovery and the original common peak are constructed and the
possible peak positions are ruled out (`no_cusp_five_contact`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

/-- Every selected positive global excess at the fifth reciprocal cusp
is excluded. The actual reverse recovery and original common peak are
constructed, and all possible locations of that peak are covered. -/
theorem no_cusp_five_contact (S : SelectedHighLowStructure W m)
    (hdk : d = 12 / 25) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  have hdk' : d = (1 - 1 / (5 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  have hd := (hW.cusp_contact_parameters 5 (by norm_num) hdk' hgap hglobal).1
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  obtain ⟨r, hr⟩ := R.cusp_plateau_singleton 5 (by norm_num) hdk' hW hgap hglobal
  obtain ⟨_, i, _, _, hpeak, _, _, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
  change S.IsCommonForwardPeak d c i at hpeak
  have hir : i ≠ r := by
    intro heq
    subst i
    have hmass := R.common_peak_head_mass r (by rw [hr]; simp) hW hpeak
    change S.originalAtomMass r = R.height at hmass
    obtain ⟨_, _, _, _, _, hcap, _, _⟩ :=
      S.cusp_atom_contact_guards r hW 5 (by norm_num) hdk' hgap hglobal
    have hheight := R.cusp_height_gt_reciprocal 5 (by norm_num) hdk' hW hgap hglobal
    linarith only [hmass, hcap, hheight]
  have hlocation := S.ae_compulsorySource_iff_fiberPredicate i R.plateau hW
  change ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
    x ∈ R.cuspSource ↔ S.fiberCompulsoryPredicate i R.plateau at hlocation
  by_cases hsource : S.fiberCompulsoryPredicate i R.plateau
  · exact R.no_cusp_five_source_peak r i hdk hW hgap hglobal hr
      (hlocation.mono (fun _ hx => hx.mpr hsource)) hpeak
  · apply R.no_cusp_five_outside_original_peak r i hdk hW hgap hglobal hr hpeak
    filter_upwards [hlocation, ae_restrict_mem (S.hfibers i.val i.property).1] with x hx hi
    intro hmem
    rcases hmem with hhead | hinside
    · exact hir (Subtype.ext (hi.symm.trans hhead))
    · exact hsource (hx.mp hinside)

end Erdos1017.CappedModel.SelectedHighLowStructure

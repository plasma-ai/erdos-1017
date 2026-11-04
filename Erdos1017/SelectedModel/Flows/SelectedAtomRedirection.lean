module

public import Erdos1017.SelectedModel.Flows.FlowRedirection
public import Erdos1017.SelectedModel.Flows.FullForwardFlowClass

/-!
# Redirecting a full forward flow into one high atom

The missing region of a high whole atom consists of low sources; redirecting a
full forward flow into that atom stays in the full forward class, keeps other
avoided fibers avoided, and fills the atom with its original mass plus that of
its missing region.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Original pair homogeneity on a supplied positive whole fiber is lifted
through one common product-almost-everywhere event. -/
theorem ae_kernel_eq_fiber_row (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r → shiftedKernel W m p.1 p.2 = r p.2 := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hK : Measurable (fun p : Ω × Ω => shiftedKernel W m p.1 p.2) :=
    (W.stronglyMeasurable_moment (continuous_shiftedColor m).measurable.stronglyMeasurable).measurable
  have hP : MeasurableSet {p : Ω × Ω |
      S.ρ p.1 = r → shiftedKernel W m p.1 p.2 = r p.2} := by
    convert (S.hρ.measurable.comp measurable_fst (measurableSet_singleton r)).compl.union
      (measurableSet_eq_fun hK ((Lp.stronglyMeasurable r).measurable.comp measurable_snd)) using 1
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage,
      mem_singleton_iff, Function.comp_apply, imp_iff_not_or]
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  have hrows := (ae_restrict_iff' (S.hfibers r hr).1).mp
    ((S.hfibers r hr).2.2.2.rows.mono (fun _ hx => hx.1))
  filter_upwards [hrows] with x hx
  by_cases hxr : S.ρ x = r
  · exact (hx hxr).mono (fun _ hy _ => hy)
  · exact Eventually.of_forall (fun _ hy => False.elim (hxr hy))

/-- The actual missing region of a HIGH whole atom consists of LOW sources,
and its entire recipient-source rectangle lies in the original outside-zero
relation with the correct HIGH-to-LOW orientation. -/
theorem high_atom_missing_rectangle (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    (∀ᵐ y ∂μ, y ∈ KernelOperator.wholeFiberMissingSet S.ρ r → y ∈ S.L) ∧
      ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r →
        p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r →
        p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L := by
  have hH := (ae_restrict_iff' (S.hfibers r hr).1).mp hhigh
  have hrect : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r →
      p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r →
      p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L := by
    filter_upwards [S.ae_kernel_eq_fiber_row r hr, hnonneg, S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae hH] with p he hn hc hh hxr hy
    have hz : shiftedKernel W m p.1 p.2 = 0 :=
      le_antisymm ((he hxr).trans_le hy.2) hn
    have hZ : p ∈ actualZeroRelation W m S.ρ :=
      ⟨hz, fun h => hy.1 (h.symm.trans hxr)⟩
    refine ⟨hZ, hh hxr, ?_⟩
    rcases hc hZ with h | h
    · exact h.2.1
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hh hxr) h.2.1)
  refine ⟨?_, hrect⟩
  have hsections : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, S.ρ x = r →
      y ∈ KernelOperator.wholeFiberMissingSet S.ρ r →
      (x, y) ∈ actualZeroRelation W m S.ρ ∧ x ∈ S.H ∧ y ∈ S.L :=
    Measure.ae_ae_of_ae_prod hrect
  obtain ⟨x, hx, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r hr).2.1.ne' (ae_restrict_of_ae hsections)
  filter_upwards [hgood] with y hy hNy
  exact (hy hx hNy).2.2

/-- Every old outside-zero-supported flow receives into this whole atom
only from its actual missing region. No filled-mass premise is supplied. -/
theorem atom_receipt_sources (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I) (q : Ω × Ω → ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → p ∈ actualZeroRelation W m S.ρ) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r → q p ≠ 0 →
      p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r := by
  filter_upwards [S.ae_kernel_eq_fiber_row r hr, hsupport] with p he hs hxr hq
  have hz := hs hq
  refine ⟨fun hy => hz.2 (hxr.trans hy.symm), ?_⟩
  rw [← he hxr, hz.1]

/-- The redirection into this same original whole atom and its actual
missing region. -/
def atomRedirect (S : SelectedHighLowStructure W m) (r : Lp ℝ 2 μ)
    (q : Ω × Ω → ℝ) : Ω × Ω → ℝ :=
  MissingFlow.redirect μ q {x | S.ρ x = r} (KernelOperator.wholeFiberMissingSet S.ρ r)

/-- Actual nonnegative selected-kernel data makes the redirected density a
member of the same full forward class, for any HIGH whole atom. -/
theorem IsFullForwardFlow.atomRedirect {S : SelectedHighLowStructure W m}
    {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    S.IsFullForwardFlow (S.atomRedirect r q) := by
  have hI := (S.hfibers r hr).1
  have hpos : 0 < μ.real {x | S.ρ x = r} :=
    ENNReal.toReal_pos (S.hfibers r hr).2.1.ne' (measure_ne_top _ _)
  have hN := KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r
  have hrect := S.high_atom_missing_rectangle r hr hhigh hnonneg
  refine ⟨MissingFlow.integrable_redirect q hq.integrable _ _ hI hN,
    MissingFlow.redirect_nonnegative q hq.nonnegative _ _,
    MissingFlow.full_supply_redirect q _ _ S.L hI hpos hq.supply hrect.1, ?_⟩
  exact MissingFlow.support_redirect q _ _
    {p | p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L}
    hq.support hrect.2

/-- The recorded full stationary model supplies the required nonnegative
kernel; no extra rectangle or class-membership premise is supplied. -/
theorem IsFullForwardFlow.atomRedirect_of_stationary {S : SelectedHighLowStructure W m}
    {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H) :
    S.IsFullForwardFlow (S.atomRedirect r q) :=
  hq.atomRedirect r hr hhigh (hW.moment_mem.mono (fun _ hp => hp.1))

/-- Actual whole-row homogeneity determines the exact total redirected
receipt into the same original atom. -/
theorem IsFullForwardFlow.atomRedirect_receipt {S : SelectedHighLowStructure W m}
    {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I) :
    (∫ x in {x | S.ρ x = r}, MissingFlow.receipt μ (S.atomRedirect r q) x ∂μ) =
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ r) := by
  apply MissingFlow.integral_receipt_redirect q _ _ (S.hfibers r hr).1
    (KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r)
    (ENNReal.toReal_pos (S.hfibers r hr).2.1.ne' (measure_ne_top _ _))
  exact S.atom_receipt_sources r hr q (hq.support.mono (fun _ hp hq => (hp hq).1))

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Any distinct original whole fiber avoided by the old flow remains
avoided after redirection. The distinct fiber need not be the largest atom. -/
theorem atomRedirect_avoids (S : SelectedHighLowStructure W m)
    (r r₀ : Lp ℝ 2 μ) (hne : r ≠ r₀) (q : Ω × Ω → ℝ)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ r₀) :
    ∀ᵐ p ∂μ.prod μ, S.atomRedirect r q p ≠ 0 → S.ρ p.1 ≠ r₀ := by
  apply MissingFlow.avoids_redirect q _ _ {x | S.ρ x = r₀} _ havoid
  exact Set.disjoint_left.mpr (fun _ hx hy => hne (hx.symm.trans hy))

/-- The actual endpoint fills the selected HIGH atom with precisely its
original mass plus the mass of its actual LOW missing region. -/
theorem IsFullForwardFlow.atomRedirect_endpoint_mass {S : SelectedHighLowStructure W m}
    {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H) :
    (missingFlowEndpointLaw μ (S.atomRedirect r q)).real {x | S.ρ x = r} =
      μ.real {x | S.ρ x = r} + μ.real (KernelOperator.wholeFiberMissingSet S.ρ r) := by
  have hrect := S.high_atom_missing_rectangle r hr hhigh
    (hW.moment_mem.mono (fun _ hp => hp.1))
  apply MissingFlow.endpoint_redirect_recipient_mass q hq.integrable hq.nonnegative
    _ _ S.H S.L (S.hfibers r hr).1
    (KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r)
    (ENNReal.toReal_pos (S.hfibers r hr).2.1.ne' (measure_ne_top _ _))
    S.hpartition.2.2.2.2.1 ((ae_restrict_iff' (S.hfibers r hr).1).mp hhigh)
    hrect.1 hq.supply
  exact S.atom_receipt_sources r hr q (hq.support.mono (fun _ hp hq => (hp hq).1))

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A full forward flow avoiding an actual HIGH atom leaves that atom's
endpoint mass equal to its original mass. Both zero marginals are derived. -/
theorem IsFullForwardFlow.endpoint_mass_of_avoids_high_atom
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ r) :
    (missingFlowEndpointLaw μ q).real {x | S.ρ x = r} = μ.real {x | S.ρ x = r} := by
  have hreceipt : ∀ᵐ x ∂μ, S.ρ x = r → MissingFlow.receipt μ q x = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod havoid] with x hx hxr
    apply integral_eq_zero_of_ae
    filter_upwards [hx] with y hy
    by_contra hne
    exact hy hne hxr
  have hsupply : ∀ᵐ x ∂μ, S.ρ x = r → MissingFlow.supply μ q x = 0 := by
    filter_upwards [hq.supply, (ae_restrict_iff' (S.hfibers r hr).1).mp hhigh]
      with x hx hh hxr
    have hn : x ∉ S.L :=
      fun hl => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hh hxr) hl
    rw [hx, indicator_of_notMem hn]
  exact MissingFlow.endpoint_real_set_eq_original q hq.integrable hq.nonnegative
    hq.supply_le_one _ (S.hfibers r hr).1 hreceipt hsupply

/-- Filling a different HIGH atom retains the original mass of an actual
avoided HIGH atom at the same genuine full-forward endpoint. -/
theorem IsFullForwardFlow.atomRedirect_avoided_endpoint_mass
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (r r₀ : Lp ℝ 2 μ) (hr : r ∈ S.I) (hr₀ : r₀ ∈ S.I) (hne : r ≠ r₀)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H)
    (hhigh₀ : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r₀}, x ∈ S.H)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ r₀) :
    (missingFlowEndpointLaw μ (S.atomRedirect r q)).real {x | S.ρ x = r₀} =
      μ.real {x | S.ρ x = r₀} :=
  (hq.atomRedirect_of_stationary hW r hr hhigh).endpoint_mass_of_avoids_high_atom
    r₀ hr₀ hhigh₀ (S.atomRedirect_avoids r r₀ hne q havoid)

end Erdos1017.CappedModel.SelectedHighLowStructure

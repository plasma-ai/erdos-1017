module

public import Erdos1017.SelectedModel.Recovery.SelectedReverseRealization

/-!
# Full reverse recovery of the selected model

The structure `ReverseRecovery` bundles a completed assignment with its full
reverse flow and original plateau, satisfying the compulsory-source balance and
plateau budget bounds (`card_lt_two_div_neg_multiplier`). It is constructed from
the selected reverse data under the strict gap
(`exists_reverseRecovery_with_budget`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- A completed assignment together with its actual original-product full
reverse flow. The original coded entire-source identities are retained for
later source restriction; no relaxed vector is used as an endpoint. -/
structure ReverseRecovery (S : SelectedHighLowStructure W m) where
  data : S.ReverseAssignmentData
  fractions : ℕ → Lp ℝ 2 (μ.restrict S.H)
  feasible : ReverseAssignment.Feasible data.allowed data.δ fractions
  height : ℝ
  height_pos : 0 < height
  codePlateau : Finset ℕ
  codePlateau_nonempty : codePlateau.Nonempty
  mass_le : ∀ i, ReverseAssignment.mass data.a fractions i ≤ height
  mass_eq_iff : ∀ i, ReverseAssignment.mass data.a fractions i = height ↔ i ∈ codePlateau
  full_atomic : ∀ᵐ x ∂μ.restrict S.H, data.δ x = 0 → HasSum (fun i => fractions i x) 1
  zero_diffuse : ∀ᵐ x ∂μ.restrict S.H, data.δ x ≠ 0 → ∀ i, fractions i x = 0
  full : S.IsFullReverseFlow (data.completedFlow fractions)
  entire_source : ∀ᵐ x ∂μ.restrict S.H,
    (∑ i ∈ codePlateau, fractions i x) =
      (ReverseAssignment.compulsorySource data.allowed data.δ codePlateau).indicator (fun _ => 1) x
  source_balance : (codePlateau.card : ℝ) * height = (∑ i ∈ codePlateau, data.a i) +
    (μ.restrict S.H).real (ReverseAssignment.compulsorySource data.allowed data.δ codePlateau)

namespace ReverseRecovery

variable {S : SelectedHighLowStructure W m}

/-- The actual full recovered density on the original product carrier. -/
def flow (R : S.ReverseRecovery) : Ω × Ω → ℝ := R.data.completedFlow R.fractions

/-- The plateau consists of the same original whole-row labels, decoded
injectively from the actual positive coded plateau. -/
def plateau (R : S.ReverseRecovery) : Finset S.I := R.data.plateauLabels R.codePlateau

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem isFullReverseFlow (R : S.ReverseRecovery) : S.IsFullReverseFlow R.flow := R.full

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem active_codePlateau (R : S.ReverseRecovery) :
    ∀ i ∈ R.codePlateau, R.data.label i ≠ none :=
  R.data.plateau_label_ne_none R.fractions R.feasible R.codePlateau R.height R.height_pos
    (fun i hi => (R.mass_eq_iff i).mpr hi)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual original-label plateau is nonempty; inactive or HIGH Nat
slots cannot supply a positive-height plateau witness. -/
theorem plateau_nonempty (R : S.ReverseRecovery) : R.plateau.Nonempty := by
  apply Finset.card_pos.mp
  change 0 < (R.data.plateauLabels R.codePlateau).card
  rw [R.data.plateauLabels_card R.codePlateau R.active_codePlateau]
  exact Finset.card_pos.mpr R.codePlateau_nonempty

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every plateau member is an actual eligible original LOW or neutral
whole atom, with no artificial Nat labels retained. -/
theorem plateau_eligible (R : S.ReverseRecovery) (r : S.I) (hr : r ∈ R.plateau) :
    r ∈ S.eligibleReverseAtom := R.data.plateauLabels_eligible R.codePlateau r hr

/-- The actual recovered endpoint mass cap is derived at every original
label, including removed HIGH labels, from the realized all-cell identity. -/
theorem classMass_le (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r : S.I) : S.reverseClassMass R.flow r ≤ R.height := by
  rw [flow, R.data.completedFlow_classMass hW R.fractions R.feasible R.full_atomic R.zero_diffuse]
  exact R.mass_le (R.data.code r)

/-- The plateau is exactly the top-level set of actual endpoint masses on
the original label family. No relaxed-to-physical mass identity is assumed. -/
theorem classMass_eq_iff (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (r : S.I) :
    S.reverseClassMass R.flow r = R.height ↔ r ∈ R.plateau := by
  rw [flow, R.data.completedFlow_classMass hW R.fractions R.feasible R.full_atomic R.zero_diffuse,
    R.mass_eq_iff]
  exact R.data.code_mem_iff_plateauLabels R.codePlateau R.active_codePlateau r

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The entire original compulsory source is measurable. -/
theorem measurableSet_source (R : S.ReverseRecovery) :
    MeasurableSet (S.reverseCompulsorySource R.plateau) :=
  R.data.measurableSet_compulsorySource R.codePlateau

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual original plateau and the entire original source satisfy the
exact compulsory-source mass identity; no positive-source assumption occurs. -/
theorem original_source_balance (R : S.ReverseRecovery) :
    (R.plateau.card : ℝ) * R.height =
      (∑ r ∈ R.plateau, μ.real {x | S.ρ x = r.val}) + μ.real (S.reverseCompulsorySource R.plateau) := by
  calc
    _ = (R.codePlateau.card : ℝ) * R.height := by
      rw [plateau, R.data.plateauLabels_card R.codePlateau R.active_codePlateau]
    _ = (∑ i ∈ R.codePlateau, R.data.a i) +
        (μ.restrict S.H).real (ReverseAssignment.compulsorySource
          R.data.allowed R.data.δ R.codePlateau) := R.source_balance
    _ = _ := by
      rw [R.data.plateauLabels_original_mass_sum R.codePlateau R.active_codePlateau,
        R.data.compulsorySource_mass R.codePlateau]
      rfl

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The completed assignment's original-law lifted fractions into the
plateau come from exactly the entire original compulsory source. -/
theorem original_entire_source_fractions (R : S.ReverseRecovery) :
    ∀ᵐ x ∂μ,
      (∑ i ∈ R.codePlateau, MissingFlow.RestrictedAtomicAssignment.liftFraction S.H R.fractions i x) =
        (S.reverseCompulsorySource R.plateau).indicator (fun _ => 1) x := by
  have hglobal := (ae_restrict_iff' S.hpartition.1).mp R.entire_source
  filter_upwards [hglobal] with x hx
  rw [plateau, ← R.data.compulsorySource_eq_original]
  by_cases hxH : x ∈ S.H
  · simp only [MissingFlow.RestrictedAtomicAssignment.liftFraction, indicator_of_mem hxH]
    rw [hx hxH]
    by_cases hxC : x ∈ ReverseAssignment.compulsorySource R.data.allowed R.data.δ R.codePlateau
    · simp only [indicator_of_mem hxC, indicator_of_mem (show x ∈ S.H ∩ _ from ⟨hxH, hxC⟩)]
    · simp only [indicator_of_notMem hxC,
        indicator_of_notMem (show x ∉ S.H ∩ _ from fun h => hxC h.2)]
  · simp only [MissingFlow.RestrictedAtomicAssignment.liftFraction, indicator_of_notMem hxH,
      Finset.sum_const_zero, indicator_of_notMem (show x ∉ S.H ∩ _ from fun h => hxH h.1)]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Only after the actual full reverse flow is constructed is the physical
plateau budget applied to the recovered original-label plateau. -/
theorem card_lt_two_div_neg_multiplier (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) : (R.plateau.card : ℝ) < 2 / (-m) :=
  R.isFullReverseFlow.plateau_card_lt_two_div_neg_multiplier hW hd hgap R.plateau R.height
    R.height_pos (R.classMass_le hW) (fun r hr => (R.classMass_eq_iff hW r).mpr hr)

theorem endpoint_credit (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) ∧
      density R.isFullReverseFlow.endpoint < d ∧
      c + KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) / 2 +
          (-m) * (d - density R.isFullReverseFlow.endpoint) ≤ R.height ^ 2 ∧ c < R.height ^ 2 :=
  R.isFullReverseFlow.endpoint_credit hW hd hgap R.height (R.classMass_le hW)

theorem card_le_two_of_neg_multiplier_ge_two_thirds (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hslope : (2 / 3 : ℝ) ≤ -m) : R.plateau.card ≤ 2 :=
  R.isFullReverseFlow.plateau_card_le_two_of_neg_multiplier_ge_two_thirds hW hd hgap
    R.plateau R.height R.height_pos (R.classMass_le hW)
    (fun r hr => (R.classMass_eq_iff hW r).mpr hr) hslope

theorem card_le_two_of_half_lt_neg_multiplier (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hslope : (1 / 2 : ℝ) < -m)
    (hmissing : (1 / 12 : ℝ) < 1 / 2 - d) : R.plateau.card ≤ 2 :=
  R.isFullReverseFlow.plateau_card_le_two_of_half_lt_neg_multiplier hW hd hgap
    R.plateau R.height R.height_pos (R.classMass_le hW)
    (fun r hr => (R.classMass_eq_iff hW r).mpr hr) hslope hmissing

end ReverseRecovery

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Actual selected reverse data, the genuine compact assignment minimum,
entire-source exchange and capped residual routing construct a physical full
reverse recovery. No assignment, minimum, completion, coupling or plateau is
supplied as an input. -/
theorem exists_reverseRecovery (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    Nonempty S.ReverseRecovery := by
  obtain ⟨A⟩ := S.exists_reverseAssignmentData hW
  have hpositive := ReverseAssignmentData.exists_positive_mass S A hW hd hgap
  obtain ⟨f, hf, t, ht, P, hP, hbound, hplateau, hfull, hzero, hreceipt, hbalance⟩ :=
    ReverseAssignment.exists_completed_atomic_assignment A.hmeasurableAllowed A.hmeasurableδ
      A.hmassNonneg A.hmassSummable hpositive A.q0 A.feasible
  exact ⟨{
    data := A
    fractions := f
    feasible := hf
    height := t
    height_pos := ht
    codePlateau := P
    codePlateau_nonempty := hP
    mass_le := hbound
    mass_eq_iff := hplateau
    full_atomic := hfull
    zero_diffuse := hzero
    full := A.completedFlow_isFullReverseFlow hW f hf hfull hzero
    entire_source := hreceipt
    source_balance := hbalance
  }⟩

/-- The same original strict-gap selected model constructs an actual full
reverse endpoint with a positive finite original plateau, its entire-source
balance, the sharp reverse credit and the physical plateau cardinality bound. -/
theorem exists_reverseRecovery_with_budget (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ R : S.ReverseRecovery, R.plateau.Nonempty ∧
      (R.plateau.card : ℝ) < 2 / (-m) ∧
      MeasurableSet (S.reverseCompulsorySource R.plateau) ∧
      (R.plateau.card : ℝ) * R.height =
        (∑ r ∈ R.plateau, μ.real {x | S.ρ x = r.val}) + μ.real (S.reverseCompulsorySource R.plateau) ∧
      0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) ∧
      density R.isFullReverseFlow.endpoint < d ∧
      c + KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) / 2 +
          (-m) * (d - density R.isFullReverseFlow.endpoint) ≤ R.height ^ 2 ∧ c < R.height ^ 2 ∧
      ((2 / 3 : ℝ) ≤ -m → R.plateau.card ≤ 2) ∧
      ((1 / 2 : ℝ) < -m ∧ (1 / 12 : ℝ) < 1 / 2 - d → R.plateau.card ≤ 2) := by
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  obtain ⟨hE, hdend, hcredit, hlt⟩ := R.endpoint_credit hW hd hgap
  exact ⟨R, R.plateau_nonempty, R.card_lt_two_div_neg_multiplier hW hd hgap,
    R.measurableSet_source, R.original_source_balance, hE, hdend, hcredit, hlt,
    fun hs => R.card_le_two_of_neg_multiplier_ge_two_thirds hW hd hgap hs,
    fun hs => R.card_le_two_of_half_lt_neg_multiplier hW hd hgap hs.1 hs.2⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

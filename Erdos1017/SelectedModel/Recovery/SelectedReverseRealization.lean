module

public import Erdos1017.SelectedModel.Recovery.SelectedReverseAssignment
public import Erdos1017.SelectedModel.Recovery.FullReversePlateau
public import Erdos1017.SelectedModel.Flows.FullForwardPeakAtom
public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentAtomicCompletion
public import Erdos1017.SelectedModel.Flows.CompletedAtomicRelationFlow

/-!
# Realization of the selected reverse assignment

Active slots carry their original whole-row codes, inactive slots have empty
allowed regions, and the plateau retains the original mass sum. The compulsory
source `reverseCompulsorySource` is identified with its coded form, with
measurability and mass derived from that identity; this feeds
`SelectedReverseRecovery`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

namespace ReverseAssignmentData

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- An active Nat slot has exactly its original whole-row code. -/
theorem label_code (A : S.ReverseAssignmentData) (i : ℕ) (r : S.I)
    (hi : A.label i = some r) : A.code r = i := by
  have hr := A.label_eligible i r hi
  have hc : A.label (A.code r) = some r := by
    rw [A.hlabel]
    exact S.reverseAtomLabel_eq_some A.code r hr
  exact (A.label_unique i (A.code r) r hi hc).symm

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem label_at_code (A : S.ReverseAssignmentData) (r : S.I)
    (hr : r ∈ S.eligibleReverseAtom) : A.label (A.code r) = some r := by
  rw [A.hlabel]
  exact S.reverseAtomLabel_eq_some A.code r hr

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every inactive slot has empty actual allowed region, not a fictional
positive recipient with an unlicensed source set. -/
theorem allowed_eq_empty_of_label_none (A : S.ReverseAssignmentData)
    (i : ℕ) (hi : A.label i = none) : A.allowed i = ∅ := by
  rw [A.hallowed]
  simp only [reverseAllowed, hi]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Feasibility forces every inactive coordinate to vanish on the original
restricted HIGH source law. -/
theorem inactive_coordinate_zero (A : S.ReverseAssignmentData)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f)
    (i : ℕ) (hi : A.label i = none) : (f i : Ω → ℝ) =ᵐ[μ.restrict S.H] 0 := by
  filter_upwards [hf.support i] with x hx
  exact hx (by rw [A.allowed_eq_empty_of_label_none i hi]; exact notMem_empty x)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem inactive_mass_zero (A : S.ReverseAssignmentData)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f)
    (i : ℕ) (hi : A.label i = none) : ReverseAssignment.mass A.a f i = 0 := by
  rw [ReverseAssignment.mass, integral_congr_ae (A.inactive_coordinate_zero f hf i hi)]
  rw [A.ha]
  simp only [reverseAtomMass, hi, Pi.zero_apply, integral_zero, add_zero]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Original full geometric cells retain only their non-HIGH mass. HIGH
slots have positive old geometric mass but zero retained baseline. -/
theorem original_mass_eq_retained_cell (A : S.ReverseAssignmentData) (i : ℕ) :
    A.a i = μ.real (S.reverseAllAtomFiber A.code i \ S.H) := by
  by_cases hi : ∃ r : S.I, A.code r = i
  · obtain ⟨r, hr⟩ := hi
    rw [← hr, S.reverseAllAtomFiber_code]
    by_cases hel : r ∈ S.eligibleReverseAtom
    · have hl := A.label_at_code r hel
      rw [A.ha]
      simp only [reverseAtomMass, hl]
      apply congrArg ENNReal.toReal
      apply measure_congr
      have hnot := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hel
      filter_upwards [hnot] with x hx
      exact propext ⟨fun h => ⟨h, hx h⟩, And.left⟩
    · have hl : A.label (A.code r) = none := by
        rw [A.hlabel]
        exact S.reverseAtomLabel_eq_none_of_not_eligible A.code r hel
      rw [A.ha]
      simp only [reverseAtomMass, hl]
      have hHigh := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp
        (S.ae_high_of_not_eligibleReverseAtom r hel)
      have hz : μ ({x | S.ρ x = r.val} \ S.H) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hHigh] with x hx hmem
        exact hmem.2 (hx hmem.1)
      exact (congrArg ENNReal.toReal hz).symm
  · have hl : A.label i = none := by
      rw [A.hlabel]
      exact S.reverseAtomLabel_eq_none_of_hole A.code i hi
    rw [A.ha]
    simp only [reverseAtomMass, hl]
    simp [reverseAllAtomFiber, hi]

/-- The generic original-relation section test is exactly the selected
literal allowed missing region on the original HIGH source measure. -/
theorem ae_allowed_iff_raw_cell_mass_pos (A : S.ReverseAssignmentData)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (i : ℕ) :
    ∀ᵐ x ∂μ.restrict S.H,
      x ∈ A.allowed i ↔ 0 < S.reverseCellMass A.code i x := by
  rw [A.hallowed, A.hlabel]
  exact S.ae_reverseAllowed_iff_cellMass_pos hW A.code i

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual complement of all geometric cells is the original diffuse
remainder; removed HIGH cells are not reclassified as dust. -/
theorem all_cells_complement (A : S.ReverseAssignmentData) :
    (⋃ i, S.reverseAllAtomFiber A.code i)ᶜ = S.D := by
  rw [S.reverseAllAtomFiber_union]
  exact S.hDeq.symm

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The raw diffuse relation section and the selected diffuse LOW section
agree on the actual original HIGH source law. -/
theorem ae_raw_diffuse_mass_eq (A : S.ReverseAssignmentData) :
    ∀ᵐ x ∂μ.restrict S.H,
      μ.real {y | y ∈ (⋃ i, S.reverseAllAtomFiber A.code i)ᶜ ∧
        (y, x) ∈ S.reverseAssignmentRelation} = A.δ x := by
  rw [A.all_cells_complement, A.hδ]
  exact S.ae_reverseRawDiffuse_eq_reverseDiffuseSupply

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The generic raw diffuse section uses exactly the selected original
HIGH-source diffuse mass, modulo the original restricted source law. -/
theorem ae_raw_remainder_eq (A : S.ReverseAssignmentData) :
    MissingFlow.NormalizedAtomicFractions.remainderSectionMass μ S.reverseAssignmentRelation
      (S.reverseAllAtomFiber A.code) =ᵐ[μ.restrict S.H] A.δ := by
  filter_upwards [A.ae_raw_diffuse_mass_eq] with x hx
  simpa only [MissingFlow.NormalizedAtomicFractions.remainderSectionMass,
    Set.inter_def, Set.mem_ofPred_eq] using hx

/-- A selected feasible assignment is feasible for the actual raw relation
sections used by the original-product realization adapter. -/
theorem raw_feasible (A : S.ReverseAssignmentData) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f) :
    ReverseAssignment.Feasible
      (MissingFlow.NormalizedAtomicFractions.allowed μ S.reverseAssignmentRelation
        (S.reverseAllAtomFiber A.code))
      (MissingFlow.NormalizedAtomicFractions.remainderSectionMass μ S.reverseAssignmentRelation
        (S.reverseAllAtomFiber A.code)) f := by
  have hallowed : ∀ i, ∀ᵐ x ∂μ.restrict S.H,
      x ∈ MissingFlow.NormalizedAtomicFractions.allowed μ S.reverseAssignmentRelation
        (S.reverseAllAtomFiber A.code) i ↔ x ∈ A.allowed i := by
    intro i
    filter_upwards [A.ae_allowed_iff_raw_cell_mass_pos hW i] with x hx
    simpa only [MissingFlow.NormalizedAtomicFractions.allowed,
      MissingFlow.NormalizedAtomicFractions.atomSectionMass, reverseCellMass,
      Set.inter_def, Set.mem_ofPred_eq] using hx.symm
  have hδ : ∀ᵐ x ∂μ.restrict S.H,
      MissingFlow.NormalizedAtomicFractions.remainderSectionMass μ S.reverseAssignmentRelation
        (S.reverseAllAtomFiber A.code) x = 0 ↔ A.δ x = 0 :=
    A.ae_raw_remainder_eq.mono (fun _ hx => by rw [hx])
  exact (ReverseAssignment.feasible_congr hallowed hδ).mpr hf

/-- The actual whole-row geometry licenses every original-cell/source
rectangle required by the generic physical-density construction. -/
theorem raw_cell_rectangle (A : S.ReverseAssignmentData) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (i : ℕ) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.reverseAllAtomFiber A.code i →
      p.2 ∈ S.H ∩ MissingFlow.NormalizedAtomicFractions.allowed μ S.reverseAssignmentRelation
        (S.reverseAllAtomFiber A.code) i → p ∈ S.reverseAssignmentRelation := by
  have hallowed : ∀ᵐ x ∂μ, x ∈ S.H →
      (x ∈ A.allowed i ↔ 0 < S.reverseCellMass A.code i x) :=
    (ae_restrict_iff' S.hpartition.1).mp (A.ae_allowed_iff_raw_cell_mass_pos hW i)
  cases hi : A.label i with
  | none =>
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hallowed] with p hp _ hy
    have hypos : 0 < S.reverseCellMass A.code i p.2 := hy.2
    have hmem := (hp hy.1).mpr hypos
    rw [A.allowed_eq_empty_of_label_none i hi] at hmem
    exact False.elim (notMem_empty _ hmem)
  | some r =>
    have hcell : S.reverseAllAtomFiber A.code i = {x | S.ρ x = r.val} := by
      rw [← A.label_code i r hi, S.reverseAllAtomFiber_code]
    have hall : A.allowed i = KernelOperator.wholeFiberMissingSet S.ρ r.val := by
      rw [A.hallowed]
      simp only [reverseAllowed, hi]
    filter_upwards [S.ae_reverse_fiber_relation_iff_missing r.val r.property
      (hW.moment_mem.mono (fun _ hp => hp.1)),
      Measure.quasiMeasurePreserving_snd.ae hallowed] with p hp ha hx hy
    have hxr : S.ρ p.1 = r.val := by simpa only [hcell, mem_ofPred_eq] using hx
    have hmem : p.2 ∈ A.allowed i := (ha hy.1).mpr hy.2
    exact (hp hxr hy.1).mpr (hall ▸ hmem)

/-- The actual original-product recovered density, combining completed
atomic fractions with the normalized literal diffuse recipient relation. -/
def completedFlow (A : S.ReverseAssignmentData)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) : Ω × Ω → ℝ :=
  MissingFlow.CompletedAtomicRelation.density μ S.H S.reverseAssignmentRelation
    (S.reverseAllAtomFiber A.code) f

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Completion statements transfer to the equal raw diffuse section on the
same original restricted HIGH source measure. -/
theorem raw_completion (A : S.ReverseAssignmentData)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H))
    (hfull : ∀ᵐ x ∂μ.restrict S.H, A.δ x = 0 → HasSum (fun i => f i x) 1)
    (hzero : ∀ᵐ x ∂μ.restrict S.H, A.δ x ≠ 0 → ∀ i, f i x = 0) :
    (∀ᵐ x ∂μ.restrict S.H,
      MissingFlow.NormalizedAtomicFractions.remainderSectionMass μ S.reverseAssignmentRelation
        (S.reverseAllAtomFiber A.code) x = 0 → HasSum (fun i => f i x) 1) ∧
      ∀ᵐ x ∂μ.restrict S.H,
        MissingFlow.NormalizedAtomicFractions.remainderSectionMass μ S.reverseAssignmentRelation
          (S.reverseAllAtomFiber A.code) x ≠ 0 → ∀ i, f i x = 0 := by
  constructor
  · filter_upwards [A.ae_raw_remainder_eq, hfull] with x hx hf hz
    exact hf (hx ▸ hz)
  · filter_upwards [A.ae_raw_remainder_eq, hzero] with x hx hf hn
    exact hf (fun hz => hn (hx.trans hz))

/-- The constructed atomic and diffuse components give an actual full
reverse flow. Neither component alone is treated as a full endpoint. -/
theorem completedFlow_isFullReverseFlow (A : S.ReverseAssignmentData)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f)
    (hfull : ∀ᵐ x ∂μ.restrict S.H, A.δ x = 0 → HasSum (fun i => f i x) 1)
    (hzero : ∀ᵐ x ∂μ.restrict S.H, A.δ x ≠ 0 → ∀ i, f i x = 0) :
    S.IsFullReverseFlow (A.completedFlow f) := by
  have hraw := A.raw_feasible hW f hf
  have hc := A.raw_completion f hfull hzero
  have hR : MeasurableSet S.reverseAssignmentRelation := S.measurable_oriented_relations.2
  have hsources : ∀ᵐ x ∂μ,
      x ∈ MissingFlow.positiveSources μ S.reverseAssignmentRelation ↔ x ∈ S.H :=
    Eventually.of_forall (fun x => by rw [S.reverseAssignment_positiveSources])
  have hprops := MissingFlow.CompletedAtomicRelation.integrable_nonnegative
    hR S.hpartition.1 (S.measurableSet_reverseAllAtomFiber A.code) hraw
  have hsupply := MissingFlow.CompletedAtomicRelation.supply_density hR S.hpartition.1
    (S.measurableSet_reverseAllAtomFiber A.code) hsources hraw hc.1 hc.2
  have hsupport := MissingFlow.CompletedAtomicRelation.supported_density S.hpartition.1
    hraw (A.raw_cell_rectangle hW)
  refine ⟨hprops.1, hprops.2, hsupply.1, ?_⟩
  filter_upwards [hsupport, S.hrelation] with p hp hr hne
  have hRmem : p ∈ S.reverseAssignmentRelation := by
    by_contra hn
    exact hne (hp hn)
  have hclass : p.1 ∈ S.L ∧ p.2 ∈ S.H := by
    rcases hr hRmem.1 with h | h
    · exact False.elim ((not_lt_of_ge h.2.2.le) hRmem.2)
    · exact ⟨h.2.1, h.1⟩
  exact ⟨hRmem.1, hclass⟩

/-- Each original geometric Nat cell has its actual endpoint mass. The
retained baseline removes HIGH and the assigned receipt is on μ restricted
to HIGH; these two original measures are kept distinct. -/
theorem completedFlow_cell_mass (A : S.ReverseAssignmentData)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f)
    (hfull : ∀ᵐ x ∂μ.restrict S.H, A.δ x = 0 → HasSum (fun i => f i x) 1)
    (hzero : ∀ᵐ x ∂μ.restrict S.H, A.δ x ≠ 0 → ∀ i, f i x = 0) (i : ℕ) :
    (missingFlowEndpointLaw μ (A.completedFlow f)).real (S.reverseAllAtomFiber A.code i) =
      ReverseAssignment.mass A.a f i := by
  have hq := A.completedFlow_isFullReverseFlow hW f hf hfull hzero
  have hraw := A.raw_feasible hW f hf
  have hc := A.raw_completion f hfull hzero
  have hR : MeasurableSet S.reverseAssignmentRelation := S.measurable_oriented_relations.2
  have hsources : ∀ᵐ x ∂μ,
      x ∈ MissingFlow.positiveSources μ S.reverseAssignmentRelation ↔ x ∈ S.H :=
    Eventually.of_forall (fun x => by rw [S.reverseAssignment_positiveSources])
  rw [missingFlowEndpointLaw, weightedMeasure_real_set _
    (integrableTiltWeight_integrable _ (MissingFlow.integrable_direction hq.integrable) 1)
    (integrableTiltWeight_nonnegative _ (MissingFlow.direction_ge_neg_one hq.nonnegative hq.supply_le_one)
      1 ⟨by norm_num, le_rfl⟩) _ (S.measurableSet_reverseAllAtomFiber A.code i)]
  simp only [integrableTiltWeight, one_mul]
  rw [completedFlow, MissingFlow.CompletedAtomicRelation.endpoint_mass_on_atom hR S.hpartition.1
    (S.measurableSet_reverseAllAtomFiber A.code) hsources hraw hc.1 hc.2
    (S.reverseAllAtomFiber_pairwise A.code) i, ← A.original_mass_eq_retained_cell]
  rfl

/-- Every original whole-row label, including a removed HIGH label, has
its exact physical endpoint mass at its original Nat code. -/
theorem completedFlow_classMass (A : S.ReverseAssignmentData)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f)
    (hfull : ∀ᵐ x ∂μ.restrict S.H, A.δ x = 0 → HasSum (fun i => f i x) 1)
    (hzero : ∀ᵐ x ∂μ.restrict S.H, A.δ x ≠ 0 → ∀ i, f i x = 0) (r : S.I) :
    S.reverseClassMass (A.completedFlow f) r = ReverseAssignment.mass A.a f (A.code r) := by
  rw [reverseClassMass, S.collapsedPartLabel_fiber, ← S.reverseAllAtomFiber_code A.code r]
  exact A.completedFlow_cell_mass hW f hf hfull hzero (A.code r)

/-- Removed HIGH classes have zero actual endpoint mass, derived from
inactivity and the true all-cell mass formula. -/
theorem completedFlow_classMass_zero_of_not_eligible (A : S.ReverseAssignmentData)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f)
    (hfull : ∀ᵐ x ∂μ.restrict S.H, A.δ x = 0 → HasSum (fun i => f i x) 1)
    (hzero : ∀ᵐ x ∂μ.restrict S.H, A.δ x ≠ 0 → ∀ i, f i x = 0)
    (r : S.I) (hr : r ∉ S.eligibleReverseAtom) : S.reverseClassMass (A.completedFlow f) r = 0 := by
  rw [A.completedFlow_classMass hW f hf hfull hzero r]
  apply A.inactive_mass_zero f hf
  rw [A.hlabel]
  exact S.reverseAtomLabel_eq_none_of_not_eligible A.code r hr

/-- Map a finite coded plateau back to actual original whole-row labels.
Inactive slots disappear; no two active slots are merged. -/
def plateauLabels (A : S.ReverseAssignmentData) (P : Finset ℕ) : Finset S.I :=
  P.filterMap A.label A.label_unique

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem mem_plateauLabels (A : S.ReverseAssignmentData) (P : Finset ℕ) (r : S.I) :
    r ∈ A.plateauLabels P ↔ ∃ i ∈ P, A.label i = some r :=
  Finset.mem_filterMap A.label

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem plateauLabels_eligible (A : S.ReverseAssignmentData) (P : Finset ℕ)
    (r : S.I) (hr : r ∈ A.plateauLabels P) : r ∈ S.eligibleReverseAtom := by
  obtain ⟨i, _, hi⟩ := (A.mem_plateauLabels P r).mp hr
  exact A.label_eligible i r hi

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A positive coded plateau has no inactive labels, as a consequence of
actual feasible-coordinate support. -/
theorem plateau_label_ne_none (A : S.ReverseAssignmentData)
    (f : ℕ → Lp ℝ 2 (μ.restrict S.H)) (hf : ReverseAssignment.Feasible A.allowed A.δ f)
    (P : Finset ℕ) (t : ℝ) (ht : 0 < t)
    (hplateau : ∀ i ∈ P, ReverseAssignment.mass A.a f i = t) :
    ∀ i ∈ P, A.label i ≠ none := by
  intro i hi hl
  have hz := A.inactive_mass_zero f hf i hl
  rw [hplateau i hi] at hz
  exact ht.ne' hz

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem plateauLabels_code_image (A : S.ReverseAssignmentData) (P : Finset ℕ)
    (hactive : ∀ i ∈ P, A.label i ≠ none) :
    (A.plateauLabels P).image A.code = P := by
  ext i
  constructor
  · intro hi
    obtain ⟨r, hr, hri⟩ := Finset.mem_image.mp hi
    obtain ⟨j, hj, hlabel⟩ := (A.mem_plateauLabels P r).mp hr
    exact ((A.label_code j r hlabel).symm.trans hri) ▸ hj
  · intro hi
    cases hl : A.label i with
    | none => exact False.elim (hactive i hi hl)
    | some r => exact Finset.mem_image.mpr ⟨r, (A.mem_plateauLabels P r).mpr ⟨i, hi, hl⟩,
        A.label_code i r hl⟩

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Membership in the original plateau is exactly membership of the
original atom's code in the positive active Nat plateau. -/
theorem code_mem_iff_plateauLabels (A : S.ReverseAssignmentData) (P : Finset ℕ)
    (hactive : ∀ i ∈ P, A.label i ≠ none) (r : S.I) :
    A.code r ∈ P ↔ r ∈ A.plateauLabels P := by
  constructor
  · intro hr
    have hi : A.code r ∈ (A.plateauLabels P).image A.code :=
      (A.plateauLabels_code_image P hactive).symm ▸ hr
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hi
    exact A.code.injective heq ▸ hu
  · intro hr
    have hi := Finset.mem_image_of_mem A.code hr
    rwa [A.plateauLabels_code_image P hactive] at hi

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem plateauLabels_card (A : S.ReverseAssignmentData) (P : Finset ℕ)
    (hactive : ∀ i ∈ P, A.label i ≠ none) : (A.plateauLabels P).card = P.card := by
  calc
    _ = ((A.plateauLabels P).image A.code).card :=
      (Finset.card_image_of_injective _ A.code.injective).symm
    _ = P.card := congrArg Finset.card (A.plateauLabels_code_image P hactive)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The code-to-original map retains the literal original mass sum. -/
theorem plateauLabels_original_mass_sum (A : S.ReverseAssignmentData) (P : Finset ℕ)
    (hactive : ∀ i ∈ P, A.label i ≠ none) :
    (∑ i ∈ P, A.a i) = ∑ r ∈ A.plateauLabels P, μ.real {x | S.ρ x = r.val} := by
  calc
    _ = ∑ i ∈ (A.plateauLabels P).image A.code, A.a i :=
      congrArg (fun F : Finset ℕ => ∑ i ∈ F, A.a i) (A.plateauLabels_code_image P hactive).symm
    _ = ∑ r ∈ A.plateauLabels P, A.a (A.code r) :=
      Finset.sum_image (fun _ _ _ _ he => A.code.injective he)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [A.ha]
      simp only [reverseAtomMass, A.label_at_code r (A.plateauLabels_eligible P r hr)]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Literal selected missing incidence, including inactive Nat slots. -/
theorem mem_allowed_iff (A : S.ReverseAssignmentData) (i : ℕ) (x : Ω) :
    x ∈ A.allowed i ↔ ∃ r : S.I, A.label i = some r ∧
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val := by
  rw [A.hallowed]
  cases hi : A.label i <;> simp [reverseAllowed, hi]

end ReverseAssignmentData

/-- The entire original HIGH source whose nonempty eligible original
missing-label set lies in the displayed original plateau and has no diffuse
LOW recipient mass. The definition does not choose a source subset. -/
def reverseCompulsorySource (S : SelectedHighLowStructure W m) (P : Finset S.I) : Set Ω :=
  S.H ∩ {x | S.reverseDiffuseSupply x = 0 ∧
    (∃ r : S.I, r ∈ S.eligibleReverseAtom ∧ x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val) ∧
    ∀ r : S.I, r ∈ S.eligibleReverseAtom →
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val → r ∈ P}

namespace ReverseAssignmentData

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The entire coded compulsory source is literally the same entire
original geometric source after injective label decoding. -/
theorem compulsorySource_eq_original (A : S.ReverseAssignmentData) (P : Finset ℕ) :
    S.H ∩ ReverseAssignment.compulsorySource A.allowed A.δ P =
      S.reverseCompulsorySource (A.plateauLabels P) := by
  ext x
  constructor
  · rintro ⟨hxH, hxδ, hsome, hall⟩
    refine ⟨hxH, ?_, ?_, ?_⟩
    · simpa only [A.hδ] using hxδ
    · obtain ⟨i, hi⟩ := hsome
      obtain ⟨r, hir, hxr⟩ := (A.mem_allowed_iff i x).mp hi
      exact ⟨r, A.label_eligible i r hir, hxr⟩
    · intro r hr hxr
      obtain ⟨i, hi⟩ := A.label_exhaustive r hr
      have hxi : x ∈ A.allowed i := (A.mem_allowed_iff i x).mpr ⟨r, hi, hxr⟩
      exact (A.mem_plateauLabels P r).mpr ⟨i, hall i hxi, hi⟩
  · rintro ⟨hxH, hxδ, hsome, hall⟩
    refine ⟨hxH, ?_, ?_, ?_⟩
    · simpa only [A.hδ] using hxδ
    · obtain ⟨r, hr, hxr⟩ := hsome
      obtain ⟨i, hi⟩ := A.label_exhaustive r hr
      exact ⟨i, (A.mem_allowed_iff i x).mpr ⟨r, hi, hxr⟩⟩
    · intro i hxi
      obtain ⟨r, hi, hxr⟩ := (A.mem_allowed_iff i x).mp hxi
      have hrP := hall r (A.label_eligible i r hi) hxr
      obtain ⟨j, hj, hjr⟩ := (A.mem_plateauLabels P r).mp hrP
      exact (A.label_unique j i r hjr hi) ▸ hj

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Measurability of the entire original source is derived from its exact
coded source identity, not assumed. -/
theorem measurableSet_compulsorySource (A : S.ReverseAssignmentData) (P : Finset ℕ) :
    MeasurableSet (S.reverseCompulsorySource (A.plateauLabels P)) := by
  rw [← A.compulsorySource_eq_original]
  exact S.hpartition.1.inter
    (ReverseAssignment.measurableSet_compulsorySource A.hmeasurableAllowed A.hmeasurableδ P)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual restricted HIGH-source mass is exactly the original-law
mass of the entire physical compulsory source. -/
theorem compulsorySource_mass (A : S.ReverseAssignmentData) (P : Finset ℕ) :
    (μ.restrict S.H).real (ReverseAssignment.compulsorySource A.allowed A.δ P) =
      μ.real (S.reverseCompulsorySource (A.plateauLabels P)) := by
  rw [← A.compulsorySource_eq_original]
  simp only [measureReal_def]
  rw [Measure.restrict_apply
    (ReverseAssignment.measurableSet_compulsorySource A.hmeasurableAllowed A.hmeasurableδ P),
    Set.inter_comm]

end ReverseAssignmentData

end Erdos1017.CappedModel.SelectedHighLowStructure

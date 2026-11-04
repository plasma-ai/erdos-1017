module

public import Erdos1017.SelectedModel.Flows.SelectedMissingFlowConstruction
public import Erdos1017.SelectedModel.Flows.SelectedMissingFlowEndpoints
public import Erdos1017.SelectedModel.Flows.SelectedAtomRedirection
public import Erdos1017.SelectedModel.Structure.SelectedMultipartiteHalves
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassMasses
public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentCompactness
public import Erdos1017.SelectedModel.Structure.NormalizedAtomicFractions
public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentCongruence

/-!
# Reverse assignment data of the selected model

Eligible reverse atoms (positive whole-row fibers that are low or neutral, with
high fibers excluded) and the structure `ReverseAssignmentData`, a feasible
relaxed assignment on the original high source law built from the reverse flow,
with positive recipient mass under the strict-gap hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

namespace SelectedHighLowStructure

/-- Original positive whole-row fibers retained as reverse endpoint recipient
labels. HIGH fibers are excluded; each remaining fiber is LOW or neutral. -/
def eligibleReverseAtom (S : SelectedHighLowStructure W m) : Set S.I :=
  {r | ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∉ S.H}

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem eligibleReverseAtom_low_or_neutral (S : SelectedHighLowStructure W m)
    (r : S.I) (hr : r ∈ S.eligibleReverseAtom) :
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.L) ∨
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) := by
  rcases S.hfiberClass r.val r.property with hH | hL | hN
  · obtain ⟨x, _, _, hxH, hxnotH⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers r.val r.property).2.1.ne'
      ((ae_restrict_mem (S.hfibers r.val r.property).1).and (hH.and hr))
    exact False.elim (hxnotH hxH)
  · exact Or.inl hL
  · exact Or.inr hN

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem ae_high_of_not_eligibleReverseAtom (S : SelectedHighLowStructure W m)
    (r : S.I) (hr : r ∉ S.eligibleReverseAtom) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H := by
  rcases S.hfiberClass r.val r.property with hH | hL | hN
  · exact hH
  · exact False.elim (hr (hL.mono (fun _ hx hy =>
      Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hy hx)))
  · exact False.elim (hr (hN.mono (fun _ hx hy =>
      Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hy hx)))

/-- A partial Nat coding of the eligible original whole-row fibers. -/
def reverseAtomLabel (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) : Option S.I :=
  if h : ∃ r : S.I, e r = i ∧ r ∈ S.eligibleReverseAtom
  then some (Classical.choose h) else none

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAtomLabel_eq_some (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (r : S.I) (hr : r ∈ S.eligibleReverseAtom) :
    S.reverseAtomLabel e (e r) = some r := by
  classical
  have h : ∃ u : S.I, e u = e r ∧ u ∈ S.eligibleReverseAtom := ⟨r, rfl, hr⟩
  simp only [reverseAtomLabel, dite_eq_left h, Option.some.injEq]
  exact e.injective (Classical.choose_spec h).1

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAtomLabel_eligible (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) (r : S.I)
    (h : S.reverseAtomLabel e i = some r) : r ∈ S.eligibleReverseAtom := by
  classical
  by_cases hex : ∃ u : S.I, e u = i ∧ u ∈ S.eligibleReverseAtom
  · have heq : Classical.choose hex = r := by
      simpa only [reverseAtomLabel, dite_eq_left hex, Option.some.injEq] using h
    exact heq ▸ (Classical.choose_spec hex).2
  · simp only [reverseAtomLabel, dite_eq_right hex, reduceCtorEq] at h

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAtomLabel_unique (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i j : ℕ) (r : S.I)
    (hi : S.reverseAtomLabel e i = some r)
    (hj : S.reverseAtomLabel e j = some r) : i = j := by
  classical
  have hcode (k : ℕ) (hk : S.reverseAtomLabel e k = some r) : e r = k := by
    by_cases hex : ∃ u : S.I, e u = k ∧ u ∈ S.eligibleReverseAtom
    · have heq : Classical.choose hex = r := by
        simpa only [reverseAtomLabel, dite_eq_left hex, Option.some.injEq] using hk
      simpa only [heq] using (Classical.choose_spec hex).1
    · simp only [reverseAtomLabel, dite_eq_right hex, reduceCtorEq] at hk
  exact (hcode i hi).symm.trans (hcode j hj)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAtomLabel_eq_none_of_not_eligible (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (r : S.I) (hr : r ∉ S.eligibleReverseAtom) :
    S.reverseAtomLabel e (e r) = none := by
  classical
  have h : ¬∃ u : S.I, e u = e r ∧ u ∈ S.eligibleReverseAtom := by
    rintro ⟨u, hu, heligible⟩
    exact hr (e.injective hu ▸ heligible)
  simp only [reverseAtomLabel, dite_eq_right h]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAtomLabel_eq_none_of_hole (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) (hi : ¬∃ r : S.I, e r = i) :
    S.reverseAtomLabel e i = none := by
  classical
  have h : ¬∃ r : S.I, e r = i ∧ r ∈ S.eligibleReverseAtom := by
    rintro ⟨r, hr, _⟩
    exact hi ⟨r, hr⟩
  simp only [reverseAtomLabel, dite_eq_right h]

/-- All original whole-row fibers, including the HIGH fibers that receive
no reverse flow, form the Nat-coded partition used for integration. -/
def reverseAllAtomFiber (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) : Set Ω :=
  if h : ∃ r : S.I, e r = i then {x | S.ρ x = (Classical.choose h).val} else ∅

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAllAtomFiber_code (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (r : S.I) :
    S.reverseAllAtomFiber e (e r) = {x | S.ρ x = r.val} := by
  classical
  have h : ∃ u : S.I, e u = e r := ⟨r, rfl⟩
  simp only [reverseAllAtomFiber, dite_eq_left h]
  exact congrArg (fun u : S.I => {x | S.ρ x = u.val}) (e.injective (Classical.choose_spec h))

theorem measurableSet_reverseAllAtomFiber (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) : MeasurableSet (S.reverseAllAtomFiber e i) := by
  classical
  unfold reverseAllAtomFiber
  split
  · let : MeasurableSpace (Lp ℝ 2 μ) := borel _
    let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
    exact S.hρ.measurable (measurableSet_singleton _)
  · exact MeasurableSet.empty

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAllAtomFiber_pairwise (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) :
    Pairwise (fun i j => Disjoint (S.reverseAllAtomFiber e i) (S.reverseAllAtomFiber e j)) := by
  classical
  intro i j hij
  by_cases hi : ∃ r : S.I, e r = i
  · by_cases hj : ∃ r : S.I, e r = j
    · have hne : Classical.choose hi ≠ Classical.choose hj := by
        intro heq
        exact hij ((Classical.choose_spec hi).symm.trans
          (heq ▸ Classical.choose_spec hj))
      have hne' : (Classical.choose hi).val ≠ (Classical.choose hj).val := by
        intro heq
        exact hne (Subtype.ext heq)
      simpa only [reverseAllAtomFiber, dite_eq_left hi, dite_eq_left hj] using
        S.hdisjoint (Classical.choose hi).property (Classical.choose hj).property hne'
    · simp only [reverseAllAtomFiber, dite_eq_left hi, dite_eq_right hj]
      exact disjoint_empty _
  · simp only [reverseAllAtomFiber, dite_eq_right hi]
    exact empty_disjoint _

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAllAtomFiber_union (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) :
    (⋃ i, S.reverseAllAtomFiber e i) = ⋃ r ∈ S.I, {x | S.ρ x = r} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hex : ∃ r : S.I, e r = i
    · have hr : S.ρ x = (Classical.choose hex).val := by
        simpa only [reverseAllAtomFiber, dite_eq_left hex, Set.mem_ofPred_eq] using hi
      exact mem_iUnion.mpr ⟨(Classical.choose hex).val,
        mem_iUnion.mpr ⟨(Classical.choose hex).property, hr⟩⟩
    · simp only [reverseAllAtomFiber, dite_eq_right hex] at hi
      simp at hi
  · intro hx
    obtain ⟨r, hr⟩ := mem_iUnion.mp hx
    obtain ⟨hrI, hrx⟩ := mem_iUnion.mp hr
    exact mem_iUnion.mpr ⟨e ⟨r, hrI⟩, by
      rw [S.reverseAllAtomFiber_code e ⟨r, hrI⟩]
      exact hrx⟩

/-- The original mass of one active recipient atom, with zero in unused slots. -/
def reverseAtomMass (S : SelectedHighLowStructure W m)
    (label : ℕ → Option S.I) (i : ℕ) : ℝ :=
  match label i with
  | some r => μ.real {x | S.ρ x = r.val}
  | none => 0

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAtomMass_nonneg (S : SelectedHighLowStructure W m)
    (label : ℕ → Option S.I) (i : ℕ) : 0 ≤ S.reverseAtomMass label i := by
  cases h : label i with
  | none => simp only [reverseAtomMass, h, le_refl]
  | some r =>
    simp only [reverseAtomMass, h]
    exact measureReal_nonneg

theorem reverseAtomMass_summable (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) : Summable (S.reverseAtomMass (S.reverseAtomLabel e)) := by
  classical
  have hfull : Summable (fun i => μ.real (S.reverseAllAtomFiber e i)) := by
    apply ENNReal.summable_toReal
    rw [← measure_iUnion (S.reverseAllAtomFiber_pairwise e)
      (S.measurableSet_reverseAllAtomFiber e)]
    exact measure_ne_top _ _
  apply Summable.of_nonneg_of_le (S.reverseAtomMass_nonneg (S.reverseAtomLabel e))
    (fun i => ?_) hfull
  by_cases hi : ∃ r : S.I, e r = i ∧ r ∈ S.eligibleReverseAtom
  · have hAll : ∃ r : S.I, e r = i := ⟨Classical.choose hi, (Classical.choose_spec hi).1⟩
    simp only [reverseAtomMass, reverseAtomLabel, dite_eq_left hi,
      reverseAllAtomFiber, dite_eq_left hAll]
    have heq : Classical.choose hi = Classical.choose hAll :=
      e.injective ((Classical.choose_spec hi).1.trans (Classical.choose_spec hAll).symm)
    rw [heq]
  · simp only [reverseAtomMass, reverseAtomLabel, dite_eq_right hi]
    exact measureReal_nonneg

/-- A source may send reverse-flow mass to an active atom only when its
original whole row has that atom as an actual missing region. -/
def reverseAllowed (S : SelectedHighLowStructure W m)
    (label : ℕ → Option S.I) (i : ℕ) : Set Ω :=
  match label i with
  | some r => KernelOperator.wholeFiberMissingSet S.ρ r.val
  | none => ∅

/-- Raw diffuse LOW missing-section mass, distinct from the weighted reverse
flow received by that diffuse section. -/
def reverseDiffuseSupply (S : SelectedHighLowStructure W m) (x : Ω) : ℝ :=
  μ.real {y | y ∈ S.D ∩ S.L ∧ (y, x) ∈ actualZeroRelation W m S.ρ}

/-- The actual oriented relation used by the selected reverse flow. -/
def reverseAssignmentRelation (S : SelectedHighLowStructure W m) : Set (Ω × Ω) :=
  MissingFlow.reverseRelation (actualZeroRelation W m S.ρ)
    (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)))

/-- The raw reverse-relation mass of one Nat-coded original recipient cell. -/
def reverseCellMass (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) (x : Ω) : ℝ :=
  μ.real {y | y ∈ S.reverseAllAtomFiber e i ∧
    (y, x) ∈ S.reverseAssignmentRelation}

theorem measurable_reverseCellMass (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) : Measurable (S.reverseCellMass e i) := by
  have hset : MeasurableSet
      {p : Ω × Ω | p.1 ∈ S.reverseAllAtomFiber e i ∧
        p ∈ S.reverseAssignmentRelation} :=
    ((S.measurableSet_reverseAllAtomFiber e i).preimage measurable_fst).inter
      S.measurable_oriented_relations.2
  exact (measurable_measure_prodMk_right (μ := μ) hset).ennreal_toReal

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseCellMass_code (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (r : S.I) (x : Ω) :
    S.reverseCellMass e (e r) x =
      μ.real {y | S.ρ y = r.val ∧ (y, x) ∈ S.reverseAssignmentRelation} := by
  simp only [reverseCellMass, S.reverseAllAtomFiber_code e r, Set.mem_ofPred_eq]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseFlow_eq_normalizedDensity (S : SelectedHighLowStructure W m) :
    S.reverseFlow = MissingFlow.normalizedDensity μ S.reverseAssignmentRelation := rfl

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem reverseAssignment_positiveSources (S : SelectedHighLowStructure W m) :
    MissingFlow.positiveSources μ S.reverseAssignmentRelation = S.H := by
  rw [reverseAssignmentRelation, MissingFlow.positiveSources_reverseRelation, ← S.hH]

/-- Whole-row homogeneity and the selected crossing order identify the raw
reverse relation into any original atom, on the original HIGH source side. -/
theorem ae_reverse_fiber_relation_iff_missing (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r → p.2 ∈ S.H →
      (p ∈ S.reverseAssignmentRelation ↔
        p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r) := by
  filter_upwards [S.ae_kernel_eq_fiber_row r hr, hnonneg, S.hrelation]
    with p hrow hK0 hrel hrec hsrc
  constructor
  · intro hrev
    have hZ : p ∈ actualZeroRelation W m S.ρ := hrev.1
    exact ⟨fun h => hZ.2 (hrec.trans h.symm), by rw [← hrow hrec, hZ.1]⟩
  · intro hN
    have hKzero : shiftedKernel W m p.1 p.2 = 0 :=
      le_antisymm ((hrow hrec).trans_le hN.2) hK0
    have hZ : p ∈ actualZeroRelation W m S.ρ :=
      ⟨hKzero, fun h => hN.1 (h.symm.trans hrec)⟩
    have hdegree : adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
      rcases hrel hZ with h | h
      · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hsrc h.2.1)
      · exact h.2.2
    exact ⟨hZ, hdegree⟩

/-- The raw reverse section into any original positive whole-row atom is
either that whole atom or null, according to its actual missing region. -/
theorem ae_reverseCellMass_code (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (r : S.I)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    ∀ᵐ x ∂μ.restrict S.H,
      S.reverseCellMass e (e r) x =
        if x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val
        then μ.real {y | S.ρ y = r.val} else 0 := by
  classical
  let Br := {y | S.ρ y = r.val}
  let N := KernelOperator.wholeFiberMissingSet S.ρ r.val
  have hpair := S.ae_reverse_fiber_relation_iff_missing r.val r.property hnonneg
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hpair
  have hsections := Measure.ae_ae_of_ae_prod hswap
  have hsectionsH := ae_restrict_of_ae (s := S.H) hsections
  filter_upwards [hsectionsH, ae_restrict_mem S.hpartition.1] with x hx hHx
  rw [S.reverseCellMass_code e r x]
  by_cases hN : x ∈ N
  · have heq : μ {y | S.ρ y = r.val ∧ (y, x) ∈ S.reverseAssignmentRelation} = μ Br := by
      apply measure_congr
      filter_upwards [hx] with y hy
      apply propext
      constructor
      · intro h
        exact h.1
      · intro hyBr
        exact ⟨hyBr, (hy hyBr hHx).mpr hN⟩
    change (μ {y | S.ρ y = r.val ∧ (y, x) ∈ S.reverseAssignmentRelation}).toReal = _
    rw [heq, ite_eq_left hN]
    rfl
  · have hzero : μ {y | S.ρ y = r.val ∧ (y, x) ∈ S.reverseAssignmentRelation} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hx] with y hy hz
      exact hN ((hy hz.1 hHx).mp hz.2)
    change (μ {y | S.ρ y = r.val ∧ (y, x) ∈ S.reverseAssignmentRelation}).toReal = _
    rw [hzero, ite_eq_right hN]
    simp

/-- The generic raw positive-recipient condition is precisely the actual
whole-row missing condition for every coded positive original atom. -/
theorem ae_reverseCellMass_code_pos_iff_missing (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (r : S.I)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    ∀ᵐ x ∂μ.restrict S.H,
      0 < S.reverseCellMass e (e r) x ↔
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val := by
  have hBrpos : 0 < μ.real {y | S.ρ y = r.val} :=
    ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top _ _)
  filter_upwards [S.ae_reverseCellMass_code e r hnonneg] with x hx
  rw [hx]
  by_cases hN : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val
  · simp only [ite_eq_left hN, hBrpos]
    exact ⟨fun _ => hN, fun _ => trivial⟩
  · simp only [ite_eq_right hN, lt_irrefl, false_iff]
    exact hN

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- An original HIGH atom is a Nat-coded partition cell but receives no
raw reverse-relation mass from almost every original source. -/
theorem ae_reverseCellMass_zero_of_not_eligible (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (r : S.I) (hr : r ∉ S.eligibleReverseAtom) :
    ∀ᵐ x ∂μ.restrict S.H, S.reverseCellMass e (e r) x = 0 := by
  let Br := {y | S.ρ y = r.val}
  have hHigh := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp
    (S.ae_high_of_not_eligibleReverseAtom r hr)
  have hLow : ∀ᵐ p ∂μ.prod μ, p ∈ S.reverseAssignmentRelation → p.1 ∈ S.L := by
    filter_upwards [S.hrelation] with p hp hR
    rcases hp hR.1 with h | h
    · exact False.elim ((not_lt_of_ge h.2.2.le) hR.2)
    · exact h.2.1
  have hno : ∀ᵐ p ∂μ.prod μ,
      ¬(S.ρ p.1 = r.val ∧ p ∈ S.reverseAssignmentRelation) := by
    filter_upwards [hLow, Measure.quasiMeasurePreserving_fst.ae hHigh]
      with p hL hH hp
    exact Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hH hp.1) (hL hp.2)
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hno
  have hsections := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [ae_restrict_of_ae hsections] with x hx
  rw [S.reverseCellMass_code e r x]
  have hzero : μ {y | S.ρ y = r.val ∧ (y, x) ∈ S.reverseAssignmentRelation} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hx] with y hy hmem
    exact hy hmem
  change (μ {y | S.ρ y = r.val ∧ (y, x) ∈ S.reverseAssignmentRelation}).toReal = 0
  rw [hzero]
  simp

/-- Every generic positive raw recipient section agrees almost everywhere
with the literal allowed missing region of the selected original model. -/
theorem ae_reverseAllowed_iff_cellMass_pos (S : SelectedHighLowStructure W m)
    {d c : ℝ}
    (hW : FullStationaryClass d c W m) (e : S.I ↪ ℕ) (i : ℕ) :
    ∀ᵐ x ∂μ.restrict S.H,
      x ∈ S.reverseAllowed (S.reverseAtomLabel e) i ↔
        0 < S.reverseCellMass e i x := by
  classical
  by_cases hi : ∃ r : S.I, e r = i
  · let r := Classical.choose hi
    have hr : e r = i := Classical.choose_spec hi
    rw [← hr]
    by_cases hactive : r ∈ S.eligibleReverseAtom
    · have hlabel := S.reverseAtomLabel_eq_some e r hactive
      filter_upwards [S.ae_reverseCellMass_code_pos_iff_missing e r
        (hW.moment_mem.mono fun _ hp => hp.1)] with x hx
      simpa only [reverseAllowed, hlabel] using hx.symm
    · have hlabel := S.reverseAtomLabel_eq_none_of_not_eligible e r hactive
      filter_upwards [S.ae_reverseCellMass_zero_of_not_eligible e r hactive]
        with x hx
      simp [reverseAllowed, hlabel, hx]
  · have hlabel := S.reverseAtomLabel_eq_none_of_hole e i hi
    have hzero (x : Ω) : S.reverseCellMass e i x = 0 := by
      simp [reverseCellMass, reverseAllAtomFiber, hi]
    exact Eventually.of_forall (fun x => by
      simp [reverseAllowed, hlabel, hzero x])

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem ae_reverseRawDiffuse_eq_reverseDiffuseSupply (S : SelectedHighLowStructure W m) :
    ∀ᵐ x ∂μ.restrict S.H,
      μ.real {y | y ∈ S.D ∧ (y, x) ∈ S.reverseAssignmentRelation} =
        S.reverseDiffuseSupply x := by
  let Z := actualZeroRelation W m S.ρ
  let g : Ω → ℝ := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hrel : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      (y, x) ∈ Z → (y ∈ S.H ∧ x ∈ S.L ∧ g x < g y) ∨
        (x ∈ S.H ∧ y ∈ S.L ∧ g y < g x) := by
    simpa only [Prod.swap, Prod.fst_swap, Prod.snd_swap] using
      (Measure.ae_ae_of_ae_prod
        (Measure.measurePreserving_swap.quasiMeasurePreserving.ae S.hrelation))
  filter_upwards [ae_restrict_mem S.hpartition.1, ae_restrict_of_ae hrel]
    with x hxH hrelx
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hrelx] with y hy
  apply propext
  change (y ∈ S.D ∧ (y, x) ∈ Z ∧ g y < g x) ↔
    (y ∈ S.D ∩ S.L ∧ (y, x) ∈ Z)
  constructor
  · rintro ⟨hyD, hyZ, hylt⟩
    rcases hy hyZ with h | h
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxH h.2.1)
    · exact ⟨⟨hyD, h.2.1⟩, hyZ⟩
  · rintro ⟨⟨hyD, hyL⟩, hyZ⟩
    rcases hy hyZ with h | h
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxH h.2.1)
    · exact ⟨hyD, hyZ, h.2.2⟩

/-- The actual reverse-flow supply assigned to one original recipient atom. -/
def reverseAtomicReceipt (S : SelectedHighLowStructure W m)
    (label : ℕ → Option S.I) (i : ℕ) (x : Ω) : ℝ :=
  match label i with
  | some r => ∫ y in {y | S.ρ y = r.val}, S.reverseFlow (y, x) ∂μ
  | none => 0

/-- The generic normalized cell fraction is the actual selected reverse-flow
coefficient on active atoms and zero on all inactive labels. -/
theorem ae_reverse_rawFraction_eq_atomicReceipt (S : SelectedHighLowStructure W m)
    (e : S.I ↪ ℕ) (i : ℕ) :
    MissingFlow.NormalizedAtomicFractions.rawFraction μ
      S.reverseAssignmentRelation (S.reverseAllAtomFiber e) i =ᵐ[μ.restrict S.H]
        S.reverseAtomicReceipt (S.reverseAtomLabel e) i := by
  classical
  let Z := S.reverseAssignmentRelation
  let I := S.reverseAllAtomFiber e
  by_cases hi : ∃ r : S.I, e r = i
  · let r := Classical.choose hi
    have hr : e r = i := Classical.choose_spec hi
    rw [← hr]
    by_cases hactive : r ∈ S.eligibleReverseAtom
    · have hlabel := S.reverseAtomLabel_eq_some e r hactive
      exact Eventually.of_forall (fun x => by
        rw [MissingFlow.NormalizedAtomicFractions.rawFraction_eq_setIntegral_normalizedDensity
          Z S.measurable_oriented_relations.2 I (e r) x]
        simp only [reverseAtomicReceipt, hlabel, S.reverseFlow_eq_normalizedDensity]
        change (∫ y in S.reverseAllAtomFiber e (e r),
          MissingFlow.normalizedDensity μ S.reverseAssignmentRelation (y, x) ∂μ) = _
        rw [S.reverseAllAtomFiber_code e r])
    · have hlabel := S.reverseAtomLabel_eq_none_of_not_eligible e r hactive
      filter_upwards [S.ae_reverseCellMass_zero_of_not_eligible e r hactive]
        with x hx
      simp only [reverseAtomicReceipt, hlabel]
      change MissingFlow.NormalizedAtomicFractions.rawFraction μ Z I (e r) x = 0
      have hN : MissingFlow.NormalizedAtomicFractions.atomSectionMass μ Z I (e r) x = 0 := by
        simpa only [reverseCellMass, MissingFlow.NormalizedAtomicFractions.atomSectionMass,
          Set.inter_def, Set.mem_ofPred_eq] using hx
      simp only [MissingFlow.NormalizedAtomicFractions.rawFraction, hN, zero_div]
  · have hlabel := S.reverseAtomLabel_eq_none_of_hole e i hi
    exact Eventually.of_forall (fun x => by
      simp only [reverseAtomicReceipt, hlabel]
      simp [MissingFlow.NormalizedAtomicFractions.rawFraction,
        MissingFlow.NormalizedAtomicFractions.atomSectionMass,
        reverseAllAtomFiber, hi])

theorem measurable_reverseDiffuseSupply (S : SelectedHighLowStructure W m) :
    Measurable S.reverseDiffuseSupply := by
  have hset : MeasurableSet
      {p : Ω × Ω | p.1 ∈ S.D ∩ S.L ∧ p ∈ actualZeroRelation W m S.ρ} :=
    ((S.hD.inter S.hpartition.2.1).preimage measurable_fst).inter
      (measurableSet_actualZeroRelation W m S.ρ S.hρ)
  exact (measurable_measure_prodMk_right (μ := μ) hset).ennreal_toReal

theorem measurableSet_reverseAllowed (S : SelectedHighLowStructure W m)
    (label : ℕ → Option S.I) (i : ℕ) :
    MeasurableSet (S.reverseAllowed label i) := by
  cases h : label i with
  | none =>
    simp only [reverseAllowed, h]
    exact MeasurableSet.empty
  | some r =>
    simpa only [reverseAllowed, h] using
      KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r.val

/-- A relaxed assignment constructed on the original HIGH source measure.
The coding records exactly the eligible positive original whole-row atoms. -/
structure ReverseAssignmentData (S : SelectedHighLowStructure W m) where
  code : S.I ↪ ℕ
  label : ℕ → Option S.I
  hlabel : label = S.reverseAtomLabel code
  label_unique : ∀ i j r, label i = some r → label j = some r → i = j
  label_eligible : ∀ i r, label i = some r → r ∈ S.eligibleReverseAtom
  label_exhaustive : ∀ r ∈ S.eligibleReverseAtom, ∃ i, label i = some r
  a : ℕ → ℝ
  allowed : ℕ → Set Ω
  δ : Ω → ℝ
  q0 : ℕ → Lp ℝ 2 (μ.restrict S.H)
  ha : a = S.reverseAtomMass label
  hallowed : allowed = S.reverseAllowed label
  hδ : δ = S.reverseDiffuseSupply
  hq0 : ∀ i, q0 i =ᵐ[μ.restrict S.H] S.reverseAtomicReceipt label i
  hmeasurableAllowed : ∀ i, MeasurableSet (allowed i)
  hmeasurableδ : Measurable δ
  hmassNonneg : ∀ i, 0 ≤ a i
  hmassSummable : Summable a
  feasible : ReverseAssignment.Feasible allowed δ q0

/-- The actual reverse flow constructs a feasible relaxed assignment on the
original HIGH source law. Every active Nat label is an original LOW or neutral
positive whole-row atom; all other Nat slots carry zero mass and receipt. -/
theorem exists_reverseAssignmentData (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    Nonempty S.ReverseAssignmentData := by
  classical
  let : Countable S.I := S.hI.to_subtype
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat S.I
  let e : S.I ↪ ℕ := ⟨f, hf⟩
  let Z := S.reverseAssignmentRelation
  let I := S.reverseAllAtomFiber e
  have hZ : MeasurableSet Z := S.measurable_oriented_relations.2
  have hI : ∀ i, MeasurableSet (I i) := S.measurableSet_reverseAllAtomFiber e
  have hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)) :=
    S.reverseAllAtomFiber_pairwise e
  have hsource : MissingFlow.positiveSources μ Z = S.H :=
    S.reverseAssignment_positiveSources
  have hbase := MissingFlow.NormalizedAtomicFractions.exists_normalized_assignment (μ := μ)
    Z hZ I hI hdisjoint
  rw [hsource] at hbase
  obtain ⟨_, _, q, hq, hqRaw, _⟩ := hbase
  let label := S.reverseAtomLabel e
  let allowed := S.reverseAllowed label
  let δ := S.reverseDiffuseSupply
  have hAllowed : ∀ i, ∀ᵐ x ∂μ.restrict S.H,
      x ∈ MissingFlow.NormalizedAtomicFractions.allowed μ Z I i ↔ x ∈ allowed i := by
    intro i
    have h := S.ae_reverseAllowed_iff_cellMass_pos hW e i
    filter_upwards [h] with x hx
    exact hx.symm
  have hD : (⋃ i, I i)ᶜ = S.D := by
    dsimp only [I]
    rw [S.reverseAllAtomFiber_union e]
    exact S.hDeq.symm
  have hRawDiffuse : ∀ᵐ x ∂μ.restrict S.H,
      MissingFlow.NormalizedAtomicFractions.remainderSectionMass μ Z I x = δ x := by
    filter_upwards [S.ae_reverseRawDiffuse_eq_reverseDiffuseSupply] with x hx
    change μ.real (((⋃ i, I i)ᶜ) ∩ {y | (y, x) ∈ Z}) = δ x
    rw [hD]
    exact hx
  have hδzero : ∀ᵐ x ∂μ.restrict S.H,
      MissingFlow.NormalizedAtomicFractions.remainderSectionMass μ Z I x = 0 ↔ δ x = 0 :=
    hRawDiffuse.mono (fun _ hx => by rw [hx])
  have hfeasible : ReverseAssignment.Feasible allowed δ q :=
    (ReverseAssignment.feasible_congr hAllowed hδzero).mp hq
  refine ⟨{
    code := e
    label := label
    hlabel := rfl
    label_unique := S.reverseAtomLabel_unique e
    label_eligible := S.reverseAtomLabel_eligible e
    label_exhaustive := fun r hr => ⟨e r, S.reverseAtomLabel_eq_some e r hr⟩
    a := S.reverseAtomMass label
    allowed := allowed
    δ := δ
    q0 := q
    ha := rfl
    hallowed := rfl
    hδ := rfl
    hq0 := ?_
    hmeasurableAllowed := S.measurableSet_reverseAllowed label
    hmeasurableδ := S.measurable_reverseDiffuseSupply
    hmassNonneg := S.reverseAtomMass_nonneg label
    hmassSummable := S.reverseAtomMass_summable e
    feasible := hfeasible
  }⟩
  intro i
  exact (hqRaw i).trans (S.ae_reverse_rawFraction_eq_atomicReceipt e i)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The actual reverse endpoint has a retained positive original whole-row
atom, since its density is strictly below one half. -/
theorem exists_eligibleReverseAtom (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ r : S.I, r ∈ S.eligibleReverseAtom := by
  classical
  let : Countable S.I := S.hI.to_subtype
  let ν := missingFlowEndpointLaw μ S.reverseFlow
  have : IsProbabilityMeasure ν := S.endpoint_probabilities.2
  have hprofile : 1 - 2 * density S.reverseEndpoint =
      ∑' r : S.I, (MultipartiteClassMasses.classMass ν S.collapsedPartLabel r) ^ 2 := by
    apply MultipartiteClassMasses.one_sub_two_density_eq_tsum_classMass_sq
      S.reverseEndpoint S.collapsedPartLabel S.measurable_collapsedPartLabel
    filter_upwards [(S.endpoint_collapsed_support hW hd hgap).2] with p hp
    by_cases h : S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨
        S.collapsedPartLabel p.1 = none
    · simpa only [h, ↓reduceIte] using hp
    · simpa only [h, ↓reduceIte] using hp
  have hpositive : 0 < ∑' r : S.I,
      (MultipartiteClassMasses.classMass ν S.collapsedPartLabel r) ^ 2 := by
    rw [← hprofile]
    have hdR := (S.endpoint_densities_strict hW hd hgap).2
    have hdHalf := hd.2
    linarith
  have hexists : ∃ r : S.I,
      0 < MultipartiteClassMasses.classMass ν S.collapsedPartLabel r := by
    by_contra h
    have hzero : ∀ r : S.I, MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = 0 :=
      fun r => le_antisymm (le_of_not_gt (fun hr => h ⟨r, hr⟩))
        (MultipartiteClassMasses.classMass_nonneg ν S.collapsedPartLabel r)
    simp [hzero] at hpositive
  obtain ⟨r, hr⟩ := hexists
  rcases S.hfiberClass r.val r.property with hH | hL | hN
  · have hnot : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∉ S.half false := by
      filter_upwards [hH] with x hx hhalf
      change x ∈ S.L ∪ S.N at hhalf
      rcases hhalf with hLow | hNeutral
      · exact Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hLow
      · exact Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hx hNeutral
    have hzero : (μ.restrict (S.half false)) {x | S.ρ x = r.val} = 0 := by
      rw [Measure.restrict_apply (S.hfibers r.val r.property).1,
        Set.inter_comm, ← Measure.restrict_apply (S.measurableSet_half false)]
      exact measure_eq_zero_iff_ae_notMem.mpr hnot
    have hνzero : ν {x | S.ρ x = r.val} = 0 := S.endpoint_laws_ac_halves.2 hzero
    have hcmzero : MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = 0 := by
      have hfiber : S.collapsedPartLabel ⁻¹' {some r} = {x | S.ρ x = r.val} := by
        ext x
        change (if h : S.ρ x ∈ S.I then some ⟨S.ρ x, h⟩ else none) = some r ↔
          S.ρ x = r.val
        by_cases hx : S.ρ x ∈ S.I
        · simp only [hx, ↓reduceDIte, Option.some.injEq, Subtype.ext_iff]
        · simp only [hx, ↓reduceDIte, reduceCtorEq, false_iff]
          exact fun he => hx (he ▸ r.property)
      rw [MultipartiteClassMasses.classMass, hfiber]
      exact congrArg ENNReal.toReal hνzero
    exact False.elim ((ne_of_gt hr) hcmzero)
  · exact ⟨r, hL.mono (fun _ hx hy =>
      Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hy hx)⟩
  · exact ⟨r, hN.mono (fun _ hx hy =>
      Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hy hx)⟩

/-- Every correctly coded selected reverse assignment has a positive
original recipient mass under the actual strict-gap hypotheses. -/
theorem ReverseAssignmentData.exists_positive_mass
    (S : SelectedHighLowStructure W m) (A : S.ReverseAssignmentData)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ i, 0 < A.a i := by
  obtain ⟨r, hr⟩ := S.exists_eligibleReverseAtom hW hd hgap
  obtain ⟨i, hi⟩ := A.label_exhaustive r hr
  refine ⟨i, ?_⟩
  rw [A.ha]
  simp only [reverseAtomMass, hi]
  exact ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top _ _)

end SelectedHighLowStructure

end Erdos1017.CappedModel

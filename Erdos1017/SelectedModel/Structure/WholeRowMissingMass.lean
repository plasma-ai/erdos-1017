module

public import Erdos1017.SelectedModel.Structure.SelectedHighLowClassification
public import Erdos1017.SelectedModel.Flows.NormalizedRelationFlow

/-!
# Decomposition of the missing mass of a source

This module defines same-atom pairs, the source's own independent fiber mass and
the outside missing-section mass of the distinct-row zero relation; the
shifted-kernel zero set is the disjoint union of same-atom pairs and
distinct-row zero pairs, so the missing degree is the sum of these two masses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Pairs inside one actual positive independent whole-row fiber. -/
def SelectedHighLowStructure.sameAtomRelation {W : Model Ω μ} {m : ℝ}
    (S : SelectedHighLowStructure W m) : Set (Ω × Ω) :=
  {p | S.ρ p.1 = S.ρ p.2 ∧ S.ρ p.1 ∈ S.I}

/-- The original mass of the source's own positive independent fiber,
with value zero on the diffuse remainder. -/
def SelectedHighLowStructure.ownIndependentMass {W : Model Ω μ} {m : ℝ}
    (S : SelectedHighLowStructure W m) (y : Ω) : ℝ :=
  μ.real {x | (x, y) ∈ S.sameAtomRelation}

/-- Original outside missing-section mass of the actual distinct-row
zero relation, with the source in the second coordinate. -/
def SelectedHighLowStructure.outsideSectionMass {W : Model Ω μ} {m : ℝ}
    (S : SelectedHighLowStructure W m) (y : Ω) : ℝ :=
  MissingFlow.columnMass μ (actualZeroRelation W m S.ρ) y

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The same-fiber pair relation is measurable from the countable actual
positive whole-row family and its strongly measurable row map. -/
theorem SelectedHighLowStructure.measurableSet_sameAtomRelation
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m) :
    MeasurableSet S.sameAtomRelation := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  exact (measurableSet_eq_fun (S.hρ.measurable.comp measurable_fst)
    (S.hρ.measurable.comp measurable_snd)).inter
    (S.hρ.measurable.comp measurable_fst S.hI.measurableSet)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Both original one-vertex mass functions are measurable. -/
theorem SelectedHighLowStructure.measurable_ownIndependentMass
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m) :
    Measurable S.ownIndependentMass :=
  (measurable_measure_prodMk_right (μ := μ) S.measurableSet_sameAtomRelation).ennreal_toReal

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
theorem SelectedHighLowStructure.measurable_outsideSectionMass
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m) :
    Measurable S.outsideSectionMass :=
  MissingFlow.measurable_columnMass (μ := μ)
    (actualZeroRelation W m S.ρ) (measurableSet_actualZeroRelation W m S.ρ S.hρ)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem SelectedHighLowStructure.ownIndependentMass_eq_fiber
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I) (y : Ω) (hy : S.ρ y = r) :
    S.ownIndependentMass y = μ.real {x | S.ρ x = r} := by
  have heq : {x | (x, y) ∈ S.sameAtomRelation} = {x | S.ρ x = r} := by
    ext x
    constructor
    · rintro ⟨hxy, hI⟩
      exact hxy.trans hy
    · intro hx
      exact ⟨hx.trans hy.symm, hx ▸ hr⟩
  exact congrArg μ.real heq

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem SelectedHighLowStructure.ownIndependentMass_eq_zero_of_not_mem
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m)
    (y : Ω) (hy : S.ρ y ∉ S.I) : S.ownIndependentMass y = 0 := by
  have heq : {x | (x, y) ∈ S.sameAtomRelation} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact hy (hx.1 ▸ hx.2)
  simp only [SelectedHighLowStructure.ownIndependentMass, heq, measureReal_empty]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem section_union_real_eq_add_right
    (A Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (hdisj : Disjoint A Z)
    (y : Ω) :
    μ.real {x | (x, y) ∈ A ∪ Z} =
      μ.real {x | (x, y) ∈ A} + μ.real {x | (x, y) ∈ Z} := by
  have hsecZ : MeasurableSet {x | (x, y) ∈ Z} := measurable_prodMk_right hZ
  have hsecDisj : Disjoint {x | (x, y) ∈ A} {x | (x, y) ∈ Z} := by
    apply Set.disjoint_left.mpr
    intro x hxA hxZ
    exact Set.disjoint_left.mp hdisj hxA hxZ
  have hsecUnion : {x | (x, y) ∈ A ∪ Z} =
      {x | (x, y) ∈ A} ∪ {x | (x, y) ∈ Z} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_union]
  rw [hsecUnion, measureReal_union hsecDisj hsecZ]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem degree_mass (r : Lp ℝ 2 μ) :
    wholeRowDegree r = μ.real {x | 0 < r x} := by
  let s := {x | 0 < r x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (Lp.stronglyMeasurable r).measurable
  have hfun : (fun x => if 0 < r x then (1 : ℝ) else 0) = s.indicator (fun _ => 1) := by
    funext x
    by_cases hx : 0 < r x
    · have hsx : x ∈ s := hx
      simp only [hx, ↓reduceIte, Set.indicator_of_mem hsx]
    · have hsx : x ∉ s := hx
      simp only [hx, ↓reduceIte, Set.indicator_of_notMem hsx]
  rw [wholeRowDegree, hfun]
  change (∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real s
  exact integral_indicator_one hs

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem one_sub_degree_mass (r : Lp ℝ 2 μ) :
    1 - wholeRowDegree r = μ.real {x | r x ≤ 0} := by
  let s := {x | 0 < r x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (Lp.stronglyMeasurable r).measurable
  have hcompl : {x | r x ≤ 0} = sᶜ := by
    ext x
    change (r x ≤ 0) ↔ ¬ (0 < r x)
    exact (not_lt).symm
  rw [degree_mass, hcompl, measureReal_compl hs, probReal_univ]

/-- Every same-atom pair is a shifted-kernel zero pair almost everywhere.
The countable union is assembled from actual independent fiber squares. -/
theorem SelectedHighLowStructure.ae_sameAtomRelation_zero
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, p ∈ S.sameAtomRelation →
      shiftedKernel W m p.1 p.2 = 0 := by
  have hsupport := (hW.strict_gap_structure hd hgap).strict_support
  have hzero (r : Lp ℝ 2 μ) (hr : r ∈ S.I) :
      ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r → S.ρ p.2 = r →
        shiftedKernel W m p.1 p.2 = 0 := by
    let Br := {x | S.ρ x = r}
    have hBr := (S.hfibers r hr).1
    have hrr := shiftedKernel_zero_of_adjacency_zero W m hW.moment_mem hsupport
      Br Br (S.hfibers r hr).2.2.1
    rw [Measure.prod_restrict] at hrr
    have hglobal := (ae_restrict_iff' (hBr.prod hBr)).mp hrr
    filter_upwards [hglobal] with p hp hpr hps
    exact hp ⟨hpr, hps⟩
  have hall : ∀ᵐ p ∂μ.prod μ, ∀ r ∈ S.I,
      S.ρ p.1 = r → S.ρ p.2 = r → shiftedKernel W m p.1 p.2 = 0 := by
    apply (ae_ball_iff S.hI).mpr
    intro r hr
    exact hzero r hr
  filter_upwards [hall] with p hp hA
  exact hp (S.ρ p.1) hA.2 rfl hA.1.symm

/-- The actual shifted-kernel zero set is exactly the disjoint union of
same-atom pairs and distinct-row zero pairs modulo product null sets. -/
theorem SelectedHighLowStructure.ae_zero_iff_sameAtom_or_relation
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 ↔
      p ∈ S.sameAtomRelation ∨ p ∈ actualZeroRelation W m S.ρ := by
  filter_upwards [S.hcoverage, S.ae_sameAtomRelation_zero hW hd hgap]
    with p hcover hA
  constructor
  · intro hzero
    rcases hcover hzero with ⟨r, hr, hx, hy⟩ | hZ
    · exact Or.inl ⟨hx.trans hy.symm, hx ▸ hr⟩
    · exact Or.inr hZ
  · rintro (hAtom | hZ)
    · exact hA hAtom
    · exact hZ.1

/-- The full selected model's original missing degree is the sum of
its own independent-fiber mass and its outside zero-relation section mass. -/
theorem SelectedHighLowStructure.ae_missing_mass_decomposition
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, 1 - adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) y =
      S.ownIndependentMass y + S.outsideSectionMass y := by
  let K := shiftedKernel W m
  let A := S.sameAtomRelation
  let Z := actualZeroRelation W m S.ρ
  have hsupport := (hW.strict_gap_structure hd hgap).strict_support
  have hdegree := ae_degree_eq_wholeRowDegree W m S.ρ S.hrow hsupport
  have hzero := S.ae_zero_iff_sameAtom_or_relation hW hd hgap
  have hzeroSwap :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hzero
  have hKsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hzeroIncoming : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 ↔
      p.swap ∈ A ∪ Z := by
    filter_upwards [hzeroSwap, hKsym] with p hz hs
    change (K p.2 p.1 = 0 ↔ p.swap ∈ A ∨ p.swap ∈ Z) at hz
    rw [hs]
    exact hz
  have hzeroSections := Measure.ae_ae_of_ae_prod hzeroIncoming
  have hnonnegSections := Measure.ae_ae_of_ae_prod
    (hW.moment_mem.mono fun _ hp => hp.1)
  have hA : MeasurableSet A := S.measurableSet_sameAtomRelation
  have hZ : MeasurableSet Z := measurableSet_actualZeroRelation W m S.ρ S.hρ
  have hdisj : Disjoint A Z := by
    apply Set.disjoint_left.mpr
    intro p hpA hpZ
    exact hpZ.2 hpA.1
  filter_upwards [hdegree, S.hrow, hzeroSections, hnonnegSections]
    with y hgy hrowy hzeroY hnonnegY
  have hmeasure : μ.real {x | S.ρ y x ≤ 0} = μ.real {x | (x, y) ∈ A ∪ Z} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hrowy, hzeroY, hnonnegY] with x hr hz hn
    apply propext
    change (S.ρ y x ≤ 0) ↔ (y, x).swap ∈ A ∪ Z
    rw [hr]
    constructor
    · intro h
      exact hz.mp (le_antisymm h hn)
    · intro h
      exact (hz.mpr h).le
  calc
    1 - adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) y =
        μ.real {x | S.ρ y x ≤ 0} := by rw [hgy]; exact one_sub_degree_mass (S.ρ y)
    _ = μ.real {x | (x, y) ∈ A ∪ Z} := hmeasure
    _ = S.ownIndependentMass y + S.outsideSectionMass y :=
      section_union_real_eq_add_right A Z hZ hdisj y

end Erdos1017.CappedModel

module

public import Erdos1017.SelectedModel.Structure.HighLowRelationClassification
public import Erdos1017.SelectedModel.Structure.SelectedWholeRowStructure
public import Erdos1017.SelectedModel.Structure.WholeAtomDegreeOrder
public import Erdos1017.SelectedModel.Structure.DiffuseDegreeOrder

/-!
# High-low classification of the selected model

This module defines the zero relation between distinct whole shifted rows and
the structure `SelectedHighLowStructure`, which keeps the whole-row
representation, zero cut and derived high, low and neutral classes; almost every
vertex has zero-relation neighbors on at most one side of its degree.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Distinct whole shifted rows joined by a zero kernel pair form the
actual relation to be ordered by original adjacency degree. -/
def actualZeroRelation (W : Model Ω μ) (m : ℝ) (ρ : Ω → Lp ℝ 2 μ) :
    Set (Ω × Ω) :=
  {p | shiftedKernel W m p.1 p.2 = 0 ∧ ρ p.1 ≠ ρ p.2}

omit [IsProbabilityMeasure μ] in
theorem measurableSet_actualZeroRelation (W : Model Ω μ) (m : ℝ)
    (ρ : Ω → Lp ℝ 2 μ) (hρ : StronglyMeasurable ρ) :
    MeasurableSet (actualZeroRelation W m ρ) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hK : Measurable (fun p : Ω × Ω => shiftedKernel W m p.1 p.2) :=
    (W.stronglyMeasurable_moment (continuous_shiftedColor m).measurable.stronglyMeasurable).measurable
  have hneq : MeasurableSet {p : Ω × Ω | ρ p.1 ≠ ρ p.2} :=
    (measurableSet_eq_fun (hρ.measurable.comp measurable_fst)
      (hρ.measurable.comp measurable_snd)).compl
  exact (measurableSet_eq_fun hK measurable_const).inter hneq

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem actualZeroRelation_symm (W : Model Ω μ) (m : ℝ) (ρ : Ω → Lp ℝ 2 μ) :
    ∀ᵐ p ∂μ.prod μ, p ∈ actualZeroRelation W m ρ ↔
      p.swap ∈ actualZeroRelation W m ρ := by
  filter_upwards [shiftedMoment_symm W m] with p hp
  change (shiftedMoment W m p = 0 ∧ ρ p.1 ≠ ρ p.2) ↔
    (shiftedMoment W m p.swap = 0 ∧ ρ p.2 ≠ ρ p.1)
  rw [hp]
  simp only [ne_comm]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Reverse Fubini for homogeneous rows: if almost every row of a symmetric kernel on `s`
equals `r`, then `K x y = r x` for almost every `x` and almost every `y ∈ s`. -/
private theorem ae_columns_of_homogeneous_rows
    (K : Ω → Ω → ℝ)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (s : Set Ω) (r : Ω → ℝ) (hr : StronglyMeasurable r)
    (hrows : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] r) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ.restrict s, K x y = r x := by
  have hle : (μ.restrict s).prod μ ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hm := hK.mono_measure hle
  have hgood : ∀ᵐ x ∂μ.restrict s, ∀ᵐ y ∂μ,
      hm.mk (fun p : Ω × Ω => K p.1 p.2) (x, y) = r y := by
    filter_upwards [hrows, Measure.ae_ae_of_ae_prod hm.ae_eq_mk] with x hx heq
    filter_upwards [hx, heq] with y hy hz
    exact hz.symm.trans hy
  have hprod : ∀ᵐ p ∂(μ.restrict s).prod μ, K p.1 p.2 = r p.2 := by
    apply hm.ae_eq_mk.trans
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm.stronglyMeasurable_mk.measurable
      (hr.comp_measurable measurable_snd).measurable)).mpr hgood
  have hswap :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ.restrict s)).quasiMeasurePreserving.ae hprod
  have hsym' : ∀ᵐ p ∂μ.prod (μ.restrict s), K p.1 p.2 = K p.2 p.1 :=
    ae_mono (Measure.prod_mono le_rfl Measure.restrict_le_self) hsym
  apply Measure.ae_ae_of_ae_prod (p := fun p : Ω × Ω => K p.1 p.2 = r p.1)
  filter_upwards [hswap, hsym'] with p hp hq
  exact hq.trans hp

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem exists_positive_fiber_of_ae_cover {ι : Type*} [Countable ι]
    (S : Set Ω) (T : ι → Set Ω) (hSpos : 0 < μ S)
    (hcover : ∀ᵐ x ∂μ, x ∈ S → ∃ i, x ∈ T i) :
    ∃ i, 0 < μ (S ∩ T i) := by
  have heq : μ S = μ (⋃ i, S ∩ T i) := by
    apply measure_congr
    filter_upwards [hcover] with x hx
    apply propext
    constructor
    · intro h
      obtain ⟨i, hi⟩ := hx h
      exact mem_iUnion.mpr ⟨i, ⟨h, hi⟩⟩
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hi.1
  apply exists_measure_pos_of_not_measure_iUnion_null
  rw [← heq]
  exact hSpos.ne'

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem exists_common_fiber_witness
    (R : Ω → Lp ℝ 2 μ) (r : Lp ℝ 2 μ) (S : Set Ω)
    (K : Ω → Ω → ℝ) (g : Ω → ℝ) (x : Ω)
    (hpos : 0 < μ (S ∩ {y | R y = r}))
    (hcol : ∀ᵐ y ∂μ.restrict {y | R y = r}, K x y = r x)
    (hdegree : ∀ᵐ y ∂μ.restrict {y | R y = r},
      g y = Erdos1017.CappedModel.wholeRowDegree r) :
    ∃ y ∈ S, K x y = r x ∧
      g y = Erdos1017.CappedModel.wholeRowDegree r := by
  have hsub : S ∩ {y | R y = r} ⊆ {y | R y = r} := fun _ hy => hy.2
  have hc : ∀ᵐ y ∂μ.restrict (S ∩ {y | R y = r}), K x y = r x :=
    ae_mono (μ.restrict_mono_set hsub) hcol
  have hd : ∀ᵐ y ∂μ.restrict (S ∩ {y | R y = r}),
      g y = Erdos1017.CappedModel.wholeRowDegree r :=
    ae_mono (μ.restrict_mono_set hsub) hdegree
  obtain ⟨y, hy, hcy, hdy⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (hc.and hd)
  exact ⟨y, hy.1, hcy, hdy⟩

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem lower_fiber_of_positive_section
    (R : Ω → Lp ℝ 2 μ) (r : Lp ℝ 2 μ) (S : Set Ω)
    (K : Ω → Ω → ℝ) (g : Ω → ℝ) (x : Ω)
    (hpos : 0 < μ (S ∩ {y | R y = r}))
    (hcol : ∀ᵐ y ∂μ.restrict {y | R y = r}, K x y = r x)
    (hdegree : ∀ᵐ y ∂μ.restrict {y | R y = r},
      g y = Erdos1017.CappedModel.wholeRowDegree r)
    (hS : ∀ y ∈ S, K x y = 0 ∧ g y < g x) :
    r x = 0 ∧ Erdos1017.CappedModel.wholeRowDegree r < g x := by
  obtain ⟨y, hy, hcy, hdy⟩ :=
    exists_common_fiber_witness R r S K g x hpos hcol hdegree
  obtain ⟨hzero, hlt⟩ := hS y hy
  exact ⟨hcy.symm.trans hzero, hdy ▸ hlt⟩

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem upper_fiber_of_positive_section
    (R : Ω → Lp ℝ 2 μ) (r : Lp ℝ 2 μ) (S : Set Ω)
    (K : Ω → Ω → ℝ) (g : Ω → ℝ) (x : Ω)
    (hpos : 0 < μ (S ∩ {y | R y = r}))
    (hcol : ∀ᵐ y ∂μ.restrict {y | R y = r}, K x y = r x)
    (hdegree : ∀ᵐ y ∂μ.restrict {y | R y = r},
      g y = Erdos1017.CappedModel.wholeRowDegree r)
    (hS : ∀ y ∈ S, K x y = 0 ∧ g x < g y) :
    r x = 0 ∧ g x < Erdos1017.CappedModel.wholeRowDegree r := by
  obtain ⟨y, hy, hcy, hdy⟩ :=
    exists_common_fiber_witness R r S K g x hpos hcol hdegree
  obtain ⟨hzero, hlt⟩ := hS y hy
  exact ⟨hcy.symm.trans hzero, hdy ▸ hlt⟩

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_no_both_of_homogeneous_sections
    (Z : Set (Ω × Ω)) (g : Ω → ℝ) (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (s N : Set Ω) (a : ℝ)
    (hdegree : g =ᵐ[μ.restrict s] fun _ => a)
    (hsections : ∀ᵐ x ∂μ.restrict s, ∀ᵐ y ∂μ, (x, y) ∈ Z ↔ y ∈ N)
    (hside : (∀ᵐ y ∂μ.restrict N, g y < a) ∨
      (∀ᵐ y ∂μ.restrict N, a < g y))
    (hN : MeasurableSet N) :
    ∀ᵐ x ∂μ.restrict s,
      OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
        OrderedZeroRelation.rightNeighborMass μ Z g x = 0 := by
  have hsym' := ae_restrict_of_ae (s := s) (Measure.ae_ae_of_ae_prod hsym)
  rcases hside with hlo | hhi
  · have hlo' := (ae_restrict_iff' hN).mp hlo
    filter_upwards [hdegree, hsections, hsym'] with x hx hs hz
    right
    have hno : ∀ᵐ y ∂μ, ¬((x, y) ∈ Z ∧ g x < g y) := by
      filter_upwards [hs, hlo'] with y hy hly
      rintro ⟨hxy, hlt⟩
      exact (not_lt_of_ge (le_of_lt (hly (hy.mp hxy)))) (hx ▸ hlt)
    simpa only [OrderedZeroRelation.rightNeighborMass, ae_iff, not_not,
      Set.ofPred_mem_eq] using hno
  · have hhi' := (ae_restrict_iff' hN).mp hhi
    filter_upwards [hdegree, hsections, hsym'] with x hx hs hz
    left
    have hno : ∀ᵐ y ∂μ, ¬((y, x) ∈ Z ∧ g y < g x) := by
      filter_upwards [hs, hhi', hz] with y hy hhy hzy
      rintro ⟨hyx, hlt⟩
      exact (not_lt_of_ge (le_of_lt (hhy (hy.mp (hzy.mpr hyx))))) (hx ▸ hlt)
    simpa only [OrderedZeroRelation.leftNeighborMass, ae_iff, not_not,
      Set.ofPred_mem_eq] using hno

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_relation_section_of_homogeneous_rows
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ)
    (r : Lp ℝ 2 μ)
    (hrows : ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ))
    (hmem : ∀ᵐ x ∂μ.restrict {x | R x = r}, R x = r) :
    ∀ᵐ x ∂μ.restrict {x | R x = r}, ∀ᵐ y ∂μ,
      (K x y = 0 ∧ R x ≠ R y) ↔ (r y = 0 ∧ R y ≠ r) := by
  filter_upwards [hrows, hmem] with x hx hxr
  filter_upwards [hx] with y hxy
  rw [hxy, hxr]
  simp only [ne_comm]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_no_both_of_diffuse_cover
    (K : Ω → Ω → ℝ) (g : Ω → ℝ) (R : Ω → Lp ℝ 2 μ)
    (I : Set (Lp ℝ 2 μ)) (D : Set Ω) (hD : MeasurableSet D)
    (hI : I.Countable)
    (hDeq : D = (⋃ r ∈ I, {x | R x = r})ᶜ)
    (Z : Set (Ω × Ω))
    (hzero : ∀ p ∈ Z, K p.1 p.2 = 0)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (hnoDD : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → p ∉ Z)
    (hcolumns : ∀ r ∈ I, ∀ᵐ x ∂μ,
      ∀ᵐ y ∂μ.restrict {y | R y = r}, K x y = r x)
    (hdegrees : ∀ r ∈ I, g =ᵐ[μ.restrict {y | R y = r}]
      fun _ => wholeRowDegree r)
    (hnostraddle : ∀ᵐ x ∂μ.restrict D, ¬∃ r ∈ I, ∃ u ∈ I,
      r ≠ u ∧ r x ≤ 0 ∧ u x ≤ 0 ∧
        wholeRowDegree r < g x ∧ g x < wholeRowDegree u) :
    ∀ᵐ x ∂μ.restrict D,
      OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
        OrderedZeroRelation.rightNeighborMass μ Z g x = 0 := by
  let : Countable I := hI.to_subtype
  let Slo (x : Ω) := {y | (x, y) ∈ Z ∧ g y < g x}
  let Shi (x : Ω) := {y | (x, y) ∈ Z ∧ g x < g y}
  have hcolumnsAll : ∀ᵐ x ∂μ, ∀ r ∈ I,
      ∀ᵐ y ∂μ.restrict {y | R y = r}, K x y = r x := by
    apply (ae_ball_iff hI).mpr
    intro r hr
    exact hcolumns r hr
  have hsymSections := Measure.ae_ae_of_ae_prod hsym
  have hnoDDSections := Measure.ae_ae_of_ae_prod hnoDD
  have hcover (x : Ω) (hxD : x ∈ D)
      (hx : ∀ᵐ y ∂μ, x ∈ D → y ∈ D → (x, y) ∉ Z)
      (S : Set Ω) (hS : ∀ y ∈ S, (x, y) ∈ Z) :
      ∀ᵐ y ∂μ, y ∈ S → ∃ r : I, R y = r.val := by
    filter_upwards [hx] with y hy hyS
    have hyNotD : y ∉ D := fun hyD => hy hxD hyD (hS y hyS)
    have hyU : y ∈ ⋃ r ∈ I, {x | R x = r} := by
      simpa only [hDeq, mem_compl_iff, not_not] using hyNotD
    obtain ⟨r, hr⟩ := mem_iUnion.mp hyU
    obtain ⟨hrI, hyr⟩ := mem_iUnion.mp hr
    exact ⟨⟨r, hrI⟩, hyr⟩
  have hglobal : ∀ᵐ x ∂μ,
      x ∈ D → ¬∃ r ∈ I, ∃ u ∈ I,
        r ≠ u ∧ r x ≤ 0 ∧ u x ≤ 0 ∧
          wholeRowDegree r < g x ∧ g x < wholeRowDegree u :=
    (ae_restrict_iff' hD).mp hnostraddle
  have hresult : ∀ᵐ x ∂μ, x ∈ D →
      OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
        OrderedZeroRelation.rightNeighborMass μ Z g x = 0 := by
    filter_upwards [hsymSections, hnoDDSections, hcolumnsAll, hglobal]
      with x hxsym hxnoDD hxcol hnostr hxD
    by_cases hleft : OrderedZeroRelation.leftNeighborMass μ Z g x = 0
    · exact Or.inl hleft
    right
    by_contra hright
    have hleftEq : OrderedZeroRelation.leftNeighborMass μ Z g x = μ (Slo x) := by
      apply measure_congr
      filter_upwards [hxsym] with y hy
      apply propext
      change ((y, x) ∈ Z ∧ g y < g x) ↔ ((x, y) ∈ Z ∧ g y < g x)
      simpa only [Prod.swap_prod_mk] using and_congr hy.symm Iff.rfl
    have hloPos : 0 < μ (Slo x) := by
      rw [← hleftEq]
      exact pos_iff_ne_zero.mpr hleft
    have hhiPos : 0 < μ (Shi x) := pos_iff_ne_zero.mpr hright
    obtain ⟨r, hrpos⟩ := exists_positive_fiber_of_ae_cover (μ := μ)
      (Slo x) (fun r : I => {y | R y = r.val}) hloPos
      (hcover x hxD hxnoDD (Slo x) (fun _ hy => hy.1))
    obtain ⟨u, hupos⟩ := exists_positive_fiber_of_ae_cover (μ := μ)
      (Shi x) (fun r : I => {y | R y = r.val}) hhiPos
      (hcover x hxD hxnoDD (Shi x) (fun _ hy => hy.1))
    have hr := lower_fiber_of_positive_section R r.val (Slo x) K g x
      hrpos (hxcol r.val r.property) (hdegrees r.val r.property)
      (fun y hy => ⟨hzero (x, y) hy.1, hy.2⟩)
    have hu := upper_fiber_of_positive_section R u.val (Shi x) K g x
      hupos (hxcol u.val u.property) (hdegrees u.val u.property)
      (fun y hy => ⟨hzero (x, y) hy.1, hy.2⟩)
    have hru : r.val ≠ u.val := by
      intro heq
      rw [heq] at hr
      exact (not_lt_of_ge (le_of_lt hr.2)) hu.2
    exact hnostr hxD ⟨r.val, r.property, u.val, u.property,
      hru, hr.1.le, hu.1.le, hr.2, hu.2⟩
  exact (ae_restrict_iff' hD).mpr hresult

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The original adjacency degrees of almost every distinct-row zero pair
are different in the same selected full model. The atomic missing-region
order and the complete diffuse remainder are both used. -/
theorem FullStationaryClass.ae_actual_zero_relation_degree_ne
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D Bcut : Set Ω)
    (hρ : StronglyMeasurable ρ)
    (hrow : ∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x)
    (hI : I.Countable)
    (hfibers : ∀ r ∈ I, MeasurableSet {x | ρ x = r} ∧ 0 < μ {x | ρ x = r} ∧
      (∀ᵐ p ∂(μ.restrict {x | ρ x = r}).prod (μ.restrict {x | ρ x = r}),
        adjacencyKernel W p.1 p.2 = 0) ∧
      KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
        (adjacencyKernel W) (chargeKernel W) 4 m ρ r)
    (hDeq : D = (⋃ r ∈ I, {x | ρ x = r})ᶜ)
    (hDcomplete : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      W.moment CappedColor.adjacency p = 1)
    (hcross : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
      (p.1 ∈ Bcut ∧ p.2 ∉ Bcut) ∨ (p.2 ∈ Bcut ∧ p.1 ∉ Bcut)) :
    ∀ᵐ p ∂μ.prod μ, p ∈ actualZeroRelation W m ρ →
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 ≠
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let Z := actualZeroRelation W m ρ
  have hZ : MeasurableSet Z := measurableSet_actualZeroRelation W m ρ hρ
  have hg : Measurable (fun x => g x) := (Lp.stronglyMeasurable g).measurable
  have hdegreeNe : MeasurableSet {p : Ω × Ω | g p.1 ≠ g p.2} :=
    (measurableSet_eq_fun (hg.comp measurable_fst) (hg.comp measurable_snd)).compl
  have hs := hW.strict_gap_structure hd hgap
  have hAtom (r : Lp ℝ 2 μ) (hr : r ∈ I) :
      ∀ᵐ p ∂μ.prod μ, ρ p.1 = r → p ∈ Z → g p.1 ≠ g p.2 := by
    let Br := {x | ρ x = r}
    let N := KernelOperator.wholeFiberMissingSet ρ r
    have hBr := hfibers r hr
    have hN : MeasurableSet N := KernelOperator.measurableSet_wholeFiberMissingSet ρ hρ r
    have hside := hW.whole_atom_missing_degree_one_side hd hgap hmin
      ρ I D Bcut hρ hrow hI hfibers hDeq hDcomplete hcross r hr
    have hsideGlobal : ∀ᵐ y ∂μ, y ∈ N → g y ≠ wholeRowDegree r := by
      rcases hside with hlo | hhi
      · exact ((ae_restrict_iff' hN).mp hlo).mono (fun _ hy hN hyEq =>
          (ne_of_lt (hy hN)) hyEq)
      · exact ((ae_restrict_iff' hN).mp hhi).mono (fun _ hy hN hyEq =>
          (ne_of_gt (hy hN)) hyEq)
    have hdegree := wholeRowFiber_degree W m ρ r hBr.2.2.2
    have hrows := hBr.2.2.2.rows.mono (fun _ hx => hx.1)
    have hsection : ∀ᵐ x ∂μ, ρ x = r → ∀ᵐ y ∂μ,
        (x, y) ∈ Z → g x ≠ g y := by
      have hBr' := (ae_restrict_iff' hBr.1).mp (hdegree.and hrows)
      filter_upwards [hBr'] with x hx hxr
      obtain ⟨hxdegree, hxrow⟩ := hx hxr
      filter_upwards [hxrow, hsideGlobal] with y hxy hside hZxy
      have hyN : y ∈ N := by
        have hρne : ρ y ≠ r := fun heq => hZxy.2 (hxr.trans heq.symm)
        exact ⟨hρne, by rw [← hxy, hZxy.1]⟩
      exact fun hgeq => hside hyN (hxdegree ▸ hgeq.symm)
    have hP : MeasurableSet {p : Ω × Ω | ρ p.1 = r → p ∈ Z → g p.1 ≠ g p.2} :=
      ((hBr.1.preimage measurable_fst).imp (hZ.imp hdegreeNe))
    apply (Measure.ae_prod_iff_ae_ae hP).mpr
    filter_upwards [hsection] with x hx
    by_cases hxr : ρ x = r
    · filter_upwards [hx hxr] with y hy
      exact fun _ hZxy => hy hZxy
    · exact Filter.Eventually.of_forall (fun _ h => (hxr h).elim)
  have hAtoms : ∀ᵐ p ∂μ.prod μ, ∀ r ∈ I,
      ρ p.1 = r → p ∈ Z → g p.1 ≠ g p.2 := by
    apply (ae_ball_iff hI).mpr
    intro r hr
    exact hAtom r hr
  have hAtomsSwap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hAtoms
  have hZsym := actualZeroRelation_symm W m ρ
  have hnoDD : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → p ∉ Z := by
    filter_upwards [hDcomplete, hs.strict_support] with p hc hs hx hy hZp
    have hG := hc hx hy
    have hzero : shiftedMoment W m p = 0 := hZp.1
    rw [hzero] at hs
    simp only [lt_irrefl, ↓reduceIte] at hs
    linarith
  have hAtomOfNotD (x : Ω) (hx : x ∉ D) : ∃ r ∈ I, ρ x = r := by
    have hxu : x ∈ ⋃ r ∈ I, {x | ρ x = r} := by simpa only [hDeq, mem_compl_iff, not_not] using hx
    obtain ⟨r, hr⟩ := mem_iUnion.mp hxu
    obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
    exact ⟨r, hrI, hxr⟩
  filter_upwards [hAtoms, hAtomsSwap, hZsym, hnoDD] with p hl hr hz hdd hZp
  by_cases hfirst : p.1 ∈ D
  · by_cases hsecond : p.2 ∈ D
    · exact (hdd hfirst hsecond hZp).elim
    · obtain ⟨r, hrI, hpr⟩ := hAtomOfNotD p.2 hsecond
      exact (hr r hrI hpr (hz.mp hZp)).symm
  · obtain ⟨r, hrI, hpr⟩ := hAtomOfNotD p.1 hfirst
    exact hl r hrI hpr hZp

/-- Almost every selected vertex has strict actual zero-relation neighbors
on at most one side of its original adjacency degree. -/
theorem FullStationaryClass.ae_actual_zero_relation_no_both
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D Bcut : Set Ω)
    (hρ : StronglyMeasurable ρ)
    (hrow : ∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x)
    (hI : I.Countable)
    (hfibers : ∀ r ∈ I, MeasurableSet {x | ρ x = r} ∧ 0 < μ {x | ρ x = r} ∧
      (∀ᵐ p ∂(μ.restrict {x | ρ x = r}).prod (μ.restrict {x | ρ x = r}),
        adjacencyKernel W p.1 p.2 = 0) ∧
      KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
        (adjacencyKernel W) (chargeKernel W) 4 m ρ r)
    (hDeq : D = (⋃ r ∈ I, {x | ρ x = r})ᶜ)
    (hD : MeasurableSet D)
    (hDcomplete : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      W.moment CappedColor.adjacency p = 1)
    (hcross : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
      (p.1 ∈ Bcut ∧ p.2 ∉ Bcut) ∨ (p.2 ∈ Bcut ∧ p.1 ∉ Bcut)) :
    ∀ᵐ x ∂μ,
      OrderedZeroRelation.leftNeighborMass μ (actualZeroRelation W m ρ)
          (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) x = 0 ∨
        OrderedZeroRelation.rightNeighborMass μ (actualZeroRelation W m ρ)
          (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) x = 0 := by
  let K := shiftedKernel W m
  let g : Ω → ℝ := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let Z := actualZeroRelation W m ρ
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hZsym := actualZeroRelation_symm W m ρ
  have hnoDD : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → p ∉ Z := by
    filter_upwards [hDcomplete, (hW.strict_gap_structure hd hgap).strict_support]
      with p hc hs hx hy hZp
    have hG := hc hx hy
    have hzero : shiftedMoment W m p = 0 := hZp.1
    rw [hzero] at hs
    simp only [lt_irrefl, ↓reduceIte] at hs
    linarith
  have hKsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hKmeas : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2)
      (μ.prod μ) := shiftedKernel_measurable W m
  have hAtom (r : Lp ℝ 2 μ) (hr : r ∈ I) :
      ∀ᵐ x ∂μ.restrict {x | ρ x = r},
        OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
          OrderedZeroRelation.rightNeighborMass μ Z g x = 0 := by
    let Br := {x | ρ x = r}
    let N := KernelOperator.wholeFiberMissingSet ρ r
    let T := {y | r y = 0 ∧ ρ y ≠ r}
    have hBr := hfibers r hr
    have hT : MeasurableSet T :=
      (measurableSet_eq_fun (Lp.stronglyMeasurable r).measurable measurable_const).inter
        (hρ.measurable (measurableSet_singleton r)).compl
    have hTN : T ⊆ N := fun _ hy => ⟨hy.2, hy.1.le⟩
    have hrows := hBr.2.2.2.rows.mono (fun _ hx => hx.1)
    have hsection := ae_relation_section_of_homogeneous_rows K ρ r hrows
      (ae_restrict_mem hBr.1)
    have hdegree := wholeRowFiber_degree W m ρ r hBr.2.2.2
    have hside := hW.whole_atom_missing_degree_one_side hd hgap hmin
      ρ I D Bcut hρ hrow hI hfibers hDeq hDcomplete hcross r hr
    have hsideT : (∀ᵐ y ∂μ.restrict T, g y < wholeRowDegree r) ∨
        (∀ᵐ y ∂μ.restrict T, wholeRowDegree r < g y) := by
      rcases hside with h | h
      · exact Or.inl (ae_mono (μ.restrict_mono_set hTN) h)
      · exact Or.inr (ae_mono (μ.restrict_mono_set hTN) h)
    exact ae_no_both_of_homogeneous_sections Z g hZsym Br T
      (wholeRowDegree r) hdegree hsection hsideT hT
  have hAtoms : ∀ᵐ x ∂μ, ∀ r ∈ I, ρ x = r →
      OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
        OrderedZeroRelation.rightNeighborMass μ Z g x = 0 := by
    apply (ae_ball_iff hI).mpr
    intro r hr
    exact (ae_restrict_iff' (hfibers r hr).1).mp (hAtom r hr)
  have hcolumns (r : Lp ℝ 2 μ) (hr : r ∈ I) : ∀ᵐ x ∂μ,
      ∀ᵐ y ∂μ.restrict {y | ρ y = r}, K x y = r x :=
    ae_columns_of_homogeneous_rows K hKmeas hKsym _ _
      (Lp.stronglyMeasurable r) ((hfibers r hr).2.2.2.rows.mono (fun _ hx => hx.1))
  have hdegrees (r : Lp ℝ 2 μ) (hr : r ∈ I) :
      g =ᵐ[μ.restrict {y | ρ y = r}] fun _ => wholeRowDegree r :=
    wholeRowFiber_degree W m ρ r (hfibers r hr).2.2.2
  have hnostraddle := hW.ae_diffuse_no_degree_straddle hd hgap
    ρ hρ Bcut hcross I hI
    (fun r hr => ⟨(hfibers r hr).2.1, (hfibers r hr).2.2.2⟩) D hD hDeq
  have hDiffuse := ae_no_both_of_diffuse_cover K g ρ I D hD hI hDeq Z
    (fun _ hp => hp.1) hZsym hnoDD hcolumns hdegrees hnostraddle
  have hDiffuse' := (ae_restrict_iff' hD).mp hDiffuse
  filter_upwards [hAtoms, hDiffuse'] with x ha hdiff
  by_cases hxD : x ∈ D
  · exact hdiff hxD
  · have hxU : x ∈ ⋃ r ∈ I, {x | ρ x = r} := by
      simpa only [hDeq, mem_compl_iff, not_not] using hxD
    obtain ⟨r, hr⟩ := mem_iUnion.mp hxU
    obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
    exact ha r hrI hxr

/-- A selected shifted zero pair is either inside one actual positive
independent whole-row fiber or belongs to the distinct-row relation. -/
theorem FullStationaryClass.ae_shifted_zero_same_fiber_or_relation
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D : Set Ω)
    (hDeq : D = (⋃ r ∈ I, {x | ρ x = r})ᶜ)
    (hDcomplete : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      W.moment CappedColor.adjacency p = 1) :
    ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 →
      (∃ r ∈ I, ρ p.1 = r ∧ ρ p.2 = r) ∨ p ∈ actualZeroRelation W m ρ := by
  filter_upwards [hDcomplete, (hW.strict_gap_structure hd hgap).strict_support]
    with p hc hs hzero
  by_cases hne : ρ p.1 ≠ ρ p.2
  · exact Or.inr ⟨hzero, hne⟩
  · have heq : ρ p.1 = ρ p.2 := not_ne_iff.mp hne
    by_cases hr : ∃ r ∈ I, ρ p.1 = r
    · obtain ⟨r, hrI, hpr⟩ := hr
      exact Or.inl ⟨r, hrI, hpr, heq.symm ▸ hpr⟩
    · have hxD : p.1 ∈ D := by
        rw [hDeq]
        intro hx
        obtain ⟨r, hrr⟩ := mem_iUnion.mp hx
        obtain ⟨hrI, hpr⟩ := mem_iUnion.mp hrr
        exact hr ⟨r, hrI, hpr⟩
      have hyD : p.2 ∈ D := by
        rw [hDeq]
        intro hy
        obtain ⟨r, hrr⟩ := mem_iUnion.mp hy
        obtain ⟨hrI, hpr⟩ := mem_iUnion.mp hrr
        exact hr ⟨r, hrI, heq.trans hpr⟩
      have hG := hc hxD hyD
      change shiftedMoment W m p = 0 at hzero
      rw [hzero] at hs
      simp only [lt_irrefl, ↓reduceIte] at hs
      linarith

/-- The selected whole-row structure and its derived original-degree
classification are kept on one row representative and one multiplier. -/
structure SelectedHighLowStructure (W : Model Ω μ) (m : ℝ) where
  ρ : Ω → Lp ℝ 2 μ
  I : Set (Lp ℝ 2 μ)
  D : Set Ω
  Bcut : Set Ω
  H : Set Ω
  L : Set Ω
  N : Set Ω
  hρ : StronglyMeasurable ρ
  hrow : ∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x
  hI : I.Countable
  hfibers : ∀ r ∈ I, MeasurableSet {x | ρ x = r} ∧ 0 < μ {x | ρ x = r} ∧
    (∀ᵐ p ∂(μ.restrict {x | ρ x = r}).prod (μ.restrict {x | ρ x = r}),
      adjacencyKernel W p.1 p.2 = 0) ∧
    KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) 4 m ρ r
  hdisjoint : I.Pairwise (fun r t => Disjoint {x | ρ x = r} {x | ρ x = t})
  hDeq : D = (⋃ r ∈ I, {x | ρ x = r})ᶜ
  hD : MeasurableSet D
  hDcomplete : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
    W.moment CappedColor.adjacency p = 1
  hBcut : MeasurableSet Bcut
  hcross : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
    (p.1 ∈ Bcut ∧ p.2 ∉ Bcut) ∨ (p.2 ∈ Bcut ∧ p.1 ∉ Bcut)
  hfiberSide : ∀ r : Lp ℝ 2 μ, 0 < μ {x | ρ x = r} →
    (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ Bcut) ∨
      (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∉ Bcut)
  hH : H = OrderedZeroRelation.highClass μ (actualZeroRelation W m ρ)
    (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x)
  hL : L = OrderedZeroRelation.lowClass μ (actualZeroRelation W m ρ)
    (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x)
  hN : N = OrderedZeroRelation.neutralClass μ (actualZeroRelation W m ρ)
    (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x)
  hpartition : MeasurableSet H ∧ MeasurableSet L ∧ MeasurableSet N ∧
    H ∪ L ∪ N = univ ∧ Disjoint H L ∧ Disjoint H N ∧ Disjoint L N
  hdegreeNe : ∀ᵐ p ∂μ.prod μ, p ∈ actualZeroRelation W m ρ →
    adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 ≠
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2
  hnoBoth : ∀ᵐ x ∂μ,
    OrderedZeroRelation.leftNeighborMass μ (actualZeroRelation W m ρ)
        (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) x = 0 ∨
      OrderedZeroRelation.rightNeighborMass μ (actualZeroRelation W m ρ)
        (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) x = 0
  hrelation : ∀ᵐ p ∂μ.prod μ, p ∈ actualZeroRelation W m ρ →
    (p.1 ∈ H ∧ p.2 ∈ L ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1) ∨
    (p.2 ∈ H ∧ p.1 ∈ L ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2)
  hneutral : ∀ᵐ x ∂μ, x ∈ N → μ {y | (x, y) ∈ actualZeroRelation W m ρ} = 0
  hfiberClass : ∀ r ∈ I,
    (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ H) ∨
    (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ L) ∨
    (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ N)
  hcoverage : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 →
    (∃ r ∈ I, ρ p.1 = r ∧ ρ p.2 = r) ∨ p ∈ actualZeroRelation W m ρ

/-- The actual selected model supplies one common whole-row representation,
zero cut and derived high/low/neutral classification. No degree-order or
class-label hypothesis is supplied to this construction. -/
theorem FullStationaryClass.exists_selected_high_low_structure
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    Nonempty (SelectedHighLowStructure W m) := by
  obtain ⟨ρ, I, D, Bcut, hρ, hrow, hI, hfibers, hdisjoint, hDeq, hD,
    hDcomplete, hBcut, hcross, hfiberSide⟩ :=
    hW.exists_whole_row_structure hd hgap hmax
  let K := shiftedKernel W m
  let g : Ω → ℝ := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let Z := actualZeroRelation W m ρ
  let H := OrderedZeroRelation.highClass μ Z g
  let L := OrderedZeroRelation.lowClass μ Z g
  let N := OrderedZeroRelation.neutralClass μ Z g
  have hZ : MeasurableSet Z := measurableSet_actualZeroRelation W m ρ hρ
  have hg : Measurable g := (Lp.stronglyMeasurable _).measurable
  have hZsym := actualZeroRelation_symm W m ρ
  have hdegreeNe := hW.ae_actual_zero_relation_degree_ne hd hgap hmin
    ρ I D Bcut hρ hrow hI hfibers hDeq hDcomplete hcross
  have hnoBoth := hW.ae_actual_zero_relation_no_both hd hgap hmin
    ρ I D Bcut hρ hrow hI hfibers hDeq hD hDcomplete hcross
  have hpartition := OrderedZeroRelation.measurable_high_low_neutral_partition (μ := μ) Z hZ g hg
  have hrelation := OrderedZeroRelation.ae_relation_crosses_high_low (μ := μ)
    Z hZ g hg hZsym hdegreeNe hnoBoth
  have hneutral := OrderedZeroRelation.ae_neutral_section_null (μ := μ)
    Z hZ g hg hZsym hdegreeNe hnoBoth
  have hfiberClass (r : Lp ℝ 2 μ) (hr : r ∈ I) :
      (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ H) ∨
      (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ L) ∨
      (∀ᵐ x ∂μ.restrict {x | ρ x = r}, x ∈ N) := by
    let Br := {x | ρ x = r}
    let T := {y | r y = 0 ∧ ρ y ≠ r}
    have hBr := hfibers r hr
    have hrows := hBr.2.2.2.rows.mono (fun _ hx => hx.1)
    have hsection := ae_relation_section_of_homogeneous_rows K ρ r hrows
      (ae_restrict_mem hBr.1)
    have hdegree := wholeRowFiber_degree W m ρ r hBr.2.2.2
    exact OrderedZeroRelation.ae_one_class_of_homogeneous_sections (μ := μ) Z g hZsym
      Br T (wholeRowDegree r) hdegree hsection
  have hcoverage := hW.ae_shifted_zero_same_fiber_or_relation hd hgap
    ρ I D hDeq hDcomplete
  exact ⟨{
    ρ := ρ
    I := I
    D := D
    Bcut := Bcut
    H := H
    L := L
    N := N
    hρ := hρ
    hrow := hrow
    hI := hI
    hfibers := hfibers
    hdisjoint := hdisjoint
    hDeq := hDeq
    hD := hD
    hDcomplete := hDcomplete
    hBcut := hBcut
    hcross := hcross
    hfiberSide := hfiberSide
    hH := rfl
    hL := rfl
    hN := rfl
    hpartition := hpartition
    hdegreeNe := hdegreeNe
    hnoBoth := hnoBoth
    hrelation := hrelation
    hneutral := hneutral
    hfiberClass := hfiberClass
    hcoverage := hcoverage
  }⟩

end Erdos1017.CappedModel

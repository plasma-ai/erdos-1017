module

public import Erdos1017.Exclusions.Common.FiniteNeighborPatterns
public import Erdos1017.SelectedModel.Flows.SelectedAtomRedirection
public import Erdos1017.SelectedModel.Structure.WholeRowMissingMass

/-!
# Incidence of diffuse points with whole atoms

The outside missing mass at a diffuse point is the sum of the masses
`originalAtomMass` of its incident atoms, those atoms are low at diffuse high
points, and a positive diffuse high region with missing mass above a threshold
yields finitely many low atoms of total mass above it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Original masses on the actual countable family of positive independent
whole-row fibers, without choosing an enumeration or an anchor. -/
def originalAtomMass (S : SelectedHighLowStructure W m) (r : S.I) : ℝ :=
  μ.real {x | S.ρ x = r.val}

/-- The actual row-value test for incidence with one original whole atom. -/
def atomMissingIncidence (S : SelectedHighLowStructure W m) (r : S.I) : Set Ω :=
  {x | r.val x ≤ 0}

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Actual original atom masses are nonnegative and summable. -/
theorem originalAtomMass_summable (S : SelectedHighLowStructure W m) :
    (∀ r, 0 ≤ S.originalAtomMass r) ∧ Summable S.originalAtomMass := by
  let : Countable S.I := S.hI.to_subtype
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_⟩
  change Summable (fun r : S.I => (μ {x | S.ρ x = r.val}).toReal)
  apply ENNReal.summable_toReal
  rw [← measure_iUnion (fun r u hne => Set.disjoint_left.mpr (fun x hx hy =>
    hne (Subtype.ext (hx.symm.trans hy)))) (fun r => (S.hfibers r.val r.property).1)]
  exact measure_ne_top _ _

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The source's actual remainder excludes each original positive whole
fiber pointwise; this is a set identity, not an AE row assertion. -/
theorem row_ne_atom_of_mem_diffuse (S : SelectedHighLowStructure W m)
    (x : Ω) (hx : x ∈ S.D) (r : S.I) : S.ρ x ≠ r.val := by
  rw [S.hDeq] at hx
  intro he
  exact hx (mem_iUnion.mpr ⟨r.val, mem_iUnion.mpr ⟨r.property, he⟩⟩)

/-- On the same diffuse remainder, the actual incoming outside-zero
section on each positive whole fiber is exactly its row incidence test. -/
theorem ae_diffuse_atom_section (S : SelectedHighLowStructure W m)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    ∀ᵐ x ∂μ, x ∈ S.D → ∀ r : S.I, ∀ᵐ y ∂μ,
      S.ρ y = r.val → ((y, x) ∈ actualZeroRelation W m S.ρ ↔
        x ∈ S.atomMissingIncidence r) := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ p ∂μ.prod μ, ∀ r : S.I,
      S.ρ p.1 = r.val → shiftedKernel W m p.1 p.2 = r.val p.2 := by
    rw [ae_all_iff]
    intro r
    exact S.ae_kernel_eq_fiber_row r.val r.property
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (hall.and hnonneg)
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with x hx hxD r
  filter_upwards [hx] with y hy hyr
  have he : shiftedKernel W m y x = r.val x := hy.1 r hyr
  have hn : 0 ≤ shiftedKernel W m y x := hy.2
  constructor
  · intro hz
    change r.val x ≤ 0
    rw [← he, hz.1]
  · intro hinc
    refine ⟨le_antisymm (he.trans_le hinc) hn, ?_⟩
    exact fun heq => S.row_ne_atom_of_mem_diffuse x hxD r (heq.symm.trans hyr)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Complete diffuse support forces every actual incoming outside missing
neighbor of a diffuse point into one original positive whole atom. -/
theorem ae_diffuse_missing_covered_by_atoms (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∈ S.D → ∀ᵐ y ∂μ,
      (y, x) ∈ actualZeroRelation W m S.ρ → ∃ r : S.I, S.ρ y = r.val := by
  have hno : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
      p ∉ actualZeroRelation W m S.ρ := by
    filter_upwards [S.hDcomplete, (hW.strict_gap_structure hd hgap).strict_support]
      with p hc hs hx hy hz
    have hA := hc hx hy
    have hz' : shiftedMoment W m p = 0 := hz.1
    rw [hz'] at hs
    simp only [lt_self_iff_false, ↓reduceIte] at hs
    linarith
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hno
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with x hx hxD
  filter_upwards [hx] with y hy hZ
  have hyD : y ∉ S.D := fun hyD => hy hyD hxD hZ
  have hyU : y ∈ ⋃ r ∈ S.I, {x | S.ρ x = r} := by
    simpa only [S.hDeq, mem_compl_iff, not_not] using hyD
  obtain ⟨r, hr⟩ := mem_iUnion.mp hyU
  obtain ⟨hrI, hyr⟩ := mem_iUnion.mp hr
  exact ⟨⟨r, hrI⟩, hyr⟩

/-- The actual outside missing mass on the diffuse remainder is a justified
countable sum of original atom masses with their actual row incidences. -/
theorem ae_diffuse_outsideSectionMass_hasSum (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∈ S.D → HasSum
      (fun r : S.I => if x ∈ S.atomMissingIncidence r then S.originalAtomMass r else 0)
      (S.outsideSectionMass x) := by
  let : Countable S.I := S.hI.to_subtype
  let A (r : S.I) := {y | S.ρ y = r.val}
  let U := ⋃ r : S.I, A r
  have hA (r : S.I) : MeasurableSet (A r) := (S.hfibers r.val r.property).1
  have hdis : Pairwise (Disjoint on A) := by
    intro r u hne
    exact Set.disjoint_left.mpr (fun y hy hz => hne (Subtype.ext (hy.symm.trans hz)))
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  have hZ := measurableSet_actualZeroRelation W m S.ρ S.hρ
  filter_upwards [S.ae_diffuse_atom_section (hW.moment_mem.mono (fun _ hp => hp.1)),
    S.ae_diffuse_missing_covered_by_atoms hW hd hgap] with x hx hcover hxD
  let V := {y | (y, x) ∈ actualZeroRelation W m S.ρ}
  have hV : MeasurableSet V := measurable_prodMk_right hZ
  let f := V.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f μ := (integrable_const _).indicator hV
  have hsum := hasSum_integral_iUnion hA hdis hf.restrict
  have hterm (r : S.I) : (∫ y in A r, f y ∂μ) =
      if x ∈ S.atomMissingIncidence r then S.originalAtomMass r else 0 := by
    have heq : f =ᵐ[μ.restrict (A r)]
        fun _ => if x ∈ S.atomMissingIncidence r then 1 else 0 := by
      apply (ae_restrict_iff' (hA r)).mpr
      filter_upwards [hx hxD r] with y hy hyr
      have hiff := hy hyr
      by_cases hi : x ∈ S.atomMissingIncidence r
      · have hyV : y ∈ V := hiff.mpr hi
        simp only [f, indicator_of_mem hyV, hi, ↓reduceIte]
      · have hyV : y ∉ V := fun h => hi (hiff.mp h)
        simp only [f, indicator_of_notMem hyV, hi, ↓reduceIte]
    rw [integral_congr_ae heq]
    by_cases hi : x ∈ S.atomMissingIncidence r
    · simp only [hi, ↓reduceIte, setIntegral_const, smul_eq_mul, mul_one, originalAtomMass, A]
    · simp only [hi, ↓reduceIte, integral_zero]
  have htotal : (∫ y in U, f y ∂μ) = S.outsideSectionMass x := by
    have heq : U.indicator f =ᵐ[μ] f := by
      filter_upwards [hcover hxD] with y hy
      by_cases hz : y ∈ V
      · have hu : y ∈ U := mem_iUnion.mpr (hy hz)
        exact indicator_of_mem hu _
      · simp only [f, indicator_of_notMem hz, indicator_apply, ite_self]
    rw [← integral_indicator hU, integral_congr_ae heq]
    rw [show f = V.indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator hV, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [htotal] at hsum
  exact hsum.congr_fun (fun r => (hterm r).symm)

/-- The countable missing-mass identity retains literal original atom
masses and actual whole-row incidences on the same diffuse carrier. -/
theorem ae_diffuse_outsideSectionMass_eq_tsum (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∈ S.D → S.outsideSectionMass x =
      ∑' r : S.I, if x ∈ S.atomMissingIncidence r then S.originalAtomMass r else 0 := by
  filter_upwards [S.ae_diffuse_outsideSectionMass_hasSum hW hd hgap] with x hx hxD
  exact (hx hxD).tsum_eq.symm

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Every incident original whole atom at almost every diffuse HIGH point
is LOW. Both section orientation and its original positive fiber are retained. -/
theorem ae_diffuse_high_incident_atoms_low (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → ∀ r : S.I,
      x ∈ S.atomMissingIncidence r →
        ∀ᵐ y ∂μ.restrict {y | S.ρ y = r.val}, y ∈ S.L := by
  have hrel := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    S.hrelation
  filter_upwards [S.ae_diffuse_atom_section (hW.moment_mem.mono (fun _ hp => hp.1)),
    Measure.ae_ae_of_ae_prod hrel] with x hx hcross hxD hxH r hinc
  apply (ae_restrict_iff' (S.hfibers r.val r.property).1).mpr
  filter_upwards [hx hxD r, hcross] with y hy hc hyr
  have hZ : (y, x) ∈ actualZeroRelation W m S.ρ := (hy hyr).mpr hinc
  rcases hc hZ with h | h
  · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxH h.2.1)
  · exact h.2.1

/-- An actual positive diffuse HIGH region with outside missing mass above
the threshold yields finitely many original LOW atoms, of total original
mass above that threshold, and a common positive measurable missing region.
The common region is pointwise contained in the original bad set. -/
theorem exists_finite_low_atoms_common_diffuse_high_set
    (S : SelectedHighLowStructure W m) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (b : ℝ)
    (hpositive : 0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x})) :
    ∃ (J : Finset S.I) (C₀ : Set Ω), MeasurableSet C₀ ∧ 0 < μ C₀ ∧
      C₀ ⊆ S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x} ∧
      b < ∑ r ∈ J, S.originalAtomMass r ∧
      (∀ r ∈ J, ∀ᵐ y ∂μ.restrict {y | S.ρ y = r.val}, y ∈ S.L) ∧
      ∀ r ∈ J, ∀ᵐ p ∂(μ.restrict {y | S.ρ y = r.val}).prod (μ.restrict C₀),
        shiftedKernel W m p.1 p.2 = 0 ∧ adjacencyKernel W p.1 p.2 = 0 := by
  let : Countable S.I := S.hI.to_subtype
  let E := S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x}
  have hE : MeasurableSet E := (S.hD.inter S.hpartition.1).inter
    (measurableSet_lt measurable_const S.measurable_outsideSectionMass)
  have hP (r : S.I) : MeasurableSet (S.atomMissingIncidence r) :=
    measurableSet_le (Lp.stronglyMeasurable r.val).measurable measurable_const
  have hbad : ∀ᵐ x ∂μ, x ∈ E →
      b < ∑' r : S.I, if x ∈ S.atomMissingIncidence r then S.originalAtomMass r else 0 := by
    filter_upwards [S.ae_diffuse_outsideSectionMass_hasSum hW hd hgap] with x hx hxE
    rw [(hx hxE.1.1).tsum_eq]
    exact hxE.2
  obtain ⟨J, C₀, hC₀, hC₀pos, hCE, hCP, hmass⟩ :=
    FiniteNeighborPatterns.exists_positive_finite_pattern S.originalAtomMass
      S.originalAtomMass_summable.1 S.originalAtomMass_summable.2
      S.atomMissingIncidence hP E hE hpositive b hbad
  have hlow : ∀ r ∈ J, ∀ᵐ y ∂μ.restrict {y | S.ρ y = r.val}, y ∈ S.L := by
    obtain ⟨x, hxC, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hC₀pos.ne'
      (ae_restrict_of_ae (S.ae_diffuse_high_incident_atoms_low hW))
    intro r hr
    exact hx (hCE hxC).1.1 (hCE hxC).1.2 r (hCP r hr hxC)
  refine ⟨J, C₀, hC₀, hC₀pos, hCE, hmass, hlow, ?_⟩
  intro r hr
  have hBr := (S.hfibers r.val r.property).1
  have hle : (μ.restrict {y | S.ρ y = r.val}).prod (μ.restrict C₀) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hle (S.ae_kernel_eq_fiber_row r.val r.property),
    ae_mono hle hW.moment_mem,
    ae_mono hle (hW.strict_gap_structure hd hgap).strict_support,
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hBr),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hC₀)] with p he hn hs hx hy
  have hz : shiftedKernel W m p.1 p.2 = 0 :=
    le_antisymm ((he hx).trans_le (hCP r hr hy)) hn.1
  refine ⟨hz, ?_⟩
  have hz' : shiftedMoment W m p = 0 := hz
  change W.moment CappedColor.adjacency p = 0
  simpa only [hz', lt_self_iff_false, ↓reduceIte] using hs

end Erdos1017.CappedModel.SelectedHighLowStructure

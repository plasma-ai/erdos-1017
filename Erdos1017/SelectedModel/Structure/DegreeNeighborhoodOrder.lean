module

public import Erdos1017.SelectedModel.Structure.DegreeStraddle
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages

/-!
# One-sided degree order of missing neighbors

Every missing neighbor of a positive independent base lies almost everywhere on
one strict side of the base's original degree, since a positive missing set at
the exact degree would contradict the full-model tangent inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem ae_pair_restrict_of_subset
    (s t s' t' : Set Ω) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (P : Ω × Ω → Prop)
    (hP : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), P p) :
    ∀ᵐ p ∂(μ.restrict s').prod (μ.restrict t'), P p :=
  ae_mono (Measure.prod_mono (μ.restrict_mono_set hs) (μ.restrict_mono_set ht)) hP

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A positive missing set of the base's exact degree contradicts the
actual full-model tangent inequality when its internal shifted kernel is positive. -/
theorem FullStationaryClass.equal_degree_missing_null
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (B N : Set Ω) (hB : MeasurableSet B) (hN : MeasurableSet N)
    (hBpos : 0 < μ B) (a : ℝ)
    (hdegreeB : ∀ᵐ x ∂μ.restrict B,
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = a)
    (hBB : ∀ᵐ p ∂(μ.restrict B).prod (μ.restrict B),
      shiftedKernel W m p.1 p.2 = 0)
    (hBN : ∀ᵐ p ∂(μ.restrict B).prod (μ.restrict N),
      shiftedKernel W m p.1 p.2 = 0)
    (hEE : ∀ᵐ p ∂(μ.restrict
      (N ∩ {x | adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = a})).prod
        (μ.restrict (N ∩ {x | adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = a})),
      0 < shiftedKernel W m p.1 p.2) :
    μ (N ∩ {x | adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = a}) = 0 := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let E := N ∩ {x | g x = a}
  have hgmeas : Measurable (fun x => g x) := (Lp.stronglyMeasurable g).measurable
  have hE : MeasurableSet E := hN.inter (measurableSet_eq_fun hgmeas measurable_const)
  by_contra hEzero
  have hEpos : 0 < μ E := pos_iff_ne_zero.mpr hEzero
  have hEsub : E ⊆ N := fun _ hx => hx.1
  have hBE : ∀ᵐ p ∂(μ.restrict B).prod (μ.restrict E),
      shiftedKernel W m p.1 p.2 = 0 :=
    ae_pair_restrict_of_subset B N B E Subset.rfl hEsub _ hBN
  have hEBswap := (Measure.measurePreserving_swap (μ := μ.restrict E)
    (ν := μ.restrict B)).quasiMeasurePreserving.ae hBE
  have hsym : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict B),
      shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
      (by
        filter_upwards [shiftedMoment_symm W m] with p hp
        exact hp.symm)
  have hEB : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict B),
      shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hEBswap, hsym] with p hp hs
    exact hs.trans hp
  have hdegreeE : ∀ᵐ x ∂μ.restrict E, g x = a :=
    (ae_restrict_iff' hE).mpr (by
      filter_upwards with x hx
      exact hx.2)
  have hne := hW.degree_ne_of_positive_missing_set hd hgap B E hB hE
    hBpos hEpos hBB hEB hEE
  have hBavg := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq
    B hB hBpos g a hdegreeB
  have hEavg := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq
    E hE hEpos g a hdegreeE
  exact hne (hEavg.trans hBavg.symm)

/-- Every missing neighbor of a positive independent base lies almost
everywhere on one strict side of the base's original degree. The side is
global across the supplied missing region, with no orientation selected. -/
theorem FullStationaryClass.neighborhood_degree_one_side
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (B N : Set Ω) (hB : MeasurableSet B) (hN : MeasurableSet N)
    (hBpos : 0 < μ B) (a : ℝ)
    (hdegreeB : ∀ᵐ x ∂μ.restrict B,
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = a)
    (hBB : ∀ᵐ p ∂(μ.restrict B).prod (μ.restrict B),
      shiftedKernel W m p.1 p.2 = 0)
    (hBN : ∀ᵐ p ∂(μ.restrict B).prod (μ.restrict N),
      shiftedKernel W m p.1 p.2 = 0)
    (hUnequal : ∀ᵐ p ∂(μ.restrict N).prod (μ.restrict N),
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 ≠
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 →
          0 < shiftedKernel W m p.1 p.2)
    (hEqual : ∀ᵐ p ∂(μ.restrict
      (N ∩ {x | adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = a})).prod
        (μ.restrict (N ∩ {x | adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = a})),
      0 < shiftedKernel W m p.1 p.2) :
    (∀ᵐ x ∂μ.restrict N,
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x < a) ∨
    (∀ᵐ x ∂μ.restrict N,
      a < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let E := N ∩ {x | g x = a}
  let L := N ∩ {x | g x < a}
  let U := N ∩ {x | a < g x}
  have hgmeas : Measurable (fun x => g x) := (Lp.stronglyMeasurable g).measurable
  have hE : MeasurableSet E := hN.inter (measurableSet_eq_fun hgmeas measurable_const)
  have hL : MeasurableSet L := hN.inter (measurableSet_lt hgmeas measurable_const)
  have hU : MeasurableSet U := hN.inter (measurableSet_lt measurable_const hgmeas)
  have hEzero : μ E = 0 :=
    hW.equal_degree_missing_null hd hgap B N hB hN hBpos a hdegreeB hBB hBN hEqual
  have hnotE : ∀ᵐ x ∂μ.restrict N, x ∉ E :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr hEzero)
  by_cases hLzero : μ L = 0
  · right
    have hnotL : ∀ᵐ x ∂μ.restrict N, x ∉ L :=
      ae_restrict_of_ae (compl_mem_ae_iff.mpr hLzero)
    filter_upwards [ae_restrict_mem hN, hnotE, hnotL] with x hx he hl
    rcases lt_trichotomy (g x) a with hlt | heq | hgt
    · exact (hl ⟨hx, hlt⟩).elim
    · exact (he ⟨hx, heq⟩).elim
    · exact hgt
  · have hLpos : 0 < μ L := pos_iff_ne_zero.mpr hLzero
    by_cases hUzero : μ U = 0
    · left
      have hnotU : ∀ᵐ x ∂μ.restrict N, x ∉ U :=
        ae_restrict_of_ae (compl_mem_ae_iff.mpr hUzero)
      filter_upwards [ae_restrict_mem hN, hnotE, hnotU] with x hx he hu
      rcases lt_trichotomy (g x) a with hlt | heq | hgt
      · exact hlt
      · exact (he ⟨hx, heq⟩).elim
      · exact (hu ⟨hx, hgt⟩).elim
    · have hUpos : 0 < μ U := pos_iff_ne_zero.mpr hUzero
      have hLsub : L ⊆ N := fun _ hx => hx.1
      have hUsub : U ⊆ N := fun _ hx => hx.1
      have hBL : ∀ᵐ p ∂(μ.restrict B).prod (μ.restrict L),
          shiftedKernel W m p.1 p.2 = 0 :=
        ae_pair_restrict_of_subset B N B L Subset.rfl hLsub _ hBN
      have hBU : ∀ᵐ p ∂(μ.restrict B).prod (μ.restrict U),
          shiftedKernel W m p.1 p.2 = 0 :=
        ae_pair_restrict_of_subset B N B U Subset.rfl hUsub _ hBN
      have hLUraw : ∀ᵐ p ∂(μ.restrict L).prod (μ.restrict U),
          g p.1 ≠ g p.2 → 0 < shiftedKernel W m p.1 p.2 :=
        ae_pair_restrict_of_subset N N L U hLsub hUsub _ hUnequal
      have hLU : ∀ᵐ p ∂(μ.restrict L).prod (μ.restrict U),
          0 < shiftedKernel W m p.1 p.2 := by
        filter_upwards [hLUraw,
          Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hL),
          Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hU)] with p hp hl hu
        exact hp (ne_of_lt (hl.2.trans hu.2))
      have hLdegree : ∀ᵐ x ∂μ.restrict L, g x < a :=
        ae_restrict_of_forall_mem hL (fun _ hx => hx.2)
      have hUdegree : ∀ᵐ x ∂μ.restrict U, a < g x :=
        ae_restrict_of_forall_mem hU (fun _ hx => hx.2)
      have hLavg := KernelOperator.normalizedSetL2_inner_lt_of_ae_lt
        L hL hLpos g a hLdegree
      have hBavg := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq
        B hB hBpos g a hdegreeB
      have hUavg := KernelOperator.normalizedSetL2_inner_gt_of_ae_gt
        U hU hUpos g a hUdegree
      exact False.elim ((hW.not_degree_straddle_sets hd hgap B L U hB hL hU
        hBpos hLpos hUpos hBB hBL hBU hLU)
        ⟨hLavg.trans_eq hBavg.symm, hBavg.trans_lt hUavg⟩)

end Erdos1017.CappedModel

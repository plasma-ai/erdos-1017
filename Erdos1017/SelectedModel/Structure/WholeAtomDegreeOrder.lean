module

public import Erdos1017.SelectedModel.Structure.WholeRowCrossBlocks
public import Erdos1017.SelectedModel.Structure.WholeRowDegreeSeparation
public import Erdos1017.SelectedModel.Structure.DegreeNeighborhoodOrder
public import Erdos1017.SelectedModel.Structure.WholeFiberMissingGeometry
public import Erdos1017.SelectedModel.Structure.WholeRowDegreeFactorization

/-!
# One-sided degree order of a whole atom's missing region

The equal-degree part of a nonneighbor region outside its own whole independent
fiber lies almost everywhere in the complete remainder, and the missing region
outside one independent whole row fiber has a single strict original-degree
side.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The equal-degree part of a nonneighbor region outside its own whole
independent fiber lies almost everywhere in the complete remainder.
Every other positive independent fiber is excluded using its actual
cross block and the proved whole-row degree separation. -/
theorem FullStationaryClass.ae_equal_degree_missing_mem_remainder
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D : Set Ω)
    (hI : I.Countable)
    (hfibers : ∀ u ∈ I, MeasurableSet {x | ρ x = u} ∧ 0 < μ {x | ρ x = u} ∧
      (∀ᵐ p ∂(μ.restrict {x | ρ x = u}).prod (μ.restrict {x | ρ x = u}),
        adjacencyKernel W p.1 p.2 = 0) ∧
      KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
        (adjacencyKernel W) (chargeKernel W) 4 m ρ u)
    (hDeq : D = (⋃ u ∈ I, {x | ρ x = u})ᶜ)
    (r : Lp ℝ 2 μ) (hr : r ∈ I)
    (N : Set Ω)
    (hNoutside : ∀ x ∈ N, ρ x ≠ r)
    (hNnonpos : ∀ x ∈ N, r x ≤ 0) :
    ∀ᵐ x ∂μ,
      x ∈ N ∩ {x | adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = wholeRowDegree r} →
        x ∈ D := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let E := N ∩ {x | g x = wholeRowDegree r}
  have hrowr := hfibers r hr
  have hsym : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hnotfiber (u : Lp ℝ 2 μ) (hu : u ∈ I) :
      μ (E ∩ {x | ρ x = u}) = 0 := by
    by_contra hzero
    have hmeet : 0 < μ (E ∩ {x | ρ x = u}) := pos_iff_ne_zero.mpr hzero
    have hru : r ≠ u := by
      intro heq
      have hempty : E ∩ {x | ρ x = u} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hNoutside x hx.1.1 (hx.2.trans heq.symm)
      rw [hempty, measure_empty] at hmeet
      exact (lt_irrefl _ hmeet).elim
    have hrowu := hfibers u hu
    have hmiss : 0 < μ ({x | ρ x = u} ∩ {x | r x ≤ 0}) := by
      apply lt_of_lt_of_le hmeet
      apply measure_mono
      intro x hx
      exact ⟨hx.2, hNnonpos x hx.1.1⟩
    obtain ⟨_, _, hcross⟩ := KernelOperator.whole_row_cross_block_zero_of_positive_nonpositive
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m ρ r u
      hrowr.2.1 hrowu.2.1 hrowr.2.2.2 hrowu.2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
      (chargeKernel_measurable W) hsym hW.moment_mem hrowu.1 hmiss
    have hdegrees := hW.wholeRowDegree_ne_of_independent_nonadjacent hd hgap hmin
      ρ r u hru hrowr.1 hrowu.1 hrowr.2.1 hrowu.2.1
      hrowr.2.2.2 hrowu.2.2.2 hrowr.2.2.1 hrowu.2.2.1
      (hcross.mono (fun _ hp => hp.2.1))
    have hdegreeu : ∀ᵐ x ∂μ.restrict {x | ρ x = u}, g x = wholeRowDegree u :=
      wholeRowFiber_degree W m ρ u hrowu.2.2.2
    have hdegreeMeet : ∀ᵐ x ∂μ.restrict (E ∩ {x | ρ x = u}),
        g x = wholeRowDegree u :=
      ae_mono (μ.restrict_mono_set (fun _ hx => hx.2)) hdegreeu
    obtain ⟨x, hx, hg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hmeet.ne' hdegreeMeet
    exact hdegrees (hx.1.2.symm.trans hg)
  have havoid : ∀ᵐ x ∂μ, ∀ u ∈ I, x ∈ E → x ∉ {x | ρ x = u} := by
    apply (ae_ball_iff hI).mpr
    intro u hu
    have hnot : ∀ᵐ x ∂μ, x ∉ E ∩ {x | ρ x = u} :=
      compl_mem_ae_iff.mpr (hnotfiber u hu)
    exact hnot.mono (fun _ hx heq hxu => hx ⟨heq, hxu⟩)
  filter_upwards [havoid] with x hx hxE
  rw [hDeq]
  intro hmem
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨huI, hxu⟩ := Set.mem_iUnion.mp hu
  exact hx u huI hxE hxu

/-- The actual missing region outside one independent whole row fiber
has a single strict original-degree side. The row cut and complete
remainder are the common structural data of the selected model. -/
theorem FullStationaryClass.whole_atom_missing_degree_one_side
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D Bcut : Set Ω)
    (hρ : StronglyMeasurable ρ)
    (hrow : ∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x)
    (hI : I.Countable)
    (hfibers : ∀ u ∈ I, MeasurableSet {x | ρ x = u} ∧ 0 < μ {x | ρ x = u} ∧
      (∀ᵐ p ∂(μ.restrict {x | ρ x = u}).prod (μ.restrict {x | ρ x = u}),
        adjacencyKernel W p.1 p.2 = 0) ∧
      KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
        (adjacencyKernel W) (chargeKernel W) 4 m ρ u)
    (hDeq : D = (⋃ u ∈ I, {x | ρ x = u})ᶜ)
    (hDcomplete : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      W.moment CappedColor.adjacency p = 1)
    (hcross : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
      (p.1 ∈ Bcut ∧ p.2 ∉ Bcut) ∨ (p.2 ∈ Bcut ∧ p.1 ∉ Bcut))
    (r : Lp ℝ 2 μ) (hr : r ∈ I) :
    (∀ᵐ x ∂μ.restrict (KernelOperator.wholeFiberMissingSet ρ r),
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x < wholeRowDegree r) ∨
    (∀ᵐ x ∂μ.restrict (KernelOperator.wholeFiberMissingSet ρ r),
      wholeRowDegree r < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let Br := {x | ρ x = r}
  let N := KernelOperator.wholeFiberMissingSet ρ r
  let E := N ∩ {x | g x = wholeRowDegree r}
  have hs := hW.strict_gap_structure hd hgap
  have hBr := hfibers r hr
  have hN : MeasurableSet N := KernelOperator.measurableSet_wholeFiberMissingSet ρ hρ r
  have hE : MeasurableSet E := hN.inter
    (measurableSet_eq_fun (Lp.stronglyMeasurable g).measurable measurable_const)
  have hEsubD : ∀ᵐ x ∂μ, x ∈ E → x ∈ D :=
    hW.ae_equal_degree_missing_mem_remainder hd hgap hmin ρ I D hI hfibers
      hDeq r hr N (fun x hx => hx.1) (fun x hx => hx.2)
  have hED : ∀ᵐ x ∂μ.restrict E, x ∈ D := by
    filter_upwards [ae_restrict_of_ae hEsubD, ae_restrict_mem hE] with x hx he
    exact hx he
  have hleE : (μ.restrict E).prod (μ.restrict E) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hEE : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict E),
      0 < shiftedKernel W m p.1 p.2 := by
    filter_upwards [ae_mono hleE hDcomplete, ae_mono hleE hs.strict_support,
      Measure.quasiMeasurePreserving_fst.ae hED,
      Measure.quasiMeasurePreserving_snd.ae hED] with p hp hs hx hy
    have hG : W.moment CappedColor.adjacency p = 1 := hp hx hy
    rw [hG] at hs
    by_contra hnot
    have hzero : ¬0 < shiftedMoment W m p := hnot
    simp only [hzero, ↓reduceIte] at hs
    norm_num at hs
  have hBB : ∀ᵐ p ∂(μ.restrict Br).prod (μ.restrict Br),
      shiftedKernel W m p.1 p.2 = 0 :=
    shiftedKernel_zero_of_adjacency_zero W m hW.moment_mem hs.strict_support Br Br hBr.2.2.1
  have hBN : ∀ᵐ p ∂(μ.restrict Br).prod (μ.restrict N),
      shiftedKernel W m p.1 p.2 = 0 :=
    KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m) ρ hρ r
      (hBr.2.2.2.rows.mono (fun _ hx => hx.1))
      (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hx => hx.1))
  by_cases hNzero : μ N = 0
  · left
    rw [Measure.restrict_zero_set hNzero]
    simp
  · have hNpos : 0 < μ N := pos_iff_ne_zero.mpr hNzero
    have hdegree := ae_row_eq_imp_degree_eq W m ρ hrow hs.strict_support
    have hUnequal : ∀ᵐ p ∂(μ.restrict N).prod (μ.restrict N),
        g p.1 ≠ g p.2 → 0 < shiftedKernel W m p.1 p.2 :=
      KernelOperator.ae_positive_of_degree_ne_on_missingSet
        (shiftedKernel W m) ρ hρ r hBr.2.1 hNpos
        (hBr.2.2.2.rows.mono (fun _ hx => hx.1))
        (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hx => hx.1))
        Bcut hcross (fun x => g x) hdegree
    exact hW.neighborhood_degree_one_side hd hgap Br N hBr.1 hN hBr.2.1
      (wholeRowDegree r) (wholeRowFiber_degree W m ρ r hBr.2.2.2)
      hBB hBN hUnequal hEE

end Erdos1017.CappedModel

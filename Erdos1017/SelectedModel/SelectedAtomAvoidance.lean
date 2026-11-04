module

public import Erdos1017.SelectedModel.Structure.WholeRowMissingMass
public import Erdos1017.SelectedModel.Structure.WholeFiberMissingGeometry
public import Erdos1017.SelectedModel.Structure.WholeRowCrossBlocks

/-!
# Reduced zero relation after deleting a recipient fiber

Removing one recipient whole-row fiber from the selected distinct-row zero
relation gives the measurable `reducedZeroRelation`, with section-mass
splitting, missing-region identities, and the fact that deleting any high whole
atom leaves a positive recipient section for almost every low source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Remove one recipient whole-row fiber from the selected distinct-row
zero relation. The recipient is the first coordinate. -/
def SelectedHighLowStructure.reducedZeroRelation {W : Model Ω μ} {m : ℝ}
    (S : SelectedHighLowStructure W m) (r : Lp ℝ 2 μ) : Set (Ω × Ω) :=
  {p | p ∈ actualZeroRelation W m S.ρ ∧ S.ρ p.1 ≠ r}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The reduced actual relation remains measurable. -/
theorem SelectedHighLowStructure.measurableSet_reducedZeroRelation
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) : MeasurableSet (S.reducedZeroRelation r) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  exact (measurableSet_actualZeroRelation W m S.ρ S.hρ).inter
    (S.hρ.measurable.comp measurable_fst (measurableSet_singleton r)).compl

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The original outside section splits into the deleted recipient fiber
and the reduced relation, at every source. -/
theorem SelectedHighLowStructure.outsideSectionMass_eq_deleted_add_reduced
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) (y : Ω) :
    S.outsideSectionMass y =
      μ.real {x | (x, y) ∈ actualZeroRelation W m S.ρ ∧ S.ρ x = r} +
        MissingFlow.columnMass μ (S.reducedZeroRelation r) y := by
  let Z := actualZeroRelation W m S.ρ
  let Br := {x | S.ρ x = r}
  have hBr : MeasurableSet Br := by
    let : MeasurableSpace (Lp ℝ 2 μ) := borel _
    let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
    exact S.hρ.measurable (measurableSet_singleton r)
  have hsplit := measureReal_inter_add_sdiff (μ := μ)
    (s := {x | (x, y) ∈ Z}) hBr
  have hleft : {x | (x, y) ∈ Z ∧ S.ρ x = r} = {x | (x, y) ∈ Z} ∩ Br := rfl
  have hright : {x | (x, y) ∈ S.reducedZeroRelation r} =
      {x | (x, y) ∈ Z} \ Br := by
    ext x
    change ((x, y) ∈ Z ∧ S.ρ x ≠ r) ↔ ((x, y) ∈ Z ∧ ¬S.ρ x = r)
    simp only [ne_eq]
  change μ.real {x | (x, y) ∈ Z} =
    μ.real {x | (x, y) ∈ Z ∧ S.ρ x = r} +
      μ.real {x | (x, y) ∈ S.reducedZeroRelation r}
  rw [hleft, hright]
  exact hsplit.symm

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem ae_forward_wholeFiberMissingSet_relation
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R)
    (r : Lp ℝ 2 μ)
    (hrows : ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ))
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2) :
    ∀ᵐ x ∂μ.restrict {x | R x = r}, ∀ᵐ y ∂μ,
      (K x y = 0 ∧ R x ≠ R y) ↔ y ∈ KernelOperator.wholeFiberMissingSet R r := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hrmeas : MeasurableSet {x | R x = r} := hR.measurable (measurableSet_singleton r)
  filter_upwards [hrows, ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hK0),
    ae_restrict_mem hrmeas] with x hx hk hxr
  filter_upwards [hx, hk] with y hxy hky
  change (K x y = 0 ∧ R x ≠ R y) ↔ (R y ≠ r ∧ r y ≤ 0)
  rw [hxr, hxy]
  constructor
  · rintro ⟨hz, hne⟩
    exact ⟨hne.symm, hz.le⟩
  · rintro ⟨hne, hle⟩
    exact ⟨le_antisymm hle (hxy ▸ hky), hne.symm⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- On the displayed independent whole-row fiber, the outside
zero-relation section has exactly the mass of its actual missing region. -/
theorem SelectedHighLowStructure.ae_outsideSectionMass_eq_missingRegion_on_fiber
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m) (r : Lp ℝ 2 μ) (hr : r ∈ S.I) :
    ∀ᵐ y ∂μ.restrict {y | S.ρ y = r},
      S.outsideSectionMass y = μ.real (KernelOperator.wholeFiberMissingSet S.ρ r) := by
  let Z := actualZeroRelation W m S.ρ
  let N := KernelOperator.wholeFiberMissingSet S.ρ r
  have hrows := (S.hfibers r hr).2.2.2.rows.mono (fun _ hx => hx.1)
  have hsection := ae_forward_wholeFiberMissingSet_relation
    (shiftedKernel W m) S.ρ S.hρ r hrows (hW.moment_mem.mono fun _ hp => hp.1)
  have hsym := ae_restrict_of_ae (s := {y | S.ρ y = r})
    (Measure.ae_ae_of_ae_prod (actualZeroRelation_symm W m S.ρ))
  filter_upwards [hsection, hsym] with y hsec hsy
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hsec, hsy] with x hx hy
  apply propext
  change ((x, y) ∈ Z) ↔ x ∈ N
  exact hy.symm.trans hx

/-- The reference whole atom's closed missing mass is its own mass plus
the mass of its actual outside missing region. -/
theorem SelectedHighLowStructure.one_sub_wholeRowDegree_eq_fiber_add_missing
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I) :
    1 - wholeRowDegree r = μ.real {x | S.ρ x = r} +
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ r) := by
  let Br := {x | S.ρ x = r}
  have hBr := S.hfibers r hr
  have hmass := ae_restrict_of_ae (s := Br) (S.ae_missing_mass_decomposition hW hd hgap)
  have hdegree := wholeRowFiber_degree W m S.ρ r hBr.2.2.2
  have hsection := S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW r hr
  obtain ⟨y, _, hy, hgy, hmy, hsy⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hBr.2.1.ne'
      ((ae_restrict_mem hBr.1).and (hdegree.and (hmass.and hsection)))
  rw [hgy] at hmy
  rw [S.ownIndependentMass_eq_fiber r hr y hy, hsy] at hmy
  exact hmy

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem incident_fiber_mass_le_missing
    (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (r u : Lp ℝ 2 μ)
    (hru : r ≠ u)
    (hzero : (r : Ω → ℝ) =ᵐ[μ.restrict {x | R x = u}] fun _ => 0) :
    μ.real {x | R x = u} ≤ μ.real (KernelOperator.wholeFiberMissingSet R r) := by
  let F := {x | R x = u}
  let N := KernelOperator.wholeFiberMissingSet R r
  have hF : MeasurableSet F := by
    let : MeasurableSpace (Lp ℝ 2 μ) := borel _
    have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
    exact hR.measurable (measurableSet_singleton u)
  have hsub : F ≤ᵐ[μ] N := by
    apply (ae_restrict_iff' hF).mp
    filter_upwards [hzero, ae_restrict_mem hF] with x hx hFx
    exact ⟨fun he => hru (he.symm.trans hFx), le_of_eq hx⟩
  exact ENNReal.toReal_mono (measure_ne_top μ N) (measure_mono_ae hsub)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [IsProbabilityMeasure μ]
  [NullSingletonClass μ] in
private theorem ae_own_mass_le_of_incident_bounds
    (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (I : Set (Lp ℝ 2 μ)) (hI : I.Countable)
    (N : Set Ω) (a : Ω → ℝ)
    (ha_in : ∀ u ∈ I, ∀ y, R y = u → a y = μ.real {x | R x = u})
    (ha_out : ∀ y, R y ∉ I → a y = 0)
    (hbound : ∀ u ∈ I, 0 < μ (N ∩ {x | R x = u}) →
      μ.real {x | R x = u} ≤ μ.real N) :
    ∀ᵐ y ∂μ.restrict N, a y ≤ μ.real N := by
  have h_each : ∀ᵐ y ∂μ.restrict N,
      ∀ u ∈ I, R y = u → a y ≤ μ.real N := by
    apply (ae_ball_iff hI).mpr
    intro u hu
    by_cases hpos : 0 < μ (N ∩ {x | R x = u})
    · filter_upwards [] with y
      intro hy
      rw [ha_in u hu y hy]
      exact hbound u hu hpos
    · have hzero : μ (N ∩ {x | R x = u}) = 0 :=
        le_antisymm (le_of_not_gt hpos) bot_le
      have hnot : ∀ᵐ y ∂μ.restrict N, R y ≠ u := by
        rw [ae_iff]
        have heq : {y | ¬ R y ≠ u} = {y | R y = u} := by
          ext y
          simp only [ne_eq, not_not]
        have hF : MeasurableSet {y | R y = u} := by
          let : MeasurableSpace (Lp ℝ 2 μ) := borel _
          have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
          exact hR.measurable (measurableSet_singleton u)
        rw [heq, Measure.restrict_apply hF]
        exact (Set.inter_comm _ _).symm ▸ hzero
      filter_upwards [hnot] with y hy hmatch
      exact (hy hmatch).elim
  filter_upwards [h_each] with y hy
  by_cases hmem : R y ∈ I
  · exact hy (R y) hmem rfl
  · rw [ha_out y hmem]
    exact measureReal_nonneg

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- An atom incident to the displayed whole atom's missing region is
contained there almost everywhere. Countability handles all other atoms. -/
theorem SelectedHighLowStructure.ae_ownIndependentMass_le_missingRegion
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m) (r : Lp ℝ 2 μ) (hr : r ∈ S.I) :
    ∀ᵐ y ∂μ.restrict (KernelOperator.wholeFiberMissingSet S.ρ r),
      S.ownIndependentMass y ≤
        μ.real (KernelOperator.wholeFiberMissingSet S.ρ r) := by
  let N := KernelOperator.wholeFiberMissingSet S.ρ r
  have hN : MeasurableSet N := KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r
  have hKsym : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hbound (u : Lp ℝ 2 μ) (hu : u ∈ S.I)
      (hpos : 0 < μ (N ∩ {x | S.ρ x = u})) :
      μ.real {x | S.ρ x = u} ≤ μ.real N := by
    have hru : r ≠ u := by
      intro heq
      have hzero : N ∩ {x | S.ρ x = u} = ∅ := by
        ext x
        simp only [N, KernelOperator.wholeFiberMissingSet, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        exact hx.1.1 (hx.2.trans heq.symm)
      rw [hzero, measure_empty] at hpos
      exact (lt_irrefl _ hpos).elim
    have hpos' : 0 < μ ({x | S.ρ x = u} ∩ {x | r x ≤ 0}) := by
      apply lt_of_lt_of_le hpos
      apply measure_mono
      intro x hx
      exact ⟨hx.2, hx.1.2⟩
    have hzero := KernelOperator.whole_row_cross_block_zero_of_positive_nonpositive
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ r u
      (S.hfibers r hr).2.1 (S.hfibers u hu).2.1
      (S.hfibers r hr).2.2.2 (S.hfibers u hu).2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
      (chargeKernel_measurable W) hKsym hW.moment_mem (S.hfibers u hu).1 hpos'
    exact incident_fiber_mass_le_missing S.ρ S.hρ r u hru hzero.1
  exact ae_own_mass_le_of_incident_bounds S.ρ S.hρ S.I S.hI N
    S.ownIndependentMass
    (fun u hu y hy => S.ownIndependentMass_eq_fiber u hu y hy)
    (fun y hy => S.ownIndependentMass_eq_zero_of_not_mem y hy) hbound

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- A HIGH whole atom's actual outside missing region consists almost
everywhere of LOW vertices with strictly smaller original degree. -/
theorem SelectedHighLowStructure.ae_missingRegion_low_degree_lt
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m) (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hHigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H) :
    ∀ᵐ y ∂μ.restrict (KernelOperator.wholeFiberMissingSet S.ρ r),
      y ∈ S.L ∧
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) y < wholeRowDegree r := by
  let Br := {x | S.ρ x = r}
  let N := KernelOperator.wholeFiberMissingSet S.ρ r
  let g : Ω → ℝ := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hBr := S.hfibers r hr
  have hN : MeasurableSet N := KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r
  have hKzero := KernelOperator.ae_zero_fiber_prod_missingSet
    (shiftedKernel W m) S.ρ S.hρ r
    (hBr.2.2.2.rows.mono (fun _ hx => hx.1))
    (shiftedKernel_measurable W m) (hW.moment_mem.mono fun _ hp => hp.1)
  have hle : (μ.restrict Br).prod (μ.restrict N) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hZrelation := Measure.ae_ae_of_ae_prod (ae_mono hle S.hrelation)
  have hzeroNested := Measure.ae_ae_of_ae_prod hKzero
  have hdegree := wholeRowFiber_degree W m S.ρ r hBr.2.2.2
  obtain ⟨_, hLmeas, _, _, hHL, _, _⟩ := S.hpartition
  have hg : Measurable g := (Lp.stronglyMeasurable _).measurable
  have hgood : ∀ᵐ x ∂μ.restrict Br, ∀ᵐ y ∂μ.restrict N,
      y ∈ S.L ∧ g y < wholeRowDegree r := by
    filter_upwards [hHigh, hdegree, ae_restrict_mem hBr.1, hzeroNested, hZrelation]
      with x hxH hxg hxBr hxzero hxrel
    filter_upwards [ae_restrict_mem hN, hxzero, hxrel] with y hyN hxy hrel
    have hZxy : (x, y) ∈ actualZeroRelation W m S.ρ := by
      refine ⟨hxy, ?_⟩
      intro heq
      exact hyN.1 (heq.symm.trans hxBr)
    rcases hrel hZxy with h | h
    · exact ⟨h.2.1, hxg ▸ h.2.2⟩
    · exact (Set.disjoint_left.mp hHL hxH h.2.1).elim
  have hgoodProd : ∀ᵐ p ∂(μ.restrict Br).prod (μ.restrict N),
      p.2 ∈ S.L ∧ g p.2 < wholeRowDegree r := by
    apply (Measure.ae_prod_iff_ae_ae
      ((hLmeas.preimage measurable_snd).inter
        (measurableSet_lt (hg.comp measurable_snd) measurable_const))).mpr
    exact hgood
  have hswap := (Measure.measurePreserving_swap (μ := μ.restrict N)
    (ν := μ.restrict Br)).quasiMeasurePreserving.ae hgoodProd
  have hgoodY := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hgoodY] with y hy
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hBr.2.1.ne' hy
  exact hx

/-- Every source in a HIGH whole atom's missing region has outside
zero-relation section mass strictly larger than that atom's original mass. -/
theorem SelectedHighLowStructure.ae_outsideSectionMass_gt_atomMass_on_missing
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hHigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H) :
    ∀ᵐ y ∂μ.restrict (KernelOperator.wholeFiberMissingSet S.ρ r),
      μ.real {x | S.ρ x = r} < S.outsideSectionMass y := by
  let N := KernelOperator.wholeFiberMissingSet S.ρ r
  have hmass := ae_restrict_of_ae (s := N) (S.ae_missing_mass_decomposition hW hd hgap)
  have hbound := S.ae_ownIndependentMass_le_missingRegion hW r hr
  have horder := S.ae_missingRegion_low_degree_lt hW r hr hHigh
  have href := S.one_sub_wholeRowDegree_eq_fiber_add_missing hW hd hgap r hr
  filter_upwards [hmass, hbound, horder] with y hm hb ho
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
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

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- LOW membership gives positive outside zero-relation mass in the
source column almost everywhere; symmetry changes outgoing to incoming. -/
theorem SelectedHighLowStructure.ae_outsideSectionMass_pos_of_low
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m) :
    ∀ᵐ y ∂μ, y ∈ S.L → 0 < S.outsideSectionMass y := by
  let Z := actualZeroRelation W m S.ρ
  let g : Ω → ℝ := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hsym := Measure.ae_ae_of_ae_prod (actualZeroRelation_symm W m S.ρ)
  filter_upwards [hsym] with y hy hLow
  have hsection : S.outsideSectionMass y = μ.real {x | (y, x) ∈ Z} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hy] with x hx
    apply propext
    exact hx.symm
  have hright : 0 < OrderedZeroRelation.rightNeighborMass μ Z g y := by
    rw [S.hL] at hLow
    exact hLow.1
  have hsub : {x | (y, x) ∈ Z ∧ g y < g x} ⊆ {x | (y, x) ∈ Z} :=
    fun _ hx => hx.1
  have hpos : 0 < μ {x | (y, x) ∈ Z} :=
    lt_of_lt_of_le hright (measure_mono hsub)
  rw [hsection]
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top μ _)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Outside the reference atom's missing region, the actual distinct-row
relation has zero recipient mass in that atom. -/
theorem SelectedHighLowStructure.ae_deletedSection_zero_outside_missing
    {W : Model Ω μ} {m : ℝ} (S : SelectedHighLowStructure W m)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I) :
    ∀ᵐ y ∂μ, y ∉ KernelOperator.wholeFiberMissingSet S.ρ r →
      μ.real {x | (x, y) ∈ actualZeroRelation W m S.ρ ∧ S.ρ x = r} = 0 := by
  let K := shiftedKernel W m
  let Br := {x | S.ρ x = r}
  let N := KernelOperator.wholeFiberMissingSet S.ρ r
  let Z := actualZeroRelation W m S.ρ
  have hKsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hcolumns : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ.restrict Br, K y x = r y :=
    ae_columns_of_homogeneous_rows K (shiftedKernel_measurable W m) hKsym
      Br r (Lp.stronglyMeasurable r)
      ((S.hfibers r hr).2.2.2.rows.mono fun _ hx => hx.1)
  have hsymSections := Measure.ae_ae_of_ae_prod hKsym
  have hBr : MeasurableSet Br := (S.hfibers r hr).1
  filter_upwards [hcolumns, hsymSections] with y hcol hsym hyNotN
  have hcolGlobal := (ae_restrict_iff' hBr).mp hcol
  have hno : ∀ᵐ x ∂μ, ¬((x, y) ∈ Z ∧ S.ρ x = r) := by
    filter_upwards [hcolGlobal, hsym] with x hx hs
    rintro ⟨hZxy, hxr⟩
    have hyNe : S.ρ y ≠ r := by
      intro hyEq
      exact hZxy.2 (hxr.trans hyEq.symm)
    have hKzero : K x y = 0 := hZxy.1
    have hry : r y = 0 := (hx hxr).symm.trans (hs.trans hKzero)
    exact hyNotN ⟨hyNe, hry.le⟩
  have hzero : μ {x | (x, y) ∈ Z ∧ S.ρ x = r} = 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hno
  change (μ {x | (x, y) ∈ Z ∧ S.ρ x = r}).toReal = 0
  rw [hzero]
  simp

/-- Removing any HIGH whole atom leaves a positive recipient section for
almost every LOW source. The source may lie anywhere in the original model;
no peak or largest-atom property is assumed. -/
theorem SelectedHighLowStructure.ae_reducedZeroRelation_columnMass_pos_of_low
    {d c m : ℝ} {W : Model Ω μ} (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (r : Lp ℝ 2 μ) (hr : r ∈ S.I)
    (hHigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H) :
    ∀ᵐ y ∂μ, y ∈ S.L →
      0 < MissingFlow.columnMass μ (S.reducedZeroRelation r) y := by
  let N := KernelOperator.wholeFiberMissingSet S.ρ r
  have hN : MeasurableSet N := KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r
  have hgt := (ae_restrict_iff' hN).mp
    (S.ae_outsideSectionMass_gt_atomMass_on_missing hW hd hgap r hr hHigh)
  have hzero := S.ae_deletedSection_zero_outside_missing r hr
  have hpos := S.ae_outsideSectionMass_pos_of_low
  filter_upwards [hgt, hzero, hpos] with y hgreater hzeroY hposY hLow
  have hsplit := S.outsideSectionMass_eq_deleted_add_reduced r y
  have hbound : μ.real {x | (x, y) ∈ actualZeroRelation W m S.ρ ∧ S.ρ x = r} ≤
      μ.real {x | S.ρ x = r} := by
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono
    intro x hx
    exact hx.2
  by_cases hyN : y ∈ N
  · have hstrict := hgreater hyN
    linarith
  · rw [hzeroY hyN] at hsplit
    have hstrict := hposY hLow
    linarith
end Erdos1017.CappedModel

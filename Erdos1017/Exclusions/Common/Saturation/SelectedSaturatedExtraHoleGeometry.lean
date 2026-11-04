module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedSources
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns
public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages

/-!
# Extra hole for a private high region

A positive high region private to one saturated head but outside its entire
compulsory source has an additional low missing rectangle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Strict degree order on a positive original missing rectangle passes to
the corresponding normalized original degree averages. -/
private theorem degree_average_gt_of_zero_rectangle
    (H L : Set Ω) (hH : MeasurableSet H) (hL : MeasurableSet L)
    (hHpos : 0 < μ H) (hLpos : 0 < μ L)
    (hHhigh : H ⊆ S.H)
    (hdifferent : ∀ p : Ω × Ω, p.1 ∈ H → p.2 ∈ L → S.ρ p.1 ≠ S.ρ p.2)
    (hzero : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L),
      shiftedKernel W m p.1 p.2 = 0) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      KernelOperator.normalizedSetL2 L hL⟫ <
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 H hH⟫ := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hle : (μ.restrict H).prod (μ.restrict L) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hrect : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L), g p.2 < g p.1 := by
    filter_upwards [hzero, ae_mono hle S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hH),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hL)]
      with p hz hrel hpH hpL
    have hpHigh : p.1 ∈ S.H := hHhigh hpH
    have hZ : (p.1, p.2) ∈ actualZeroRelation W m S.ρ :=
      ⟨hz, hdifferent p hpH hpL⟩
    rcases hrel hZ with h | h
    · exact h.2.2
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hpHigh h.2.1)
  have hsec := Measure.ae_ae_of_ae_prod hrect
  have hgt : ∀ᵐ x ∂μ.restrict H,
      ⟪g, KernelOperator.normalizedSetL2 L hL⟫ < g x :=
    hsec.mono (fun x hx =>
      KernelOperator.normalizedSetL2_inner_lt_of_ae_lt L hL hLpos g (g x) hx)
  exact KernelOperator.normalizedSetL2_inner_gt_of_ae_gt H hH hHpos g _ hgt

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A HIGH private source with no diffuse recipient and no membership in
the entire singleton source has a different eligible missing atom. -/
private theorem exists_extra_eligible_hole
    {r u : S.I} (hrEligible : r ∈ S.eligibleReverseAtom)
    (x : Ω) (hxH : x ∈ S.H) (hxδ : S.reverseDiffuseSupply x = 0)
    (hxr : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val)
    (hxu : x ∉ KernelOperator.wholeFiberMissingSet S.ρ u.val)
    (hxSA : x ∉ S.reverseCompulsorySource {r}) :
    ∃ v : S.I, v ∈ S.eligibleReverseAtom ∧ v ≠ r ∧ v ≠ u ∧
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ v.val := by
  by_contra hnot
  push Not at hnot
  apply hxSA
  refine ⟨hxH, hxδ, ⟨r, hrEligible, hxr⟩, ?_⟩
  intro v hv hxv
  by_contra hvnot
  have hvr : v ≠ r := by simpa using hvnot
  have hvu : v ≠ u := by
    intro he
    exact hxu (he ▸ hxv)
  exact hnot v hv hvr hvu hxv

/-- The actual complete diffuse square has no diffuse LOW missing section. -/
private theorem ae_reverseDiffuseSupply_zero_on_diffuse
    [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∈ S.D → S.reverseDiffuseSupply x = 0 := by
  have hcover := S.ae_diffuse_missing_covered_by_atoms hW hd hgap
  filter_upwards [hcover] with x hx hxD
  have hnull : μ {y | y ∈ S.D ∩ S.L ∧
      (y, x) ∈ actualZeroRelation W m S.ρ} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hx hxD] with y hy hbad
    obtain ⟨r, hr⟩ := hy hbad.2
    exact S.row_ne_atom_of_mem_diffuse y hbad.1.1 r hr
  change (μ {y | y ∈ S.D ∩ S.L ∧
    (y, x) ∈ actualZeroRelation W m S.ρ}).toReal = 0
  rw [hnull]
  rfl

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A positive set covered almost everywhere by countably many literal
cells has a positive intersection with one cell. -/
private theorem exists_positive_cell_of_ae_cover
    {ι : Type*} [Countable ι]
    (E : Set Ω) (T : ι → Set Ω) (hEpos : 0 < μ E)
    (hcover : ∀ᵐ x ∂μ, x ∈ E → ∃ i, x ∈ T i) :
    ∃ i, 0 < μ (E ∩ T i) := by
  have heq : μ E = μ (⋃ i, E ∩ T i) := by
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
  exact hEpos.ne'

/-- A HIGH region missing a positive original atom has a positive LOW
subfiber on a genuine zero rectangle, ordered by original degree. -/
private theorem exists_low_witness_of_atom_hole
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (H : Set Ω) (hH : MeasurableSet H) (hHpos : 0 < μ H)
    (hHhigh : H ⊆ S.H) (v : S.I)
    (hHmissing : H ⊆ KernelOperator.wholeFiberMissingSet S.ρ v.val) :
    ∃ (L : Set Ω) (hL : MeasurableSet L), 0 < μ L ∧
      L ⊆ S.L ∧ L ⊆ {x | S.ρ x = v.val} ∧
      (∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L),
        shiftedKernel W m p.1 p.2 = 0) ∧
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 L hL⟫ <
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
          KernelOperator.normalizedSetL2 H hH⟫ := by
  let Iv := {x | S.ρ x = v.val}
  let Nv := KernelOperator.wholeFiberMissingSet S.ρ v.val
  have hIv : MeasurableSet Iv := (S.hfibers v.val v.property).1
  have hIvpos : 0 < μ Iv := (S.hfibers v.val v.property).2.1
  have hzeroV := KernelOperator.ae_zero_fiber_prod_missingSet
    (shiftedKernel W m) S.ρ S.hρ v.val
    ((S.hfibers v.val v.property).2.2.2.rows.mono (fun _ hx => hx.1))
    (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hp => hp.1))
  have hle : (μ.restrict Iv).prod (μ.restrict H) ≤
      (μ.restrict Iv).prod (μ.restrict Nv) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono hHmissing le_rfl)
  have hzeroIH : ∀ᵐ p ∂(μ.restrict Iv).prod (μ.restrict H),
      shiftedKernel W m p.1 p.2 = 0 := ae_mono hle hzeroV
  have hzeroHI : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict Iv),
      shiftedKernel W m p.1 p.2 = 0 := by
    have hswap := (Measure.measurePreserving_swap (μ := μ.restrict H)
      (ν := μ.restrict Iv)).quasiMeasurePreserving.ae hzeroIH
    filter_upwards [hswap, ae_mono (Measure.prod_mono Measure.restrict_le_self
      Measure.restrict_le_self) (shiftedMoment_symm W m)] with p hp hs
    change shiftedKernel W m p.2 p.1 = 0 at hp
    change shiftedKernel W m p.2 p.1 = shiftedKernel W m p.1 p.2 at hs
    exact hs.symm.trans hp
  have hlow : ∀ᵐ y ∂μ.restrict Iv, y ∈ S.L := by
    have hrect : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict Iv), p.2 ∈ S.L := by
      have hle' : (μ.restrict H).prod (μ.restrict Iv) ≤ μ.prod μ :=
        Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
      filter_upwards [hzeroHI, ae_mono hle' S.hrelation,
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hH),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hIv)]
        with p hz hrel hpH hpIv
      have hpZ : (p.1, p.2) ∈ actualZeroRelation W m S.ρ :=
        ⟨hz, fun he => (hHmissing hpH).1 (he.trans hpIv)⟩
      rcases hrel hpZ with h | h
      · exact h.2.1
      · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1
          (hHhigh hpH) h.2.1)
    have hsec := Measure.ae_ae_of_ae_prod hrect
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hHpos.ne' hsec
    exact hx
  let L := Iv ∩ S.L
  have hL : MeasurableSet L := hIv.inter S.hpartition.2.1
  have hLpos : 0 < μ L := by
    have heq : μ L = μ Iv := by
      have ht := Measure.measure_inter_eq_of_ae (s := univ) hlow
      change (μ.restrict Iv) (S.L ∩ univ) = (μ.restrict Iv) univ at ht
      rw [Set.inter_univ, Measure.restrict_apply S.hpartition.2.1,
        Measure.restrict_apply_univ] at ht
      simpa [L, Set.inter_comm] using ht
    rw [heq]
    exact hIvpos
  have hzeroHL : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L),
      shiftedKernel W m p.1 p.2 = 0 :=
    ae_mono (Measure.prod_mono le_rfl
      (Measure.restrict_mono (show L ⊆ Iv from inter_subset_left) le_rfl)) hzeroHI
  refine ⟨L, hL, hLpos, inter_subset_right, inter_subset_left, hzeroHL, ?_⟩
  apply degree_average_gt_of_zero_rectangle H L hH hL hHpos hLpos hHhigh
  · intro p hpH hpL he
    exact (hHmissing hpH).1 (he.trans hpL.1)
  · exact hzeroHL

/-- Positive diffuse LOW supply on a positive HIGH region comes from a
positive original whole atom and yields a diffuse LOW zero rectangle. -/
private theorem exists_low_witness_of_diffuse_supply
    [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (E : Set Ω) (hE : MeasurableSet E) (hEpos : 0 < μ E)
    (hEhigh : E ⊆ S.H)
    (hEδ : ∀ x ∈ E, 0 < S.reverseDiffuseSupply x) :
    ∃ (H L : Set Ω) (hH : MeasurableSet H) (hL : MeasurableSet L),
      0 < μ H ∧ H ⊆ E ∧ 0 < μ L ∧ L ⊆ S.D ∩ S.L ∧
      (∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L),
        shiftedKernel W m p.1 p.2 = 0) ∧
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 L hL⟫ <
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
          KernelOperator.normalizedSetL2 H hH⟫ := by
  let _ : Countable S.I := S.hI.to_subtype
  have hcover : ∀ᵐ x ∂μ, x ∈ E → ∃ k : S.I, S.ρ x = k.val := by
    filter_upwards [S.ae_reverseDiffuseSupply_zero_on_diffuse hW hd hgap] with x hx hxE
    have hxnotD : x ∉ S.D := by
      intro hxD
      linarith [hx hxD, hEδ x hxE]
    rw [S.hDeq] at hxnotD
    obtain ⟨r, hr⟩ := mem_iUnion.mp (not_not.mp hxnotD)
    obtain ⟨hrI, hrx⟩ := mem_iUnion.mp hr
    exact ⟨⟨r, hrI⟩, hrx⟩
  obtain ⟨k, hkpos⟩ := exists_positive_cell_of_ae_cover E
    (fun k : S.I => {x | S.ρ x = k.val}) hEpos hcover
  let H := E ∩ {x | S.ρ x = k.val}
  have hH : MeasurableSet H := hE.inter (S.hfibers k.val k.property).1
  have hHhigh : H ⊆ S.H := fun _ hx => hEhigh hx.1
  have hδk : 0 < S.fiberDiffuseMass k := by
    have hδae : ∀ᵐ x ∂μ.restrict H,
        S.reverseDiffuseSupply x = S.fiberDiffuseMass k :=
      ae_mono (Measure.restrict_mono (show H ⊆ {x | S.ρ x = k.val} from
        inter_subset_right) le_rfl) (S.ae_reverseDiffuseSupply_on_fiber k)
    obtain ⟨x, hxH, hxδ⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hkpos.ne' hδae
    have hxE : x ∈ E := hxH.1
    exact hxδ ▸ hEδ x hxE
  let L : Set Ω := {y | y ∈ S.D ∩ S.L ∧ k.val y = 0 ∧ k.val ≠ S.ρ y}
  have hL : MeasurableSet L := by
    let : MeasurableSpace (Lp ℝ 2 μ) := borel _
    let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
    have hrow := (Lp.stronglyMeasurable k.val).measurable
    have hρ := S.hρ.measurable
    have hneq : MeasurableSet {y | k.val ≠ S.ρ y} := by
      have heq : MeasurableSet {y | S.ρ y = k.val} :=
        hρ (measurableSet_singleton k.val)
      have hset : {y | k.val ≠ S.ρ y} = {y | S.ρ y = k.val}ᶜ := by
        ext y
        simp [eq_comm]
      rw [hset]
      exact heq.compl
    exact (S.hD.inter S.hpartition.2.1).inter
      ((measurableSet_eq_fun hrow measurable_const).inter hneq)
  have hLpos : 0 < μ L := by
    by_contra hn
    have hz : μ L = 0 := le_antisymm (le_of_not_gt hn) bot_le
    change 0 < (μ L).toReal at hδk
    rw [hz, ENNReal.toReal_zero] at hδk
    exact (lt_irrefl 0) hδk
  have hLsub : L ⊆ S.D ∩ S.L := fun _ hx => hx.1
  have hLmissing : L ⊆ KernelOperator.wholeFiberMissingSet S.ρ k.val := by
    intro y hy
    exact ⟨hy.2.2.symm, hy.2.1.le⟩
  have hzero : ∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L),
      shiftedKernel W m p.1 p.2 = 0 := by
    have hz := KernelOperator.ae_zero_fiber_prod_missingSet
      (shiftedKernel W m) S.ρ S.hρ k.val
      ((S.hfibers k.val k.property).2.2.2.rows.mono (fun _ hx => hx.1))
      (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hp => hp.1))
    exact ae_mono (Measure.prod_mono
      (Measure.restrict_mono (show H ⊆ {x | S.ρ x = k.val} from inter_subset_right) le_rfl)
      (Measure.restrict_mono hLmissing le_rfl)) hz
  refine ⟨H, L, hH, hL, hkpos, inter_subset_left, hLpos, hLsub, hzero, ?_⟩
  apply degree_average_gt_of_zero_rectangle H L hH hL hkpos hLpos hHhigh
  · intro p hpH hpL he
    exact (hLmissing hpL).1 (he.symm.trans hpH.2)
  · exact hzero

/-- A positive original HIGH region private to one saturated head but outside
its entire compulsory source has an actual additional LOW missing rectangle.
The strict original degree comparison is derived from the selected zero-pair
orientation, with no supplied rectangle or degree witness. -/
theorem IsSaturatedAtomPair.exists_low_extra_hole_witness
    [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
    {r u : S.I} (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (E : Set Ω) (hE : MeasurableSet E) (hEpos : 0 < μ E)
    (hEH : E ⊆ S.H)
    (hEr : E ⊆ KernelOperator.wholeFiberMissingSet S.ρ r.val)
    (hEnu : E ⊆ (KernelOperator.wholeFiberMissingSet S.ρ u.val)ᶜ)
    (hEnSA : E ⊆ (S.reverseCompulsorySource {r})ᶜ)
    (_hEnheads : E ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val})ᶜ) :
    ∃ (H L : Set Ω) (hH : MeasurableSet H) (hL : MeasurableSet L),
      0 < μ H ∧ H ⊆ E ∧ 0 < μ L ∧ L ⊆ S.L ∧
      L ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val})ᶜ ∧
      (∀ᵐ p ∂(μ.restrict H).prod (μ.restrict L),
        shiftedKernel W m p.1 p.2 = 0) ∧
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 L hL⟫ <
        ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
          KernelOperator.normalizedSetL2 H hH⟫ := by
  let Eplus := E ∩ {x | 0 < S.reverseDiffuseSupply x}
  have hEplus : MeasurableSet Eplus :=
    hE.inter (measurableSet_lt measurable_const S.measurable_reverseDiffuseSupply)
  by_cases hplus : 0 < μ Eplus
  · obtain ⟨H, L, hH, hL, hHpos, hHEplus, hLpos, hLD, hzero, hdegree⟩ :=
      S.exists_low_witness_of_diffuse_supply hW hd hgap Eplus hEplus hplus
        (fun x hx => hEH hx.1) (fun x hx => hx.2)
    refine ⟨H, L, hH, hL, hHpos, (fun x hx => (hHEplus hx).1), hLpos,
      (fun x hx => (hLD hx).2), ?_, hzero, hdegree⟩
    intro x hx hhead
    have hxD := (hLD hx).1
    rcases hhead with hr | hu
    · exact S.row_ne_atom_of_mem_diffuse x hxD r hr
    · exact S.row_ne_atom_of_mem_diffuse x hxD u hu
  · have hnull : μ Eplus = 0 := le_antisymm (le_of_not_gt hplus) bot_le
    let Ezero := E ∩ {x | S.reverseDiffuseSupply x = 0}
    have hEzero : MeasurableSet Ezero :=
      hE.inter (measurableSet_eq_fun S.measurable_reverseDiffuseSupply measurable_const)
    have hzeroAE : ∀ᵐ x ∂μ.restrict E, S.reverseDiffuseSupply x = 0 := by
      have hnullAE : ∀ᵐ x ∂μ, x ∉ Eplus :=
        (measure_eq_zero_iff_ae_notMem).mp hnull
      apply (ae_restrict_iff' hE).mpr
      filter_upwards [hnullAE] with x hx hxE
      have hnot : ¬0 < S.reverseDiffuseSupply x := by
        intro hp
        exact hx ⟨hxE, hp⟩
      exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    have hEzeropos : 0 < μ Ezero := by
      have heq : μ Ezero = μ E := by
        have ht := Measure.measure_inter_eq_of_ae (s := univ) hzeroAE
        change (μ.restrict E) ({x | S.reverseDiffuseSupply x = 0} ∩ univ) =
          (μ.restrict E) univ at ht
        rw [Set.inter_univ, Measure.restrict_apply
          (measurableSet_eq_fun S.measurable_reverseDiffuseSupply measurable_const),
          Measure.restrict_apply_univ] at ht
        simpa [Ezero, Set.inter_comm] using ht
      rw [heq]
      exact hEpos
    have hrEligible : r ∈ S.eligibleReverseAtom :=
      hpair.head_eligibleReverseAtom hW hd hgap hell
    let _ : Countable S.I := S.hI.to_subtype
    let T (v : S.I) : Set Ω :=
      if v ∈ S.eligibleReverseAtom ∧ v ≠ r ∧ v ≠ u then
        KernelOperator.wholeFiberMissingSet S.ρ v.val else ∅
    have hcover : ∀ᵐ x ∂μ, x ∈ Ezero → ∃ v : S.I, x ∈ T v :=
      Eventually.of_forall (fun x hx => by
        obtain ⟨v, hv, hvr, hvu, hxv⟩ := S.exists_extra_eligible_hole
          hrEligible x (hEH hx.1) hx.2 (hEr hx.1)
          (hEnu hx.1) (hEnSA hx.1)
        exact ⟨v, by simpa [T, hv, hvr, hvu] using hxv⟩)
    obtain ⟨v, hvpos⟩ := exists_positive_cell_of_ae_cover Ezero T hEzeropos hcover
    have hv : v ∈ S.eligibleReverseAtom ∧ v ≠ r ∧ v ≠ u := by
      by_contra hn
      have hT : T v = ∅ := by simp [T, hn]
      rw [hT, Set.inter_empty, measure_empty] at hvpos
      exact (lt_irrefl 0) hvpos
    let H := Ezero ∩ T v
    have hT : T v = KernelOperator.wholeFiberMissingSet S.ρ v.val := by
      simp [T, hv]
    have hH : MeasurableSet H := by
      rw [show H = Ezero ∩ KernelOperator.wholeFiberMissingSet S.ρ v.val from by
        simp [H, hT]]
      exact hEzero.inter (KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ v.val)
    have hHhigh : H ⊆ S.H := fun x hx => hEH hx.1.1
    have hHmissing : H ⊆ KernelOperator.wholeFiberMissingSet S.ρ v.val := by
      intro x hx
      exact hT ▸ hx.2
    obtain ⟨L, hL, hLpos, hLlow, hLfiber, hzero, hdegree⟩ :=
      S.exists_low_witness_of_atom_hole hW H hH hvpos hHhigh v hHmissing
    refine ⟨H, L, hH, hL, hvpos, (fun x hx => hx.1.1), hLpos, hLlow,
      ?_, hzero, hdegree⟩
    intro x hx hhead
    have hxv := hLfiber hx
    rcases hhead with hr | hu
    · exact hv.2.1 (Subtype.ext (hxv.symm.trans hr))
    · exact hv.2.2 (Subtype.ext (hxv.symm.trans hu))

end Erdos1017.CappedModel.SelectedHighLowStructure

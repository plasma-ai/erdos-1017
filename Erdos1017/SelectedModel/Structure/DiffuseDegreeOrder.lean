module

public import Erdos1017.SelectedModel.Structure.WholeFiberMissingGeometry
public import Erdos1017.SelectedModel.Structure.GeneralDegreeStraddle
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages
public import Erdos1017.SelectedModel.Structure.WholeRowDegreeSeparation

/-!
# No diffuse degree straddle between whole rows

A positive set missing two distinct whole shifted rows cannot have original
degree strictly between their whole-fiber degrees, so after removing the
countably many whole fibers, almost every remaining point misses no two whole
fibers whose degrees straddle its own.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Two whole fibers with a common positive missing set occupy the same
side of the actual zero-pair cut, so their cross kernel is positive. -/
private theorem positive_cross_of_common_missing
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R)
    (r u : Lp ℝ 2 μ) (hru : r ≠ u)
    (hrpos : 0 < μ {x | R x = r}) (hupos : 0 < μ {x | R x = u})
    (hrrows : ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ))
    (hurows : ∀ᵐ x ∂μ.restrict {x | R x = u}, K x =ᵐ[μ] (u : Ω → ℝ))
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (B : Set Ω)
    (hcut : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → R p.1 ≠ R p.2 →
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B))
    (S : Set Ω) (hSpos : 0 < μ S)
    (hSr : S ⊆ wholeFiberMissingSet R r)
    (hSu : S ⊆ wholeFiberMissingSet R u) :
    ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
      0 < K p.1 p.2 := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hrmeas : MeasurableSet {x | R x = r} := hR.measurable (measurableSet_singleton r)
  have humeas : MeasurableSet {x | R x = u} := hR.measurable (measurableSet_singleton u)
  have hNrpos : 0 < μ (wholeFiberMissingSet R r) :=
    lt_of_lt_of_le hSpos (measure_mono hSr)
  have hNupos : 0 < μ (wholeFiberMissingSet R u) :=
    lt_of_lt_of_le hSpos (measure_mono hSu)
  have hrside := opposite_cut_sides_of_positive_missingSet K R hR r hrpos hNrpos
    hrrows hK hK0 B hcut
  have huside := opposite_cut_sides_of_positive_missingSet K R hR u hupos hNupos
    hurows hK hK0 B hcut
  have hsame :
      ((∀ᵐ x ∂μ.restrict {x | R x = r}, x ∈ B) ∧
        (∀ᵐ x ∂μ.restrict {x | R x = u}, x ∈ B)) ∨
      ((∀ᵐ x ∂μ.restrict {x | R x = r}, x ∉ B) ∧
        (∀ᵐ x ∂μ.restrict {x | R x = u}, x ∉ B)) := by
    rcases hrside with ⟨hrB, hNrnotB⟩ | ⟨hrnotB, hNrB⟩ <;>
      rcases huside with ⟨huB, hNunotB⟩ | ⟨hunotB, hNuB⟩
    · exact Or.inl ⟨hrB, huB⟩
    · have hSnotB : ∀ᵐ x ∂μ.restrict S, x ∉ B :=
        ae_mono (μ.restrict_mono_set hSr) hNrnotB
      have hSB : ∀ᵐ x ∂μ.restrict S, x ∈ B :=
        ae_mono (μ.restrict_mono_set hSu) hNuB
      obtain ⟨x, _, hx, hy⟩ :=
        Measure.exists_mem_of_measure_ne_zero_of_ae hSpos.ne' (hSnotB.and hSB)
      exact (hx hy).elim
    · have hSB : ∀ᵐ x ∂μ.restrict S, x ∈ B :=
        ae_mono (μ.restrict_mono_set hSr) hNrB
      have hSnotB : ∀ᵐ x ∂μ.restrict S, x ∉ B :=
        ae_mono (μ.restrict_mono_set hSu) hNunotB
      obtain ⟨x, _, hx, hy⟩ :=
        Measure.exists_mem_of_measure_ne_zero_of_ae hSpos.ne' (hSB.and hSnotB)
      exact (hy hx).elim
    · exact Or.inr ⟨hrnotB, hunotB⟩
  have hle : (μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hcut' : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
      K p.1 p.2 = 0 → R p.1 ≠ R p.2 →
        (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B) := ae_mono hle hcut
  have hK0' : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
      0 ≤ K p.1 p.2 := ae_mono hle hK0
  have hrmem : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
      R p.1 = r :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hrmeas)
  have humem : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
      R p.2 = u :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem humeas)
  rcases hsame with ⟨hrB, huB⟩ | ⟨hrnotB, hunotB⟩
  · filter_upwards [hcut', hK0', hrmem, humem,
      Measure.quasiMeasurePreserving_fst.ae hrB,
      Measure.quasiMeasurePreserving_snd.ae huB] with p hc hk hx hy hb hcB
    have hne : R p.1 ≠ R p.2 := by rw [hx, hy]; exact hru
    have hnz : K p.1 p.2 ≠ 0 := by
      intro hz
      exact (hc hz hne).elim (fun h => h.2 hcB) (fun h => h.2 hb)
    exact lt_of_le_of_ne hk hnz.symm
  · filter_upwards [hcut', hK0', hrmem, humem,
      Measure.quasiMeasurePreserving_fst.ae hrnotB,
      Measure.quasiMeasurePreserving_snd.ae hunotB] with p hc hk hx hy hb hcB
    have hne : R p.1 ≠ R p.2 := by rw [hx, hy]; exact hru
    have hnz : K p.1 p.2 ≠ 0 := by
      intro hz
      exact (hc hz hne).elim (fun h => hb h.1) (fun h => hcB h.1)
    exact lt_of_le_of_ne hk hnz.symm

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A positive set missing two distinct whole shifted rows cannot have
original degree strictly between their whole-fiber degrees. The cross
rectangles come from the actual rows and common zero-pair cut. -/
theorem FullStationaryClass.no_diffuse_degree_straddle_between_whole_rows
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (B : Set Ω)
    (hcut : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → R p.1 ≠ R p.2 →
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B))
    (r u : Lp ℝ 2 μ) (hru : r ≠ u)
    (hrpos : 0 < μ {x | R x = r}) (hupos : 0 < μ {x | R x = u})
    (hr : KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) 4 m R r)
    (hu : KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) 4 m R u)
    (S : Set Ω) (hS : MeasurableSet S) (hSpos : 0 < μ S)
    (hSr : S ⊆ KernelOperator.wholeFiberMissingSet R r)
    (hSu : S ⊆ KernelOperator.wholeFiberMissingSet R u)
    (hdegree : ∀ᵐ x ∂μ.restrict S,
      wholeRowDegree r < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x ∧
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x < wholeRowDegree u) :
    False := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hrmeas : MeasurableSet {x | R x = r} := hR.measurable (measurableSet_singleton r)
  have humeas : MeasurableSet {x | R x = u} := hR.measurable (measurableSet_singleton u)
  have hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedKernel W m p.1 p.2 :=
    hW.moment_mem.mono (fun _ hp => hp.1)
  have hrzero : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict S),
      shiftedKernel W m p.1 p.2 = 0 :=
    ae_mono (Measure.prod_mono le_rfl (μ.restrict_mono_set hSr))
      (KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m) R hR r
        (hr.rows.mono (fun _ h => h.1)) (shiftedKernel_measurable W m) hK0)
  have huzero : ∀ᵐ p ∂(μ.restrict {x | R x = u}).prod (μ.restrict S),
      shiftedKernel W m p.1 p.2 = 0 :=
    ae_mono (Measure.prod_mono le_rfl (μ.restrict_mono_set hSu))
      (KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m) R hR u
        (hu.rows.mono (fun _ h => h.1)) (shiftedKernel_measurable W m) hK0)
  have hSrz := (Measure.measurePreserving_swap (μ := μ.restrict S)
    (ν := μ.restrict {x | R x = r})).quasiMeasurePreserving.ae hrzero
  have hSuz := (Measure.measurePreserving_swap (μ := μ.restrict S)
    (ν := μ.restrict {x | R x = u})).quasiMeasurePreserving.ae huzero
  have hSrzero : ∀ᵐ p ∂(μ.restrict S).prod (μ.restrict {x | R x = r}),
      shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hSrz, ae_mono (Measure.prod_mono Measure.restrict_le_self
      Measure.restrict_le_self) (shiftedMoment_symm W m)] with p hp hs
    exact hs.symm.trans hp
  have hSuzero : ∀ᵐ p ∂(μ.restrict S).prod (μ.restrict {x | R x = u}),
      shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hSuz, ae_mono (Measure.prod_mono Measure.restrict_le_self
      Measure.restrict_le_self) (shiftedMoment_symm W m)] with p hp hs
    exact hs.symm.trans hp
  have hruPos := KernelOperator.positive_cross_of_common_missing
    (shiftedKernel W m) R hR r u hru hrpos hupos
    (hr.rows.mono (fun _ h => h.1)) (hu.rows.mono (fun _ h => h.1))
    (shiftedKernel_measurable W m) hK0 B hcut S hSpos hSr hSu
  have hrdegree := wholeRowFiber_degree W m R r hr
  have hudegree := wholeRowFiber_degree W m R u hu
  have hravg := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq
    {x | R x = r} hrmeas hrpos g (wholeRowDegree r) hrdegree
  have huavg := KernelOperator.normalizedSetL2_inner_eq_of_ae_eq
    {x | R x = u} humeas hupos g (wholeRowDegree u) hudegree
  have hSabove := KernelOperator.normalizedSetL2_inner_gt_of_ae_gt
    S hS hSpos g (wholeRowDegree r) (hdegree.mono (fun _ h => h.1))
  have hSbelow := KernelOperator.normalizedSetL2_inner_lt_of_ae_lt
    S hS hSpos g (wholeRowDegree u) (hdegree.mono (fun _ h => h.2))
  exact (hW.not_degree_straddle_sets_nonnegative_base hd hgap
    S {x | R x = r} {x | R x = u} hS hrmeas humeas hSpos hrpos hupos
    hSrzero hSuzero hruPos)
    ⟨hravg.trans_lt hSabove, hSbelow.trans_eq huavg.symm⟩

/-- After removing the countably many whole fibers, almost every remaining
point cannot miss two whole fibers whose original degrees straddle its own. -/
theorem FullStationaryClass.ae_diffuse_no_degree_straddle
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (B : Set Ω)
    (hcut : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → R p.1 ≠ R p.2 →
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B))
    (I : Set (Lp ℝ 2 μ)) (hI : I.Countable)
    (hfibers : ∀ r ∈ I,
      0 < μ {x | R x = r} ∧
        KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
          (adjacencyKernel W) (chargeKernel W) 4 m R r)
    (D : Set Ω) (hD : MeasurableSet D)
    (hDeq : D = (⋃ r ∈ I, {x | R x = r})ᶜ) :
    ∀ᵐ x ∂μ.restrict D, ¬∃ r ∈ I, ∃ u ∈ I,
      r ≠ u ∧ r x ≤ 0 ∧ u x ≤ 0 ∧
        wholeRowDegree r < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x ∧
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x < wholeRowDegree u := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  let : Countable I := hI.to_subtype
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hgmeas : Measurable (fun x => g x) := (Lp.stronglyMeasurable g).measurable
  have hDnot (x : Ω) (hx : x ∈ D) (r : Lp ℝ 2 μ) (hr : r ∈ I) : R x ≠ r := by
    rw [hDeq] at hx
    intro heq
    exact hx (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, heq⟩⟩)
  have hpair (r u : I) : ∀ᵐ x ∂μ.restrict D,
      ¬(r.val ≠ u.val ∧ r.val x ≤ 0 ∧ u.val x ≤ 0 ∧
        wholeRowDegree r.val < g x ∧ g x < wholeRowDegree u.val) := by
    by_cases hru : r.val ≠ u.val
    · let S : Set Ω := {x | x ∈ D ∧ r.val x ≤ 0 ∧ u.val x ≤ 0 ∧
        wholeRowDegree r.val < g x ∧ g x < wholeRowDegree u.val}
      have hrmeas : Measurable (fun x => (r.val : Ω → ℝ) x) :=
        (Lp.stronglyMeasurable r.val).measurable
      have humeas : Measurable (fun x => (u.val : Ω → ℝ) x) :=
        (Lp.stronglyMeasurable u.val).measurable
      have hS : MeasurableSet S := by
        dsimp only [S]
        exact hD.inter ((measurableSet_le hrmeas measurable_const).inter
          ((measurableSet_le humeas measurable_const).inter
            ((measurableSet_lt measurable_const hgmeas).inter
              (measurableSet_lt hgmeas measurable_const))))
      have hSzero : μ S = 0 := by
        by_contra hnz
        have hSpos : 0 < μ S := pos_iff_ne_zero.mpr hnz
        obtain ⟨hrpos, hrdata⟩ := hfibers r.val r.property
        obtain ⟨hupos, hudata⟩ := hfibers u.val u.property
        have hSr : S ⊆ KernelOperator.wholeFiberMissingSet R r.val := by
          intro x hx
          change x ∈ D ∧ r.val x ≤ 0 ∧ u.val x ≤ 0 ∧
            wholeRowDegree r.val < g x ∧ g x < wholeRowDegree u.val at hx
          exact ⟨hDnot x hx.1 r.val r.property, hx.2.1⟩
        have hSu : S ⊆ KernelOperator.wholeFiberMissingSet R u.val := by
          intro x hx
          change x ∈ D ∧ r.val x ≤ 0 ∧ u.val x ≤ 0 ∧
            wholeRowDegree r.val < g x ∧ g x < wholeRowDegree u.val at hx
          exact ⟨hDnot x hx.1 u.val u.property, hx.2.2.1⟩
        have hdegree : ∀ᵐ x ∂μ.restrict S,
            wholeRowDegree r.val < g x ∧ g x < wholeRowDegree u.val :=
          ae_restrict_of_forall_mem hS (fun x hx => by
            change x ∈ D ∧ r.val x ≤ 0 ∧ u.val x ≤ 0 ∧
              wholeRowDegree r.val < g x ∧ g x < wholeRowDegree u.val at hx
            exact hx.2.2.2)
        exact hW.no_diffuse_degree_straddle_between_whole_rows hd hgap R hR B hcut
          r.val u.val hru hrpos hupos hrdata hudata S hS hSpos hSr hSu hdegree
      have hnotS : ∀ᵐ x ∂μ.restrict D, x ∉ S :=
        ae_restrict_of_ae (compl_mem_ae_iff.mpr hSzero)
      filter_upwards [ae_restrict_mem hD, hnotS] with x hxD hxS hx
      rcases hx with ⟨_, hrx, hux, hlo, hhi⟩
      exact hxS ⟨hxD, hrx, hux, hlo, hhi⟩
    · exact Filter.Eventually.of_forall (fun _ hx => hru hx.1)
  have hall : ∀ᵐ x ∂μ.restrict D, ∀ r u : I,
      ¬(r.val ≠ u.val ∧ r.val x ≤ 0 ∧ u.val x ≤ 0 ∧
        wholeRowDegree r.val < g x ∧ g x < wholeRowDegree u.val) :=
    ae_all_iff.mpr (fun r => ae_all_iff.mpr (fun u => hpair r u))
  filter_upwards [hall] with x hx hbad
  obtain ⟨r, hr, u, hu, hru, hrx, hux, hlo, hhi⟩ := hbad
  exact hx ⟨r, hr⟩ ⟨u, hu⟩ ⟨hru, hrx, hux, hlo, hhi⟩

end Erdos1017.CappedModel

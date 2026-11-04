module

public import Erdos1017.SelectedModel.Structure.SelectedHighLowClassification
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative

/-!
# Root neighborhood and averaged charge row

The neighborhood `rootNeighborhood` of a whole independent atom and the bounded
averaged charge row `rootChargeRow` are defined; the shifted row vanishes on the
atom's own fiber, and the averaged row equals the whole charge row on almost
every root pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The original neighborhood of one whole independent atom, with its own
fiber removed pointwise. -/
def rootNeighborhood (S : SelectedHighLowStructure W m) (r : S.I) : Set Ω :=
  {x | S.ρ x ≠ r.val ∧ 0 < r.val x}

/-- Average the actual bounded physical charge against the original root
law. The row is bounded everywhere, including exceptional points. -/
def rootChargeRow (S : SelectedHighLowStructure W m) (r : S.I) (y : Ω) : ℝ :=
  ∫ x, PhysicalRepresentative.charge W m x y
    ∂ProbabilityTheory.cond μ {x | S.ρ x = r.val}

theorem measurableSet_rootNeighborhood (S : SelectedHighLowStructure W m) (r : S.I) :
    MeasurableSet (S.rootNeighborhood r) :=
  (S.hfibers r.val r.property).1.compl.inter
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable r.val).measurable)

theorem rootNeighborhood_disjoint (S : SelectedHighLowStructure W m) (r : S.I) :
    Disjoint {x | S.ρ x = r.val} (S.rootNeighborhood r) :=
  Set.disjoint_left.mpr (fun _ hx hy => hy.1 hx)

private theorem ae_pair_of_restricted_rows (I : Set Ω) (hI : MeasurableSet I)
    (F : Ω → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (f : Ω → ℝ) (hf : Measurable f)
    (hrows : ∀ᵐ x ∂μ.restrict I, F x =ᵐ[μ] f) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → F p.1 p.2 = f p.2 := by
  have hset : MeasurableSet {p : Ω × Ω | p.1 ∈ I → F p.1 p.2 = f p.2} := by
    have hs := (hI.preimage measurable_fst).compl.union
      (measurableSet_eq_fun hF (hf.comp measurable_snd))
    convert hs using 1
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
    tauto
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  filter_upwards [(ae_restrict_iff' hI).mp hrows] with x hx
  by_cases hi : x ∈ I
  · exact (hx hi).mono (fun _ hy _ => hy)
  · exact Eventually.of_forall (fun _ h => False.elim (hi h))

theorem measurable_rootChargeRow (S : SelectedHighLowStructure W m) (r : S.I) :
    Measurable (S.rootChargeRow r) :=
  (PhysicalRepresentative.measurable_charge W m).stronglyMeasurable.integral_prod_left'.measurable

theorem rootChargeRow_mem_Icc (S : SelectedHighLowStructure W m) (r : S.I) (y : Ω) :
    S.rootChargeRow r y ∈ Icc (-3 : ℝ) 1 := by
  have hpos := (S.hfibers r.val r.property).2.1
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ {x | S.ρ x = r.val}) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos.ne'
  have hi : Integrable (fun x => PhysicalRepresentative.charge W m x y)
      (ProbabilityTheory.cond μ {x | S.ρ x = r.val}) :=
    Integrable.of_bound
      ((PhysicalRepresentative.measurable_charge W m).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable 3
      (Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
  constructor
  · simpa [rootChargeRow] using integral_mono_ae (integrable_const (-3 : ℝ)) hi
      (Eventually.of_forall (fun x => (PhysicalRepresentative.charge_mem_Icc W m x y).1))
  · simpa [rootChargeRow] using integral_mono_ae hi (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun x => (PhysicalRepresentative.charge_mem_Icc W m x y).2))

/-- Independence forces the actual whole shifted row to vanish on its own
original fiber. No value on a chosen representative point is assumed. -/
theorem root_row_zero_on_fiber (S : SelectedHighLowStructure W m) (r : S.I) :
    (r.val : Ω → ℝ) =ᵐ[μ.restrict {x | S.ρ x = r.val}] fun _ => 0 := by
  obtain ⟨q, _, hrq, _, hzero, _⟩ := (S.hfibers r.val r.property).2.2.2.internal
  have hq : q = 0 := hzero.mp (S.hfibers r.val r.property).2.2.1
  simpa only [hq] using hrq

theorem ae_rootNeighborhood_iff (S : SelectedHighLowStructure W m) (r : S.I) :
    ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood r ↔ 0 < r.val x := by
  filter_upwards [(ae_restrict_iff' (S.hfibers r.val r.property).1).mp
    (S.root_row_zero_on_fiber r)] with x hx
  by_cases hxr : S.ρ x = r.val
  · simp [rootNeighborhood, hxr, hx hxr]
  · simp [rootNeighborhood, hxr]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The literal original root neighborhood agrees with the actual bounded
physical graph row, with only one common product-null exception. -/
theorem ae_root_adjacency (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ p.2 ∈ S.rootNeighborhood r) := by
  let a : Ω → ℝ := fun x => if 0 < r.val x then 1 else 0
  have ha : Measurable a := Measurable.ite
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable r.val).measurable)
    measurable_const measurable_const
  have hrows : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, adjacencyKernel W x =ᵐ[μ] a :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.1)
  have hmeas : Measurable (Function.uncurry (adjacencyKernel W)) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable
  have hp := ae_pair_of_restricted_rows _ (S.hfibers r.val r.property).1
    (adjacencyKernel W) hmeas a ha hrows
  have hs := hW.strict_gap_structure hd hgap
  filter_upwards [hp, PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
    Measure.quasiMeasurePreserving_snd.ae (S.ae_rootNeighborhood_iff r)] with p hp hg hn hi
  have heq := (hg.symm.trans (hp hi))
  change (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then (1 : ℝ) else 0) =
    (if 0 < r.val p.2 then 1 else 0) at heq
  have hb : PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ 0 < r.val p.2 := by
    cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
      by_cases hr : 0 < r.val p.2 <;> simp_all
  exact hb.trans hn.symm

/-- The globally bounded averaged row equals the original whole charge row
on almost every root pair. This derives the row used by signed repricing. -/
theorem ae_root_charge (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      PhysicalRepresentative.charge W m p.1 p.2 = S.rootChargeRow r p.2 := by
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  let a : Ω → ℝ := fun x => if 0 < r.val x then 1 else 0
  let f : Ω → ℝ := fun x => r.val x + m * a x
  have ha : Measurable a := Measurable.ite
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable r.val).measurable)
    measurable_const measurable_const
  have hf : Measurable f := (Lp.stronglyMeasurable r.val).measurable.add
    (measurable_const.mul ha)
  have hrows : ∀ᵐ x ∂μ.restrict I, chargeKernel W x =ᵐ[μ] f :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hmeas : Measurable (Function.uncurry (chargeKernel W)) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_charge.measurable.stronglyMeasurable).measurable
  have hp := ae_pair_of_restricted_rows I hI (chargeKernel W) hmeas f hf hrows
  have hs := hW.strict_gap_structure hd hgap
  have hphysical : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I →
      PhysicalRepresentative.charge W m p.1 p.2 = f p.2 := by
    filter_upwards [hp, PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hp hy hi
    exact hy.trans (hp hi)
  have hrestricted : ∀ᵐ p ∂(μ.restrict I).prod μ,
      PhysicalRepresentative.charge W m p.1 p.2 = f p.2 := by
    filter_upwards [(ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)) hphysical,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI)] with p hp hi
    exact hp hi
  let σ := ProbabilityTheory.cond μ I
  have : IsProbabilityMeasure σ :=
    ProbabilityTheory.cond_isProbabilityMeasure (S.hfibers r.val r.property).2.1.ne'
  have hσ : σ ≪ μ.restrict I := Measure.smul_absolutelyContinuous
  have hconditioned : ∀ᵐ p ∂σ.prod μ,
      PhysicalRepresentative.charge W m p.1 p.2 = f p.2 :=
    (hσ.prod Measure.AbsolutelyContinuous.rfl).ae_le hrestricted
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := σ)).quasiMeasurePreserving.ae
    hconditioned
  have hmean : ∀ᵐ y ∂μ, S.rootChargeRow r y = f y := by
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
    change ∀ᵐ x ∂σ, PhysicalRepresentative.charge W m x y = f y at hy
    change (∫ x, PhysicalRepresentative.charge W m x y ∂σ) = f y
    rw [integral_congr_ae hy]
    simp
  filter_upwards [hphysical, Measure.quasiMeasurePreserving_snd.ae hmean] with p hp hy hi
  exact (hp hi).trans hy.symm

end Erdos1017.CappedModel.SelectedHighLowStructure

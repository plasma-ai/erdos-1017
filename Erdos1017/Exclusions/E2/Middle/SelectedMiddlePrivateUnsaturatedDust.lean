module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateUnsaturatedStock
public import Erdos1017.Exclusions.E2.Middle.MiddlePrivateUnsaturatedScalar
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2PrivateSector
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedPeak
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality

/-!
# No positive dust in the private source

The exact first-root count `A(1-A-b)` with multiplicity `n-1` at order `n`, the
same-law sum for the first-root excess, and the averaged first-root star bound
combine to show that a positive part of the private source's dust is impossible
on the middle no-saturation branch (`no_middle_private_source_dust`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  {i p : S.I} {c d : ℝ}

namespace PrivatePhysicalPrimal

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The exact first-root count: the leaves of the first-root parents
are `A(1-A-b)`, counted with multiplicity `n-1` at order `n`. -/
theorem first_root_count (P : S.PrivatePhysicalPrimal i p c) :
    μ.real {x | S.ρ x = i.val} * (1 - μ.real {x | S.ρ x = i.val} -
      μ.real {x | S.ρ x = p.val}) =
      ∑ n ∈ Finset.range (P.orderCap + 1),
        ((n : ℝ) - 1) * (P.laws n).real (firstRootEvent S i n) := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  have hIm : MeasurableSet I := (S.hfibers i.val i.property).1
  have hPm : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hdis : Disjoint I Pset := disjoint_left.mpr (fun _ hx hy =>
    P.distinct_roots (Subtype.ext (hx.symm.trans hy)))
  have hK : Integrable (fun z : Ω × Ω => if z.1 ∈ I then (1 : ℝ) else 0)
      (PhysicalPrimal.occupation P.laws) := by
    have hKi : Integrable (fun z : Ω × Ω => if z.1 ∈ I then (1 : ℝ) else 0) (μ.prod μ) :=
      Integrable.of_bound (Measurable.ite (hIm.preimage measurable_fst) measurable_const
        measurable_const).aestronglyMeasurable 1
        (Eventually.of_forall (fun z => by split_ifs <;> simp))
    rw [P.feasible.2.2.2]
    exact hKi.mono_measure Measure.restrict_le_self
  have hstock := PhysicalPrimal.integral_rootLeaves_eq_sum_of_cap P.orderCap P.laws
    (fun n hn => P.capped n (Or.inr hn)) I hIm (fun _ => (1 : ℝ)) measurable_const
    (by convert hK)
  rw [P.leaves_first, integral_smul_measure, integral_const, smul_eq_mul, smul_eq_mul,
    mul_one, measureReal_restrict_apply_univ] at hstock
  have hJ : μ.real ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ =
      1 - μ.real I - μ.real Pset := by
    rw [measureReal_compl (hIm.union hPm), probReal_univ, measureReal_union hdis hPm]
    ring
  have horder (n : ℕ) : (∫ v, (PhysicalPrimal.tupleCount I v : ℝ) * (∑ _j : Fin n, (1 : ℝ)) -
      (∑ j, if v j ∈ I then (1 : ℝ) else 0) ∂P.laws n) =
      ((n : ℝ) - 1) * (P.laws n).real (firstRootEvent S i n) := by
    have hEm := measurableSet_firstRootEvent S i n
    have heq : (fun v : Fin n → Ω => (PhysicalPrimal.tupleCount I v : ℝ) *
        (∑ _j : Fin n, (1 : ℝ)) - (∑ j, if v j ∈ I then (1 : ℝ) else 0)) =ᵐ[P.laws n]
        (firstRootEvent S i n).indicator (fun _ => ((n : ℝ) - 1)) := by
      filter_upwards [ae_tupleCount_eq_indicator P n] with v hv
      have hsum : (∑ j, if v j ∈ I then (1 : ℝ) else 0) =
          (PhysicalPrimal.tupleCount I v : ℝ) := by
        rw [PhysicalPrimal.tupleCount, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      rw [hsum, hv]
      by_cases hE : v ∈ firstRootEvent S i n
      · simp only [indicator_of_mem hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, one_mul]
      · simp only [indicator_of_notMem hE, zero_mul, sub_zero]
    rw [integral_congr_ae heq, integral_indicator hEm, setIntegral_const, smul_eq_mul,
      mul_comm]
  calc
    μ.real {x | S.ρ x = i.val} * (1 - μ.real {x | S.ρ x = i.val} -
        μ.real {x | S.ρ x = p.val}) =
        (μ {x | S.ρ x = i.val}).toReal *
          μ.real ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ := by
      rw [hJ]
      rfl
    _ = _ := hstock
    _ = _ := Finset.sum_congr rfl (fun n _ => by
      rw [← horder n]
      exact integral_congr_ae (Eventually.of_forall (fun v => by
        dsimp only
        congr 1
        exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> rfl))))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The first-root excess is the finite same-law sum. -/
theorem rootExcess_eq_sum (P : S.PrivatePhysicalPrimal i p c) :
    P.rootExcess = ∑ n ∈ Finset.range (P.orderCap + 1),
      ((n : ℝ) - 3) * (P.laws n).real (firstRootEvent S i n) := by
  rw [rootExcess, tsum_eq_sum (s := Finset.range (P.orderCap + 1))]
  · rfl
  · intro n hn
    have hz : P.laws n = 0 :=
      P.capped n (Or.inr (by simpa [Finset.mem_range, not_lt] using hn))
    simp [hz]

end PrivatePhysicalPrimal

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Every compulsory-source vertex joins every vertex outside its own
fiber and the recovered head. -/
theorem ReverseRecovery.ae_source_join (R : S.ReverseRecovery) (p : S.I)
    (hW : FullStationaryClass d c W m) (hp : R.plateau = {p}) :
    ∀ᵐ z ∂μ.prod μ, z.1 ∈ S.reverseCompulsorySource {p} →
      S.ρ z.2 ≠ S.ρ z.1 → S.ρ z.2 ≠ p.val → adjacencyKernel W z.1 z.2 = 1 := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  filter_upwards [hW.moment_mem, hW.complementary, S.hcoverage, S.hrelation,
    hswap.ae (R.ae_reverse_pair_to_singleton_source p hW hp),
    actualZeroRelation_symm W m S.ρ] with z hm hc hcover hrel hraw hZsym hC hne hnp
  have hpos : 0 < shiftedKernel W m z.1 z.2 := by
    apply lt_of_le_of_ne hm.1
    intro he
    rcases hcover he.symm with ⟨q, _, hxq, hyq⟩ | hZ
    · exact hne (hyq.trans hxq.symm)
    · rcases hrel hZ with h | h
      · have hR : (z.2, z.1) ∈ S.reverseAssignmentRelation := ⟨hZsym.mp hZ, h.2.2⟩
        exact hnp (hraw hC hR)
      · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hC.1 h.2.1
  have hz := (mul_eq_zero.mp hc).resolve_right (ne_of_gt hpos)
  change 1 - adjacencyKernel W z.1 z.2 = 0 at hz
  linarith only [hz]

/-- The averaged first-root star is at least the multiplier almost everywhere. -/
theorem ae_rootChargeRow_ge (S : SelectedHighLowStructure W m) (r : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hm : m ≤ 0) :
    ∀ᵐ y ∂μ, m ≤ S.rootChargeRow r y := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict Ir,
      chargeKernel W x =ᵐ[μ]
        fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ q ∂μ.prod μ, q.1 ∈ Ir →
      PhysicalRepresentative.charge W m q.1 q.2 = S.rootChargeRow r q.2 ∧
      PhysicalRepresentative.charge W m q.1 q.2 = chargeKernel W q.1 q.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with q hroot hp hIr
    exact ⟨hroot hIr, hp⟩
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, hxIr, hxrows, hxsection⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIrpos.ne'
      (hrows.and (ae_restrict_of_ae hsections))
  filter_upwards [hxrows, hxsection, S.ae_whole_row_nonneg r hW] with y hy hp hnn
  rw [← (hp hxIr).1, (hp hxIr).2, hy]
  split_ifs <;> nlinarith

/-- A positive part of the private source's genuine dust is impossible on
the middle no-saturation branch. The averaged dust row, its actual fresh
insertion into the same original first-root parents, the exact parent
count, root excess and every star and row bound are derived. -/
theorem no_middle_private_source_dust (S : SelectedHighLowStructure W m)
    (R : S.ReverseRecovery) (i p : S.I) (hip : i ≠ p) (hp : R.plateau = {p})
    {q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
    (hdust : 0 < μ (S.reverseCompulsorySource {p} ∩ S.D)) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hell, hγ⟩ := hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hqgt := hW.middle_unsaturated_q_gt hq hdq hvalue hgap hnull
  have hq2 : q ∈ Icc (187 / 1000 : ℝ) (1 / 5) := ⟨hqgt.le, hq.2.le⟩
  have hA := S.middle_unsaturated_peak_gt_three_tenths hW hq2 hdq hvalue hderiv hgap
    hglobal i hpeak
  have hsector := S.private_peak_large_sector i p hip hW hq hdq hvalue hderiv hgap hglobal
    hpeak hprivate
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨P⟩ := S.exists_private_physical_primal i p hip hW hd hgap hprivate
  have : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let C := S.reverseCompulsorySource {p}
  let X := C ∩ S.D
  have hC : MeasurableSet C := R.singleton_measurableSet_source p hp
  have hX : MeasurableSet X := hC.inter S.hD
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  have hIm : MeasurableSet I := (S.hfibers i.val i.property).1
  have hPm : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hadj := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  -- The genuine source dust joins everything outside the head.
  have hjoin : ∀ᵐ z ∂μ.prod μ, z.1 ∈ X → z.2 ∉ (∅ : Set Ω) → S.ρ z.2 ≠ p.val →
      PhysicalRepresentative.adjacency W m z.1 z.2 = true := by
    filter_upwards [R.ae_source_join p hW hp, S.hDcomplete, hadj] with z hj hD ha hzX _ hzp
    have hkernel : adjacencyKernel W z.1 z.2 = 1 := by
      by_cases hz2 : z.2 ∈ S.D
      · exact hD hzX.2 hz2
      · apply hj hzX.1 _ hzp
        intro heq
        have hz2' : z.2 ∈ ⋃ r ∈ S.I, {x | S.ρ x = r} := by
          simpa only [S.hDeq, mem_compl_iff, not_not] using hz2
        have hz1 : z.1 ∉ ⋃ r ∈ S.I, {x | S.ρ x = r} := by
          simpa only [S.hDeq, mem_compl_iff] using hzX.2
        obtain ⟨r, hr⟩ := mem_iUnion.mp hz2'
        obtain ⟨hrI, hzr⟩ := mem_iUnion.mp hr
        exact hz1 (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hrI, heq.symm.trans hzr⟩⟩)
    cases hb : PhysicalRepresentative.adjacency W m z.1 z.2
    · change adjacencyKernel W z.1 z.2 = if _ then 1 else 0 at ha
      rw [hb] at ha
      simp only [Bool.false_eq_true, ↓reduceIte] at ha
      linarith
    · rfl
  -- The averaged dust row.
  let φ : Ω → ℝ := fun y => ∫ x in X, PhysicalRepresentative.charge W m x y ∂μ
  have hφm : Measurable φ :=
    (PhysicalRepresentative.measurable_charge W m).stronglyMeasurable.integral_prod_left'.measurable
  have hφB (y : Ω) : |φ y| ≤ 3 := by
    have h := norm_integral_le_of_norm_le_const (μ := μ.restrict X)
      (f := fun x => PhysicalRepresentative.charge W m x y) (C := 3)
      (Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
    rw [Real.norm_eq_abs] at h
    have hX1 : (μ.restrict X).real univ ≤ 1 := by
      rw [measureReal_restrict_apply_univ]
      exact measureReal_le_one
    nlinarith
  let cI := ∫ x in X, S.rootChargeRow i x ∂μ
  have hφI : ∀ᵐ y ∂μ, S.ρ y = i.val → φ y = cI := by
    have h := Measure.ae_ae_of_ae_prod (S.ae_root_charge i hW hd hgap)
    filter_upwards [h] with y hy hyi
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hy] with x hx
    rw [PhysicalRepresentative.charge_symm]
    exact hx hyi
  have hφP : ∀ᵐ y ∂μ, S.ρ y = p.val → φ y = 0 := by
    have hz : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = p.val → z.2 ∈ C →
        PhysicalRepresentative.charge W m z.2 z.1 = 0 := by
      filter_upwards [ReverseRecovery.singleton_zero_IC (S := S) p hW hd hgap, hadj]
        with z h0 ha hzp hzC
      rw [PhysicalRepresentative.charge_symm]
      apply PhysicalRepresentative.charge_zero_of_nonedge
      cases hb : PhysicalRepresentative.adjacency W m z.1 z.2
      · rfl
      · change adjacencyKernel W z.1 z.2 = if _ then 1 else 0 at ha
        rw [hb, h0 hzp hzC] at ha
        simp at ha
    filter_upwards [Measure.ae_ae_of_ae_prod hz] with y hy hyp
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hy, ae_restrict_mem hX] with x hx hxX
    exact hx hyp hxX.1
  -- Fresh dust insertion into every first-root parent.
  have hins (n : ℕ) : (∫ v, (PrivatePhysicalPrimal.firstRootEvent S i n).indicator
      (fun _ => (1 : ℝ)) v * ∑ j, φ (v j) ∂P.laws n) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [P.ae_averaged_insertion hW hd hgap X ∅ hX hjoin n] with v hv
    by_cases hE : v ∈ PrivatePhysicalPrimal.firstRootEvent S i n
    · rw [indicator_of_mem hE, one_mul]
      exact hv hE (fun _ h => h)
    · simp [indicator_of_notMem hE]
  have hstock := P.first_root_stock φ hφm 3 hφB cI hφI hφP
  have hsum : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PrivatePhysicalPrimal.firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ∑ j, φ (v j) ∂P.laws n) ≤ 0 :=
    Finset.sum_nonpos (fun n _ => hins n)
  -- The exact count and excess.
  have hcount := P.first_root_count
  have hexcess := P.rootExcess_le hW hd hgap hnull
  rw [P.rootExcess_eq_sum] at hexcess
  let M := ∑ n ∈ Finset.range (P.orderCap + 1),
    (P.laws n).real (PrivatePhysicalPrimal.firstRootEvent S i n)
  let L := ∑ n ∈ Finset.range (P.orderCap + 1),
    ((n : ℝ) - 3) * (P.laws n).real (PrivatePhysicalPrimal.firstRootEvent S i n)
  have hML : (∑ n ∈ Finset.range (P.orderCap + 1),
      ((n : ℝ) - 1) * (P.laws n).real (PrivatePhysicalPrimal.firstRootEvent S i n)) =
      L + 2 * M := by
    simp only [L, M, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  -- Row and star bounds on the dust.
  let s := μ.real X
  have hs0 : 0 < s := ENNReal.toReal_pos hdust.ne' (measure_ne_top μ _)
  have hmle : m ≤ 0 := by linarith [hell.1]
  have hcIup : cI ≤ s := by
    have h := setIntegral_mono_on (μ := μ) (s := X) (f := S.rootChargeRow i)
      (g := fun _ => (1 : ℝ)) (Integrable.of_bound
        (S.measurable_rootChargeRow i).aestronglyMeasurable 3
        (Eventually.of_forall (fun y => by
          have := S.rootChargeRow_mem_Icc i y
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [this.1, this.2]))).integrableOn
      (integrable_const _).integrableOn hX (fun y _ => (S.rootChargeRow_mem_Icc i y).2)
    simpa [setIntegral_const, s] using h
  have hcIlo : m * s ≤ cI := by
    have h := setIntegral_mono_ae (μ := μ) (s := X) (f := fun _ => m)
      (g := S.rootChargeRow i) (integrable_const _).integrableOn
      (Integrable.of_bound (S.measurable_rootChargeRow i).aestronglyMeasurable 3
        (Eventually.of_forall (fun y => by
          have := S.rootChargeRow_mem_Icc i y
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [this.1, this.2]))).integrableOn
      (ae_rootChargeRow_ge S i hW hd hgap hmle)
    simpa [setIntegral_const, s, mul_comm] using h
  -- The averaged dust row pays its missed head only.
  have hZ : s * (2 * (c - m * d) + m * (1 - μ.real Pset)) ≤ ∫ y, φ y ∂μ := by
    have hcol := S.ae_physical_shifted_column_stationary hW hd hgap
    have hrow : ∀ᵐ x ∂μ, x ∈ C →
        2 * (c - m * d) + m * (1 - μ.real Pset) ≤
          ∫ y, PhysicalRepresentative.charge W m x y ∂μ := by
      have hz : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = p.val → z.2 ∈ C →
          PhysicalRepresentative.adjacency W m z.1 z.2 = false := by
        filter_upwards [ReverseRecovery.singleton_zero_IC (S := S) p hW hd hgap, hadj]
          with z h0 ha hzp hzC
        cases hb : PhysicalRepresentative.adjacency W m z.1 z.2
        · rfl
        · change adjacencyKernel W z.1 z.2 = if _ then 1 else 0 at ha
          rw [hb, h0 hzp hzC] at ha
          simp at ha
      have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
      filter_upwards [hcol, Measure.ae_ae_of_ae_prod (hswap.ae hz)] with x hx hxz hxC
      let g : Ω → ℝ := fun z => if PhysicalRepresentative.adjacency W m z x = true then 1 else 0
      have hgm : Measurable g := Measurable.ite ((PhysicalRepresentative.measurable_adjacency
        W m).comp (measurable_id.prodMk measurable_const) (measurableSet_singleton true))
        measurable_const measurable_const
      have hgi : Integrable g μ := Integrable.of_bound hgm.aestronglyMeasurable 1
        (Eventually.of_forall (fun z => by simp only [g]; split_ifs <;> simp))
      have hYi : Integrable (fun z => PhysicalRepresentative.charge W m z x) μ :=
        Integrable.of_bound ((PhysicalRepresentative.measurable_charge W m).comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable 3
          (Eventually.of_forall (fun z => by
            simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m z x))
      have hsplit := integral_sub hYi (hgi.const_mul m)
      simp only [g] at hsplit
      rw [hsplit, integral_const_mul] at hx
      have hgle : (∫ z, g z ∂μ) ≤ 1 - μ.real Pset := by
        have hle : g ≤ᵐ[μ] Psetᶜ.indicator (fun _ => (1 : ℝ)) := by
          filter_upwards [hxz] with z hz
          show (if PhysicalRepresentative.adjacency W m z x = true then (1 : ℝ) else 0) ≤ _
          by_cases hzp : S.ρ z = p.val
          · have hf : PhysicalRepresentative.adjacency W m z x = false := hz hzp hxC
            rw [hf]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact indicator_nonneg (fun _ _ => zero_le_one) z
          · rw [indicator_of_mem (show z ∈ Psetᶜ from hzp)]
            split_ifs <;> norm_num
        have h := integral_mono_ae hgi ((integrable_const 1).indicator hPm.compl) hle
        rwa [integral_indicator hPm.compl, setIntegral_const, smul_eq_mul, mul_one,
          measureReal_compl hPm, probReal_univ] at h
      have hYsym : (∫ y, PhysicalRepresentative.charge W m x y ∂μ) =
          ∫ z, PhysicalRepresentative.charge W m z x ∂μ := by
        congr 1
        funext z
        exact PhysicalRepresentative.charge_symm W m x z
      rw [hYsym]
      nlinarith
    have hprod : Integrable (Function.uncurry (PhysicalRepresentative.charge W m))
        ((μ.restrict X).prod μ) :=
      Integrable.of_bound (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
        (Eventually.of_forall (fun z => by
          rcases z with ⟨x, y⟩
          simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
    have hswapint : (∫ y, φ y ∂μ) =
        ∫ x in X, ∫ y, PhysicalRepresentative.charge W m x y ∂μ ∂μ :=
      (integral_integral_swap hprod).symm
    rw [hswapint]
    have h := setIntegral_mono_ae_restrict (μ := μ) (s := X)
      (f := fun _ => 2 * (c - m * d) + m * (1 - μ.real Pset))
      (g := fun x => ∫ y, PhysicalRepresentative.charge W m x y ∂μ)
      (integrable_const _).integrableOn
      (Integrable.of_bound ((PhysicalRepresentative.measurable_charge W m).stronglyMeasurable
        |>.integral_prod_right').aestronglyMeasurable 3
        (Eventually.of_forall (fun x => by
          have hb := norm_integral_le_of_norm_le_const (μ := μ)
            (f := fun y => PhysicalRepresentative.charge W m x y) (C := 3)
            (Eventually.of_forall (fun y => by
              simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
          simpa using hb))).integrableOn
      (by
        filter_upwards [ae_restrict_of_ae hrow, ae_restrict_mem hX] with x hx hxX
        exact hx hxX.1)
    rw [setIntegral_const, smul_eq_mul] at h
    linarith
  -- The phase inequality and the scalar contradiction.
  have hphase : (μ.real I - 0) * ((∫ y, φ y ∂μ) / s) ≤
      (μ.real I ^ 2 - M) * (cI / s) := by
    rw [sub_zero, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right hs0]
    rw [hstock] at hsum
    nlinarith only [hsum]
  have hR : 2 * (μ.real I ^ 2 - M) =
      μ.real I * (3 * μ.real I + μ.real Pset - 1) + L := by
    rw [hML] at hcount
    nlinarith only [hcount]
  have hE : d - 3 * c < 1 / 100 := by
    have h := MiddlePrivateUnsaturatedScalar.surplus_lt hq2
    rw [← hdq, ← hvalue] at h
    linarith
  have hl := MiddlePrivateUnsaturatedScalar.multiplier_lt hq2
  have hg := MiddlePrivateUnsaturatedScalar.gapFloor_gt hq2
  apply MiddlePrivateUnsaturatedScalar.phase_false (A := μ.real I) (b := μ.real Pset)
    (a := 0) (γ := 2 * (c - m * d) + m) (ℓ := -m) (R := μ.real I ^ 2 - M) (L := L)
    (E := d - 3 * c) (β := cI / s) (Z := (∫ y, φ y ∂μ) / s) hA hsector measureReal_nonneg
    le_rfl (by norm_num) hR hexcess.1 hexcess.2 hE (by linarith) (by linarith)
    (by rw [hm]; linarith) ((div_le_one hs0).mpr hcIup)
    (by rw [le_div_iff₀ hs0]; linarith) (by rw [le_div_iff₀ hs0]; linarith) hphase

end Erdos1017.CappedModel.SelectedHighLowStructure

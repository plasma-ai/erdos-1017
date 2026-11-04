module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateUnsaturatedAtom

/-!
# No positive secondary source on the no-saturation branch

A positive secondary whole atom in the private source is impossible on the
middle no-saturation branch (`no_middle_private_source_atom`), so a private
common peak contained in the one-center source admits no positive secondary
source (`no_middle_private_positive_secondary_source`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {c d : ℝ}
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- A positive secondary whole atom in the private source is impossible on
the middle no-saturation branch. Its averaged row, fresh insertion, `F`-root
leaves, deletion-feasible `F`-stars, closed-missing cap and the exact first
root count all come from the same original model and private primal. -/
theorem no_middle_private_source_atom (S : SelectedHighLowStructure W m)
    (R : S.ReverseRecovery) (i p f : S.I) (hip : i ≠ p) (hfi : f ≠ i)
    (hp : R.plateau = {p}) {q : ℝ} (hW : FullStationaryClass d c W m)
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
    (hsrc : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p})
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hatom : 0 < μ (S.reverseCompulsorySource {p} ∩ {x | S.ρ x = f.val})) : False := by
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
  let F := {x | S.ρ x = f.val}
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  have hFm : MeasurableSet F := (S.hfibers f.val f.property).1
  have hPm : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hadj := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  -- The whole atom lies in the source.
  have hFC : ∀ᵐ x ∂μ, x ∈ F → x ∈ C := by
    have hiff := S.ae_compulsorySource_iff_fiberPredicate f {p} hW
    by_cases hpred : S.fiberCompulsoryPredicate f {p}
    · exact (ae_restrict_iff' hFm).mp (hiff.mono (fun _ h => h.mpr hpred))
    · have hnot : ∀ᵐ x ∂μ.restrict F, x ∉ C := hiff.mono (fun _ h hx => hpred (h.mp hx))
      have hz : μ (C ∩ F) = 0 := by
        rw [← Measure.restrict_apply (R.singleton_measurableSet_source p hp)]
        exact measure_eq_zero_iff_ae_notMem.mpr hnot
      exact absurd hz hatom.ne'
  have hfp : f ≠ p := by
    rintro rfl
    apply hatom.ne'
    apply measure_mono_null (t := (∅ : Set Ω)) _ measure_empty
    intro x hx
    exact (S.mem_singleton_compulsorySource_missing f hx.1).1 hx.2
  -- The literal private-type row of the atom.
  have hFrow : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = f.val →
      (PhysicalRepresentative.adjacency W m z.1 z.2 = true ↔
        ¬(S.ρ z.2 = f.val ∨ S.ρ z.2 = p.val)) := by
    filter_upwards [R.ae_source_join p hW hp, ReverseRecovery.singleton_zero_II (S := S) f,
      hswap.ae (ReverseRecovery.singleton_zero_IC (S := S) p hW hd hgap),
      adjacencyKernel_symm W, hadj, Measure.quasiMeasurePreserving_fst.ae hFC]
      with z hj h0 h1 hsym ha hzC hzf
    change adjacencyKernel W z.1 z.2 = if _ then 1 else 0 at ha
    constructor
    · intro htrue hor
      rw [htrue] at ha
      simp only [↓reduceIte] at ha
      rcases hor with h | h
      · rw [h0 hzf h] at ha
        norm_num at ha
      · have hk : adjacencyKernel W z.1 z.2 = 0 := hsym.trans (h1 h (hzC hzf))
        rw [hk] at ha
        norm_num at ha
    · intro hnot
      have hk := hj (hzC hzf) (fun h => hnot (Or.inl (h.trans hzf))) (fun h => hnot (Or.inr h))
      cases hb : PhysicalRepresentative.adjacency W m z.1 z.2
      · rw [hb, hk] at ha
        norm_num at ha
      · rfl
  have hFpos : 0 < μ F := (S.hfibers f.val f.property).2.1
  let a := μ.real F
  have ha0 : 0 < a := ENNReal.toReal_pos hFpos.ne' (measure_ne_top μ _)
  let φ : Ω → ℝ := fun y => ∫ x in F, PhysicalRepresentative.charge W m x y ∂μ
  have hφm : Measurable φ :=
    (PhysicalRepresentative.measurable_charge W m).stronglyMeasurable.integral_prod_left'.measurable
  have hφB (y : Ω) : |φ y| ≤ 3 := by
    have h := norm_integral_le_of_norm_le_const (μ := μ.restrict F)
      (f := fun x => PhysicalRepresentative.charge W m x y) (C := 3)
      (Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
    rw [Real.norm_eq_abs] at h
    have hX1 : (μ.restrict F).real univ ≤ 1 := by
      rw [measureReal_restrict_apply_univ]
      exact measureReal_le_one
    nlinarith
  let cI := ∫ x in F, S.rootChargeRow i x ∂μ
  have hφI : ∀ᵐ y ∂μ, S.ρ y = i.val → φ y = cI := by
    filter_upwards [Measure.ae_ae_of_ae_prod (S.ae_root_charge i hW hd hgap)] with y hy hyi
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hy] with x hx
    rw [PhysicalRepresentative.charge_symm]
    exact hx hyi
  have hφP : ∀ᵐ y ∂μ, S.ρ y = p.val → φ y = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod (hswap.ae hFrow)] with y hy hyp
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hy, ae_restrict_mem hFm] with x hx hxF
    apply PhysicalRepresentative.charge_zero_of_nonedge
    cases hb : PhysicalRepresentative.adjacency W m x y
    · rfl
    · exact False.elim (((hx hxF).mp hb) (Or.inr hyp))
  have hjoin : ∀ᵐ z ∂μ.prod μ, z.1 ∈ F → z.2 ∉ F → S.ρ z.2 ≠ p.val →
      PhysicalRepresentative.adjacency W m z.1 z.2 = true := by
    filter_upwards [hFrow] with z hz hz1 hz2 hz3
    exact (hz hz1).mpr (fun h => h.elim hz2 hz3)
  -- Insertion off the atom and the `F`-parent stock.
  have hins (n : ℕ) : (∫ v, (PrivatePhysicalPrimal.firstRootEvent S i n).indicator
      (fun _ => (1 : ℝ)) v * ∑ j, φ (v j) ∂P.laws n) ≤
      ∫ v, (PrivatePhysicalPrimal.firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ((PrivatePhysicalPrimal.firstRootEvent S f n).indicator (fun _ => (1 : ℝ)) v *
          ∑ j, φ (v j)) ∂P.laws n := by
    have hbd (g : (Fin n → Ω) → ℝ) (hg : Measurable g) (hgb : ∀ v, |g v| ≤ n * 3) :
        Integrable g (P.laws n) := Integrable.of_bound hg.aestronglyMeasurable (n * 3)
          (Eventually.of_forall (fun v => by simpa [Real.norm_eq_abs] using hgb v))
    have hsumB (v : Fin n → Ω) : |∑ j, φ (v j)| ≤ n * 3 := by
      calc
        _ ≤ ∑ j, |φ (v j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun j _ => hφB (v j))
        _ = n * 3 := by simp
    have hsm : Measurable (fun v : Fin n → Ω => ∑ j, φ (v j)) :=
      Finset.measurable_sum _ (fun j _ => hφm.comp (measurable_pi_apply j))
    have hind (E : Set (Fin n → Ω)) (v : Fin n → Ω) :
        |E.indicator (fun _ => (1 : ℝ)) v| ≤ 1 := by
      by_cases h : v ∈ E <;> simp [h]
    apply integral_mono_ae
    · refine hbd _ ((measurable_const.indicator
        (PrivatePhysicalPrimal.measurableSet_firstRootEvent S i n)).mul hsm) (fun v => ?_)
      rw [abs_mul]
      nlinarith [hind (PrivatePhysicalPrimal.firstRootEvent S i n) v, hsumB v, abs_nonneg
        ((PrivatePhysicalPrimal.firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v),
        abs_nonneg (∑ j, φ (v j))]
    · refine hbd _ ((measurable_const.indicator
        (PrivatePhysicalPrimal.measurableSet_firstRootEvent S i n)).mul
        ((measurable_const.indicator
          (PrivatePhysicalPrimal.measurableSet_firstRootEvent S f n)).mul hsm)) (fun v => ?_)
      rw [abs_mul, abs_mul]
      have h1 := hind (PrivatePhysicalPrimal.firstRootEvent S i n) v
      have h2 := hind (PrivatePhysicalPrimal.firstRootEvent S f n) v
      have h3 := mul_le_mul h2 (hsumB v) (abs_nonneg _) zero_le_one
      have h4 := mul_le_mul h1 h3 (by positivity) zero_le_one
      linarith
    · filter_upwards [P.ae_averaged_insertion hW hd hgap F F hFm hjoin n] with v hv
      by_cases hEF : v ∈ PrivatePhysicalPrimal.firstRootEvent S f n
      · rw [indicator_of_mem hEF, one_mul]
      · rw [indicator_of_notMem hEF, zero_mul, mul_zero]
        by_cases hEI : v ∈ PrivatePhysicalPrimal.firstRootEvent S i n
        · rw [indicator_of_mem hEI, one_mul]
          exact hv hEI (fun j hj => hEF ⟨j, hj⟩)
        · simp [indicator_of_notMem hEI]
  have hatomstock := P.atom_stock_le hW hd hgap f hFrow
  have hstock := P.first_root_stock φ hφm 3 hφB cI hφI hφP
  have hsum : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PrivatePhysicalPrimal.firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ∑ j, φ (v j) ∂P.laws n) ≤ a * ∫ y, φ y ∂μ :=
    (Finset.sum_le_sum (fun n _ => hins n)).trans hatomstock
  -- Count and excess.
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
  -- Star bounds.
  have hmle : m ≤ 0 := by linarith [hell.1]
  have hrcI : Integrable (S.rootChargeRow i) μ :=
    Integrable.of_bound (S.measurable_rootChargeRow i).aestronglyMeasurable 3
      (Eventually.of_forall (fun y => by
        have := S.rootChargeRow_mem_Icc i y
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [this.1, this.2]))
  have hcIup : cI ≤ a := by
    have h := setIntegral_mono_on hrcI.integrableOn (integrable_const (1 : ℝ)).integrableOn hFm
      (fun y _ => (S.rootChargeRow_mem_Icc i y).2)
    simpa [setIntegral_const, a] using h
  have hcIlo : m * a ≤ cI := by
    have h := setIntegral_mono_ae (μ := μ) (s := F) (f := fun _ => m)
      (integrable_const _).integrableOn hrcI.integrableOn
      (ae_rootChargeRow_ge S i hW hd hgap hmle)
    simpa [setIntegral_const, a, mul_comm] using h
  -- The atom row pays its own atom and the head.
  have hZ : a * (2 * (c - m * d) + m * (1 - a - μ.real Pset)) ≤ ∫ y, φ y ∂μ := by
    have hcol := S.ae_physical_shifted_column_stationary hW hd hgap
    have hrow : ∀ᵐ x ∂μ, S.ρ x = f.val →
        2 * (c - m * d) + m * (1 - a - μ.real Pset) ≤
          ∫ y, PhysicalRepresentative.charge W m x y ∂μ := by
      filter_upwards [hcol, Measure.ae_ae_of_ae_prod hFrow] with x hx hxz hxf
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
      have hgle : (∫ z, g z ∂μ) ≤ 1 - a - μ.real Pset := by
        have hle : g ≤ᵐ[μ] (F ∪ Pset)ᶜ.indicator (fun _ => (1 : ℝ)) := by
          filter_upwards [hxz] with z hz
          show (if PhysicalRepresentative.adjacency W m z x = true then (1 : ℝ) else 0) ≤ _
          rw [PhysicalRepresentative.adjacency_symm]
          by_cases hzFP : z ∈ F ∪ Pset
          · have hf : PhysicalRepresentative.adjacency W m x z = false := by
              cases hb : PhysicalRepresentative.adjacency W m x z
              · rfl
              · exact False.elim (((hz hxf).mp hb) hzFP)
            rw [hf]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact indicator_nonneg (fun _ _ => zero_le_one) z
          · rw [indicator_of_mem (show z ∈ (F ∪ Pset)ᶜ from hzFP)]
            split_ifs <;> norm_num
        have h := integral_mono_ae hgi ((integrable_const 1).indicator (hFm.union hPm).compl) hle
        have hdis : Disjoint F Pset := disjoint_left.mpr (fun _ hx hy =>
          hfp (Subtype.ext (hx.symm.trans hy)))
        rwa [integral_indicator (hFm.union hPm).compl, setIntegral_const, smul_eq_mul, mul_one,
          measureReal_compl (hFm.union hPm), probReal_univ, measureReal_union hdis hPm,
          show (1 : ℝ) - (a + μ.real Pset) = 1 - a - μ.real Pset by ring] at h
      have hYsym : (∫ y, PhysicalRepresentative.charge W m x y ∂μ) =
          ∫ z, PhysicalRepresentative.charge W m z x ∂μ := by
        congr 1
        funext z
        exact PhysicalRepresentative.charge_symm W m x z
      rw [hYsym]
      nlinarith
    have hprod : Integrable (Function.uncurry (PhysicalRepresentative.charge W m))
        ((μ.restrict F).prod μ) :=
      Integrable.of_bound (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
        (Eventually.of_forall (fun z => by
          rcases z with ⟨x, y⟩
          simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
    have hswapint : (∫ y, φ y ∂μ) =
        ∫ x in F, ∫ y, PhysicalRepresentative.charge W m x y ∂μ ∂μ :=
      (integral_integral_swap hprod).symm
    rw [hswapint]
    have h := setIntegral_mono_ae_restrict (μ := μ) (s := F)
      (f := fun _ => 2 * (c - m * d) + m * (1 - a - μ.real Pset))
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
        filter_upwards [ae_restrict_of_ae hrow, ae_restrict_mem hFm] with x hx hxF
        exact hx hxF)
    rw [setIntegral_const, smul_eq_mul] at h
    linarith
  -- The closed-missing cap of the secondary atom.
  have hl := MiddleE2Parameter.multiplier_mem hq
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hnonlow : ∀ᵐ x ∂μ.restrict I, x ∉ S.L :=
    hsrc.mono (fun _ hx hL => disjoint_left.mp S.hpartition.2.2.2.2.1 hx.1 hL)
  have hhighF : ∀ᵐ x ∂μ.restrict F, x ∈ S.H :=
    (ae_restrict_iff' hFm).mpr (hFC.mono (fun _ h hxF => (h hxF).1))
  have hb0 : 0 ≤ μ.real Pset := measureReal_nonneg
  have hA' : 3 / 10 < μ.real I := hA
  have hbud := S.middle_high_atom_closed_missing_sq_bound i f hfi hW hd hgap hpeak hnonlow
    hhighF ⟨by change (1 / 4 : ℝ) ≤ μ.real I; linarith,
      by change μ.real I ≤ 1 / 3; linarith⟩ (by rw [hneg]; linarith [hl.1])
  simp only [hneg] at hbud
  have hcap := MiddleE2UniversalSmallHead.closed_missing_lt_four_twentyfifths
    ⟨by linarith [hq2.1], hq2.2⟩ hγ hbud
  have hmiss : 0 ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ f.val) := measureReal_nonneg
  have ha4 : a < 4 / 25 := by
    change S.originalAtomMass f + _ < _ at hcap
    change μ.real F < 4 / 25
    change μ.real F + _ < _ at hcap
    linarith
  -- The phase inequality and the scalar contradiction.
  have hphase : (μ.real I - a) * ((∫ y, φ y ∂μ) / a) ≤
      (μ.real I ^ 2 - M) * (cI / a) := by
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right ha0]
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
  have hl83 := MiddlePrivateUnsaturatedScalar.multiplier_lt hq2
  have hg := MiddlePrivateUnsaturatedScalar.gapFloor_gt hq2
  apply MiddlePrivateUnsaturatedScalar.phase_false (A := μ.real I) (b := μ.real Pset)
    (a := a) (γ := 2 * (c - m * d) + m) (ℓ := -m) (R := μ.real I ^ 2 - M) (L := L)
    (E := d - 3 * c) (β := cI / a) (Z := (∫ y, φ y ∂μ) / a) hA hsector hb0
    ha0.le ha4 hR hexcess.1 hexcess.2 hE (by linarith) (by linarith)
    (by rw [hneg]; linarith) ((div_le_one ha0).mpr hcIup)
    (by rw [le_div_iff₀ ha0]; linarith) (by rw [le_div_iff₀ ha0]; nlinarith) hphase

/-- The private positive-secondary-source case without saturation. On the middle E2
no-saturation branch, a private common peak contained in the one-center
source admits no positive secondary source mass: its genuine dust and each
secondary whole atom are excluded separately; no limit to null source is used. -/
theorem no_middle_private_positive_secondary_source (S : SelectedHighLowStructure W m)
    (R : S.ReverseRecovery) (i p : S.I) (hip : i ≠ p)
    (hp : R.plateau = {p}) {q : ℝ} (hW : FullStationaryClass d c W m)
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
    (hsrc : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p})
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hpos : 0 < μ (S.reverseCompulsorySource {p} \ {x | S.ρ x = i.val})) : False := by
  let : Countable S.I := S.hI.to_subtype
  let C := S.reverseCompulsorySource {p}
  let I := {x | S.ρ x = i.val}
  by_cases hdust : 0 < μ (C ∩ S.D)
  · exact S.no_middle_private_source_dust R i p hip hp hW hq hdq hvalue hderiv hgap hglobal
      hnull hpeak hprivate hdust
  have hdust0 : μ (C ∩ S.D) = 0 := le_antisymm (le_of_not_gt hdust) zero_le
  by_cases hatom : ∃ f : S.I, 0 < μ ((C \ I) ∩ {x | S.ρ x = f.val})
  · obtain ⟨f, hf⟩ := hatom
    have hfi : f ≠ i := by
      rintro rfl
      apply hf.ne'
      apply measure_mono_null (t := (∅ : Set Ω)) _ measure_empty
      intro x hx
      exact hx.1.2 hx.2
    exact S.no_middle_private_source_atom R i p f hip hfi hp hW hq hdq hvalue hderiv hgap
      hglobal hnull hpeak hsrc hprivate
      (hf.trans_le (measure_mono (fun x hx => ⟨hx.1.1, hx.2⟩)))
  · simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hatom
    apply hpos.ne'
    apply measure_mono_null (t := (C ∩ S.D) ∪ ⋃ f : S.I, ((C \ I) ∩ {x | S.ρ x = f.val}))
    · intro x hx
      by_cases hxD : x ∈ S.D
      · exact Or.inl ⟨hx.1, hxD⟩
      · right
        have hx' : x ∈ ⋃ r ∈ S.I, {y | S.ρ y = r} := by
          simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
        obtain ⟨r, hr⟩ := mem_iUnion.mp hx'
        obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
        exact mem_iUnion.mpr ⟨⟨r, hrI⟩, hx, hxr⟩
    · exact measure_union_null hdust0 (measure_iUnion_null hatom)

end Erdos1017.CappedModel.SelectedHighLowStructure

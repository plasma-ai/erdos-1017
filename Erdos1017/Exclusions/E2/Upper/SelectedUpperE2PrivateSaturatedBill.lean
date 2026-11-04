module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateCovarianceGeometry
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairStrict
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateRootStar
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass

/-!
# Whole-hole bill of a private row with saturated partner

The private `I`-row and saturated `P-Q` block force `Q`'s original degree to pay
both the private mass and `P`'s mass, and the original private row and saturated
partner pay the complete whole-hole bill including null cases
(`private_saturated_whole_hole_bill`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem bill_tupleCharge_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hsym : ∀ a b, Y a b = Y b a) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hsym y x, hsym z x, hsym z y]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_wholeRowDegree_eq_rootNeighborhood
    (S : SelectedHighLowStructure W m) (r : S.I) :
    wholeRowDegree r.val = μ.real (S.rootNeighborhood r) := by
  have hN := S.measurableSet_rootNeighborhood r
  have heq : (fun x => if 0 < (r.val : Ω → ℝ) x then (1 : ℝ) else 0) =ᵐ[μ]
      (S.rootNeighborhood r).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [S.ae_rootNeighborhood_iff r] with x hx
    by_cases hr : 0 < (r.val : Ω → ℝ) x
    · simp [hr, (hx.mpr hr)]
    · simp [hr, (not_iff_not.mpr hx).mpr hr]
  rw [wholeRowDegree, integral_congr_ae heq]
  exact integral_indicator_one hN

private theorem bill_ae_private_second_root_off_first
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    ∀ᵐ y ∂μ.restrict {x | S.ρ x = i.val}, y ∉ S.rootNeighborhood p := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hpair : ∀ᵐ q ∂μ.prod μ, q.1 ∈ P → q.2 ∈ I →
      q.2 ∉ S.rootNeighborhood p := by
    filter_upwards [hswap.ae hprivate, adjacencyKernel_symm W,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support,
      S.ae_root_adjacency p hW hd hgap] with q hpriv hsym hphys hroot hp hi hn
    have hzero := hpriv hi
    change adjacencyKernel W q.2 q.1 =
      (if S.ρ q.1 = i.val ∨ S.ρ q.1 = p.val then 0 else 1) at hzero
    have hp' : S.ρ q.1 = p.val := hp
    simp only [hp', or_true, ite_true] at hzero
    have hz : adjacencyKernel W q.1 q.2 = 0 := hsym.trans hzero
    have hfalse : PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
      cases he : PhysicalRepresentative.adjacency W m q.1 q.2
      · rfl
      · have hphys' := hphys
        simp only [he, ↓reduceIte] at hphys'
        change adjacencyKernel W q.1 q.2 = 1 at hphys'
        exact False.elim (by linarith only [hz, hphys'])
    have htrue := (hroot hp).mpr hn
    rw [hfalse] at htrue
    cases htrue
  obtain ⟨x, hx, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers p.val p.property).2.1.ne'
    ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)).and
      (ae_restrict_mem (S.hfibers p.val p.property).1))
  filter_upwards [ae_restrict_of_ae hgood.1,
    ae_restrict_mem (S.hfibers i.val i.property).1] with y hy hi
  exact hy hgood.2 hi

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem bill_ae_whole_row_zero_off_root
    (S : SelectedHighLowStructure W m) (r : S.I)
    (T : Set Ω)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hoff : ∀ᵐ x ∂μ.restrict T, x ∉ S.rootNeighborhood r) :
    ∀ᵐ x ∂μ.restrict T, (r.val : Ω → ℝ) x = 0 := by
  filter_upwards [hoff, ae_restrict_of_ae (S.ae_rootNeighborhood_iff r),
    ae_restrict_of_ae (S.ae_whole_row_nonneg r hW)] with x hx hiff hnonneg
  exact le_antisymm (le_of_not_gt (fun h => hx (hiff.mpr h))) hnonneg

private theorem bill_ae_private_second_row_zero_first
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, (p.val : Ω → ℝ) x = 0 :=
  S.bill_ae_whole_row_zero_off_root p _ hW
    (S.bill_ae_private_second_root_off_first i p hW hd hgap hprivate)

private theorem bill_private_wholeRowDegrees
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    let E := I ∪ P
    let K := Eᶜ \ S.rootNeighborhood p
    wholeRowDegree i.val = 1 - μ.real I - μ.real P ∧
      wholeRowDegree p.val = 1 - μ.real I - μ.real P - μ.real K := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let E := I ∪ P
  let N := S.rootNeighborhood p
  let K := Eᶜ \ N
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hE : MeasurableSet E := hI.union hP
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood p
  have hK : MeasurableSet K := hE.compl.diff hN
  have hdis : Disjoint I P := disjoint_left.mpr (fun _ hi hp =>
    hip (Subtype.ext (hi.symm.trans hp)))
  have hNi : S.rootNeighborhood i =ᵐ[μ] Eᶜ :=
    (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate).mono
      (fun _ hx => propext (by simpa only [E, I, P, mem_compl_iff, mem_union,
        mem_ofPred_eq, not_or] using hx))
  have hNpI := S.bill_ae_private_second_root_off_first i p hW hd hgap hprivate
  have hNpE : ∀ᵐ x ∂μ, x ∈ N → x ∉ E := by
    filter_upwards [(ae_restrict_iff' hI).mp hNpI] with x hx hn he
    rcases he with hi | hp
    · exact hx hi hn
    · exact Set.disjoint_left.mp (S.rootNeighborhood_disjoint p) hp hn
  have hclip : N =ᵐ[μ] Eᶜ ∩ N := by
    filter_upwards [hNpE] with x hx
    exact propext ⟨(fun hn => ⟨hx hn, hn⟩), And.right⟩
  have hunion : Eᶜ = (Eᶜ ∩ N) ∪ K := by
    ext x
    simp only [K, mem_compl_iff, mem_union, mem_inter_iff, Set.mem_sdiff]
    tauto
  have hdis' : Disjoint (Eᶜ ∩ N) K := disjoint_left.mpr (fun _ hx hy => hy.2 hx.2)
  have hEreal : μ.real Eᶜ = 1 - μ.real I - μ.real P := by
    rw [measureReal_compl hE, probReal_univ, measureReal_union hdis hP]
    ring
  have hNreal : μ.real N = 1 - μ.real I - μ.real P - μ.real K := by
    have hpart : μ.real Eᶜ = μ.real (Eᶜ ∩ N) + μ.real K := by
      calc
        μ.real Eᶜ = μ.real ((Eᶜ ∩ N) ∪ K) := congrArg μ.real hunion
        _ = μ.real (Eᶜ ∩ N) + μ.real K :=
          measureReal_union hdis' hK (measure_ne_top μ _) (measure_ne_top μ _)
    rw [← measureReal_congr hclip] at hpart
    linarith [hEreal]
  constructor
  · rw [S.bill_wholeRowDegree_eq_rootNeighborhood i, measureReal_congr hNi]
    exact hEreal
  · rw [S.bill_wholeRowDegree_eq_rootNeighborhood p]
    exact hNreal


omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_adjacency_inner_normalizedHead
    (S : SelectedHighLowStructure W m) (r : S.I) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), S.normalizedHead r⟫ =
      wholeRowDegree r.val := by
  rw [real_inner_comm]
  exact KernelOperator.normalizedSetL2_inner_of_constant _ _
    (S.hfibers r.val r.property).2.1 _ _
    (wholeRowFiber_degree W m S.ρ r.val (S.hfibers r.val r.property).2.2.2)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_adjacency_inner_one {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ =
      2 * d := by
  rw [← weighted_adjacency_eq, weightedPairIntegral_one]
  have hdW := hW.density_eq
  unfold density at hdW
  change (∫ q, adjacencyKernel W q.1 q.2 ∂μ.prod μ) / 2 = d at hdW
  linarith


private theorem sat_gap_and_degree
    (S : SelectedHighLowStructure W m) (p q : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hpq : S.IsSaturatedAtomPair p q) :
    0 < 1 - m - 2 * (2 * (c - m * d)) ∧
      0 < 4 * d - wholeRowDegree p.val - wholeRowDegree q.val := by
  constructor
  · exact hpq.gap_pos hW hd hgap hell
  · linarith [hpq.degree_sum_lt_four_density_of_multiplier_lt_one hW hd hgap hell]

private theorem private_high_ne_sat_head
    (S : SelectedHighLowStructure W m) (i p q : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hpq : S.IsSaturatedAtomPair p q)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) : i ≠ q := by
  intro hiq
  subst q
  have hnull := hpq.symm.high_head_null hW hd hgap hell
  have hI := S.hfibers i.val i.property
  have hnotH : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.H := by
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull),
      ae_restrict_mem hI.1] with x hx hi hH
    exact hx ⟨hi, hH⟩
  obtain ⟨x, _, hh, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hI.2.1.ne' (hhigh.and hnotH)
  exact hn hh

/-- The actual private I-row and saturated P-Q block force Q's original
degree to pay both the private mass and P's mass. -/
theorem private_saturated_other_degree_le
    (S : SelectedHighLowStructure W m) (i p q : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hpq : S.IsSaturatedAtomPair p q)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ t ∂μ.prod μ, S.ρ t.1 = i.val →
      adjacencyKernel W t.1 t.2 =
        if S.ρ t.2 = i.val ∨ S.ρ t.2 = p.val then 0 else 1) :
    2 * μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val} ≤
      wholeRowDegree q.val := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let Q := {x | S.ρ x = q.val}
  have hiq := S.private_high_ne_sat_head i p q hW hd hgap hell hpq hhigh
  have hQ := S.hfibers q.val q.property
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hQN : ∀ᵐ x ∂μ.restrict Q, x ∈ S.rootNeighborhood p := by
    filter_upwards [hpq.row_on_other, ae_restrict_mem hQ.1] with x hx hqx
    refine ⟨?_, ?_⟩
    · intro hxp
      exact hpq.1 (Subtype.ext (hxp.symm.trans hqx))
    · rw [hx]
      linarith
  have hQV : ∀ x ∈ Q, x ∈ (I ∪ P)ᶜ := by
    intro x hxQ
    simp only [mem_compl_iff, mem_union, not_or]
    constructor
    · intro hxI
      exact hiq (Subtype.ext (hxI.symm.trans hxQ))
    · intro hxP
      exact hpq.1 (Subtype.ext (hxP.symm.trans hxQ))
  have hdegree := S.ae_private_neighbor_degree_ge i p hip hW hd hgap hell hhigh hprivate
  have hdegreeQ := wholeRowFiber_degree W m S.ρ q.val hQ.2.2.2
  have hop : ∀ᵐ x ∂μ,
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x =
        ∫ z, adjacencyKernel W x z ∂μ := by
    filter_upwards [KernelOperator.onL2_coe (adjacencyKernel W)
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (Lp.const 2 μ (1 : ℝ))] with x hx
    change KernelOperator.onL2 (adjacencyKernel W)
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (Lp.const 2 μ (1 : ℝ)) x = _
    rw [hx, KernelOperator.applyKernel]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with z _hz
    simp
  obtain ⟨x, hx, ⟨hN, hdg⟩, ⟨hwhole, heq⟩⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hQ.2.1.ne' ((hQN.and (ae_restrict_of_ae hdegree)).and
      (hdegreeQ.and (ae_restrict_of_ae hop)))
  have hxV : x ∈ (I ∪ P)ᶜ := hQV x hx
  have hb := hdg ⟨hxV, hN⟩
  rw [← heq, hwhole] at hb
  exact hb

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_saturated_headPairing
    (S : SelectedHighLowStructure W m) (p q : S.I)
    (hpq : S.IsSaturatedAtomPair p q) :
    S.headPairing p q = 1 - m := by
  change ⟪shiftedOperator W m (S.normalizedHead p), S.normalizedHead q⟫ = _
  rw [S.operator_normalizedHead p, real_inner_comm]
  exact KernelOperator.normalizedSetL2_inner_of_constant _ _
    (S.hfibers q.val q.property).2.1 p.val (1 - m) hpq.row_on_other

private theorem bill_private_headPairing_zero
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ t ∂μ.prod μ, S.ρ t.1 = i.val →
      adjacencyKernel W t.1 t.2 =
        if S.ρ t.2 = i.val ∨ S.ρ t.2 = p.val then 0 else 1) :
    S.headPairing p i = 0 := by
  change ⟪shiftedOperator W m (S.normalizedHead p), S.normalizedHead i⟫ = _
  rw [S.operator_normalizedHead p, real_inner_comm]
  exact KernelOperator.normalizedSetL2_inner_of_constant _ _
    (S.hfibers i.val i.property).2.1 p.val 0
    (S.bill_ae_private_second_row_zero_first i p hW hd hgap hprivate)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem bill_ae_whole_row_le
    (S : SelectedHighLowStructure W m) (r : S.I)
    (hm : m ≤ 1) :
    ∀ᵐ x ∂μ, r.val x ≤ 1 - m := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → r.val p.2 ≤ 1 - m := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property]
      with p hp hIr
    exact (hp hIr) ▸ shiftedKernel_le_one_sub hm p
  obtain ⟨x, hx, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair))
  exact hsection.mono (fun _ hy => hy hx)

private theorem bill_ae_saturated_neighbor_cap
    (S : SelectedHighLowStructure W m) (p q : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpq : S.IsSaturatedAtomPair p q) :
    ∀ᵐ z ∂μ.restrict (S.rootNeighborhood p),
      p.val z + q.val z + (if z ∈ S.rootNeighborhood q then 1 + m else 0) ≤
        1 - m := by
  have hm : m ≤ 1 := le_of_lt (lt_trans
    (hW.strict_gap_structure hd hgap).multiplier_neg (by norm_num))
  filter_upwards [ae_restrict_of_ae (hpq.ae_common_neighbor_score_le hW hd hgap),
    ae_restrict_of_ae (S.bill_ae_whole_row_le p hm),
    ae_restrict_of_ae (S.ae_whole_row_nonneg q hW),
    ae_restrict_of_ae (S.ae_rootNeighborhood_iff p),
    ae_restrict_of_ae (S.ae_rootNeighborhood_iff q),
    ae_restrict_mem (S.measurableSet_rootNeighborhood p)]
    with z hcommon hp hq hpiff hqiff hz
  by_cases hzq : z ∈ S.rootNeighborhood q
  · have hpz := hpiff.mp hz
    have hqz := hqiff.mp hzq
    simp only [hzq, ↓reduceIte]
    linarith [hcommon hpz hqz]
  · have hqzero : q.val z = 0 :=
      le_antisymm (le_of_not_gt (fun h => hzq (hqiff.mpr h))) hq
    simp only [hzq, ↓reduceIte, add_zero, hqzero]
    exact hp
/-- The actual original private row and saturated pair give the degree-zero tangent bound. -/
theorem private_saturated_tangent_le
    (S : SelectedHighLowStructure W m) (i p q : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hpq : S.IsSaturatedAtomPair p q)
    (hprivate : ∀ᵐ t ∂μ.prod μ, S.ρ t.1 = i.val →
      adjacencyKernel W t.1 t.2 =
        if S.ρ t.2 = i.val ∨ S.ρ t.2 = p.val then 0 else 1)
    (hk : 0 < μ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p)) :
    let k := μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p)
    let η := 1 - m - S.headPairing i q
    let Δ := 1 - m - 2 * (2 * (c - m * d))
    let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
    Δ * k ≤ η * v := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
  let A := μ.real I
  let k := μ.real K
  let a := S.normalizedHead i
  let b := S.normalizedHead p
  let h := S.normalizedHead q
  let e := Lp.const 2 μ (1 : ℝ)
  let g := adjacencyOperator W e
  let B := schurForm W m
  let ν := 2 * (c - m * d)
  let η := 1 - m - S.headPairing i q
  let Δ := 1 - m - 2 * ν
  let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
  let wI := A • (b - a)
  let s := b + h - (2 : ℝ) • e
  have hdeg := S.bill_private_wholeRowDegrees i p hip hW hd hgap hprivate
  have hA : 0 < A := ENNReal.toReal_pos
    (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ I)
  have hv : 0 < v := by
    dsimp [v]
    exact (S.sat_gap_and_degree p q hW hd hgap hell hpq).2
  have hs : s = S.saturatedDirection p q := rfl
  have hss : B s s = 2 * Δ := by
    change ⟪shiftedOperator W m s, s⟫ = _
    rw [hs]
    simpa only [Δ, ν] using hpq.shifted_energy hW
  have hba : B b a = 0 := S.bill_private_headPairing_zero i p hW hd hgap hprivate
  have hab : B a b = 0 := (schurForm_symm a b).trans hba
  have haa : B a a = 0 := S.schurForm_head_self i
  have hbb : B b b = 0 := S.schurForm_head_self p
  have hbh : B b h = 1 - m := S.bill_saturated_headPairing p q hpq
  have hah : B a h = S.headPairing i q := rfl
  have hbe : B b e = ν := (schurForm_symm b e).trans (S.schurForm_constant_head p hW)
  have hae : B a e = ν := (schurForm_symm a e).trans (S.schurForm_constant_head i hW)
  have hwIwI : B wI wI = 0 := by
    simp only [wI, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply,
      smul_eq_mul]
    rw [hbb, hba, hab, haa]
    ring
  have hwIs : B wI s = A * η := by
    simp only [wI, s, map_smul, map_sub, map_add, LinearMap.smul_apply,
      LinearMap.sub_apply, smul_eq_mul]
    rw [hbb, hbh, hbe, hab, hah, hae]
    dsimp [η]
    ring
  have hgi : ⟪g, a⟫ = wholeRowDegree i.val := S.bill_adjacency_inner_normalizedHead i
  have hgp : ⟪g, b⟫ = wholeRowDegree p.val := S.bill_adjacency_inner_normalizedHead p
  have hgq : ⟪g, h⟫ = wholeRowDegree q.val := S.bill_adjacency_inner_normalizedHead q
  have hge : ⟪g, e⟫ = 2 * d := bill_adjacency_inner_one hW
  have hDI : ⟪g, a - b⟫ = k := by
    rw [inner_sub_right, hgi, hgp]
    rcases hdeg with ⟨hdi, hdp⟩
    dsimp [I, P, K, A, k] at hdi hdp ⊢
    linarith
  have hgs : ⟪g, s⟫ = -v := by
    simp only [s, inner_sub_right, inner_add_right, real_inner_smul_right]
    rw [hgp, hgq, hge]
    dsimp [v]
    ring
  have hgwI : ⟪g, wI⟫ = -(A * k) := by
    simp only [wI, real_inner_smul_right, inner_sub_right]
    rw [hgi, hgp]
    rw [inner_sub_right, hgi, hgp] at hDI
    calc
      A * (wholeRowDegree p.val - wholeRowDegree i.val) =
          -(A * (wholeRowDegree i.val - wholeRowDegree p.val)) := by ring
      _ = -(A * k) := by rw [hDI]
  have hea : ⟪e, a⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers i.val i.property).2.1
  have heb : ⟪e, b⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers p.val p.property).2.1
  have hes : ⟪e, s⟫ = 0 := by
    rw [hs, KernelOperator.inner_constant_one]
    exact S.saturatedDirection_integral p q
  have hewI : ⟪e, wI⟫ = 0 := by
    simp only [wI, real_inner_smul_right, inner_sub_right, heb, hea]
    ring
  have hkreal : 0 < k := ENNReal.toReal_pos hk.ne' (measure_ne_top μ K)
  let coef := A * k / v
  let tdir := wI - coef • s
  have hcoefpos : 0 < coef := div_pos (mul_pos hA hkreal) hv
  have hcoefv : coef * v = A * k := by
    dsimp [coef]
    field_simp [ne_of_gt hv]
  have htmean : (∫ x, tdir x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪e, tdir⟫ = 0
    simp only [tdir, inner_sub_right, real_inner_smul_right, hewI, hes, mul_zero, sub_zero]
  have htbound : tdir ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      ((KernelOperator.boundedL2Submodule μ).smul_mem A
        ((KernelOperator.boundedL2Submodule μ).sub_mem
          (KernelOperator.normalizedSetL2_bounded _ _)
          (KernelOperator.normalizedSetL2_bounded _ _)))
      ((KernelOperator.boundedL2Submodule μ).smul_mem coef
        (S.saturatedDirection_bounded p q))
  have htdegree : ⟪g, tdir⟫ = 0 := by
    simp only [tdir, inner_sub_right, real_inner_smul_right, hgwI, hgs]
    linear_combination hcoefv
  have hQ : B tdir tdir ≤ 0 :=
    hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular
      tdir htbound htmean htdegree
  have hswI : B s wI = A * η := (schurForm_symm s wI).trans hwIs
  have hQexp : B tdir tdir = 2 * coef * (coef * Δ - A * η) := by
    simp only [tdir, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hwIwI, hwIs, hswI, hss]
    ring
  have hscalar : coef * Δ ≤ A * η := by
    rw [hQexp] at hQ
    nlinarith only [hQ, hcoefpos]
  have hresult : Δ * k ≤ η * v := by
    have hm : Δ * (A * k) ≤ A * (η * v) := by
      calc
        Δ * (A * k) = (coef * Δ) * v := by rw [← hcoefv]; ring
        _ ≤ (A * η) * v := mul_le_mul_of_nonneg_right hscalar hv.le
        _ = A * (η * v) := by ring
    have hm' : A * (Δ * k) ≤ A * (η * v) := by nlinarith only [hm]
    exact (mul_le_mul_iff_of_pos_left hA).mp hm'
  exact hresult
omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_generic_row_upper
    (P Np Nq : Set Ω) (hP : MeasurableSet P) (hNp : MeasurableSet Np)
    (hNq : MeasurableSet Nq) (hdis : Disjoint P Np)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (α δ ν : ℝ)
    (hrowf : ∫ z, f z ∂μ = ν) (hrowg : ∫ z, g z ∂μ = ν)
    (hfsupport : ∀ᵐ z ∂μ, z ∉ Np → f z = 0)
    (hgP : ∀ᵐ z ∂μ.restrict P, g z = α)
    (hcap : ∀ᵐ z ∂μ.restrict Np,
      f z + g z + Nq.indicator (fun _ => δ) z ≤ α) :
    let H := (P ∪ Np)ᶜ
    α * μ.real H - (∫ z in H, g z ∂μ) ≤
      α - 2 * ν - δ * μ.real (Np ∩ Nq) := by
  let H := (P ∪ Np)ᶜ
  have hH : MeasurableSet H := (hP.union hNp).compl
  have hC : MeasurableSet (Np ∩ Nq) := hNp.inter hNq
  have hFoff : (∫ z in Npᶜ, f z ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hfsupport, ae_restrict_mem hNp.compl]
      with z hz hnot
    exact hz hnot
  have hFN : (∫ z in Np, f z ∂μ) = ν := by
    have hpart := integral_add_compl hNp hf
    rw [hFoff, add_zero, hrowf] at hpart
    exact hpart
  have hGP : (∫ z in P, g z ∂μ) = α * μ.real P := by
    rw [integral_congr_ae hgP, setIntegral_const, smul_eq_mul]
    ring
  have hGH : (∫ z in H, g z ∂μ) = ν - α * μ.real P - (∫ z in Np, g z ∂μ) := by
    have hpart := integral_add_compl (hP.union hNp) hg
    have hunion : (∫ z in P ∪ Np, g z ∂μ) =
        (∫ z in P, g z ∂μ) + (∫ z in Np, g z ∂μ) :=
      setIntegral_union hdis hNp hg.integrableOn hg.integrableOn
    rw [hunion, hGP, hrowg] at hpart
    dsimp [H]
    linarith only [hpart]
  have hCint : (∫ z in Np, Nq.indicator (fun _ => δ) z ∂μ) =
      δ * μ.real (Np ∩ Nq) := by
    rw [setIntegral_indicator hNq, setIntegral_const, smul_eq_mul]
    ring
  have hJ : Integrable (Nq.indicator (fun _ => δ)) μ :=
    (integrable_const δ).indicator hNq
  have hbound := integral_mono_ae ((hf.add hg).add hJ).integrableOn
    (integrable_const α).integrableOn hcap
  rw [integral_add' (hf.add hg).integrableOn hJ.integrableOn,
    integral_add' hf.integrableOn hg.integrableOn,
    hCint, setIntegral_const, smul_eq_mul, hFN] at hbound
  dsimp only at *
  rw [hGH]
  have hmass : μ.real H = 1 - μ.real P - μ.real Np := by
    rw [measureReal_compl (hP.union hNp), probReal_univ,
      measureReal_union hdis hNp]
    ring
  rw [hmass]
  linarith only [hbound]

private theorem bill_saturated_row_upper
    (S : SelectedHighLowStructure W m) (p q : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpq : S.IsSaturatedAtomPair p q) :
    let P := {x | S.ρ x = p.val}
    let Np := S.rootNeighborhood p
    let Nq := S.rootNeighborhood q
    let H := (P ∪ Np)ᶜ
    (1 - m) * μ.real H - (∫ z in H, (q.val : Ω → ℝ) z ∂μ) ≤
      (1 - m) - 2 * (2 * (c - m * d)) -
        (1 + m) * μ.real (Np ∩ Nq) := by
  let P := {x | S.ρ x = p.val}
  let Np := S.rootNeighborhood p
  let Nq := S.rootNeighborhood q
  have hP := (S.hfibers p.val p.property).1
  have hNp := S.measurableSet_rootNeighborhood p
  have hNq := S.measurableSet_rootNeighborhood q
  have hf : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hg : Integrable (q.val : Ω → ℝ) μ := (Lp.memLp q.val).integrable (by norm_num)
  have hfsupport : ∀ᵐ z ∂μ, z ∉ Np → (p.val : Ω → ℝ) z = 0 := by
    have hz := S.bill_ae_whole_row_zero_off_root p Npᶜ hW (ae_restrict_mem hNp.compl)
    exact (ae_restrict_iff' hNp.compl).mp hz
  have hgP : ∀ᵐ z ∂μ.restrict P, (q.val : Ω → ℝ) z = 1 - m :=
    hpq.symm.row_on_other
  have hcap := S.bill_ae_saturated_neighbor_cap p q hW hd hgap hpq
  exact bill_generic_row_upper P Np Nq hP hNp hNq
    (S.rootNeighborhood_disjoint p) _ _ hf hg _ _ _
    (S.row_integral_of_stationary p hW)
    (S.row_integral_of_stationary q hW) hfsupport hgP hcap
omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_generic_mass_partition
    (P Np Nq : Set Ω) (hP : MeasurableSet P) (hNp : MeasurableSet Np)
    (hNq : MeasurableSet Nq)
    (hPq : ∀ᵐ z ∂μ.restrict P, z ∈ Nq) :
    let H := (P ∪ Np)ᶜ
    μ.real (Np ∩ Nq) + 1 = μ.real Np + μ.real Nq + μ.real (H \ Nq) := by
  let H := (P ∪ Np)ᶜ
  have hPq' := (ae_restrict_iff' hP).mp hPq
  have heq : (H \ Nq) =ᵐ[μ] (Np ∪ Nq)ᶜ := by
    filter_upwards [hPq'] with z hz
    exact propext (by
      dsimp [H]
      simp only [mem_sdiff, mem_compl_iff, mem_union]
      tauto)
  have hmass : μ.real (H \ Nq) = 1 - μ.real (Np ∪ Nq) := by
    rw [measureReal_congr heq, measureReal_compl (hNp.union hNq), probReal_univ]
  have hunion := measureReal_union_add_inter (s := Np) hNq
    (measure_ne_top μ Np) (measure_ne_top μ Nq)
  dsimp only
  linarith only [hmass, hunion]
private theorem bill_saturated_upper_with_hole
    (S : SelectedHighLowStructure W m) (p q : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpq : S.IsSaturatedAtomPair p q) :
    let P := {x | S.ρ x = p.val}
    let Np := S.rootNeighborhood p
    let Nq := S.rootNeighborhood q
    let H := (P ∪ Np)ᶜ
    let u := μ.real (H \ Nq)
    let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
    let K0 := 2 * c - (1 - 2 * d)
    (1 - m) * μ.real H - (∫ z in H, (q.val : Ω → ℝ) z ∂μ) +
      2 * K0 + (1 + m) * u ≤ (1 + m) * v := by
  let P := {x | S.ρ x = p.val}
  let Np := S.rootNeighborhood p
  let Nq := S.rootNeighborhood q
  let H := (P ∪ Np)ᶜ
  let u := μ.real (H \ Nq)
  let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
  let K0 := 2 * c - (1 - 2 * d)
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hP := (S.hfibers p.val p.property).1
  have hPq : ∀ᵐ z ∂μ.restrict P, z ∈ Nq := by
    filter_upwards [hpq.symm.row_on_other,
      ae_restrict_of_ae (S.ae_rootNeighborhood_iff q)] with z hrow hiff
    exact hiff.mpr (by rw [hrow]; linarith)
  have hmass := bill_generic_mass_partition P Np Nq hP
    (S.measurableSet_rootNeighborhood p) (S.measurableSet_rootNeighborhood q) hPq
  have hupper := S.bill_saturated_row_upper p q hW hd hgap hpq
  have hdegP := S.bill_wholeRowDegree_eq_rootNeighborhood p
  have hdegQ := S.bill_wholeRowDegree_eq_rootNeighborhood q
  dsimp only [P, Np, Nq, H, u, v, K0] at hmass hupper ⊢
  rw [hdegP, hdegQ]
  have hmassmul := congrArg (fun t : ℝ => (1 + m) * t) hmass
  nlinarith only [hupper, hmassmul]
/-- One actual root section of the original product triangle test gives
an AE inequality on exterior pairs. Whole-row homogeneity removes the
chosen root, so the result subsequently transfers to pair-AC parent laws. -/
private theorem bill_ae_any_root_triangle (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.rootNeighborhood r → p.2 ∈ S.rootNeighborhood r →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      S.rootChargeRow r p.1 + S.rootChargeRow r p.2 +
        PhysicalRepresentative.charge W m p.1 p.2 ≤ 1 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := hW.strict_gap_structure hd hgap
  have htest := PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
    hW.deterministic 3
  have hroot : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      (A p.1 p.2 = true ↔ p.2 ∈ S.rootNeighborhood r) ∧ Y p.1 p.2 = S.rootChargeRow r p.2 := by
    filter_upwards [S.ae_root_adjacency r hW hd hgap,
      S.ae_root_charge r hW hd hgap] with p ha hy hx
    exact ⟨ha hx, hy hx⟩
  have hsections := FiniteArity.ae_root_sections μ 2 _ htest
  obtain ⟨x, hx, hrow, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hroot)).and
      (ae_restrict_of_ae hsections))
  have hpairTest : ∀ᵐ p ∂μ.prod μ, FiniteArity.TupleClique A ![x, p.1, p.2] →
      FiniteArity.tupleCharge Y ![x, p.1, p.2] ≤ 1 := by
    have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
      (measurePreserving_finTwoArrow μ)
    have hvec (p : Ω × Ω) :
        Fin.cons x ((MeasurableEquiv.finTwoArrow (α := Ω)).symm p) = ![x, p.1, p.2] := by
      ext i
      fin_cases i <;> rfl
    filter_upwards [hmp.quasiMeasurePreserving.ae hsection] with p hp
    simpa only [hvec] using hp
  filter_upwards [hpairTest, Measure.quasiMeasurePreserving_fst.ae hrow,
    Measure.quasiMeasurePreserving_snd.ae hrow] with p ht hy hz hp1 hp2 hpA
  have hxy := (hy hx).1.mpr hp1
  have hxz := (hz hx).1.mpr hp2
  have hyx : A p.1 x = true := by simpa [A, PhysicalRepresentative.adjacency_symm] using hxy
  have hzx : A p.2 x = true := by simpa [A, PhysicalRepresentative.adjacency_symm] using hxz
  have hzy : A p.2 p.1 = true := by simpa [A, PhysicalRepresentative.adjacency_symm] using hpA
  have hclique : FiniteArity.TupleClique A ![x, p.1, p.2] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at * <;>
      first | exact hxy | exact hxz | exact hyx | exact hpA | exact hzx | exact hzy
  have hbound := ht hclique
  rw [bill_tupleCharge_three Y x p.1 p.2 (PhysicalRepresentative.charge_symm W m),
    (hy hx).2, (hz hx).2] at hbound
  exact hbound

private theorem bill_ae_rootChargeRow_eq_shifted_row_plus
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y = r.val y + m * (if 0 < r.val y then 1 else 0) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict Ir,
      chargeKernel W x =ᵐ[μ]
        fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir →
      PhysicalRepresentative.charge W m p.1 p.2 = S.rootChargeRow r p.2 ∧
      PhysicalRepresentative.charge W m p.1 p.2 = chargeKernel W p.1 p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hroot hp hIr
    exact ⟨hroot hIr, hp⟩
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, hxIr, hxrows, hxsection⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIrpos.ne'
      (hrows.and (ae_restrict_of_ae hsections))
  filter_upwards [hxrows, hxsection] with y hy hp
  exact (hp hxIr).1.symm.trans ((hp hxIr).2.trans hy)

private theorem bill_ae_IQK_triangle_bound
    (S : SelectedHighLowStructure W m) (i p q : S.I) (hiq : i ≠ q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpq : S.IsSaturatedAtomPair p q)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ z ∂μ.restrict
      ((({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p) ∩ S.rootNeighborhood q),
      (q.val : Ω → ℝ) z ≤ (1 - m - S.headPairing i q) - 2 * m - (i.val : Ω → ℝ) z := by
  let I := {x | S.ρ x = i.val}
  let Q := {x | S.ρ x = q.val}
  let K := ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p
  let Z := K ∩ S.rootNeighborhood q
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hQ : MeasurableSet Q := (S.hfibers q.val q.property).1
  have hZ : MeasurableSet Z :=
    (((S.hfibers i.val i.property).1.union (S.hfibers p.val p.property).1).compl.diff
      (S.measurableSet_rootNeighborhood p)).inter (S.measurableSet_rootNeighborhood q)
  have hNiQ : ∀ᵐ y ∂μ.restrict Q, y ∈ S.rootNeighborhood i := by
    filter_upwards [ae_restrict_of_ae (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate),
      ae_restrict_mem hQ] with y hy hqy
    apply hy.mpr
    exact ⟨(fun he => hiq (Subtype.ext (he.symm.trans hqy))),
      fun he => hpq.1 (Subtype.ext (he.symm.trans hqy))⟩
  have hiQ : (i.val : Ω → ℝ) =ᵐ[μ.restrict Q] (fun _ => S.headPairing i q) := by
    obtain ⟨a, _, hia, _, _⟩ := KernelOperator.exists_whole_row_cross_block
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ i.val q.val
      (S.hfibers i.val i.property).2.1 (S.hfibers q.val q.property).2.1
      (S.hfibers i.val i.property).2.2.2 (S.hfibers q.val q.property).2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W) (chargeKernel_measurable W)
      ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) hW.moment_mem
    have hhead : S.headPairing i q = a := by
      change ⟪shiftedOperator W m (S.normalizedHead i), S.normalizedHead q⟫ = a
      rw [S.operator_normalizedHead i, real_inner_comm]
      exact KernelOperator.normalizedSetL2_inner_of_constant Q hQ
        (S.hfibers q.val q.property).2.1 i.val a hia
    exact hia.mono (fun _ h => h.trans hhead.symm)
  have hYiQ : ∀ᵐ y ∂μ.restrict Q, S.rootChargeRow i y = S.headPairing i q + m := by
    filter_upwards [hNiQ, hiQ, ae_restrict_of_ae
      (S.bill_ae_rootChargeRow_eq_shifted_row_plus i hW hd hgap)] with y hn hM hY
    rw [hY, ite_eq_left hn.2, hM]
    ring
  have htest := S.bill_ae_any_root_triangle i hW hd hgap
  obtain ⟨y, hyQ, hytest, hyadj, hycharge, hyNi, hyvalue⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae (S.hfibers q.val q.property).2.1.ne'
      ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod htest)).and
        ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod (S.ae_root_adjacency q hW hd hgap))).and
          ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod (S.ae_root_charge q hW hd hgap))).and
            (hNiQ.and hYiQ))))
  filter_upwards [ae_restrict_of_ae hytest, ae_restrict_of_ae hyadj,
    ae_restrict_of_ae hycharge,
    ae_restrict_of_ae (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate),
    ae_restrict_of_ae (S.bill_ae_rootChargeRow_eq_shifted_row_plus i hW hd hgap),
    ae_restrict_of_ae (S.bill_ae_rootChargeRow_eq_shifted_row_plus q hW hd hgap),
    ae_restrict_mem hZ] with z ht ha hY hn hYi hYq hz
  have hzNi : z ∈ S.rootNeighborhood i := hn.mpr (by
    have hzV := hz.1.1
    simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or] at hzV
    exact hzV)
  have hadj := (ha hyQ).mpr hz.2
  have hbound := ht hyNi hzNi hadj
  rw [hyvalue, hY hyQ, hYi, hYq, ite_eq_left hzNi.2, ite_eq_left hz.2.2] at hbound
  linarith only [hbound]
private theorem bill_private_hole_partition
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
    let H := (P ∪ S.rootNeighborhood p)ᶜ
    H =ᵐ[μ] I ∪ K := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let Np := S.rootNeighborhood p
  let K := (I ∪ P)ᶜ \ Np
  let H := (P ∪ Np)ᶜ
  have hI := (S.hfibers i.val i.property).1
  have hIoff := S.bill_ae_private_second_root_off_first i p hW hd hgap hprivate
  have hIoff' := (ae_restrict_iff' hI).mp hIoff
  filter_upwards [hIoff'] with x hx
  exact propext (by
    simp only [mem_compl_iff, mem_union, mem_sdiff]
    have hnotboth : S.ρ x = i.val → S.ρ x ≠ p.val := by
      intro hi hp
      exact hip (Subtype.ext (hi.symm.trans hp))
    tauto)
omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_q_row_on_I
    (S : SelectedHighLowStructure W m) (i q : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    (q.val : Ω → ℝ) =ᵐ[μ.restrict {x | S.ρ x = i.val}]
      (fun _ => S.headPairing i q) := by
  let I := {x | S.ρ x = i.val}
  let Q := {x | S.ρ x = q.val}
  have hQ : MeasurableSet Q := (S.hfibers q.val q.property).1
  obtain ⟨a, _, hia, hqa, _⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ i.val q.val
    (S.hfibers i.val i.property).2.1 (S.hfibers q.val q.property).2.1
    (S.hfibers i.val i.property).2.2.2 (S.hfibers q.val q.property).2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W) (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) hW.moment_mem
  have hhead : S.headPairing i q = a := by
    change ⟪shiftedOperator W m (S.normalizedHead i), S.normalizedHead q⟫ = a
    rw [S.operator_normalizedHead i, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant Q hQ
      (S.hfibers q.val q.property).2.1 i.val a hia
  exact hqa.mono (fun _ h => h.trans hhead.symm)
private theorem bill_ae_private_hole_lower
    (S : SelectedHighLowStructure W m) (i p q : S.I) (hiq : i ≠ q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpq : S.IsSaturatedAtomPair p q)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    let K := (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p)
    let Nq := S.rootNeighborhood q
    let η := 1 - m - S.headPairing i q
    let δ := 1 + m
    let correction := max (δ - η) 0
    ∀ᵐ z ∂μ.restrict K,
      (1 - m) - q.val z ≥ i.val z + δ - η -
        correction * (if z ∈ Nq then 0 else 1) := by
  let K := (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p)
  let Nq := S.rootNeighborhood q
  let η := 1 - m - S.headPairing i q
  let δ := 1 + m
  let correction := max (δ - η) 0
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union (S.hfibers p.val p.property).1).compl.diff
      (S.measurableSet_rootNeighborhood p)
  have hNq := S.measurableSet_rootNeighborhood q
  have hZ : MeasurableSet (K ∩ Nq) := hK.inter hNq
  have htriangle := S.bill_ae_IQK_triangle_bound i p q hiq hW hd hgap hpq hprivate
  have htriangle' := (ae_restrict_iff' hZ).mp htriangle
  have hm : m ≤ 1 := le_of_lt (lt_trans
    (hW.strict_gap_structure hd hgap).multiplier_neg (by norm_num))
  have hcorrection : δ - η ≤ correction := le_max_left _ _
  filter_upwards [ae_restrict_of_ae htriangle',
    ae_restrict_of_ae (S.ae_rootNeighborhood_iff q),
    ae_restrict_of_ae (S.ae_whole_row_nonneg q hW),
    ae_restrict_of_ae (S.bill_ae_whole_row_le i hm),
    ae_restrict_mem hK] with z ht hiff hnonneg hi hKz
  change (1 - m) - q.val z ≥ i.val z + δ - η -
    correction * (if z ∈ Nq then 0 else 1)
  by_cases hz : z ∈ Nq
  · have hbound := ht ⟨hKz, hz⟩
    simp only [hz, ↓reduceIte, mul_zero, sub_zero]
    dsimp [η, δ] at hbound ⊢
    linarith only [hbound]
  · have hqzero : (q.val : Ω → ℝ) z = 0 :=
      le_antisymm (le_of_not_gt (fun h => hz (hiff.mpr h))) hnonneg
    simp only [hz, ↓reduceIte, mul_one]
    rw [hqzero]
    linarith only [hi, hcorrection]
omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem bill_generic_hole_lower
    (I K H Nq : Set Ω) (hK : MeasurableSet K)
    (hNq : MeasurableSet Nq) (hdis : Disjoint I K)
    (hH : H =ᵐ[μ] I ∪ K) (hKsub : K ⊆ H)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (α δ η correction : ℝ) (hcorr : 0 ≤ correction)
    (hgI : ∀ᵐ z ∂μ.restrict I, g z = α - η)
    (hKlower : ∀ᵐ z ∂μ.restrict K,
      α - g z ≥ f z + δ - η -
        (Nqᶜ).indicator (fun _ => correction) z) :
    (∫ z in K, f z ∂μ) + δ * μ.real K +
      (μ.real I - μ.real K) * η -
        correction * μ.real (H \ Nq) ≤
      α * μ.real H - (∫ z in H, g z ∂μ) := by
  have hHmass : μ.real H = μ.real I + μ.real K := by
    rw [measureReal_congr hH, measureReal_union hdis hK]
  have hHintegral : (∫ z in H, g z ∂μ) =
      (∫ z in I, g z ∂μ) + (∫ z in K, g z ∂μ) := by
    rw [Measure.restrict_congr_set hH]
    exact setIntegral_union hdis hK hg.integrableOn hg.integrableOn
  have hIintegral : (∫ z in I, g z ∂μ) = (α - η) * μ.real I := by
    rw [integral_congr_ae hgI, setIntegral_const, smul_eq_mul]
    ring
  have hOffIntegral :
      (∫ z in K, (Nqᶜ).indicator (fun _ => correction) z ∂μ) =
        correction * μ.real (K \ Nq) := by
    rw [setIntegral_indicator hNq.compl, setIntegral_const, smul_eq_mul]
    simp only [sdiff_eq]
    ring
  have hJ : Integrable ((Nqᶜ).indicator (fun _ => correction)) μ :=
    (integrable_const correction).indicator hNq.compl
  have hbound := integral_mono_ae
    ((hf.add (integrable_const δ)).sub (integrable_const η) |>.sub hJ).integrableOn
    ((integrable_const α).sub hg).integrableOn hKlower
  rw [integral_sub' ((hf.add (integrable_const δ)).sub (integrable_const η)).integrableOn
      hJ.integrableOn,
    integral_sub' (hf.add (integrable_const δ)).integrableOn
      (integrable_const η).integrableOn,
    integral_add' hf.integrableOn (integrable_const δ).integrableOn,
    integral_sub' (integrable_const α).integrableOn hg.integrableOn,
    hOffIntegral, setIntegral_const, setIntegral_const, setIntegral_const] at hbound
  simp only [smul_eq_mul] at hbound
  have hsub : μ.real (K \ Nq) ≤ μ.real (H \ Nq) :=
    measureReal_mono (sdiff_subset_sdiff_left hKsub)
  rw [hHmass, hHintegral, hIintegral]
  nlinarith only [hbound, hsub, hcorr]
private theorem bill_saturated_lower_with_hole
    (S : SelectedHighLowStructure W m) (i p q : S.I) (hip : i ≠ p) (hiq : i ≠ q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpq : S.IsSaturatedAtomPair p q)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
    let H := (P ∪ S.rootNeighborhood p)ᶜ
    let Nq := S.rootNeighborhood q
    let A := μ.real I
    let k := μ.real K
    let η := 1 - m - S.headPairing i q
    let δ := 1 + m
    let correction := max (δ - η) 0
    let u := μ.real (H \ Nq)
    (∫ z in K, (i.val : Ω → ℝ) z ∂μ) + δ * k +
      (A - k) * η - correction * u ≤
      (1 - m) * μ.real H - (∫ z in H, (q.val : Ω → ℝ) z ∂μ) := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
  let H := (P ∪ S.rootNeighborhood p)ᶜ
  let Nq := S.rootNeighborhood q
  let A := μ.real I
  let k := μ.real K
  let η := 1 - m - S.headPairing i q
  let δ := 1 + m
  let correction := max (δ - η) 0
  let u := μ.real (H \ Nq)
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union (S.hfibers p.val p.property).1).compl.diff
      (S.measurableSet_rootNeighborhood p)
  have hdis : Disjoint I K := disjoint_left.mpr (fun _ hi hk => hk.1 (Or.inl hi))
  have hKsub : K ⊆ H := by
    intro x hx
    have hxIP := hx.1
    have hxP : x ∉ P := fun hp => hxIP (Or.inr hp)
    exact fun h => h.elim hxP hx.2
  have hH := S.bill_private_hole_partition i p hip hW hd hgap hprivate
  have hi : Integrable (i.val : Ω → ℝ) μ := (Lp.memLp i.val).integrable (by norm_num)
  have hq : Integrable (q.val : Ω → ℝ) μ := (Lp.memLp q.val).integrable (by norm_num)
  have hcorr : 0 ≤ correction := le_max_right _ _
  have hqI : ∀ᵐ z ∂μ.restrict I, q.val z = 1 - m - η :=
    (S.bill_q_row_on_I i q hW).mono (fun z hz => by
      calc
        q.val z = S.headPairing i q := hz
        _ = 1 - m - η := by dsimp [η]; ring)
  have hklower : ∀ᵐ z ∂μ.restrict K,
      (1 - m) - q.val z ≥ i.val z + δ - η -
        (Nqᶜ).indicator (fun _ => correction) z := by
    filter_upwards [S.bill_ae_private_hole_lower i p q hiq hW hd hgap hpq hprivate]
      with z hz
    have hz' := hz
    change (1 - m) - q.val z ≥ i.val z + δ - η -
      correction * (if z ∈ Nq then 0 else 1) at hz'
    by_cases hNz : z ∈ Nq
    · simpa only [indicator_of_notMem (show z ∉ Nqᶜ from fun h => h hNz),
        hNz, ↓reduceIte, mul_zero] using hz'
    · simpa only [indicator_of_mem (show z ∈ Nqᶜ from hNz),
        hNz, ↓reduceIte, mul_one] using hz'
  exact bill_generic_hole_lower I K H Nq hK (S.measurableSet_rootNeighborhood q)
    hdis hH hKsub _ _ hi hq (1 - m) δ η correction hcorr hqI hklower
/-- The original private row and saturated partner pay the complete whole-hole bill.
The correction uses the entire original H-mass missing Q, including null cases. -/
theorem private_saturated_whole_hole_bill
    (S : SelectedHighLowStructure W m) (i p q : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hpq : S.IsSaturatedAtomPair p q)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
    let H := (P ∪ S.rootNeighborhood p)ᶜ
    let Nq := S.rootNeighborhood q
    let A := μ.real I
    let k := μ.real K
    let η := 1 - m - S.headPairing i q
    let δ := 1 + m
    let u := μ.real (H \ Nq)
    let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
    let K0 := 2 * c - (1 - 2 * d)
    (∫ z in K, (i.val : Ω → ℝ) z ∂μ) + δ * k + (A - k) * η +
      min δ η * u + 2 * K0 ≤ δ * v := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
  let H := (P ∪ S.rootNeighborhood p)ᶜ
  let Nq := S.rootNeighborhood q
  let A := μ.real I
  let k := μ.real K
  let η := 1 - m - S.headPairing i q
  let δ := 1 + m
  let u := μ.real (H \ Nq)
  let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
  let K0 := 2 * c - (1 - 2 * d)
  have hiq := S.private_high_ne_sat_head i p q hW hd hgap hell hpq hhigh
  have hlower := S.bill_saturated_lower_with_hole i p q hip hiq hW hd hgap hpq hprivate
  have hupper := S.bill_saturated_upper_with_hole p q hW hd hgap hpq
  have hmin : δ - max (δ - η) 0 = min δ η := by
    rcases le_total δ η with h | h
    · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
  have hminmul := congrArg (fun x : ℝ => x * u) hmin
  dsimp only [I, P, K, H, Nq, A, k, η, δ, u, v, K0] at hlower hupper ⊢
  nlinarith only [hlower, hupper, hminmul]
private theorem bill_private_eta_pos
    (S : SelectedHighLowStructure W m) (i p q : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hpq : S.IsSaturatedAtomPair p q)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    0 < 1 - m - S.headPairing i q := by
  let I := {x | S.ρ x = i.val}
  let Q := {x | S.ρ x = q.val}
  have hiq := S.private_high_ne_sat_head i p q hW hd hgap hell hpq hhigh
  have hQ := (S.hfibers q.val q.property).1
  have hnot : ¬S.IsSaturatedAtomPair i q := by
    intro hpair
    have hnull := hpair.high_head_null hW hd hgap hell
    have hhigh' := (ae_restrict_iff' (S.hfibers i.val i.property).1).mp hhigh
    have heq : μ (I ∩ S.H) = μ I := by
      apply measure_congr
      filter_upwards [hhigh'] with x hx
      exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
    rw [heq] at hnull
    exact (S.hfibers i.val i.property).2.1.ne' hnull
  have hstrict := S.ae_rootChargeRow_lt_one_of_not_saturated i q hiq hW hd hgap hnot
  have hNiQ : ∀ᵐ y ∂μ.restrict Q, y ∈ S.rootNeighborhood i := by
    filter_upwards [ae_restrict_of_ae (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate),
      ae_restrict_mem hQ] with y hy hqy
    apply hy.mpr
    exact ⟨(fun he => hiq (Subtype.ext (he.symm.trans hqy))),
      fun he => hpq.1 (Subtype.ext (he.symm.trans hqy))⟩
  have hrowQ : (i.val : Ω → ℝ) =ᵐ[μ.restrict Q]
      (fun _ => S.headPairing i q) := by
    have h := S.bill_q_row_on_I q i hW
    have hsym : S.headPairing q i = S.headPairing i q :=
      schurForm_symm (S.normalizedHead q) (S.normalizedHead i)
    exact h.mono (fun _ hz => hz.trans hsym)
  have hcharge : ∀ᵐ y ∂μ.restrict Q,
      S.rootChargeRow i y = S.headPairing i q + m := by
    filter_upwards [hNiQ, hrowQ, ae_restrict_of_ae
      (S.bill_ae_rootChargeRow_eq_shifted_row_plus i hW hd hgap)]
      with y hN hrow hY
    rw [hY, ite_eq_left hN.2, hrow]
    ring
  obtain ⟨y, _, hlt, heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers q.val q.property).2.1.ne' (hstrict.and hcharge)
  rw [heq] at hlt
  linarith
private theorem bill_stationary_row_le_degree
    (S : SelectedHighLowStructure W m) (p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    2 * (c - m * d) ≤ (1 - m) * wholeRowDegree p.val := by
  let Np := S.rootNeighborhood p
  have hNp := S.measurableSet_rootNeighborhood p
  have hf : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hoff := S.bill_ae_whole_row_zero_off_root p Npᶜ hW (ae_restrict_mem hNp.compl)
  have hoffint : (∫ z in Npᶜ, (p.val : Ω → ℝ) z ∂μ) = 0 :=
    integral_eq_zero_of_ae hoff
  have hN : (∫ z in Np, (p.val : Ω → ℝ) z ∂μ) = 2 * (c - m * d) := by
    have hpart := integral_add_compl hNp hf
    rw [hoffint, add_zero, S.row_integral_of_stationary p hW] at hpart
    exact hpart
  have hm : m ≤ 1 := le_of_lt (lt_trans
    (hW.strict_gap_structure hd hgap).multiplier_neg (by norm_num))
  have hbound : (∫ z in Np, (p.val : Ω → ℝ) z ∂μ) ≤
      (∫ z in Np, (1 - m : ℝ) ∂μ) :=
    integral_mono_ae hf.integrableOn (integrable_const (1 - m)).integrableOn
      (ae_restrict_of_ae (S.bill_ae_whole_row_le p hm))
  rw [hN, setIntegral_const, smul_eq_mul] at hbound
  rw [S.bill_wholeRowDegree_eq_rootNeighborhood p]
  nlinarith only [hbound]

/-- The actual original private row and saturated partner supply every
scalar and degree guard used by the saturated bill comparison. -/
theorem private_saturated_bill_geometry
    (S : SelectedHighLowStructure W m) (i p q : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hpq : S.IsSaturatedAtomPair p q)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
    let A := μ.real I
    let b := μ.real P
    let k := μ.real K
    let η := 1 - m - S.headPairing i q
    let Δ := 1 - m - 2 * (2 * (c - m * d))
    let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
    0 < η ∧ 0 < Δ ∧ 0 < v ∧
      2 * A + b ≤ wholeRowDegree q.val ∧
      wholeRowDegree p.val = 1 - A - b - k ∧
      2 * (c - m * d) ≤ (1 - m) * wholeRowDegree p.val := by
  have hgapdeg := S.sat_gap_and_degree p q hW hd hgap hell hpq
  have hhinge := S.private_saturated_other_degree_le i p q hip hW hd hgap
    hell hpq hhigh hprivate
  have hdegrees := S.bill_private_wholeRowDegrees i p hip hW hd hgap hprivate
  exact ⟨S.bill_private_eta_pos i p q hW hd hgap hell hpq hhigh hprivate,
    hgapdeg.1, hgapdeg.2, hhinge, hdegrees.2,
    S.bill_stationary_row_le_degree p hW hd hgap⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

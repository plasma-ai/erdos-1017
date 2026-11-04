module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedSourceBudget
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateSaturatedBill
public import Erdos1017.Exclusions.Common.SelectedReverseSingletonGeometry

/-!
# Geometry of the compulsory sources

A whole original atom in an entire singleton source misses its own atom and the
compulsory head, the compulsory source and its head are disjoint from the head's
neighborhood, and a private source atom is bounded strictly below one half and
below the score ratio (`compulsory_source_atom_lt_score_ratio`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem ae_no_diffuse_pair_to_compulsory_source
    (S : SelectedHighLowStructure W m) (P : Finset S.I) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.reverseCompulsorySource P →
      p ∉ S.reverseAssignmentRelation := by
  let Z := (S.D ×ˢ S.reverseCompulsorySource P) ∩ S.reverseAssignmentRelation
  have hZ : MeasurableSet Z :=
    (S.hD.prod (S.measurableSet_reverseCompulsorySource P)).inter S.measurable_oriented_relations.2
  have hsec := (ae_restrict_iff' S.hpartition.1).mp
    S.ae_reverseRawDiffuse_eq_reverseDiffuseSupply
  have hzero : ∀ᵐ x ∂μ, μ {y | (y, x) ∈ Z} = 0 := by
    filter_upwards [hsec] with x hx
    by_cases hc : x ∈ S.reverseCompulsorySource P
    · have hm : μ.real {y | y ∈ S.D ∧ (y, x) ∈ S.reverseAssignmentRelation} = 0 :=
        (hx hc.1).trans hc.2.1
      have hz : μ {y | y ∈ S.D ∧ (y, x) ∈ S.reverseAssignmentRelation} = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hm |>.resolve_right (measure_ne_top _ _)
      have he : {y | (y, x) ∈ Z} =
          {y | y ∈ S.D ∧ (y, x) ∈ S.reverseAssignmentRelation} := by
        ext y
        simp only [Z, mem_inter_iff, mem_prod, hc, and_true, mem_ofPred_eq]
      rw [he, hz]
    · have he : {y | (y, x) ∈ Z} = ∅ := by
        ext y
        simp only [Z, mem_inter_iff, mem_prod, hc, and_false, false_and,
          mem_ofPred_eq, mem_empty_iff_false]
      rw [he, measure_empty]
  have hswap : (μ.prod μ) (Prod.swap ⁻¹' Z) = 0 :=
    (Measure.measure_prod_null (measurable_swap hZ)).mpr hzero
  have hz : (μ.prod μ) Z = 0 := by
    simpa only [Measure.measurePreserving_swap.measure_preimage hZ.nullMeasurableSet] using hswap
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with p hp hD hC hR
  exact hp ⟨⟨hD, hC⟩, hR⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Every actual reverse-relation pair from the entire singleton source
has its recipient in that original atom. No flow-support hypothesis is used. -/
theorem ae_reverse_pair_to_compulsory_source (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ p ∂μ.prod μ, p.2 ∈ S.reverseCompulsorySource {r} →
      p ∈ S.reverseAssignmentRelation → S.ρ p.1 = r.val := by
  let : Countable S.I := S.hI.to_subtype
  have hrows : ∀ᵐ p ∂μ.prod μ, ∀ u : S.I,
      S.ρ p.1 = u.val → p.2 ∈ S.H →
        (p ∈ S.reverseAssignmentRelation ↔
          p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val) :=
    ae_all_iff.mpr (fun u => S.ae_reverse_fiber_relation_iff_missing u.val u.property
      (hW.moment_mem.mono (fun _ hp => hp.1)))
  have heligible : ∀ᵐ x ∂μ, ∀ u : S.I,
      u ∉ S.eligibleReverseAtom → S.ρ x = u.val → x ∈ S.H :=
    ae_all_iff.mpr (fun u => by
      by_cases hu : u ∈ S.eligibleReverseAtom
      · exact Eventually.of_forall (fun _ h => False.elim (h hu))
      · filter_upwards [(ae_restrict_iff' (S.hfibers u.val u.property).1).mp
          (S.ae_high_of_not_eligibleReverseAtom u hu)] with x hx _ hxu
        exact hx hxu)
  filter_upwards [hrows, Measure.quasiMeasurePreserving_fst.ae heligible,
    S.ae_no_diffuse_pair_to_compulsory_source {r}, S.hrelation] with p hp he hd hz hc hR
  have hnD : p.1 ∉ S.D := fun h => hd h hc hR
  have hU : p.1 ∈ ⋃ u ∈ S.I, {x | S.ρ x = u} := by
    by_contra h
    exact hnD (by rw [S.hDeq]; exact h)
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hU
  let v : S.I := ⟨u, hu⟩
  have hv : v ∈ S.eligibleReverseAtom := by
    by_contra hnot
    have hH := he v hnot hpu
    rcases hz hR.1 with h | h
    · exact (not_lt_of_ge h.2.2.le) hR.2
    · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hH h.2.1
  have hmissing := (hp v hpu hc.1).mp hR
  have hvr : v = r := Finset.mem_singleton.mp (hc.2.2.2 v hv hmissing)
  exact hpu.trans (congrArg Subtype.val hvr)

/-- A whole original atom in an entire singleton source misses precisely
its own atom and the compulsory head. No recovery plateau is needed. -/
theorem ae_compulsory_fiber_private_row (S : SelectedHighLowStructure W m) (k p : S.I)
    {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∈ S.reverseCompulsorySource {p}) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val then 0 else 1 := by
  have hsrc := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hsource
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsrc,
    ReverseRecovery.singleton_zero_II (S := S) k,
    hswap.ae (ReverseRecovery.singleton_zero_IC (S := S) p hW hd hgap),
    adjacencyKernel_symm W, hW.moment_mem, hW.complementary, S.hcoverage, S.hrelation,
    hswap.ae (S.ae_reverse_pair_to_compulsory_source p hW),
    actualZeroRelation_symm W m S.ρ] with z hC hself hhead hsym hm hc hcover hrel hraw hZsym hk
  have hxC := hC hk
  by_cases hy : S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val
  · rw [ite_eq_left hy]
    rcases hy with hy | hy
    · exact hself hk hy
    · exact hsym.trans (hhead hy hxC)
  · rw [ite_eq_right hy]
    have hpos : 0 < shiftedKernel W m z.1 z.2 := by
      apply lt_of_le_of_ne hm.1
      intro he
      rcases hcover he.symm with ⟨q, _, hxq, hyq⟩ | hZ
      · exact hy (Or.inl (hyq.trans (hxq.symm.trans hk)))
      · rcases hrel hZ with h | h
        · have hR : (z.2, z.1) ∈ S.reverseAssignmentRelation := ⟨hZsym.mp hZ, h.2.2⟩
          exact hy (Or.inr (hraw hxC hR))
        · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hxC.1 h.2.1
    have hz := (mul_eq_zero.mp hc).resolve_right (ne_of_gt hpos)
    change 1 - adjacencyKernel W z.1 z.2 = 0 at hz
    linarith only [hz]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem offpair_whole_row_le {S : SelectedHighLowStructure W m} (r : S.I) (hm : m ≤ 1) :
    ∀ᵐ x ∂μ, r.val x ≤ 1 - m := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → r.val p.2 ≤ 1 - m := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property] with p hp hIr
    exact (hp hIr) ▸ shiftedKernel_le_one_sub hm p
  obtain ⟨x, hx, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair))
  exact hsection.mono (fun _ hy => hy hx)

private theorem offpair_stationary_row_le_neighborhood
    {S : SelectedHighLowStructure W m} {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) :
    2 * (c - m * d) ≤ (1 - m) * μ.real (S.rootNeighborhood r) := by
  let N := S.rootNeighborhood r
  have hN := S.measurableSet_rootNeighborhood r
  have hf : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hoff : (r.val : Ω → ℝ) =ᵐ[μ.restrict Nᶜ] fun _ => 0 := by
    filter_upwards [ae_restrict_mem hN.compl, ae_restrict_of_ae (S.ae_rootNeighborhood_iff r),
      ae_restrict_of_ae (S.ae_whole_row_nonneg r hW)] with x hx hiff hnonneg
    exact le_antisymm (le_of_not_gt (fun h => hx (hiff.mpr h))) hnonneg
  have hoffint : (∫ x in Nᶜ, (r.val : Ω → ℝ) x ∂μ) = 0 := integral_eq_zero_of_ae hoff
  have hNint : (∫ x in N, (r.val : Ω → ℝ) x ∂μ) = 2 * (c - m * d) := by
    have hpart := integral_add_compl hN hf
    rw [hoffint, add_zero, S.row_integral_of_stationary r hW] at hpart
    exact hpart
  have hm : m ≤ 1 := le_of_lt (lt_trans
    (hW.strict_gap_structure hd hgap).multiplier_neg (by norm_num))
  have hbound : (∫ x in N, (r.val : Ω → ℝ) x ∂μ) ≤
      (∫ x in N, (1 - m : ℝ) ∂μ) :=
    integral_mono_ae hf.integrableOn (integrable_const (1 - m)).integrableOn
      (ae_restrict_of_ae (offpair_whole_row_le (S := S) r hm))
  rw [hNint, setIntegral_const, smul_eq_mul] at hbound
  simpa only [N, mul_comm] using hbound

/-- The entire compulsory source and its original head are disjoint from
that head's neighborhood. Flatness therefore pays their combined mass. -/
theorem compulsory_source_head_mass_bound (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (1 - m) * (S.originalAtomMass r + μ.real (S.reverseCompulsorySource {r})) ≤
      1 - m - 2 * (c - m * d) := by
  let I := {x | S.ρ x = r.val}
  let C := S.reverseCompulsorySource {r}
  let N := S.rootNeighborhood r
  have hC := S.measurableSet_reverseCompulsorySource {r}
  have hN := S.measurableSet_rootNeighborhood r
  have hCN : Disjoint C N := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt hy.2) (S.mem_singleton_compulsorySource_missing r hx).2
  have hdis : Disjoint (I ∪ C) N :=
    disjoint_union_left.mpr ⟨S.rootNeighborhood_disjoint r, hCN⟩
  have hmass : S.originalAtomMass r + μ.real C + μ.real N ≤ 1 := by
    have hb := measureReal_mono (μ := μ) (subset_univ (I ∪ C ∪ N))
    rw [measureReal_union hdis hN,
      measureReal_union (S.disjoint_singleton_fiber_source r) hC, probReal_univ] at hb
    exact hb
  have hrow := offpair_stationary_row_le_neighborhood (S := S) hW hd hgap r
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hmul := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 1 - m by linarith)
  dsimp only [C, N] at hmul
  nlinarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem offpair_wholeRowDegree_eq_rootNeighborhood
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

/-- Repricing at the other saturated head bounds a private source atom
strictly below one half; no endpoint atom is substituted for this atom. -/
theorem compulsory_source_atom_lt_half (S : SelectedHighLowStructure W m) (i r u : S.I)
    (hir : i ≠ r) (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.reverseCompulsorySource {r}) : S.originalAtomMass i < 1 / 2 := by
  have hhigh := hsource.mono (fun _ hx => hx.1)
  have hprivate := S.ae_compulsory_fiber_private_row i r hW hd hgap hsource
  have hdegree := S.private_saturated_other_degree_le i r u hir hW hd hgap
    hell hpair hhigh hprivate
  have hcap : wholeRowDegree u.val ≤ 1 := by
    rw [S.offpair_wholeRowDegree_eq_rootNeighborhood u]
    simpa only [probReal_univ] using measureReal_mono (μ := μ)
      (subset_univ (S.rootNeighborhood u))
  have hrpos : 0 < S.originalAtomMass r :=
    ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top μ _)
  change 2 * S.originalAtomMass i + S.originalAtomMass r ≤ _ at hdegree
  linarith

private theorem offpair_tupleCharge_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hsym : ∀ a b, Y a b = Y b a) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hsym y x, hsym z x, hsym z y]
  ring


private theorem offpair_ae_any_root_triangle (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
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
  rw [offpair_tupleCharge_three Y x p.1 p.2 (PhysicalRepresentative.charge_symm W m),
    (hy hx).2, (hz hx).2] at hbound
  exact hbound

private theorem offpair_ae_rootChargeRow_eq_shifted_row_plus
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

private theorem offpair_ae_IQK_triangle_bound
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
      (S.offpair_ae_rootChargeRow_eq_shifted_row_plus i hW hd hgap)] with y hn hM hY
    rw [hY, ite_eq_left hn.2, hM]
    ring
  have htest := S.offpair_ae_any_root_triangle i hW hd hgap
  obtain ⟨y, hyQ, hytest, hyadj, hycharge, hyNi, hyvalue⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae (S.hfibers q.val q.property).2.1.ne'
      ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod htest)).and
        ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod (S.ae_root_adjacency q hW hd hgap))).and
          ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod (S.ae_root_charge q hW hd hgap))).and
            (hNiQ.and hYiQ))))
  filter_upwards [ae_restrict_of_ae hytest, ae_restrict_of_ae hyadj,
    ae_restrict_of_ae hycharge,
    ae_restrict_of_ae (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate),
    ae_restrict_of_ae (S.offpair_ae_rootChargeRow_eq_shifted_row_plus i hW hd hgap),
    ae_restrict_of_ae (S.offpair_ae_rootChargeRow_eq_shifted_row_plus q hW hd hgap),
    ae_restrict_mem hZ] with z ht ha hY hn hYi hYq hz
  have hzNi : z ∈ S.rootNeighborhood i := hn.mpr (by
    have hzV := hz.1.1
    simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or] at hzV
    exact hzV)
  have hadj := (ha hyQ).mpr hz.2
  have hbound := ht hyNi hzNi hadj
  rw [hyvalue, hY hyQ, hYi, hYq, ite_eq_left hzNi.2, ite_eq_left hz.2.2] at hbound
  linarith only [hbound]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem offpair_q_row_on_I
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

/-- The other saturated head is joined to almost every point of the entire
singleton source, directly from the source's actual missing-label condition. -/
private theorem ae_compulsory_source_in_other_neighborhood
    {S : SelectedHighLowStructure W m} {r u : S.I} (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {r}), x ∈ S.rootNeighborhood u := by
  filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr
    (hpair.symm.high_head_null hW hd hgap hell)),
    ae_restrict_mem (S.measurableSet_reverseCompulsorySource {r})] with x hx hC
  have hne : S.ρ x ≠ u.val := fun hu => hx ⟨hu, hC.1⟩
  refine ⟨hne, lt_of_not_ge ?_⟩
  intro hle
  have hu := hC.2.2.2 u (hpair.symm.head_eligibleReverseAtom hW hd hgap hell) ⟨hne, hle⟩
  exact hpair.1 (Finset.mem_singleton.mp hu).symm

/-- On a private source atom the other-head deficit is one positive
constant; on the remaining entire source the genuine triangle gives its lower floor. -/
theorem compulsory_source_deficit_bounds (S : SelectedHighLowStructure W m) (i r u : S.I)
    (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.reverseCompulsorySource {r}) :
    let e := 1 - m - S.headPairing i u
    0 < e ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, 1 - S.rootChargeRow u x = e) ∧
      (∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {r} \ {x | S.ρ x = i.val}),
        max (1 + m - e) 0 ≤ 1 - S.rootChargeRow u x) := by
  let I := {x | S.ρ x = i.val}
  let C := S.reverseCompulsorySource {r}
  let K := ((I ∪ {x | S.ρ x = r.val})ᶜ \ S.rootNeighborhood r)
  let Z := K ∩ S.rootNeighborhood u
  let e := 1 - m - S.headPairing i u
  have hI := (S.hfibers i.val i.property).1
  have hC := S.measurableSet_reverseCompulsorySource {r}
  have hZ : MeasurableSet Z :=
    ((hI.union (S.hfibers r.val r.property).1).compl.diff
      (S.measurableSet_rootNeighborhood r)).inter (S.measurableSet_rootNeighborhood u)
  have hhigh := hsource.mono (fun _ hx => hx.1)
  have hprivate := S.ae_compulsory_fiber_private_row i r hW hd hgap hsource
  have hgeom := S.private_saturated_bill_geometry i r u hir hW hd hgap hell
    hpair hhigh hprivate
  have hNu := ae_compulsory_source_in_other_neighborhood hpair hW hd hgap hell
  have hNu' := (ae_restrict_iff' hC).mp hNu
  have hrow := S.offpair_ae_rootChargeRow_eq_shifted_row_plus u hW hd hgap
  refine ⟨hgeom.1, ?_, ?_⟩
  · filter_upwards [hsource, ae_restrict_of_ae hNu',
      S.offpair_q_row_on_I i u hW, ae_restrict_of_ae hrow] with x hx hn hv hY
    rw [hY, ite_eq_left (hn hx).2, hv]
    ring
  · have htri := (ae_restrict_iff' hZ).mp
      (S.offpair_ae_IQK_triangle_bound i r u hiu hW hd hgap hpair hprivate)
    filter_upwards [ae_restrict_of_ae htri, ae_restrict_of_ae hNu',
      ae_restrict_of_ae hrow, ae_restrict_of_ae (S.ae_whole_row_nonneg i hW),
      ae_restrict_mem (hC.diff hI)] with x ht hn hY hi hx
    have hxr := S.mem_singleton_compulsorySource_missing r hx.1
    have hxZ : x ∈ Z := ⟨⟨by
        intro h
        exact h.elim hx.2 hxr.1,
      fun h => not_le_of_gt h.2 hxr.2⟩, hn hx.1⟩
    have hb := ht hxZ
    have hYbound := (S.rootChargeRow_mem_Icc u x).2
    rw [hY, ite_eq_left (hn hx.1).2] at hYbound ⊢
    apply max_le
    · linarith
    · linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem source_integral_strict (I C : Set Ω) (hI : MeasurableSet I)
    (hC : MeasurableSet C) (hIC : ∀ᵐ x ∂μ, x ∈ I → x ∈ C)
    (f : Ω → ℝ) (hf : Integrable f μ) (delta e : ℝ)
    (hdelta : 0 < delta) (he : 0 < e) (hmass : μ.real C < 2 * μ.real I)
    (hfi : ∀ᵐ x ∂μ.restrict I, f x = e)
    (hfj : ∀ᵐ x ∂μ.restrict (C \ I), max (delta - e) 0 ≤ f x) :
    delta * (μ.real C - μ.real I) < ∫ x in C, f x ∂μ := by
  have hsubset : I ∩ C =ᵐ[μ] I := by
    filter_upwards [hIC] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
  have hunion : C ∪ I =ᵐ[μ] C := by
    filter_upwards [hIC] with x hx
    exact propext ⟨fun h => h.elim id hx, Or.inl⟩
  have hJmass : μ.real (C \ I) = μ.real C - μ.real I := by
    rw [measureReal_sdiff' hI, measureReal_congr hunion]
  have hIint : (∫ x in I, f x ∂μ) = e * μ.real I := by
    rw [integral_congr_ae hfi, setIntegral_const, smul_eq_mul]
    ring
  have hJint : max (delta - e) 0 * μ.real (C \ I) ≤ ∫ x in C \ I, f x ∂μ := by
    have hb := integral_mono_ae (integrable_const (max (delta - e) 0)).integrableOn
      hf.integrableOn hfj
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hb
  have hpart : (∫ x in C, f x ∂μ) = (∫ x in I, f x ∂μ) + ∫ x in C \ I, f x ∂μ := by
    have heq : (I ∩ C) ∪ (C \ I) = C := by ext x; simp; tauto
    rw [← heq, setIntegral_union (disjoint_left.mpr (fun x hx hy => hy.2 hx.1))
      (hC.diff hI) hf.integrableOn hf.integrableOn,
      Measure.restrict_congr_set hsubset]
    congr 1
    rw [heq]
  rw [hJmass] at hJint
  rw [hIint] at hpart
  have hj : 0 ≤ μ.real C - μ.real I := by rw [← hJmass]; positivity
  by_cases hed : e ≤ delta
  · rw [max_eq_left (sub_nonneg.mpr hed)] at hJint
    have hpos := mul_pos (show 0 < 2 * μ.real I - μ.real C by linarith) he
    nlinarith
  · rw [max_eq_right (by linarith : delta - e ≤ 0), zero_mul] at hJint
    have hpos := mul_pos hdelta (show 0 < 2 * μ.real I - μ.real C by linarith)
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_ge hed)
      (show 0 ≤ μ.real I from measureReal_nonneg)
    nlinarith

/-- One original triangle budget gives a strict deficit excess on the entire
private source once its actual mass is below twice the original peak mass. -/
theorem compulsory_source_deficit_strict (S : SelectedHighLowStructure W m) (i r u : S.I)
    (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.reverseCompulsorySource {r})
    (hmass : μ.real (S.reverseCompulsorySource {r}) < 2 * S.originalAtomMass i) :
    (1 + m) * (μ.real (S.reverseCompulsorySource {r}) - S.originalAtomMass i) <
      ∫ x in S.reverseCompulsorySource {r}, 1 - S.rootChargeRow u x ∂μ := by
  obtain ⟨he, hfi, hfj⟩ :=
    S.compulsory_source_deficit_bounds i r u hir hiu hpair hW hd hgap hell hsource
  have hf : Integrable (S.rootChargeRow u) μ := by
    apply Integrable.of_bound (S.measurable_rootChargeRow u).aestronglyMeasurable 3
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(S.rootChargeRow_mem_Icc u x).1,
      (S.rootChargeRow_mem_Icc u x).2.trans (by norm_num)⟩
  exact source_integral_strict _ _ (S.hfibers i.val i.property).1
    (S.measurableSet_reverseCompulsorySource {r})
    ((ae_restrict_iff' (S.hfibers i.val i.property).1).mp hsource)
    _ ((integrable_const 1).sub hf) (1 + m) _ (by linarith) he hmass hfi hfj

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem source_head_degree_mass_le_one (S : SelectedHighLowStructure W m) (r : S.I) :
    S.originalAtomMass r + μ.real (S.reverseCompulsorySource {r}) +
      wholeRowDegree r.val ≤ 1 := by
  let I := {x | S.ρ x = r.val}
  let C := S.reverseCompulsorySource {r}
  let N := S.rootNeighborhood r
  have hC := S.measurableSet_reverseCompulsorySource {r}
  have hN := S.measurableSet_rootNeighborhood r
  have hCN : Disjoint C N := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt hy.2) (S.mem_singleton_compulsorySource_missing r hx).2
  have hdis : Disjoint (I ∪ C) N :=
    disjoint_union_left.mpr ⟨S.rootNeighborhood_disjoint r, hCN⟩
  have hb := measureReal_mono (μ := μ) (subset_univ (I ∪ C ∪ N))
  rw [measureReal_union hdis hN,
    measureReal_union (S.disjoint_singleton_fiber_source r) hC, probReal_univ] at hb
  rw [S.offpair_wholeRowDegree_eq_rootNeighborhood r]
  exact hb

/-- The strict entire-source deficit and original repricing bound use one
and the same saturated score budget. This is the physical private-source implication. -/
theorem compulsory_source_atom_lt_score_ratio (S : SelectedHighLowStructure W m) (i r u : S.I)
    (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.reverseCompulsorySource {r})
    (hmass : μ.real (S.reverseCompulsorySource {r}) < 2 * S.originalAtomMass i) :
    S.originalAtomMass i < (1 - m - 2 * (2 * (c - m * d))) / (1 + m) := by
  let Ir := {x | S.ρ x = r.val}
  let Iu := {x | S.ρ x = u.val}
  let C := S.reverseCompulsorySource {r}
  let D := S.reverseCompulsorySource {u}
  let O := (Ir ∪ Iu ∪ C ∪ D)ᶜ
  have hIr := (S.hfibers r.val r.property).1
  have hIu := (S.hfibers u.val u.property).1
  have hC := S.measurableSet_reverseCompulsorySource {r}
  have hD := S.measurableSet_reverseCompulsorySource {u}
  have hmassO : 1 - S.originalAtomMass r - S.originalAtomMass u - μ.real C - μ.real D ≤
      μ.real O := by
    have h1 := measureReal_union_le (μ := μ) Ir Iu
    have h2 := measureReal_union_le (μ := μ) (Ir ∪ Iu) C
    have h3 := measureReal_union_le (μ := μ) (Ir ∪ Iu ∪ C) D
    have he : μ.real O = 1 - μ.real (Ir ∪ Iu ∪ C ∪ D) := by
      rw [measureReal_compl (((hIr.union hIu).union hC).union hD), probReal_univ]
    change 1 - μ.real Ir - μ.real Iu - μ.real C - μ.real D ≤ μ.real O
    linarith
  have hbudget := hpair.entire_source_score_budget hW hd hgap hell
  have hstrict := S.compulsory_source_deficit_strict i r u hir hiu hpair hW hd hgap
    hell hsource hmass
  have hnonneg : 0 ≤ ∫ x in D, 1 - S.rootChargeRow r x ∂μ :=
    integral_nonneg (fun x => sub_nonneg.mpr (S.rootChargeRow_mem_Icc r x).2)
  have hscaled := mul_le_mul_of_nonneg_left hmassO (show 0 ≤ 1 + m by linarith)
  have hdegree := S.private_saturated_other_degree_le i r u hir hW hd hgap hell hpair
    (hsource.mono (fun _ hx => hx.1)) (S.ae_compulsory_fiber_private_row i r hW hd hgap hsource)
  have hcap := S.source_head_degree_mass_le_one u
  change 2 * S.originalAtomMass i + S.originalAtomMass r ≤ _ at hdegree
  have hmass : S.originalAtomMass i ≤
      1 - S.originalAtomMass r - S.originalAtomMass u - S.originalAtomMass i - μ.real D := by
    dsimp only [D]
    linarith
  have hscaled' := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 1 + m by linarith)
  apply (lt_div_iff₀ (by linarith)).mpr
  dsimp only [Ir, Iu, C, D, O] at hscaled hscaled' hnonneg
  nlinarith only [hscaled, hscaled', hnonneg, hstrict, hbudget]

end Erdos1017.CappedModel.SelectedHighLowStructure

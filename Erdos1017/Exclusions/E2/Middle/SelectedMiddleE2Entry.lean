module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2Scalar
public import Erdos1017.Exclusions.E2.Upper.SelectedE2TwoCenter
public import Erdos1017.Exclusions.E2.Upper.SelectedE2EmptySource
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedOneCenterSourceCredit
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedScoreFloor

/-!
# Entry to the middle `E₂` exclusion

On `1/10 < q < 1/5` the selected model has multiplier above `9/11`, density
above one third, and a one-center recovery whose head, entire source and head
neighborhood are disjoint (`exists_middle_e2_one_center_entry`,
`one_center_core_mass`). The common peak stays in that source or joins the
recovered head (`middle_e2_one_center_peak_location`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem middle_peak_ne_head
    (hW : FullStationaryClass d c W m) (r : S.I) (hr : R.plateau = {r})
    (hsource : 0 < μ (S.reverseCompulsorySource {r}))
    (k : S.I) (hpeak : S.IsCommonForwardPeak d c k) : k ≠ r := by
  intro heq
  subst k
  have hmass := R.common_peak_head_mass r (by rw [hr]; simp) hW hpeak
  have hheight := R.singleton_height_eq_mass_add_source r hr
  rw [← hmass] at hheight
  have hs : 0 < μ.real (S.reverseCompulsorySource {r}) :=
    ENNReal.toReal_pos hsource.ne' (measure_ne_top μ _)
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem middle_whole_row_le (r : S.I) (hm : m ≤ 1) :
    ∀ᵐ x ∂μ, r.val x ≤ 1 - m := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → r.val p.2 ≤ 1 - m := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property] with p hp hIr
    exact (hp hIr) ▸ shiftedKernel_le_one_sub hm p
  obtain ⟨x, hx, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair))
  exact hsection.mono (fun _ hy => hy hx)

private theorem middle_stationary_row_le_neighborhood
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
      (ae_restrict_of_ae (middle_whole_row_le (S := S) r hm))
  rw [hNint, setIntegral_const, smul_eq_mul] at hbound
  simpa only [N, mul_comm] using hbound

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The recovered head, its entire source and the head neighborhood are
disjoint, and their total mass is the recovered height plus the
neighborhood mass. -/
theorem one_center_core_mass
    (r : S.I) (hr : R.plateau = {r}) :
    μ.real (({x | S.ρ x = r.val} ∪ S.reverseCompulsorySource {r}) ∪
      S.rootNeighborhood r) = R.height + μ.real (S.rootNeighborhood r) := by
  let I : Set Ω := {x | S.ρ x = r.val}
  let C : Set Ω := S.reverseCompulsorySource {r}
  let N := S.rootNeighborhood r
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hC : MeasurableSet C := R.singleton_measurableSet_source r hr
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood r
  have hIC : Disjoint I C := S.disjoint_singleton_fiber_source r
  have hIN : Disjoint I N := S.rootNeighborhood_disjoint r
  have hCN : Disjoint C N := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt hy.2) (S.mem_singleton_compulsorySource_missing r hx).2
  have hUC : Disjoint (I ∪ C) N := disjoint_union_left.mpr ⟨hIN, hCN⟩
  rw [measureReal_union hUC hN, measureReal_union hIC hC,
    R.singleton_height_eq_mass_add_source r hr]

private theorem middle_source_fiber_private_row (k p : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {p})
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∈ S.reverseCompulsorySource {p}) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val then 0 else 1 := by
  have hsrc := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hsource
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsrc,
    singleton_zero_II (S := S) k,
    hswap.ae (singleton_zero_IC (S := S) p hW hd hgap),
    adjacencyKernel_symm W, hW.moment_mem, hW.complementary, S.hcoverage, S.hrelation,
    hswap.ae (R.ae_reverse_pair_to_singleton_source p hW hp),
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

/-- At a middle-E2 contact, a one-center recovery with positive entire
source retains the original common peak in that source or joins it to the
recovered head. The extra-hole position is excluded by the actual height
credit, original forward reserve and flat head row; no peak mass floor is
an input. -/
theorem middle_e2_one_center_peak_location
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (p k : S.I) (hp : R.plateau = {p}) (hkp : k ≠ p)
    (hpeak : S.IsCommonForwardPeak d c k) :
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.reverseCompulsorySource {p}) ∨
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood p) := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  by_cases hC : S.fiberCompulsoryPredicate k {p}
  · left
    exact (S.ae_compulsorySource_iff_fiberPredicate k {p} hW).mono
      (fun _ hx => hx.mpr hC)
  have hnotC : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∉ S.reverseCompulsorySource {p} :=
    (S.ae_compulsorySource_iff_fiberPredicate k {p} hW).mono
      (fun _ hx h => hC (hx.mp h))
  rcases S.ae_fiber_missing_or_not k p hW with hmissing | hjoined
  · exfalso
    let O : Set Ω := (({y | S.ρ y = p.val} ∪ S.reverseCompulsorySource {p}) ∪
      S.rootNeighborhood p)ᶜ
    have hK : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ O := by
      filter_upwards [hmissing, hnotC, ae_restrict_mem (S.hfibers k.val k.property).1]
        with x hm hc hk
      have hxr : S.ρ x ≠ p.val := fun heq => hkp (Subtype.ext (hk.symm.trans heq))
      have hnotN : x ∉ S.rootNeighborhood p := fun hN => not_le_of_gt hN.2 hm.2
      exact fun h => h.elim (fun h => h.elim (fun h => hxr h) hc) hnotN
    have hle : S.originalAtomMass k ≤ μ.real O :=
      ENNReal.toReal_mono (measure_ne_top μ _)
        (measure_mono_ae ((ae_restrict_iff' (S.hfibers k.val k.property).1).mp hK))
    have hO : μ.real O = 1 - (R.height + μ.real (S.rootNeighborhood p)) := by
      rw [measureReal_compl ((S.hfibers p.val p.property).1.union
        (R.singleton_measurableSet_source p hp) |>.union (S.measurableSet_rootNeighborhood p)),
        probReal_univ, R.one_center_core_mass p hp]
    have hrow := middle_stationary_row_le_neighborhood (S := S) hW hd hgap p
    obtain ⟨_, _, _, hct⟩ := R.endpoint_credit hW hd hgap
    obtain ⟨hΔ, i, _, _, hi, _, hreserve, _⟩ :=
      S.exists_original_atomic_square_reserve hW hd hgap
    have heq : i = k := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
    subst i
    have hsquare : (S.originalAtomMass k) ^ 2 ≤ ∑' i, (S.originalAtomMass i) ^ 2 := by
      have hh := Summable.sum_le_tsum (s := {k})
        (fun i _ => sq_nonneg (S.originalAtomMass i)) S.originalAtomMass_sq_summable
      simpa using hh
    have hl := MiddleE2Parameter.multiplier_mem hq
    have hell : 0 ≤ -m := by rw [hm, neg_neg]; linarith [hl.1]
    have hforward : 2 * (c - m * d) + m ≤
        (2 - LowerE2Scalar.multiplier q) * (S.originalAtomMass k) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hsquare hell
      have heq : 2 - LowerE2Scalar.multiplier q = 2 + m := by linarith
      rw [heq]
      nlinarith only [hh, hreserve]
    have hrow' : (1 + LowerE2Scalar.multiplier q) *
        (S.originalAtomMass k + R.height) ≤ 1 - (2 * (c - m * d) + m) := by
      have heq : 1 + LowerE2Scalar.multiplier q = 1 - m := by linarith
      rw [heq]
      have hmul := mul_le_mul_of_nonneg_left (show S.originalAtomMass k + R.height ≤
        1 - μ.real (S.rootNeighborhood p) by linarith)
        (show 0 ≤ 1 - m by linarith)
      linarith
    exact MiddleE2Parameter.not_extra_hole hq rfl hgamma (hvalue ▸ hgap)
      (S.originalAtomMass_summable.1 k) R.height_pos.le hct.le hforward hrow'
  · right
    filter_upwards [hjoined, ae_restrict_mem (S.hfibers k.val k.property).1] with x hx hk
    have hxr : S.ρ x ≠ p.val := fun heq => hkp (Subtype.ext (hk.symm.trans heq))
    exact ⟨hxr, lt_of_not_ge (fun h => hx ⟨hxr, h⟩)⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c q : ℝ}

/-- The actual middle-E2 entry. On `1/10 < q < 1/5`, the same selected
original model has its own multiplier above `9/11`, density above one
third, and an actual one-center reverse recovery with positive entire
source. Its internally selected unique largest original common peak is
not the head, keeps its full atomic-square reserve, and lies in the source
with its exact private row or is joined to the head. Two-center and
empty-source exits are discharged; no geometry is an input. -/
theorem exists_middle_e2_one_center_entry (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    m = -LowerE2Scalar.multiplier q ∧ 9 / 11 < LowerE2Scalar.multiplier q ∧
      LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m ∧ 1 / 3 < d ∧
      ∃ (R : S.ReverseRecovery) (p k : S.I), R.plateau = {p} ∧
        0 < μ (S.reverseCompulsorySource {p}) ∧ k ≠ p ∧
        S.IsCommonForwardPeak d c k ∧ 0 < S.originalAtomMass k ∧
        (∀ j : S.I, j ≠ k → S.originalAtomMass j < S.originalAtomMass k) ∧
        (2 * (c - m * d) + m + (-m) * (∑' j, (S.originalAtomMass j) ^ 2) ≤
          2 * (S.originalAtomMass k) ^ 2) ∧
        (((∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.reverseCompulsorySource {p}) ∧
            ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
              adjacencyKernel W z.1 z.2 =
                if S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val then 0 else 1) ∨
          ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood p) := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hl := MiddleE2Parameter.multiplier_mem hq
  have hthird : 1 / 3 < d := by
    rw [hdq]
    linarith [MiddleE2Parameter.missingMass_lt_third hq]
  refine ⟨hm, hl.1, hgamma, hthird, ?_⟩
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  have hle := R.card_le_two_of_neg_multiplier_ge_two_thirds hW hd hgap
    (by rw [hm, neg_neg]; linarith [hl.1])
  have hpos := Finset.card_pos.mpr R.plateau_nonempty
  have hcard : R.plateau.card = 1 := by
    by_contra hne
    exact R.no_e2_two_center hW ⟨hq.1.le, by linarith [hq.2]⟩ hdq hvalue hderiv hgap hglobal
      (by omega)
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  have hsource : 0 < μ (S.reverseCompulsorySource {p}) := by
    apply pos_iff_ne_zero.mpr
    intro hnull
    exact R.no_e2_one_center_empty_source p hp hW ⟨hq'.1, by linarith [hq.2]⟩ hdq hvalue
      hderiv hgap hglobal (by rw [hp]; exact hnull)
  obtain ⟨_, k, hA, _, hpeak, hlargest, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hkp := R.middle_peak_ne_head hW p hp hsource k hpeak
  refine ⟨R, p, k, hp, hsource, hkp, hpeak, hA, hlargest, hreserve, ?_⟩
  rcases R.middle_e2_one_center_peak_location hW hq hdq hvalue hderiv hgap hglobal
      p k hp hkp hpeak with hsrc | hjoin
  · exact Or.inl ⟨hsrc, R.middle_source_fiber_private_row k p hW hd hgap hp hsrc⟩
  · exact Or.inr hjoin

end Erdos1017.CappedModel.SelectedHighLowStructure

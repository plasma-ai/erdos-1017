module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleOffPairThird
public import Erdos1017.Exclusions.Common.Universal.UniversalDeficitCompleteParts
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpMissingCap
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpDiffuseCap
public import Erdos1017.Exclusions.E2.Middle.MiddleE2UniversalSmallHeadScalar
public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateRadius

/-!
# Compulsory sources for peaks off the saturated pair

Every original common peak off the saturated pair belongs to one of its entire
compulsory sources (`middle_e2_off_pair_compulsory`), and the compulsory
alternative keeps the private row: the peak misses exactly its own fiber and one
saturated head.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Encode the actual countable whole-row classes by positive natural labels;
zero records exactly the collapsed clique dust. -/
private theorem compulsory_part_code
    (S : SelectedHighLowStructure W m) :
    ∃ (e : S.I → ℕ) (label : Ω → ℕ), Function.Injective e ∧ Measurable label ∧
      (∀ x, label x = 0 ↔ S.collapsedPartLabel x = none) ∧
      (∀ i : S.I, S.collapsedPartLabel ⁻¹' {some i} =
        label ⁻¹' {e i + 1}) := by
  let : Countable S.I := S.hI.to_subtype
  let : MeasurableSpace (Option S.I) := ⊤
  obtain ⟨e, he⟩ := Countable.exists_injective_nat S.I
  let code : Option S.I → ℕ
    | none => 0
    | some i => e i + 1
  let label : Ω → ℕ := code ∘ S.collapsedPartLabel
  have hlabel : Measurable label :=
    (measurable_of_countable code).comp S.measurable_collapsedPartLabel
  refine ⟨e, label, he, hlabel, ?_, ?_⟩
  · intro x
    cases h : S.collapsedPartLabel x with
    | none => simp [label, code, h]
    | some i => simp [label, code, h]
  · intro i
    ext x
    change (S.collapsedPartLabel x = some i) ↔ label x = e i + 1
    cases h : S.collapsedPartLabel x with
    | none => simp [label, code, h]
    | some j =>
        simp only [label, Function.comp_apply, h, code, Option.some.injEq]
        constructor
        · intro hji
          rw [hji]
        · intro heq
          exact he (by omega)

private theorem compulsory_tupleCharge_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hsym : ∀ a b, Y a b = Y b a) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hsym y x, hsym z x, hsym z y]
  ring

private theorem compulsory_ae_root_triangle (S : SelectedHighLowStructure W m) (r : S.I)
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
  rw [compulsory_tupleCharge_three Y x p.1 p.2 (PhysicalRepresentative.charge_symm W m),
    (hy hx).2, (hz hx).2] at hbound
  exact hbound

/-- The entire source of one saturated head is joined to the other head.
This is a source-membership fact, without a universal-head premise. -/
theorem ae_compulsory_source_joined_other_head
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ x ∂μ, x ∈ S.reverseCompulsorySource {p} → x ∈ S.rootNeighborhood r := by
  have hel := hpair.head_eligibleReverseAtom hW hd hgap hell
  filter_upwards [S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell]
    with x hx hs
  have hne : S.ρ x ≠ r.val := fun h => hx hs (Or.inl (Or.inl h))
  refine ⟨hne, ?_⟩
  by_contra hn
  have hmem : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val :=
    ⟨hne, le_of_not_gt hn⟩
  exact hpair.1 (Finset.mem_singleton.mp (hs.2.2.2 r hel hmem))

private theorem compulsory_deficit_pair
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (e : S.I → ℕ) (label : Ω → ℕ)
    (hcode : ∀ i : S.I, S.collapsedPartLabel ⁻¹' {some i} = label ⁻¹' {e i + 1}) :
    ∀ᵐ z ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
        (μ.restrict (S.reverseCompulsorySource {p})),
      (label z.1 = 0 ∨ label z.2 = 0 ∨ label z.1 ≠ label z.2) →
        1 + m ≤ S.universalRootDeficit r z.1 + S.universalRootDeficit r z.2 := by
  let source := S.reverseCompulsorySource {p}
  let ν := μ.restrict source
  have hνμ : ν.prod ν ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hsub : source ⊆ S.half true := fun _ hx => Or.inl hx.1
  have hhalf := ae_mono (Measure.prod_mono (Measure.restrict_mono hsub le_rfl)
    (Measure.restrict_mono hsub le_rfl)) (S.ae_collapsed_half_support hW hd hgap true)
  have hjoined : ∀ᵐ x ∂ν, x ∈ S.rootNeighborhood r := by
    filter_upwards [ae_restrict_of_ae (S.ae_compulsory_source_joined_other_head
      r p hpair hW hd hgap hell), ae_restrict_mem
        (S.measurableSet_reverseCompulsorySource {p})] with x hx hs
    exact hx hs
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [hhalf, Measure.quasiMeasurePreserving_fst.ae hjoined,
    Measure.quasiMeasurePreserving_snd.ae hjoined,
    ae_mono hνμ (S.compulsory_ae_root_triangle r hW hd hgap),
    ae_mono hνμ (PhysicalRepresentative.adjacency_moment_ae_eq W m hs),
    ae_mono hνμ (PhysicalRepresentative.charge_ae_eq W m hs),
    ae_mono hνμ hW.moment_mem] with z ha hx hy ht hphys hcharge hmem hcross
  have hlabels : S.collapsedPartLabel z.1 ≠ S.collapsedPartLabel z.2 ∨
      S.collapsedPartLabel z.1 = none := by
    by_contra hn
    push Not at hn
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hn.2
    have hxi : z.1 ∈ label ⁻¹' {e j + 1} := (hcode j) ▸ hj
    have hyi : z.2 ∈ label ⁻¹' {e j + 1} := (hcode j) ▸ (hn.1.symm.trans hj)
    rcases hcross with hzero | hzero | hne
    · change label z.1 = e j + 1 at hxi
      omega
    · change label z.2 = e j + 1 at hyi
      omega
    · exact hne (hxi.trans hyi.symm)
  change adjacencyKernel W z.1 z.2 = _ at ha hphys
  rw [ite_eq_left hlabels] at ha
  have hA : PhysicalRepresentative.adjacency W m z.1 z.2 = true := by
    cases hh : PhysicalRepresentative.adjacency W m z.1 z.2 <;> simp_all
  have htri := ht hx hy hA
  have hY : m ≤ chargeKernel W z.1 z.2 := by
    have hK := hmem.1
    rw [shiftedMoment_eq] at hK
    change 0 ≤ chargeKernel W z.1 z.2 - m * adjacencyKernel W z.1 z.2 at hK
    rw [ha] at hK
    linarith
  dsimp only [universalRootDeficit]
  linarith

/-- The actual entire source, including its diffuse part, pays half of
its mass beyond an upper bound on every restricted independent part. -/
theorem compulsory_source_deficit_lower_of_part_cap
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c C : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1) (hC : 0 ≤ C)
    (hcap : ∀ j : S.I,
      μ.real (S.reverseCompulsorySource {p} ∩ {x | S.ρ x = j.val}) ≤ C) :
    (1 + m) * (μ.real (S.reverseCompulsorySource {p}) - C) / 2 ≤
      ∫ x in S.reverseCompulsorySource {p}, 1 - S.rootChargeRow r x ∂μ := by
  let source := S.reverseCompulsorySource {p}
  obtain ⟨e, label, _, hlabel, hcode0, hcode⟩ := S.compulsory_part_code
  have hcell (n : ℕ) :
      (∃ j : S.I, {x | label x = n + 1} = {x | S.ρ x = j.val}) ∨
        {x | label x = n + 1} = ∅ := by
    by_cases hex : ∃ j : S.I, e j = n
    · obtain ⟨j, hj⟩ := hex
      left
      refine ⟨j, ?_⟩
      have hh := hcode j
      rw [S.collapsedPartLabel_fiber, hj] at hh
      exact hh.symm
    · right
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hn : S.collapsedPartLabel x ≠ none := by
        intro he
        have hz := (hcode0 x).mpr he
        change label x = n + 1 at hx
        omega
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hn
      have hc : x ∈ label ⁻¹' {e j + 1} := (hcode j) ▸ hj
      exact hex ⟨j, by change label x = e j + 1 at hc; change label x = n + 1 at hx; omega⟩
  have hmass (n : ℕ) : (μ.restrict source).real {x | label x = n + 1} ≤ C := by
    rcases hcell n with ⟨j, hj⟩ | hempty
    · rw [hj, measureReal_restrict_apply (S.hfibers j.val j.property).1, Set.inter_comm]
      exact hcap j
    · rw [hempty, measureReal_empty]
      exact hC
  have hconstant (n : ℕ) : ∃ t : ℝ,
      ∀ᵐ x ∂(μ.restrict source).restrict {x | label x = n + 1},
        S.universalRootDeficit r x = t := by
    rcases hcell n with ⟨j, hj⟩ | hempty
    · rw [hj, Measure.restrict_restrict (S.hfibers j.val j.property).1, Set.inter_comm]
      refine ⟨1 - S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl j), ?_⟩
      have hc : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
          S.universalRootDeficit r x =
            1 - S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl j) := by
        filter_upwards [S.ae_atomic_rootChargeRow r j hW hd hgap] with x hx
        exact congrArg (fun t : ℝ => 1 - t) hx
      exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hc
    · rw [hempty]
      exact ⟨0, by simp⟩
  have hδ : 0 < 1 + m := by linarith
  have hnonneg : ∀ᵐ x ∂μ.restrict source, 0 ≤ S.universalRootDeficit r x :=
    Eventually.of_forall (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  have hbound : ∀ᵐ x ∂μ.restrict source, S.universalRootDeficit r x ≤ 4 :=
    Eventually.of_forall (fun x => (S.universalRootDeficit_mem_Icc r x).2)
  have h := UniversalDeficit.complete_part_deficit_integral_lower source
    (S.measurableSet_reverseCompulsorySource {p}) label hlabel
    (S.universalRootDeficit r) (S.measurable_universalRootDeficit r) 4 hnonneg hbound
    (1 + m) C hδ hmass hconstant
    (S.compulsory_deficit_pair r p hpair hW hd hgap hell e label hcode)
  have hD : 0 ≤ ∫ x in source, S.universalRootDeficit r x ∂μ :=
    integral_nonneg_of_ae hnonneg
  change (1 + m) * (μ.real source - C) / 2 ≤
    ∫ x in source, S.universalRootDeficit r x ∂μ
  by_cases ha : μ.real source ≤ C
  · have hprod := mul_nonpos_of_nonneg_of_nonpos hδ.le (sub_nonpos.mpr ha)
    linarith
  · have hmin : (μ.real source - C) / 2 ≤ min (μ.real source / 2) (μ.real source - C) :=
      le_min (by linarith) (by linarith)
    have hscaled := (le_div_iff₀ hδ).mp (hmin.trans h)
    nlinarith

/-- A positive source atom misses the partner's entire original fiber. -/
private theorem compulsory_partner_mass_le_missing
    (S : SelectedHighLowStructure W m) (r p j : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hjp : j ≠ p)
    (hcell : 0 < μ (S.reverseCompulsorySource {p} ∩ {x | S.ρ x = j.val})) :
    S.originalAtomMass p ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
  let Ip : Set Ω := {x | S.ρ x = p.val}
  let Ij : Set Ω := {x | S.ρ x = j.val}
  let source : Set Ω := S.reverseCompulsorySource {p}
  let H : Set Ω := S.universalPartnerHoleRegion r p
  have hsourceH : ∀ᵐ x ∂μ.restrict (source ∩ Ij), x ∈ H := by
    filter_upwards [ae_restrict_of_ae
      (S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell),
      ae_restrict_mem ((S.measurableSet_reverseCompulsorySource {p}).inter
        (S.hfibers j.val j.property).1)] with x hx hmem
    exact hx hmem.1
  have hmissingJ : 0 < μ (Ij ∩ {x | p.val x ≤ 0}) := by
    have hsub : ∀ᵐ x ∂μ, x ∈ source ∩ Ij → x ∈ Ij ∩ {x | p.val x ≤ 0} := by
      have h := (ae_restrict_iff'
        ((S.measurableSet_reverseCompulsorySource {p}).inter
          (S.hfibers j.val j.property).1)).mp hsourceH
      filter_upwards [h] with x hx hcellmem
      have hH := hx hcellmem
      have hnotp : S.ρ x ≠ p.val := by
        intro hp
        exact hH (Or.inl (Or.inr hp))
      have hnotN : x ∉ S.rootNeighborhood p := fun hn => hH (Or.inr hn)
      exact ⟨hcellmem.2, le_of_not_gt (fun hp => hnotN ⟨hnotp, hp⟩)⟩
    exact lt_of_lt_of_le hcell (measure_mono_ae hsub)
  have hcross := KernelOperator.whole_row_cross_block_zero_of_positive_nonpositive
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ
    p.val j.val
    (S.hfibers p.val p.property).2.1 (S.hfibers j.val j.property).2.1
    (S.hfibers p.val p.property).2.2.2 (S.hfibers j.val j.property).2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
    (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun q hq => hq.symm)) hW.moment_mem
    (S.hfibers j.val j.property).1 hmissingJ
  have hsub : ∀ᵐ x ∂μ, x ∈ Ip →
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ j.val := by
    have h := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp hcross.2.1
    filter_upwards [h] with x hx hxp
    have hxzero : j.val x = 0 := hx hxp
    refine ⟨?_, by simp [hxzero]⟩
    intro hsame
    exact hjp (Subtype.ext (hsame.symm.trans hxp))
  change μ.real Ip ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono_ae hsub)

private theorem compulsory_part_mass_bound
    (S : SelectedHighLowStructure W m) (i r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d c ρ : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hnot : ¬S.fiberCompulsoryPredicate i {p}) (hp : S.originalAtomMass p ≤ ρ)
    (hcap : ∀ j : S.I, j ≠ i →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H) →
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤ ρ)
    (j : S.I) :
    μ.real (S.reverseCompulsorySource {p} ∩ {x | S.ρ x = j.val}) ≤
      ρ - S.originalAtomMass p := by
  let source := S.reverseCompulsorySource {p}
  let Ij := {x | S.ρ x = j.val}
  by_cases hcell : 0 < μ (source ∩ Ij)
  · have hpredAE : ∀ᵐ x ∂μ.restrict (source ∩ Ij),
        x ∈ source ↔ S.fiberCompulsoryPredicate j {p} :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
        (S.ae_compulsorySource_iff_fiberPredicate j {p} hW)
    obtain ⟨x, hx, heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcell.ne' hpredAE
    have hpred := heq.mp hx.1
    have hji : j ≠ i := fun he => hnot (he ▸ hpred)
    have hsourceJ : ∀ᵐ x ∂μ.restrict Ij, x ∈ source :=
      (S.ae_compulsorySource_iff_fiberPredicate j {p} hW).mono
        (fun _ hh => hh.mpr hpred)
    have hhigh := hsourceJ.mono (fun _ hh => hh.1)
    have hjp : j ≠ p := by
      intro he
      exact (S.mem_singleton_compulsorySource_missing p hx.1).1
        (hx.2.trans (congrArg Subtype.val he))
    have hmissing := S.compulsory_partner_mass_le_missing r p j hpair hW hd hgap
      hell hjp hcell
    have hc := hcap j hji hhigh
    have hle : μ.real (source ∩ Ij) ≤ S.originalAtomMass j :=
      measureReal_mono Set.inter_subset_right
    linarith
  · have hz : μ (source ∩ Ij) = 0 := le_antisymm (le_of_not_gt hcell) zero_le
    change μ.real (source ∩ Ij) ≤ _
    rw [Measure.real, hz, ENNReal.toReal_zero]
    linarith

/-- Avoiding both entire saturated sources forces any valid common cap
on their HIGH parts and original heads to exceed the source-score threshold.
The two deficits and the complement use one original score budget. -/
theorem source_avoidance_cap_lower_bound
    (S : SelectedHighLowStructure W m) (i r u : S.I)
    (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    {d c ρ : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hrnot : ¬S.fiberCompulsoryPredicate i {r})
    (hunot : ¬S.fiberCompulsoryPredicate i {u})
    (hrcap : S.originalAtomMass r ≤ ρ) (hucap : S.originalAtomMass u ≤ ρ)
    (hcap : ∀ j : S.I, j ≠ i →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H) →
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤ ρ) :
    (1 + S.originalAtomMass i) / 2 -
      (1 - m - 2 * (2 * (c - m * d))) / (1 + m) ≤ ρ := by
  let Ir := {x | S.ρ x = r.val}
  let Iu := {x | S.ρ x = u.val}
  let I := {x | S.ρ x = i.val}
  let SA := S.reverseCompulsorySource {r}
  let SB := S.reverseCompulsorySource {u}
  let O := (Ir ∪ Iu ∪ SA ∪ SB)ᶜ
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIu : MeasurableSet Iu := (S.hfibers u.val u.property).1
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hSA : MeasurableSet SA := S.measurableSet_reverseCompulsorySource {r}
  have hSB : MeasurableSet SB := S.measurableSet_reverseCompulsorySource {u}
  have hru : Disjoint Ir Iu := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hpair.1 (Subtype.ext (hx.symm.trans hy))
  have hdA : AEDisjoint μ (Ir ∪ Iu) SA := by
    change μ ((Ir ∪ Iu) ∩ SA) = 0
    rw [union_inter_distrib_right]
    exact measure_union_null (hpair.head_compulsorySource_null hW hd hgap hell {r})
      (hpair.symm.head_compulsorySource_null hW hd hgap hell {r})
  have hdB : AEDisjoint μ (Ir ∪ Iu ∪ SA) SB := by
    change μ ((Ir ∪ Iu ∪ SA) ∩ SB) = 0
    rw [union_inter_distrib_right, union_inter_distrib_right]
    apply measure_union_null
    · exact measure_union_null (hpair.head_compulsorySource_null hW hd hgap hell {u})
        (hpair.symm.head_compulsorySource_null hW hd hgap hell {u})
    · rw [(S.disjoint_singleton_compulsorySources r u hpair.1).inter_eq]
      exact measure_empty
  have hOmass : μ.real O = 1 -
      (S.originalAtomMass r + S.originalAtomMass u + μ.real SA + μ.real SB) := by
    rw [measureReal_compl (((hIr.union hIu).union hSA).union hSB),
      measureReal_union₀ hSB.nullMeasurableSet hdB,
      measureReal_union₀ hSA.nullMeasurableSet hdA, measureReal_union hru hIu, probReal_univ]
    rfl
  have hIO : ∀ᵐ x ∂μ.restrict I, x ∈ O := by
    filter_upwards [S.ae_compulsorySource_iff_fiberPredicate i {r} hW,
      S.ae_compulsorySource_iff_fiberPredicate i {u} hW, ae_restrict_mem hI]
      with x hr hu hx
    have hnr : S.ρ x ≠ r.val := fun h => hir (Subtype.ext (hx.symm.trans h))
    have hnu : S.ρ x ≠ u.val := fun h => hiu (Subtype.ext (hx.symm.trans h))
    exact fun h => h.elim (fun h => h.elim (fun h => h.elim hnr hnu)
      (fun h => hrnot (hr.mp h))) (fun h => hunot (hu.mp h))
  have hAO : S.originalAtomMass i ≤ μ.real O :=
    ENNReal.toReal_mono (measure_ne_top μ O)
      (measure_mono_ae ((ae_restrict_iff' hI).mp hIO))
  have hDA := S.compulsory_source_deficit_lower_of_part_cap u r hpair.symm hW hd hgap
    hell (by linarith only [hrcap])
    (S.compulsory_part_mass_bound i u r hpair.symm hW hd hgap hell hrnot hrcap hcap)
  have hDB := S.compulsory_source_deficit_lower_of_part_cap r u hpair hW hd hgap
    hell (by linarith only [hucap])
    (S.compulsory_part_mass_bound i r u hpair hW hd hgap hell hunot hucap hcap)
  have hbudget := hpair.entire_source_score_budget hW hd hgap hell
  change _ + _ + (1 + m) * μ.real O ≤ _ at hbudget
  have hδ : 0 < 1 + m := by linarith
  have hAmul := mul_le_mul_of_nonneg_left hAO hδ.le
  have htarget : ((1 + S.originalAtomMass i) / 2 - ρ) * (1 + m) ≤
      1 - m - 2 * (2 * (c - m * d)) := by
    dsimp only [SA, SB] at hOmass
    nlinarith [hOmass]
  have hdiv := (le_div_iff₀ hδ).mpr htarget
  linarith

private theorem offpair_ratio_le_third {q : ℝ}
    (hq : q ∈ Icc (1 / 10 : ℝ) (157 / 1000)) : MiddleE2OffPair.ratioCap q ≤ 1 / 3 := by
  have hR := LowerE2Scalar.denominator_pos (show 0 ≤ q by linarith [hq.1])
  unfold MiddleE2OffPair.ratioCap
  rw [div_le_iff₀ (by positivity)]
  have hprod := mul_nonneg (sub_nonneg.mpr hq.2)
    (show 0 ≤ 13 - 2 * q - 2 * (157 / 1000 : ℝ) by linarith [hq.2])
  unfold LowerE2Scalar.denominator
  nlinarith

private theorem offpair_ratio_lt_two_fifths {q : ℝ}
    (hq : q ∈ Icc (1 / 10 : ℝ) (1 / 5)) : MiddleE2OffPair.ratioCap q < 2 / 5 := by
  have hR := LowerE2Scalar.denominator_pos (show 0 ≤ q by linarith [hq.1])
  unfold MiddleE2OffPair.ratioCap
  rw [div_lt_iff₀ (by positivity)]
  unfold LowerE2Scalar.denominator
  nlinarith [sq_nonneg q, hq.2]

private theorem offpair_sharp_neutral_sq_bound (S : SelectedHighLowStructure W m)
    (i j : S.I) (hji : j ≠ i) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hneutral : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.N)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3)) (hell : 2 / 3 ≤ -m) :
    2 * (c - m * d) + m + (-m - 2 / 3) * (S.originalAtomMass j) ^ 2 ≤
      (-1 + 8 * S.originalAtomMass i - (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hret := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  have hmassJ := hq.classMass_eq_original_of_neutral j hneutral
  have hp := hq.classMass_properties
  have hbdd : BddAbove (insert (0 : ℝ) (range (S.forwardClassMass q))) := by
    refine ⟨1, ?_⟩
    rintro y (rfl | ⟨k, rfl⟩)
    · norm_num
    · exact (hp.1 k).2
  have hmax (k : S.I) : S.forwardClassMass q k ≤ S.forwardClassMass q i := by
    rw [← (hpeak q hq).2.1]
    exact le_csSup hbdd (Or.inr (mem_range_self k))
  obtain ⟨_, _, _, _, hmiddle, _⟩ :=
    hq.endpoint_sharp_selector_bounds hW hd hgap i (hpeak q hq).1 hmax
  rw [hret] at hmiddle
  let A := S.originalAtomMass i
  have hApos : 0 < A := by dsimp only [A]; linarith [hA.1]
  have hT : (1 - A) / A ∈ Icc (2 : ℝ) 3 := by
    constructor
    · apply (le_div_iff₀ hApos).mpr
      linarith [hA.2]
    · apply (div_le_iff₀ hApos).mpr
      linarith [hA.1]
  have hcost := hmiddle hT
  have hid : 2 * (A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12) -
      (-m) * A ^ 2 = (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 := by
    field_simp
    ring
  have hsq : Summable (fun k => (S.forwardClassMass q k) ^ 2) :=
    hp.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => by
      nlinarith only [(hp.1 k).1, (hp.1 k).2])
  have htwo := (hsq.sum_le_tsum {i, j} (fun _ _ => sq_nonneg _)).trans_eq
    (hq.missing_density_eq_classMass_sq hW hd hgap).symm
  rw [Finset.sum_pair hji.symm, hret, hmassJ] at htwo
  have htail := mul_le_mul_of_nonneg_left htwo (sub_nonneg.mpr hell)
  have henergy := hq.energy_nonnegative hW hd hgap
  have hbudget := hq.endpoint_budget hW
  change 2 * (c - m * d) + m + (-m - 2 / 3) * (S.originalAtomMass j) ^ 2 ≤ _
  dsimp only [A, originalAtomMass] at hid hcost ⊢
  nlinarith only [hcost, hid, henergy, hbudget, htail]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Every original common peak off the actual saturated pair belongs to
one of its entire compulsory sources. All source, dust and LOW-tail caps
are obtained on the same selected model. -/
theorem middle_e2_off_pair_compulsory (S : SelectedHighLowStructure W m)
    (i r u : S.I) (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i) :
    S.fiberCompulsoryPredicate i {r} ∨ S.fiberCompulsoryPredicate i {u} := by
  by_contra hn
  push Not at hn
  obtain ⟨hrnot, hunot⟩ := hn
  have hqclosed : q ∈ Icc (1 / 10 : ℝ) (1 / 5) := ⟨hq.1.le, hq.2.le⟩
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hneg : -m = LowerE2Scalar.multiplier q := by linarith
  have hδ : 0 < 1 + m := by linarith [hell.2]
  have hthird := S.middle_e2_off_pair_peak_lt_third i r u hir hiu hpair hW hq
    hdq hvalue hderiv hgap hglobal hpeak
  have hratio := hpair.middle_e2_score_ratio_bounds hW hqclosed hdq hvalue hderiv hgap hglobal
  obtain ⟨hDelta, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
  obtain ⟨j, hApos, hside, hj, _, _, _, hhigh, hneutral, htail⟩ :=
    S.exists_conditional_missing_mass_cap hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hh hl => disjoint_left.mp S.hpartition.2.2.2.2.1 hh hl)
    · exact hN.mono (fun _ hh hl => disjoint_left.mp S.hpartition.2.2.2.2.2.2 hl hh)
  by_cases hsmall : q ≤ 157 / 1000
  · have hintercept := hW.e2_intercept_guard ⟨hq'.1, hq.2.le⟩ hdq hgap hglobal
    have hAsq : (S.originalAtomMass i) ^ 2 < (1 / 3 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hthird hApos.le (by norm_num)
    have hscaled := mul_lt_mul_of_pos_left hAsq hδ
    have hguard : 2 * (1 + m) * (S.originalAtomMass i) ^ 2 <
        2 * (c - m * d) + m := by nlinarith
    obtain ⟨hρA, _, hlow⟩ := htail hguard
    have hatoms : ∀ j : S.I, j ≠ i →
        S.originalAtomMass j ≤ missingMassCapRadius d c m (S.originalAtomMass i) := by
      intro j hji
      rcases S.hfiberClass j j.property with hH | hL | hN
      · have h := hhigh j hji hH
        have hz : 0 ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) :=
          measureReal_nonneg
        linarith
      · exact hlow j hL
      · exact hneutral j hji hN
    have hsource := S.source_avoidance_cap_lower_bound i r u hir hiu hpair hW hd hgap
      hell.2 hrnot hunot (hatoms r hir.symm) (hatoms u hiu.symm) hhigh
    have hAr := hpair.off_source_atom_mass_le_score_ratio i hir hiu hW hd hgap
      hell.2 hrnot hunot
    have hrthird := offpair_ratio_le_third ⟨hq.1.le, hsmall⟩
    linarith [hratio.2.1]
  · have hqsharp : q ∈ Icc (157 / 1000 : ℝ) (1 / 5) :=
      ⟨(lt_of_not_ge hsmall).le, hq.2.le⟩
    obtain ⟨hDelta', k, hquarter, _, hk, _, _, _, _⟩ :=
      S.exists_original_forward_quarter_peak hW ⟨by linarith [hqsharp.1], hq.2.le⟩
        hdq hgap hglobal
    have hki : k = i := (hk S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta'
    subst k
    have hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3) :=
      ⟨hquarter.le, hthird.le⟩
    have hell23 : 2 / 3 ≤ -m := by
      rw [hneg]
      unfold LowerE2Scalar.multiplier
      rw [le_div_iff₀ (by linarith [hq.1])]
      linarith [hq.2]
    have hatomic : ∀ j : S.I, j ≠ i →
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H) →
        S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) ≤
          4 / 25 := by
      intro j hji hjH
      have hb := S.middle_high_atom_closed_missing_sq_bound i j hji hW hd hgap hpeak
        hnonlow hjH hA hell23
      rw [hneg] at hb
      exact (MiddleE2UniversalSmallHead.closed_missing_lt_four_twentyfifths
        hqsharp hgamma hb).le
    have hmargin := MiddleE2UniversalSmallHead.selector_margin (A := S.originalAtomMass i) hqsharp
    rw [← hneg] at hmargin
    have hdiffuse := S.ae_middle_diffuse_high_outside_le i hW hd hgap hpeak hnonlow hA
      hell23 (R := 4 / 25) (by norm_num) (by linarith [hA.1])
      (by linarith [hgamma])
    have hrecipients := S.ae_nonpeak_high_outside_le hW i (4 / 25) hatomic hdiffuse
    obtain ⟨f, hf, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
    have hatoms : ∀ j : S.I, j ≠ i → S.originalAtomMass j ≤ 4 / 25 := by
      intro j hji
      rcases S.hfiberClass j j.property with hH | hL | hN
      · have h := hatomic j hji hH
        have hz : 0 ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) :=
          measureReal_nonneg
        linarith
      · exact hf.low_atom_mass_le_of_recipient_bound hW i (4 / 25) havoid hrecipients j hL
      · have hb := S.offpair_sharp_neutral_sq_bound i j hji hW hd hgap hpeak hnonlow hN hA hell23
        rw [hneg] at hb
        exact (MiddleE2UniversalSmallHead.closed_missing_lt_four_twentyfifths
          hqsharp hgamma hb).le
    have hsource := S.source_avoidance_cap_lower_bound i r u hir hiu hpair hW hd hgap
      hell.2 hrnot hunot (hatoms r hir.symm) (hatoms u hiu.symm) hatomic
    have hrcap := offpair_ratio_lt_two_fifths hqclosed
    linarith [hratio.2.1]

/-- The compulsory alternative retains the literal original private row:
the peak misses exactly its own fiber and one saturated head. -/
theorem middle_e2_off_pair_private_row (S : SelectedHighLowStructure W m)
    (i r u : S.I) (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i) :
    ∃ p : S.I, (p = r ∨ p = u) ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p}) ∧
      ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val → adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1 := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hchoice : ∃ p : S.I, (p = r ∨ p = u) ∧ S.fiberCompulsoryPredicate i {p} := by
    rcases S.middle_e2_off_pair_compulsory i r u hir hiu hpair hW hq hdq hvalue
      hderiv hgap hglobal hpeak with hr | hu
    · exact ⟨r, Or.inl rfl, hr⟩
    · exact ⟨u, Or.inr rfl, hu⟩
  obtain ⟨p, hp, hpred⟩ := hchoice
  have hsource := (S.ae_compulsorySource_iff_fiberPredicate i {p} hW).mono
    (fun _ hx => hx.mpr hpred)
  exact ⟨p, hp, hsource, S.ae_compulsory_fiber_private_row i p hW hd hgap hsource⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

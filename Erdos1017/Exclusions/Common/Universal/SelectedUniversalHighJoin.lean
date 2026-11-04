module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPrice

/-!
# Join of high partner holes with good common vertices

A partner hole in the high region joins every good common vertex in the high
region, with both the missing-row and class exclusions derived in the same
model.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Whole-row cross blocks make the partner's shifted row constant on
each positive original atom, modulo the product law. -/
private theorem ae_partner_row_eq_on_sameAtom_for_high_join
    (S : SelectedHighLowStructure W m) (p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ q ∂μ.prod μ, q ∈ S.sameAtomRelation → p.val q.1 = p.val q.2 := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ j : S.I,
      S.ρ x = j.val →
        ∃ a : ℝ, p.val x = a ∧
          ∀ᵐ y ∂μ.restrict {y | S.ρ y = j.val}, p.val y = a := by
    apply ae_all_iff.mpr
    intro j
    obtain ⟨a, _, hpa, _, _⟩ := KernelOperator.exists_whole_row_cross_block
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ p.val j.val
      (S.hfibers p.val p.property).2.1 (S.hfibers j.val j.property).2.1
      (S.hfibers p.val p.property).2.2.2 (S.hfibers j.val j.property).2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
      (chargeKernel_measurable W)
      ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) hW.moment_mem
    exact ((ae_restrict_iff' (S.hfibers j.val j.property).1).mp hpa).mono
      (fun _ hx hmem => ⟨a, hx hmem, hpa⟩)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hall,
    Measure.quasiMeasurePreserving_snd.ae hall] with q hx hy hsame
  let j : S.I := ⟨S.ρ q.1, hsame.2⟩
  obtain ⟨a, hxa, hyae⟩ := hx j rfl
  have hboth : ∀ᵐ z ∂μ, S.ρ z = j.val → p.val z = a :=
    (ae_restrict_iff' (S.hfibers j.val j.property).1).mp hyae
  have hya := hy j hsame.1.symm
  obtain ⟨b, hyb, hybae⟩ := hya
  have hba : a = b := by
    obtain ⟨z, hz, hza, hzb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers j.val j.property).2.1.ne'
      ((ae_restrict_of_ae hboth).and hybae |>.and
        (ae_restrict_mem (S.hfibers j.val j.property).1))
    exact (hza.1 hz).symm.trans hza.2
  rw [hxa, hyb, hba]

/-- An original HIGH partner hole joins every HIGH good common vertex.
Both the missing-row and class exclusions are derived in the same model. -/
theorem ae_universalHole_highGood_join
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalHighGoodRegion r p d c →
        adjacencyKernel W q.1 q.2 = 1 := by
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hhigh := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell)
  have hzeroRow := (ae_restrict_iff' hH).mp
    (S.ae_partner_row_zero_on_universalHole r p hW)
  have hposRow := (ae_restrict_iff' hU).mp
    (S.ae_partner_row_pos_on_universalCommon r p)
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hhigh,
    Measure.quasiMeasurePreserving_fst.ae hzeroRow,
    Measure.quasiMeasurePreserving_snd.ae hposRow,
    S.ae_partner_row_eq_on_sameAtom_for_high_join p hW,
    S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    S.hrelation, hW.moment_mem, hs]
    with q hhigh hzeroRow hposRow hsame hzero hrelation hnonneg hsupport hx hy
  have hxH : q.1 ∈ S.H := hhigh hx
  have hyU : q.2 ∈ U := hy.1.1
  have hyH : q.2 ∈ S.H := hy.2
  have hnotSame : q ∉ S.sameAtomRelation := by
    intro hz
    linarith [hsame hz, hzeroRow hx, hposRow hyU]
  have hnotRelation : q ∉ actualZeroRelation W m S.ρ := by
    intro hz
    rcases hrelation hz with h | h
    · exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hyH h.2.1).elim
    · exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxH h.2.1).elim
  have hnotK : shiftedKernel W m q.1 q.2 ≠ 0 := by
    intro hk
    rcases hzero.mp hk with h | h
    · exact hnotSame h
    · exact hnotRelation h
  have hKpos : 0 < shiftedKernel W m q.1 q.2 :=
    lt_of_le_of_ne hnonneg.1 (Ne.symm hnotK)
  change 0 < shiftedMoment W m q at hKpos
  have heq : adjacencyKernel W q.1 q.2 =
      if 0 < shiftedMoment W m q then 1 else 0 := hsupport
  simpa only [ite_eq_left hKpos] using heq

end Erdos1017.CappedModel.SelectedHighLowStructure

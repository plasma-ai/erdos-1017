module

public import Erdos1017.SelectedModel.Flows.OriginalForwardPeakLargest
public import Erdos1017.Exclusions.Common.Flows.FullForwardFiniteRerouting

/-!
# Receivers for low atoms of a full forward flow

The region `lowAtomRecipientRegion` consists of the high points missing a given
atom, with the peak fiber removed; full supply on a positive low atom forces
this region positive outside every avoided atom, so each low atom has a positive
receiver outside the avoided peak.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- Original HIGH points missing a specified original atom, with the
specified original peak fiber removed. -/
def lowAtomRecipientRegion (S : SelectedHighLowStructure W m) (i j : S.I) : Set Ω :=
  (S.H ∩ KernelOperator.wholeFiberMissingSet S.ρ j) \ {x | S.ρ x = i}

theorem measurableSet_lowAtomRecipientRegion (S : SelectedHighLowStructure W m) (i j : S.I) :
    MeasurableSet (S.lowAtomRecipientRegion i j) :=
  (S.hpartition.1.inter (KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ j)).diff
    (S.hfibers i i.property).1

/-- The actual original whole source row supplies the missing rectangle
for every recipient in its canonical missing region. -/
theorem lowAtomRecipientRegion_rectangle (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (i j : S.I)
    (hjL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j}, x ∈ S.L) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.lowAtomRecipientRegion i j → S.ρ p.2 = j →
      p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L := by
  have hrows := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_kernel_eq_fiber_row j j.property)
  have hL := (ae_restrict_iff' (S.hfibers j j.property).1).mp hjL
  filter_upwards [hrows, shiftedMoment_symm W m, hW.moment_mem,
    Measure.quasiMeasurePreserving_snd.ae hL] with p hr hs hn hl hx hy
  have he : shiftedKernel W m p.1 p.2 = (j : Lp ℝ 2 μ) p.1 := hs.symm.trans (hr hy)
  have hz : shiftedKernel W m p.1 p.2 = 0 := le_antisymm (he.trans_le hx.1.2.2) hn.1
  exact ⟨⟨hz, fun h => hx.1.2.1 (h.trans hy)⟩, hx.1.1, hl hy⟩

/-- Actual full supply on a positive LOW atom forces a positive recipient
region outside every atom avoided by the same actual full flow. -/
theorem IsFullForwardFlow.positive_lowAtomRecipientRegion
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    (i j : S.I) (hjL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j}, x ∈ S.L)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    0 < μ (S.lowAtomRecipientRegion i j) := by
  have hrows := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_kernel_eq_fiber_row j j.property)
  have hsupport : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.2 = j →
      p.1 ∈ S.lowAtomRecipientRegion i j := by
    filter_upwards [hq.support, havoid, hrows, shiftedMoment_symm W m]
      with p hs ha hr hsym hq0 hy
    have hz := (hs hq0).1
    refine ⟨⟨(hs hq0).2.1, ⟨fun h => hz.2 (h.trans hy.symm), ?_⟩⟩, ha hq0⟩
    have he : (j : Lp ℝ 2 μ) p.1 = shiftedKernel W m p.2 p.1 := (hr hy).symm
    exact le_of_eq (he.trans (hsym.trans hz.1))
  by_contra hpos
  have hnull : μ (S.lowAtomRecipientRegion i j) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hpos)
  have hnot : ∀ᵐ x ∂μ, x ∉ S.lowAtomRecipientRegion i j := by
    rw [ae_iff]
    have he : {x | ¬x ∉ S.lowAtomRecipientRegion i j} = S.lowAtomRecipientRegion i j := by
      ext x
      simp only [mem_ofPred_eq, not_not]
    rw [he]
    exact hnull
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hsupport
  obtain ⟨y, hy, hyL, hys, hyp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j j.property).2.1.ne'
    (hjL.and ((ae_restrict_of_ae hq.supply).and
      (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hswap))))
  have hz : MissingFlow.supply μ q y = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hyp, hnot] with x hx hn
    by_contra hne
    exact hn (hx hne hy)
  rw [indicator_of_mem hyL] at hys
  linarith

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A positive actual HIGH subset of a whole fiber forces that entire
positive fiber to be in the HIGH alternative of the original classification. -/
theorem high_fiber_of_positive_high_subset (S : SelectedHighLowStructure W m)
    (k : S.I) (C : Set Ω) (hpos : 0 < μ C) (hCH : C ⊆ S.H)
    (hCk : C ⊆ {x | S.ρ x = k}) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H := by
  rcases S.hfiberClass k k.property with hH | hL | hN
  · exact hH
  · have hl := (ae_restrict_iff' (S.hfibers k k.property).1).mp hL
    obtain ⟨x, hx, hxl⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
      (ae_restrict_of_ae hl)
    exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hCH hx) (hxl (hCk hx)))
  · have hn := (ae_restrict_iff' (S.hfibers k k.property).1).mp hN
    obtain ⟨x, hx, hxn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
      (ae_restrict_of_ae hn)
    exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 (hCH hx) (hxn (hCk hx)))

/-- Each original LOW atom has an actual positive receiver outside the
avoided peak. Atomic receivers may be positive subsets of their fibers;
this already transfers their full redirected source mass into that class. -/
theorem IsFullForwardFlow.exists_low_atom_receiver
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (i j : S.I)
    (hjL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j}, x ∈ S.L)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    ∃ C : Set Ω, MeasurableSet C ∧ 0 < μ C ∧ C ⊆ S.H ∧
      Disjoint C {x | S.ρ x = i} ∧
      ((∃ k : S.I, k ≠ i ∧ C ⊆ {x | S.ρ x = k} ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H)) ∨ C ⊆ S.D) ∧
      (∀ᵐ p ∂μ.prod μ, p.1 ∈ C → S.ρ p.2 = j →
        p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L) := by
  let : Countable S.I := S.hI.to_subtype
  let R := S.lowAtomRecipientRegion i j
  have hR := S.measurableSet_lowAtomRecipientRegion i j
  have hRp := hq.positive_lowAtomRecipientRegion i j hjL havoid
  have hRH : R ⊆ S.H := fun _ hx => hx.1.1
  have hRi : Disjoint R {x | S.ρ x = i} := Set.disjoint_left.mpr (fun _ hx hi => hx.2 hi)
  have hrect := S.lowAtomRecipientRegion_rectangle hW i j hjL
  by_cases hatom : ∃ k : S.I, 0 < μ (R ∩ {x | S.ρ x = k})
  · obtain ⟨k, hk⟩ := hatom
    let C := R ∩ {x | S.ρ x = k}
    have hCk : C ⊆ {x | S.ρ x = k} := inter_subset_right
    have hCR : C ⊆ R := inter_subset_left
    have hki : k ≠ i := by
      intro he
      obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hk.ne'
      exact hx.1.2 (he ▸ hx.2)
    refine ⟨C, hR.inter (S.hfibers k k.property).1, hk, hCR.trans hRH,
      hRi.mono_left hCR, Or.inl ⟨k, hki, hCk,
        S.high_fiber_of_positive_high_subset k C hk (hCR.trans hRH) hCk⟩, ?_⟩
    exact hrect.mono (fun _ hp hx hy => hp (hCR hx) hy)
  · have hnull (k : S.I) : μ (R ∩ {x | S.ρ x = k}) = 0 :=
      nonpos_iff_eq_zero.mp (le_of_not_gt (fun h => hatom ⟨k, h⟩))
    have hno : ∀ᵐ x ∂μ, ∀ k : S.I, x ∈ R → S.ρ x ≠ k := by
      apply ae_all_iff.mpr
      intro k
      rw [ae_iff]
      have he : {x | ¬(x ∈ R → S.ρ x ≠ k)} = R ∩ {x | S.ρ x = k} := by
        ext x
        simp only [mem_ofPred_eq, not_imp, not_not, mem_inter_iff]
      rw [he]
      exact hnull k
    have hRD : ∀ᵐ x ∂μ, x ∈ R → x ∈ S.D := by
      filter_upwards [hno] with x hx hxR
      rw [S.hDeq]
      intro hmem
      obtain ⟨r, hr⟩ := mem_iUnion.mp hmem
      obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
      exact hx ⟨r, hrI⟩ hxR hxr
    have heq : R =ᵐ[μ] R ∩ S.D := by
      filter_upwards [hRD] with x hx
      exact propext ⟨fun hr => ⟨hr, hx hr⟩, fun h => h.1⟩
    have hpos : 0 < μ (R ∩ S.D) := by rw [← measure_congr heq]; exact hRp
    refine ⟨R ∩ S.D, hR.inter S.hD, hpos, inter_subset_left.trans hRH,
      hRi.mono_left inter_subset_left, Or.inr inter_subset_right, ?_⟩
    exact hrect.mono (fun _ hp hx hy => hp hx.1 hy)

end Erdos1017.CappedModel.SelectedHighLowStructure

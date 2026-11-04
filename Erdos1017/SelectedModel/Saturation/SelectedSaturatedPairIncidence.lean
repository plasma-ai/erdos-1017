module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedHeadScore
public import Erdos1017.SelectedModel.Structure.WholeRowCrossBlocks

/-!
# Symmetry and shared heads of saturated pairs

Saturation of two whole atom fibers is symmetric, and two saturated pairs
sharing a head have a missing outer whole-fiber block with homogeneous rows and
zero moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {W : Model Ω μ} {m : ℝ}

/-- Saturation of two original whole atom fibers is symmetric under the
original product law. -/
theorem IsSaturatedAtomPair.symm {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) : S.IsSaturatedAtomPair u r := by
  refine ⟨hpair.1.symm, ?_⟩
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hpair.2
  filter_upwards [hswap, chargeKernel_symm W] with p hp hsym hu hr
  exact hsym.trans (hp hr hu)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- If two actual saturated original atom pairs share a head, the outer
original whole-fiber block is missing, with both homogeneous rows and all
three original moments zero on that block. -/
theorem IsSaturatedAtomPair.outer_block_zero
    {S : SelectedHighLowStructure W m} {r u v : S.I}
    (hru : S.IsSaturatedAtomPair r u) (huv : S.IsSaturatedAtomPair u v)
    (_hrv : r ≠ v) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ((r.val : Ω → ℝ) =ᵐ[μ.restrict {x | S.ρ x = v.val}] fun _ => 0) ∧
      ((v.val : Ω → ℝ) =ᵐ[μ.restrict {x | S.ρ x = r.val}] fun _ => 0) ∧
      (∀ᵐ p ∂(μ.restrict {x | S.ρ x = r.val}).prod
        (μ.restrict {x | S.ρ x = v.val}),
        shiftedKernel W m p.1 p.2 = 0 ∧ adjacencyKernel W p.1 p.2 = 0 ∧
          chargeKernel W p.1 p.2 = 0) := by
  let V : Set Ω := {x | S.ρ x = v.val}
  have hVmeas : MeasurableSet V := (S.hfibers v.val v.property).1
  have hVpos : 0 < μ V := (S.hfibers v.val v.property).2.1
  have hscore := S.ae_saturated_head_score_le hW hd hgap hell r u hru.1 hru.2
  have hurow := huv.row_on_other
  have hnonpos : ∀ᵐ x ∂μ.restrict V, r.val x ≤ 0 := by
    filter_upwards [ae_mono Measure.restrict_le_self hscore, hurow] with x hs hu
    linarith
  have hmass : μ (V ∩ {x | r.val x ≤ 0}) = μ V := by
    have h := Measure.measure_inter_eq_of_ae (μ := μ.restrict V)
      (s := univ) hnonpos
    have hTmeas : MeasurableSet {x | r.val x ≤ 0} :=
      (Lp.stronglyMeasurable r.val).measurableSet_le stronglyMeasurable_const
    change (μ.restrict V) ({x | r.val x ≤ 0} ∩ univ) = (μ.restrict V) univ at h
    rw [Set.inter_univ, Measure.restrict_apply hTmeas, Measure.restrict_apply_univ] at h
    simpa only [inter_comm] using h
  have hmissing : 0 < μ (V ∩ {x | r.val x ≤ 0}) := by rw [hmass]; exact hVpos
  exact KernelOperator.whole_row_cross_block_zero_of_positive_nonpositive
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ
    r.val v.val
    (S.hfibers r.val r.property).2.1 (S.hfibers v.val v.property).2.1
    (S.hfibers r.val r.property).2.2.2 (S.hfibers v.val v.property).2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
    (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun p hp => hp.symm)) hW.moment_mem
    hVmeas hmissing

end Erdos1017.CappedModel.SelectedHighLowStructure

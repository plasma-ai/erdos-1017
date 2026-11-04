module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedMissingScore
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairIncidence
public import Erdos1017.Exclusions.Common.SelectedLowAtomReceivers
public import Erdos1017.SelectedModel.SelectedAtomAvoidance
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages

/-!
# Saturated heads have no high part

An original saturated head has no positive high part, since its missing region
would have smaller degree but a larger head score than the original global score
cap (`high_head_null`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- An original saturated head has no positive HIGH part. Its actual
missing region would have smaller degree but a larger head score than
the original global score cap permits. -/
theorem IsSaturatedAtomPair.high_head_null
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    μ ({x | S.ρ x = r.val} ∩ S.H) = 0 := by
  by_contra hnull
  let I := {x | S.ρ x = r.val}
  let N := KernelOperator.wholeFiberMissingSet S.ρ r.val
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let s := r.val + u.val
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hIpos : 0 < μ I := (S.hfibers r.val r.property).2.1
  have hN : MeasurableSet N :=
    KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r.val
  have hhigh : ∀ᵐ x ∂μ.restrict I, x ∈ S.H :=
    S.high_fiber_of_positive_high_subset r (I ∩ S.H)
      (pos_iff_ne_zero.mpr hnull) inter_subset_right inter_subset_left
  have hmass := S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW r.val r.property
  obtain ⟨y, _, hyH, hyEq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hIpos.ne' (hhigh.and hmass)
  rw [S.hH] at hyH
  change 0 < μ {x | (x, y) ∈ actualZeroRelation W m S.ρ ∧ g x < g y} at hyH
  have hcol : 0 < μ {x | (x, y) ∈ actualZeroRelation W m S.ρ} :=
    lt_of_lt_of_le hyH (measure_mono (fun _ hx => hx.1))
  have hout : 0 < S.outsideSectionMass y :=
    ENNReal.toReal_pos hcol.ne' (measure_ne_top μ _)
  have hNr : 0 < μ.real N := hyEq ▸ hout
  have hNpos : 0 < μ N := pos_iff_ne_zero.mpr (by
    intro hz
    change 0 < (μ N).toReal at hNr
    rw [hz, ENNReal.toReal_zero] at hNr
    exact (lt_irrefl _ hNr))
  have hzero := KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m)
    S.ρ S.hρ r.val ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1))
    (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hp => hp.1))
  have hdegreeI : ⟪g, KernelOperator.normalizedSetL2 I hI⟫ = wholeRowDegree r.val :=
    KernelOperator.normalizedSetL2_inner_eq_of_ae_eq I hI hIpos g _
      (wholeRowFiber_degree W m S.ρ r.val (S.hfibers r.val r.property).2.2.2)
  have hdegreeN : ⟪g, KernelOperator.normalizedSetL2 N hN⟫ < wholeRowDegree r.val :=
    KernelOperator.normalizedSetL2_inner_lt_of_ae_lt N hN hNpos g _
      ((S.ae_missingRegion_low_degree_lt hW r.val r.property hhigh).mono (fun _ hx => hx.2))
  have hscoreI : ⟪s, KernelOperator.normalizedSetL2 I hI⟫ = 1 - m := by
    apply KernelOperator.normalizedSetL2_inner_eq_of_ae_eq I hI hIpos
    filter_upwards [S.root_row_zero_on_fiber r, hpair.symm.row_on_other,
      ae_restrict_of_ae (Lp.coeFn_add r.val u.val)] with x hr hu hs
    change (r.val + u.val) x = 1 - m
    rw [hs, Pi.add_apply, hr, hu, zero_add]
  have hscore : ∀ᵐ x ∂μ.restrict N, s x ≤ 1 - m := by
    filter_upwards [ae_restrict_of_ae
      (S.ae_saturated_head_score_le hW hd hgap hell r u hpair.1 hpair.2),
      ae_restrict_of_ae (Lp.coeFn_add r.val u.val)] with x hx hs
    change (r.val + u.val) x ≤ 1 - m
    simpa only [hs, Pi.add_apply] using hx
  have hscoreN : ⟪s, KernelOperator.normalizedSetL2 N hN⟫ ≤ 1 - m := by
    have hi : Integrable (fun x => s x) (μ.restrict N) :=
      ((Lp.memLp s).integrable (by norm_num)).integrableOn
    have hint := integral_mono_ae hi (integrable_const (1 - m)) hscore
    have hmasspos : 0 < μ.real N := ENNReal.toReal_pos hNpos.ne' (measure_ne_top μ _)
    rw [setIntegral_const, smul_eq_mul] at hint
    rw [real_inner_comm, KernelOperator.normalizedSetL2_inner]
    calc
      _ ≤ (μ.real N)⁻¹ * (μ.real N * (1 - m)) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hmasspos.le)
      _ = 1 - m := by field_simp
  have hstrict := hpair.score_increases_across_missing_sets hW hd hgap hell
    I N hI hN hIpos hNpos hzero (by rw [hdegreeI]; exact hdegreeN)
  change ⟪s, KernelOperator.normalizedSetL2 I hI⟫ <
    ⟪s, KernelOperator.normalizedSetL2 N hN⟫ at hstrict
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure

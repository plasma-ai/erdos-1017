module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateCapacity
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterPartialScore

/-!
# Deficit capacity of the entire compulsory source

The entire original reverse compulsory source and the remaining plateau half
obey the two-head deficit capacity inequality
(`entire_source_deficit_capacity`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_head_deficit_zero (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hp : R.plateau = {r, u}) :
    ∀ᵐ x ∂μ, x ∈ R.plateauRegion →
      S.headPairing r u - r.val x - u.val x = 0 := by
  obtain ⟨q, _, hrq, huq, _⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ r.val u.val
    (S.hfibers r.val r.property).2.1 (S.hfibers u.val u.property).2.1
    (S.hfibers r.val r.property).2.2.2 (S.hfibers u.val u.property).2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
    (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) hW.moment_mem
  have hκ : S.headPairing r u = q := by
    change ⟪shiftedOperator W m (S.normalizedHead r), S.normalizedHead u⟫ = q
    rw [S.operator_normalizedHead r, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _
      (S.hfibers u.val u.property).1 (S.hfibers u.val u.property).2.1 r.val q hrq
  have hrr := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp
    (S.root_row_zero_on_fiber r)
  have huu := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
    (S.root_row_zero_on_fiber u)
  have hrurow := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp huq
  have hurrow := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp hrq
  filter_upwards [hrr, huu, hrurow, hurrow] with x hrr huu hrurow hurrow hx
  rw [R.plateauRegion_eq_pair r u hp] at hx
  rcases hx with hx | hx
  · have hr0 := hrr hx
    have huq := hrurow hx
    rw [hκ, hr0, huq]
    ring
  · have hu0 := huu hx
    have hrq := hurrow hx
    rw [hκ, hrq, hu0]
    ring

/-- The entire original reverse compulsory source and the remaining
plateau half obey the actual two-head deficit capacity inequality. -/
theorem entire_source_deficit_capacity (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hdegree0 : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0) :
    (∫ x in S.reverseCompulsorySource R.plateau,
      S.headPairing r u - r.val x - u.val x ∂μ) +
      (2 * S.headPairing r u - 1 + 3 * m) * (1 - 2 * R.height) ≤
        S.headPairing r u - 2 * (2 * (c - m * d)) := by
  let H := R.plateauRegion
  let C := S.reverseCompulsorySource R.plateau
  let O := R.plateauOther
  let f : Ω → ℝ := fun x => S.headPairing r u - r.val x - u.val x
  let w := R.retainedWeight
  let ζ := 2 * S.headPairing r u - 1 + 3 * m
  let q := MissingFlow.sourceSlice Cᶜ R.flow
  let v := MissingFlow.direction μ q
  have hH : MeasurableSet H := R.measurableSet_plateauRegion
  have hC : MeasurableSet C := R.measurableSet_source
  have hO : MeasurableSet O := S.hpartition.1.compl.diff R.measurableSet_plateauRegion
  have hq : Integrable q (μ.prod μ) :=
    MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable hC.compl
  have hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p :=
    MissingFlow.nonnegative_sourceSlice R.isFullReverseFlow.nonnegative _
  have hv : Integrable v μ := MissingFlow.integrable_direction hq
  have hvm : (∫ x, v x ∂μ) = 0 := MissingFlow.integral_direction hq
  have hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1 := by
    filter_upwards [R.isFullReverseFlow.sourceSlice_compl_supply C] with x hx
    rw [hx]
    by_cases h : x ∈ S.H \ C
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]; exact zero_le_one
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ w x :=
    integrableTiltWeight_nonnegative v (MissingFlow.direction_ge_neg_one hq0 hsupply)
      1 ⟨by norm_num, le_rfl⟩
  have hw : Integrable w μ := integrableTiltWeight_integrable v hv 1
  have hwmean : (∫ x, w x ∂μ) = 1 := integrableTiltWeight_integral v hv hvm 1
  have hf : Integrable f μ :=
    ((integrable_const _).sub ((Lp.memLp r.val).integrable (by norm_num))).sub
      ((Lp.memLp u.val).integrable (by norm_num))
  have hfw : Integrable (fun x => f x * w x) μ :=
    integrable_head_deficit_mul (S := S) r u (S.headPairing r u) w hw
  have hHC : ∀ᵐ x ∂μ, x ∈ C → x ∉ H := by
    filter_upwards [R.ae_plateau_not_high] with x hx hc hh
    exact hx hh hc.1
  have hheads : ∀ᵐ x ∂μ, x ∈ H → f x = 0 ∧ w x = 1 := by
    filter_upwards [R.ae_head_deficit_zero r u hW hp,
      R.retainedWeight_on_plateau hW] with x hf hw hx
    exact ⟨hf hx, hw hx⟩
  have hsource : ∀ᵐ x ∂μ, x ∈ C → w x = 1 := R.retainedWeight_on_source
  have hother : ∀ᵐ x ∂μ, x ∈ O → ζ ≤ f x :=
    (ae_restrict_iff' hO).mp
      (R.ae_head_deficit_floor_on_plateauOther r u hru hW hd hgap hp hintercept)
  have hoff : ∀ᵐ x ∂μ, x ∉ H ∪ C ∪ O → w x = 0 :=
    R.retainedWeight_zero_off_plateau
  have hpart := weighted_partition_capacity (μ := μ) H C O hH hC f w ζ
    hf hw hfw hnonneg hwmean hHC hheads hsource hother hoff
  have hmass : μ.real H + μ.real C = 2 * R.height := by
    have hdisj : Disjoint {x | S.ρ x = r.val} {x | S.ρ x = u.val} := by
      apply disjoint_left.mpr
      intro x hx hy
      exact hru (Subtype.ext (hx.symm.trans hy))
    have hh : μ.real H =
        μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = u.val} := by
      dsimp only [H]
      rw [R.plateauRegion_eq_pair r u hp]
      apply measureReal_union _ (S.hfibers u.val u.property).1
      exact hdisj
    have hb := R.original_source_balance
    simp only [hp, Finset.card_pair hru, Nat.cast_ofNat, Finset.sum_pair hru] at hb
    have hb' : 2 * R.height =
        μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = u.val} + μ.real C := by
      simpa only [C, hp] using hb
    linarith only [hh, hb']
  have hupper := R.retained_deficit_integral_le_original r u hru hW hd hgap hp
    hintercept hdegree0
  change (∫ x in C, f x ∂μ) + ζ * (1 - 2 * R.height) ≤ _
  rw [← hmass]
  exact hpart.trans hupper

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

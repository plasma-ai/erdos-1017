module

public import Erdos1017.Exclusions.Common.SelectedRootRows
public import Erdos1017.SelectedModel.Structure.NormalizedSetKernelEnergy
public import Erdos1017.SelectedModel.Selection.FullNullDirectionRigidity

/-!
# Saturated atom pairs and their shifted energy

This module defines `IsSaturatedAtomPair` (saturation on two distinct original
whole independent atoms) and the bounded normalized two-head direction
`saturatedDirection`, and computes the unhalved shifted energy of that direction
on the original law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Saturation on two distinct original whole independent atoms. -/
def IsSaturatedAtomPair (S : SelectedHighLowStructure W m) (r u : S.I) : Prop :=
  r ≠ u ∧ ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
    chargeKernel W p.1 p.2 = 1

/-- The bounded original normalized two-head direction, with its mass
correction on the original probability space. -/
def saturatedDirection (S : SelectedHighLowStructure W m) (r u : S.I) : Lp ℝ 2 μ :=
  KernelOperator.normalizedSetL2 {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 +
    KernelOperator.normalizedSetL2 {x | S.ρ x = u.val} (S.hfibers u.val u.property).1 -
    (2 : ℝ) • Lp.const 2 μ (1 : ℝ)

theorem saturatedDirection_bounded (S : SelectedHighLowStructure W m) (r u : S.I) :
    S.saturatedDirection r u ∈ KernelOperator.boundedL2Submodule μ :=
  (KernelOperator.boundedL2Submodule μ).sub_mem
    ((KernelOperator.boundedL2Submodule μ).add_mem
      (KernelOperator.normalizedSetL2_bounded _ _) (KernelOperator.normalizedSetL2_bounded _ _))
    ((KernelOperator.boundedL2Submodule μ).smul_mem 2 Variation.constant_one_bounded)

theorem saturatedDirection_integral (S : SelectedHighLowStructure W m) (r u : S.I) :
    (∫ x, S.saturatedDirection r u x ∂μ) = 0 := by
  let one := Lp.const 2 μ (1 : ℝ)
  have hinner (k : S.I) :
      ⟪one, KernelOperator.normalizedSetL2 {x | S.ρ x = k.val}
        (S.hfibers k.val k.property).1⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers k.val k.property).2.1
  rw [← KernelOperator.inner_constant_one]
  change ⟪one, _⟫ = 0
  simp only [saturatedDirection, inner_sub_right, inner_add_right, real_inner_smul_right,
    hinner r, hinner u]
  have ho : ⟪one, one⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  change 1 + 1 - 2 * ⟪one, one⟫ = 0
  rw [ho]
  ring

theorem shiftedOperator_normalized_atom (S : SelectedHighLowStructure W m) (r : S.I) :
    shiftedOperator W m (KernelOperator.normalizedSetL2 {x | S.ρ x = r.val}
      (S.hfibers r.val r.property).1) = r.val :=
  KernelOperator.operator_normalizedSetL2_of_homogeneous_rows (shiftedKernel W m)
    (by positivity) (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm)) _ _
    (S.hfibers r.val r.property).2.1 r.val
    ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1))

theorem shiftedOperator_saturatedDirection (S : SelectedHighLowStructure W m) (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    shiftedOperator W m (S.saturatedDirection r u) =
      r.val + u.val - (2 * (2 * (c - m * d))) • Lp.const 2 μ (1 : ℝ) := by
  have hstationary := KernelOperator.constant_one_eigenvector_of_stationary
    (shiftedKernel W m) (by positivity) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) _ hW.stationary
  change shiftedOperator W m (Lp.const 2 μ (1 : ℝ)) = _ at hstationary
  rw [saturatedDirection, map_sub, map_add, map_smul,
    S.shiftedOperator_normalized_atom r, S.shiftedOperator_normalized_atom u, hstationary,
    smul_smul]

theorem IsSaturatedAtomPair.shifted_block {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
      adjacencyKernel W p.1 p.2 = 1 ∧ shiftedKernel W m p.1 p.2 = 1 - m := by
  filter_upwards [hpair.2] with p hp hr hu
  have hy := hp hr hu
  have ha : adjacencyKernel W p.1 p.2 = 1 := by
    have hupper := (adjacency_moment_mem W p).2
    have hcharge := charge_moment_le_adjacency W p
    change chargeKernel W p.1 p.2 ≤ adjacencyKernel W p.1 p.2 at hcharge
    change adjacencyKernel W p.1 p.2 ≤ 1 at hupper
    linarith
  refine ⟨ha, ?_⟩
  change shiftedMoment W m p = _
  rw [shiftedMoment_eq]
  change chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2 = _
  rw [hy, ha]
  ring

private theorem homogeneous_row_eq_of_constant_rectangle
    (K : Ω → Ω → ℝ) (I J : Set Ω) (hIpos : 0 < μ I) (r : Lp ℝ 2 μ) (a : ℝ)
    (hrows : ∀ᵐ x ∂μ.restrict I, K x =ᵐ[μ] (r : Ω → ℝ))
    (hblock : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict J), K p.1 p.2 = a) :
    ∀ᵐ y ∂μ.restrict J, r y = a := by
  obtain ⟨x, _, hx, hblockx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIpos.ne'
    (hrows.and (Measure.ae_ae_of_ae_prod hblock))
  filter_upwards [ae_restrict_of_ae hx, hblockx] with y hy hz
  exact hy.symm.trans hz

omit [IsProbabilityMeasure μ] in
private theorem operator_two_head_energy
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : T.toLinearMap.IsSymmetric)
    (v w o : Lp ℝ 2 μ) (hv : ⟪T v, v⟫ = 0) (hw : ⟪T w, w⟫ = 0) :
    ⟪T (v + w - (2 : ℝ) • o), v + w - (2 : ℝ) • o⟫ =
      2 * ⟪T v, w⟫ - 4 * ⟪T o, v + w⟫ + 4 * ⟪T o, o⟫ := by
  have hvw : ⟪T w, v⟫ = ⟪T v, w⟫ := (hT w v).trans (real_inner_comm _ _)
  have hvo : ⟪T v, o⟫ = ⟪T o, v⟫ := (hT v o).trans (real_inner_comm _ _)
  have hwo : ⟪T w, o⟫ = ⟪T o, w⟫ := (hT w o).trans (real_inner_comm _ _)
  simp only [map_sub, map_add, map_smul, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hv, hw, hvw, hvo, hwo]
  ring

private theorem shiftedOperator_symmetric (W : Model Ω μ) (m : ℝ) :
    (shiftedOperator W m).toLinearMap.IsSymmetric :=
  KernelOperator.operator_symmetric (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm))

theorem IsSaturatedAtomPair.row_on_other {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) :
    (r.val : Ω → ℝ) =ᵐ[μ.restrict {x | S.ρ x = u.val}] fun _ => 1 - m := by
  apply homogeneous_row_eq_of_constant_rectangle (shiftedKernel W m)
    {x | S.ρ x = r.val} {x | S.ρ x = u.val} (S.hfibers r.val r.property).2.1 r.val (1 - m)
    ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1))
  filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
      hpair.shifted_block,
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (S.hfibers r.val r.property).1),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (S.hfibers u.val u.property).1)]
    with p hp hr hu
  exact (hp hr hu).2

private theorem normalized_atom_inner_one (S : SelectedHighLowStructure W m) (r : S.I) :
    ⟪Lp.const 2 μ (1 : ℝ), KernelOperator.normalizedSetL2 {x | S.ρ x = r.val}
      (S.hfibers r.val r.property).1⟫ = 1 := by
  rw [KernelOperator.inner_constant_one]
  exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers r.val r.property).2.1

theorem row_integral_of_stationary (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    (∫ x, r.val x ∂μ) = 2 * (c - m * d) := by
  have hstationary := KernelOperator.constant_one_eigenvector_of_stationary
    (shiftedKernel W m) (by positivity) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) _ hW.stationary
  change shiftedOperator W m (Lp.const 2 μ (1 : ℝ)) = _ at hstationary
  have hsym := shiftedOperator_symmetric W m
  have heq := hsym (Lp.const 2 μ (1 : ℝ))
    (KernelOperator.normalizedSetL2 {x | S.ρ x = r.val} (S.hfibers r.val r.property).1)
  change ⟪shiftedOperator W m (Lp.const 2 μ (1 : ℝ)), _⟫ =
    ⟪Lp.const 2 μ (1 : ℝ), shiftedOperator W m _⟫ at heq
  rw [hstationary, S.shiftedOperator_normalized_atom r, real_inner_smul_left,
    S.normalized_atom_inner_one r, mul_one, KernelOperator.inner_constant_one] at heq
  exact heq.symm

/-- The unhalved shifted energy of the actual saturated two-head direction.
All means and cross-block values are taken on the original law. -/
theorem IsSaturatedAtomPair.shifted_energy {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ⟪shiftedOperator W m (S.saturatedDirection r u), S.saturatedDirection r u⟫ =
      2 * (1 - m - 2 * (2 * (c - m * d))) := by
  let v : Lp ℝ 2 μ :=
    KernelOperator.normalizedSetL2 {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
  let w : Lp ℝ 2 μ :=
    KernelOperator.normalizedSetL2 {x | S.ρ x = u.val} (S.hfibers u.val u.property).1
  let o := Lp.const 2 μ (1 : ℝ)
  have hv : ⟪shiftedOperator W m v, v⟫ = 0 := by
    rw [show shiftedOperator W m v = r.val from S.shiftedOperator_normalized_atom r,
      real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers r.val r.property).2.1 r.val 0 (S.root_row_zero_on_fiber r)
  have hw : ⟪shiftedOperator W m w, w⟫ = 0 := by
    rw [show shiftedOperator W m w = u.val from S.shiftedOperator_normalized_atom u,
      real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers u.val u.property).2.1 u.val 0 (S.root_row_zero_on_fiber u)
  have hvw : ⟪shiftedOperator W m v, w⟫ = 1 - m := by
    rw [show shiftedOperator W m v = r.val from S.shiftedOperator_normalized_atom r,
      real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers u.val u.property).2.1 r.val (1 - m) hpair.row_on_other
  have hTo : shiftedOperator W m o = (2 * (c - m * d)) • o :=
    KernelOperator.constant_one_eigenvector_of_stationary (shiftedKernel W m) (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m) _ hW.stationary
  have hoo : ⟪o, o⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  have hov : ⟪o, v⟫ = 1 := S.normalized_atom_inner_one r
  have how : ⟪o, w⟫ = 1 := S.normalized_atom_inner_one u
  change ⟪shiftedOperator W m (v + w - (2 : ℝ) • o), v + w - (2 : ℝ) • o⟫ = _
  rw [operator_two_head_energy _ (shiftedOperator_symmetric W m) v w o hv hw,
    hvw, hTo]
  simp only [real_inner_smul_left, inner_add_right, hov, how, hoo]
  ring

end Erdos1017.CappedModel.SelectedHighLowStructure

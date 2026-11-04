module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterAtomLocation
public import Erdos1017.Exclusions.Common.TwoCenter.SchurSourceEnergy
public import Erdos1017.SelectedModel.Structure.NormalizedSetKernelEnergy

/-!
# Schur form data of a two-center recovery

This module defines the original shifted operator form, the normalized head
indicators and the cross-head pairing, and computes the Gram entries: missing
source blocks pair to zero, shared and private patterns pair strictly
positively, and stationary pairings with heads and the constant equal `ν`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The original shifted operator form, before any flow change of measure. -/
def schurForm (W : Model Ω μ) (m : ℝ) : LinearMap.BilinForm ℝ (Lp ℝ 2 μ) :=
  SchurHeadPlane.operatorForm (shiftedOperator W m)

/-- The actual normalized original whole-head indicator. -/
def normalizedHead (S : SelectedHighLowStructure W m) (r : S.I) : Lp ℝ 2 μ :=
  KernelOperator.normalizedSetL2 {x | S.ρ x = r.val} (S.hfibers r.val r.property).1

/-- The original cross-head coefficient, defined by the actual normalized
physical pairing. Its homogeneous-block identification is proved below. -/
def headPairing (S : SelectedHighLowStructure W m) (r u : S.I) : ℝ :=
  schurForm W m (S.normalizedHead r) (S.normalizedHead u)

/-- The original form is the original physical mixed kernel integral. -/
theorem schurForm_eq_kernelPairing (f g : Lp ℝ 2 μ) :
    schurForm W m f g = KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) f g := by
  change ⟪shiftedOperator W m f, g⟫ = _
  rw [shiftedOperator, KernelOperator.operator_inner]
  rfl

/-- Actual AE symmetry gives symmetry of the original form. -/
theorem schurForm_symm (f g : Lp ℝ 2 μ) : schurForm W m f g = schurForm W m g f := by
  rw [schurForm_eq_kernelPairing, schurForm_eq_kernelPairing]
  apply KernelOperator.kernelPairing_symm
  exact (shiftedMoment_symm W m).mono (fun _ hp => hp.symm)

/-- The original actual spectral index pays the finite Gram-form bound;
no Schur index or cone condition is assumed. -/
theorem schurForm_positiveIndexOn [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {d c : ℝ} (hW : FullStationaryClass d c W m) :
    SchurHeadPlane.PositiveIndexOn (schurForm W m) ⊤ 2 := by
  let := hW.finite_positive
  have hsym : (shiftedOperator W m).toLinearMap.IsSymmetric :=
    KernelOperator.operator_symmetric _ _ _ _
      ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm))
  exact SchurHeadPlane.operator_positiveIndexOn (shiftedOperator W m)
    (KernelOperator.operator_isCompact _ _ _ _) hsym 2 hW.index_le_two

/-- The actual normalized L² head is its original physical uniform density. -/
theorem normalizedHead_coe (r : S.I) :
    (S.normalizedHead r : Ω → ℝ) =ᵐ[μ]
      MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} := by
  filter_upwards [KernelOperator.normalizedSetL2_coe {x | S.ρ x = r.val}
    (S.hfibers r.val r.property).1] with x hx
  rw [show S.normalizedHead r x =
    (μ.real {x | S.ρ x = r.val})⁻¹ * {x | S.ρ x = r.val}.indicator (fun _ => (1 : ℝ)) x from hx]
  by_cases hm : S.ρ x = r.val
  · have hi : x ∈ {x | S.ρ x = r.val} := hm
    simp only [MissingFlow.AtomicAssignment.recipientDensity, indicator_of_mem hi, mul_one]
  · have hi : x ∉ {x | S.ρ x = r.val} := hm
    simp only [MissingFlow.AtomicAssignment.recipientDensity, indicator_of_notMem hi, mul_zero]

/-- The original shifted operator sends each normalized head to its actual
whole row, using the original homogeneous rows and positive original mass. -/
theorem operator_normalizedHead (r : S.I) : shiftedOperator W m (S.normalizedHead r) = r.val := by
  exact KernelOperator.operator_normalizedSetL2_of_homogeneous_rows _ _ _ _
    ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) _
    (S.hfibers r.val r.property).1 (S.hfibers r.val r.property).2.1 r.val
    ((S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1))

/-- Every original independent head is null for the original shifted form. -/
theorem schurForm_head_self (r : S.I) : schurForm W m (S.normalizedHead r) (S.normalizedHead r) = 0 := by
  obtain ⟨q, _, hrq, _, hzero, _⟩ := (S.hfibers r.val r.property).2.2.2.internal
  have hq : q = 0 := hzero.mp (S.hfibers r.val r.property).2.2.1
  have hnorm := KernelOperator.normalizedSetL2_inner_of_constant
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
    (S.hfibers r.val r.property).2.1 r.val 0 (by
      filter_upwards [hrq] with x hx
      exact hx.trans hq)
  change ⟪shiftedOperator W m (S.normalizedHead r), S.normalizedHead r⟫ = 0
  rw [S.operator_normalizedHead r, real_inner_comm]
  exact hnorm

/-- The actual normalized physical coefficient is the original homogeneous
K/G/Y block. -/
theorem exists_original_head_block (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∃ q ∈ Icc (0 : ℝ) 4, S.headPairing r u = q ∧
      ∀ᵐ p ∂(μ.restrict {x | S.ρ x = r.val}).prod (μ.restrict {x | S.ρ x = u.val}),
        shiftedKernel W m p.1 p.2 = q ∧
          adjacencyKernel W p.1 p.2 = (if 0 < q then 1 else 0) ∧
          chargeKernel W p.1 p.2 = q + m * (if 0 < q then 1 else 0) := by
  obtain ⟨q, hq, hrq, _, hblock⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ r.val u.val
    (S.hfibers r.val r.property).2.1 (S.hfibers u.val u.property).2.1
    (S.hfibers r.val r.property).2.2.2 (S.hfibers u.val u.property).2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W) (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) hW.moment_mem
  refine ⟨q, hq, ?_, hblock⟩
  change ⟪shiftedOperator W m (S.normalizedHead r), S.normalizedHead u⟫ = q
  rw [S.operator_normalizedHead r, real_inner_comm]
  exact KernelOperator.normalizedSetL2_inner_of_constant _
    (S.hfibers u.val u.property).1 (S.hfibers u.val u.property).2.1 r.val q hrq

/-- The original stationary constant pairs with every L² vector by its
original integral. -/
theorem schurForm_constant {d c : ℝ} (hW : FullStationaryClass d c W m) (f : Lp ℝ 2 μ) :
    schurForm W m (Lp.const 2 μ (1 : ℝ)) f = 2 * (c - m * d) * ∫ x, f x ∂μ := by
  have he := KernelOperator.constant_one_eigenvector_of_stationary (shiftedKernel W m)
    (by positivity) (shiftedKernel_measurable W m) (shiftedKernel_bound W m) _ hW.stationary
  change shiftedOperator W m (Lp.const 2 μ (1 : ℝ)) =
    (2 * (c - m * d)) • Lp.const 2 μ (1 : ℝ) at he
  change ⟪shiftedOperator W m (Lp.const 2 μ (1 : ℝ)), f⟫ = _
  rw [he, real_inner_smul_left, KernelOperator.inner_constant_one]

/-- The actual original indicator mean, retaining its measurable set. -/
def indicatorVector (A : Set Ω) (hA : MeasurableSet A) : Lp ℝ 2 μ :=
  indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)

/-- Its original integral is exactly its original set mass. -/
theorem indicatorVector_integral (A : Set Ω) (hA : MeasurableSet A) :
    (∫ x, indicatorVector (μ := μ) A hA x ∂μ) = μ.real A := by
  rw [integral_congr_ae (show (indicatorVector A hA : Ω → ℝ) =ᵐ[μ]
    A.indicator (fun _ => 1) from indicatorConstLp_coeFn), integral_indicator hA,
    setIntegral_const, smul_eq_mul, mul_one]

/-- Null original sets give the zero original L² mean. -/
theorem indicatorVector_zero_of_null (A : Set Ω) (hA : MeasurableSet A) (hn : μ A = 0) :
    indicatorVector (μ := μ) A hA = 0 := by
  apply Lp.ext
  filter_upwards [show (indicatorVector A hA : Ω → ℝ) =ᵐ[μ] A.indicator (fun _ => 1) from
    indicatorConstLp_coeFn, measure_eq_zero_iff_ae_notMem.mp hn, Lp.coeFn_zero ℝ 2 μ]
    with x hx hnot hz
  rw [hx, hz, indicator_of_notMem hnot]
  rfl

/-- The original indicator Gram entry is the original physical rectangle
integral, with the form's first input on its second coordinate. -/
theorem schurForm_indicators (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    schurForm W m (indicatorVector A hA) (indicatorVector B hB) =
      ∫ p in B ×ˢ A, shiftedKernel W m p.1 p.2 ∂μ.prod μ := by
  rw [schurForm_eq_kernelPairing, KernelOperator.kernelPairing,
    ← integral_indicator (hB.prod hA)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (show (indicatorVector A hA : Ω → ℝ) =ᵐ[μ] A.indicator (fun _ => 1) from indicatorConstLp_coeFn),
    Measure.quasiMeasurePreserving_fst.ae
    (show (indicatorVector B hB : Ω → ℝ) =ᵐ[μ] B.indicator (fun _ => 1) from indicatorConstLp_coeFn)]
    with p hp hq
  rw [hp, hq]
  by_cases hx : p.1 ∈ B <;> by_cases hy : p.2 ∈ A <;> simp [hx, hy]

/-- Original kernel nonnegativity pays all original source self forms. -/
theorem schurForm_indicator_nonnegative (A : Set Ω) (hA : MeasurableSet A)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    0 ≤ schurForm W m (indicatorVector A hA) (indicatorVector A hA) := by
  rw [schurForm_indicators]
  exact integral_nonneg_of_ae (ae_restrict_of_ae (hW.moment_mem.mono (fun _ hp => hp.1)))

/-- A genuine positive original kernel rectangle between positive original
sets gives a strict original indicator Gram pairing. -/
theorem schurForm_indicators_positive (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAp : 0 < μ A) (hBp : 0 < μ B)
    (hpos : ∀ᵐ p ∂μ.prod μ, p.1 ∈ B → p.2 ∈ A → 0 < shiftedKernel W m p.1 p.2) :
    0 < schurForm W m (indicatorVector A hA) (indicatorVector B hB) := by
  rw [schurForm_indicators]
  have hi : Integrable (fun p : Ω × Ω => shiftedKernel W m p.1 p.2) (μ.prod μ) :=
    (integrable_const _).mono' (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
  have hp : ∀ᵐ p ∂(μ.prod μ).restrict (B ×ˢ A), 0 < shiftedKernel W m p.1 p.2 := by
    filter_upwards [ae_restrict_of_ae hpos, ae_restrict_mem (hB.prod hA)] with p hp hm
    exact hp hm.1 hm.2
  by_contra hn
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hp.mono (fun _ h => h.le)) hi.integrableOn).mp
    (le_antisymm (le_of_not_gt hn) (integral_nonneg_of_ae (hp.mono (fun _ h => h.le))))
  have hmass : (μ.prod μ) (B ×ˢ A) ≠ 0 := by
    rw [Measure.prod_prod]
    exact mul_ne_zero hBp.ne' hAp.ne'
  obtain ⟨p, _, hpositive, hzero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass (hp.and hz)
  exact (ne_of_gt hpositive) hzero

/-- A missing original source block gives an original head/source Gram
zero, using the actual whole row rather than an endpoint-price premise. -/
theorem schurForm_head_indicator_zero_of_missing [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r : S.I) (A : Set Ω) (hA : MeasurableSet A)
    (hAN : A ⊆ KernelOperator.wholeFiberMissingSet S.ρ r.val)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    schurForm W m (S.normalizedHead r) (indicatorVector A hA) = 0 := by
  have hrows := (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.1)
  have hz := KernelOperator.ae_zero_fiber_prod_missingSet (shiftedKernel W m) S.ρ S.hρ r.val
    hrows (shiftedKernel_measurable W m) (hW.moment_mem.mono (fun _ hp => hp.1))
  have hzero : ∀ᵐ p ∂(μ.restrict {x | S.ρ x = r.val}).prod (μ.restrict A),
      shiftedKernel W m p.1 p.2 = 0 :=
    ae_mono (Measure.prod_mono le_rfl (Measure.restrict_mono hAN le_rfl)) hz
  have hrzero := KernelOperator.homogeneous_row_zero_of_zero_rectangle
    (shiftedKernel W m) {x | S.ρ x = r.val} A (S.hfibers r.val r.property).2.1 r.val hrows hzero
  change ⟪shiftedOperator W m (S.normalizedHead r), indicatorVector A hA⟫ = 0
  rw [S.operator_normalizedHead r, real_inner_comm, indicatorVector,
    L2.inner_indicatorConstLp_one, integral_eq_zero_of_ae hrzero]

/-- On one original product common event, equal original whole fibers
have identical membership in each original missing-head predicate. -/
theorem ae_same_fiber_missing_iff (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ p ∂μ.prod μ, ∀ k : S.I, S.ρ p.1 = k.val → S.ρ p.2 = k.val →
      (p.1 ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val ↔
        p.2 ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val) := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ k : S.I, S.ρ x = k.val →
      (x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val ↔ r ∈ S.fiberMissingLabels k) :=
    ae_all_iff.mpr (fun k => (ae_restrict_iff' (S.hfibers k.val k.property).1).mp
      (S.ae_missing_iff_fiberMissingLabels k r hW))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hall,
    Measure.quasiMeasurePreserving_snd.ae hall] with p hp hq k hx hy
  exact (hp k hx).trans (hq k hy).symm

/-- Shared and private HIGH source patterns are joined by a strictly
positive original shifted kernel, not merely by a supplied cone sign. -/
theorem shared_private_kernel_positive (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.twoCenterPrivate r u → p.2 ∈ S.twoCenterShared r u →
      0 < shiftedKernel W m p.1 p.2 := by
  filter_upwards [S.ae_same_fiber_missing_iff u hW, S.hcoverage, S.hrelation,
    hW.moment_mem] with p hf hc hz hn hprivate hshared
  apply lt_of_le_of_ne hn.1
  intro he
  rcases hc he.symm with ⟨k, hk, hx, hy⟩ | hZ
  · exact hprivate.2 ((hf ⟨k, hk⟩ hx hy).mpr hshared.2)
  · rcases hz hZ with h | h
    · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hshared.1.1.1 h.2.1
    · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hprivate.1.1.1 h.2.1

/-- Every nonzero actual private mean has a strict original pairing with a
positive shared source; null private patterns are handled by the zero mean. -/
theorem schurForm_shared_private_positive [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (R : S.ReverseRecovery) (r u : S.I) (hp : R.plateau = {r, u})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hshared : 0 < μ (S.twoCenterShared r u))
    (hprivate : indicatorVector (μ := μ) (S.twoCenterPrivate r u)
      (R.measurableSet_twoCenter_patterns r u hp).1 ≠ 0) :
    0 < schurForm W m
      (indicatorVector (S.twoCenterShared r u) (R.measurableSet_twoCenter_patterns r u hp).2.2)
      (indicatorVector (S.twoCenterPrivate r u) (R.measurableSet_twoCenter_patterns r u hp).1) := by
  have hpositive : 0 < μ (S.twoCenterPrivate r u) := by
    by_contra h
    have hz : μ (S.twoCenterPrivate r u) = 0 := le_antisymm (le_of_not_gt h) zero_le
    exact hprivate (indicatorVector_zero_of_null _ _ hz)
  exact schurForm_indicators_positive _ _ _ _ hshared hpositive
    (S.shared_private_kernel_positive r u hW)

/-- Actual stationary pairings with original source means retain original
set masses and the original multiplier. -/
theorem schurForm_constant_indicator (A : Set Ω) (hA : MeasurableSet A)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    schurForm W m (Lp.const 2 μ (1 : ℝ)) (indicatorVector A hA) =
      2 * (c - m * d) * μ.real A := by
  rw [schurForm_constant hW, indicatorVector_integral]

/-- Actual stationary pairings with each normalized original head are ν. -/
theorem schurForm_constant_head (r : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m) :
    schurForm W m (Lp.const 2 μ (1 : ℝ)) (S.normalizedHead r) = 2 * (c - m * d) := by
  rw [schurForm_constant hW, normalizedHead,
    KernelOperator.normalizedSetL2_integral _ _ (S.hfibers r.val r.property).2.1, mul_one]

/-- The original stationary constant has original form value ν. -/
theorem schurForm_constant_self {d c : ℝ} (hW : FullStationaryClass d c W m) :
    schurForm W m (Lp.const 2 μ (1 : ℝ)) (Lp.const 2 μ (1 : ℝ)) = 2 * (c - m * d) := by
  rw [schurForm_constant hW, integral_congr_ae (Lp.coeFn_const 2 μ (1 : ℝ))]
  change 2 * (c - m * d) * (∫ _ : Ω, (1 : ℝ) ∂μ) = 2 * (c - m * d)
  rw [integral_const, smul_eq_mul, probReal_univ, one_mul, mul_one]

/-- Original L² Gram energy agrees with the actual energy of any AE-equal
original scalar representative. -/
theorem schurForm_energy_of_ae_coe (v : Lp ℝ 2 μ) (f : Ω → ℝ) (hv : (v : Ω → ℝ) =ᵐ[μ] f) :
    schurForm W m v v = KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) f := by
  rw [schurForm_eq_kernelPairing, KernelOperator.kernelPairing, KernelOperator.kernelEnergy]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hv,
    Measure.quasiMeasurePreserving_snd.ae hv] with p hx hy
  rw [hx, hy]

end Erdos1017.CappedModel.SelectedHighLowStructure

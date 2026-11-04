module

public import Erdos1017.Exclusions.Common.Flows.DiffuseFlowEnergyCredit

/-!
# Energy of finite sums of missing flows

For a full stationary class, finitely many oriented missing flows have total
energy at least the sum of their individual energies, and nonnegative subflows
dominated by one oriented missing flow have total individual energy at most that
flow's energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A finite sum of actual nonnegative product densities is nonnegative
on one common almost-everywhere event. -/
theorem finite_sum_nonnegative (n : ℕ) (q : Fin n → Ω × Ω → ℝ)
    (hq : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ q i p) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ ∑ i, q i p := by
  filter_upwards [ae_all_iff.mpr hq] with p hp
  exact Finset.sum_nonneg (fun i _ => hp i)

/-- The support of a finite sum lies in the common actual support; no
positivity or cancellation assumption is needed for this implication. -/
theorem finite_sum_support (n : ℕ) (q : Fin n → Ω × Ω → ℝ)
    (P : Ω × Ω → Prop) (hq : ∀ i, ∀ᵐ p ∂μ.prod μ, q i p ≠ 0 → P p) :
    ∀ᵐ p ∂μ.prod μ, (∑ i, q i p) ≠ 0 → P p := by
  filter_upwards [ae_all_iff.mpr hq] with p hp hsum
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact hp i hi

end Erdos1017.MissingFlow

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {d c m : ℝ} {W : Model Ω μ}

/-- Actual nonnegative mutual flow energy makes the energy of a sum at
least the sum of the two actual self-energies, with the unhalved factor two. -/
theorem FullStationaryClass.missing_flow_energy_add_ge
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hr0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ r p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2)
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) +
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ r) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ (q + r)) := by
  have hcross := hW.missing_flow_pairing_nonnegative hd hgap q r hq hr hq0 hr0 hqs hrs
  have hsym : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have he := KernelOperator.kernelEnergy_sub_mul (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    (MissingFlow.direction μ q) (MissingFlow.direction μ r)
    (MissingFlow.integrable_direction hq) (MissingFlow.integrable_direction hr) (-1)
  have hdir : MissingFlow.direction μ (q + r) =ᵐ[μ]
      (fun x => MissingFlow.direction μ q x - -1 * MissingFlow.direction μ r x) := by
    filter_upwards [MissingFlow.direction_add hq hr] with x hx
    simpa only [Pi.add_apply, neg_mul, one_mul, sub_neg_eq_add] using hx
  rw [KernelOperator.kernelEnergy_congr_ae _ hdir, he]
  nlinarith

/-- Finitely many actual oriented missing flows have total energy at least
the sum of their individual energies; all mutual terms are licensed internally. -/
theorem FullStationaryClass.missing_flow_energy_sum_ge
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (n : ℕ) (q : Fin n → Ω × Ω → ℝ)
    (hq : ∀ i, Integrable (q i) (μ.prod μ))
    (hq0 : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ q i p)
    (hqs : ∀ i, ∀ᵐ p ∂μ.prod μ, q i p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    (∑ i, KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ (q i))) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (fun p => ∑ i, q i p)) := by
  induction n with
  | zero => simp [MissingFlow.direction, MissingFlow.receipt, MissingFlow.supply,
      KernelOperator.kernelEnergy]
  | succ n ih =>
    let r : Ω × Ω → ℝ := fun p => ∑ j : Fin n, q j.succ p
    have hr : Integrable r (μ.prod μ) := integrable_finsetSum _ (fun j _ => hq j.succ)
    have hr0 := MissingFlow.finite_sum_nonnegative n (fun j => q j.succ) (fun j => hq0 j.succ)
    have hrs := MissingFlow.finite_sum_support n (fun j => q j.succ) _ (fun j => hqs j.succ)
    have htail := ih (fun j => q j.succ) (fun j => hq j.succ)
      (fun j => hq0 j.succ) (fun j => hqs j.succ)
    have hsum := hW.missing_flow_energy_add_ge hd hgap (q 0) r (hq 0) hr (hq0 0) hr0 (hqs 0) hrs
    have heq : (fun p => ∑ i, q i p) = q 0 + r := by
      funext p
      exact Fin.sum_univ_succ (fun i => q i p)
    rw [heq, Fin.sum_univ_succ]
    linarith

/-- A finite sum of actual nonnegative subflows dominated by one oriented
missing flow has total individual energy at most that full flow's energy.
The individual support and every mutual sign are derived, not assumed. -/
theorem FullStationaryClass.sum_subflow_energy_le
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (n : ℕ) (q : Fin n → Ω × Ω → ℝ) (r : Ω × Ω → ℝ)
    (hq : ∀ i, Integrable (q i) (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ i, ∀ᵐ p ∂μ.prod μ, 0 ≤ q i p)
    (hqr : ∀ᵐ p ∂μ.prod μ, (∑ i, q i p) ≤ r p)
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    (∑ i, KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ (q i))) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ r) := by
  have hqs : ∀ i, ∀ᵐ p ∂μ.prod μ, q i p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
    intro i
    filter_upwards [ae_all_iff.mpr hq0, hqr, hrs] with p hp hle hs hne
    apply hs
    have hsingle : q i p ≤ ∑ j, q j p :=
      Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    exact ((lt_of_le_of_ne (hp i) (Ne.symm hne)).trans_le (hsingle.trans hle)).ne'
  exact (hW.missing_flow_energy_sum_ge hd hgap n q hq hq0 hqs).trans
    (hW.missing_flow_energy_mono hd hgap (fun p => ∑ i, q i p) r
      (integrable_finsetSum _ (fun i _ => hq i)) hr
      (MissingFlow.finite_sum_nonnegative n q hq0) hqr hrs)

end Erdos1017.CappedModel

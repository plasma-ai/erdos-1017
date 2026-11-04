module

public import Erdos1017.SelectedModel.Structure.IntegrableReweight
public import Erdos1017.SelectedModel.Structure.IntegrableKernelPolynomials

/-!
# Density and objective along an integrable tilt

Along an integrable direction the affine tilt weight gives a density polynomial
with the adjacency-degree linear coefficient and the quadratic energy, and the
exact shifted-objective polynomial under the original multiplier; positive
shifted energy excludes any return to the original density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual affine probability weight along an integrable direction. -/
def integrableTiltWeight (v : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ := 1 + t * v x

theorem integrableTiltWeight_integrable (v : Ω → ℝ) (hv : Integrable v μ) (t : ℝ) :
    Integrable (integrableTiltWeight v t) μ := (integrable_const 1).add (hv.const_mul t)

omit [IsProbabilityMeasure μ] in
theorem integrableTiltWeight_nonnegative (v : Ω → ℝ) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∀ᵐ x ∂μ, 0 ≤ integrableTiltWeight v t x := by
  filter_upwards [hbelow] with x hx
  change 0 ≤ 1 + t * v x
  nlinarith [ht.2, mul_nonneg ht.1 (show 0 ≤ v x + 1 by linarith)]

theorem integrableTiltWeight_integral (v : Ω → ℝ) (hv : Integrable v μ)
    (hmean : (∫ x, v x ∂μ) = 0) (t : ℝ) :
    (∫ x, integrableTiltWeight v t x ∂μ) = 1 := by
  change (∫ x, 1 + t * v x ∂μ) = 1
  rw [integral_add (integrable_const 1) (hv.const_mul t),
    integral_const_mul, hmean]
  simp

/-- The actual unchanged dual under (1+t v)μ, for every t in the full unit
interval and every integrable direction bounded below by -1. -/
def integrableTilt (W : Model Ω μ) (v : Ω → ℝ) (hv : Integrable v μ)
    (hmean : (∫ x, v x ∂μ) = 0) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Model Ω (weightedMeasure (μ := μ) (integrableTiltWeight v t)) :=
  integrableReweight W _ (integrableTiltWeight_integrable v hv t)
    (integrableTiltWeight_nonnegative v hbelow t ht) (integrableTiltWeight_integral v hv hmean t)

/-- Every actual affine law is a probability law, including the endpoint. -/
theorem integrableTilt_probability (v : Ω → ℝ) (hv : Integrable v μ)
    (hmean : (∫ x, v x ∂μ) = 0) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (weightedMeasure (μ := μ) (integrableTiltWeight v t)) :=
  weightedMeasure_probability (integrableTiltWeight_integrable v hv t)
    (integrableTiltWeight_nonnegative v hbelow t ht) (integrableTiltWeight_integral v hv hmean t)

theorem fullFeasible_integrableTilt (W : Model Ω μ) (hW : FullFeasible W)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    FullFeasible (integrableTilt W v hv hmean hbelow t ht) :=
  fullFeasible_integrableReweight W hW _ (integrableTiltWeight_integrable v hv t)
    (integrableTiltWeight_nonnegative v hbelow t ht) (integrableTiltWeight_integral v hv hmean t)

/-- The linear density coefficient is exactly the pairing with the
original physical adjacency degree, evaluated under the original measure. -/
theorem adjacency_kernelPairing_one_eq_degree (W : Model Ω μ)
    (v : Ω → ℝ) (hv : Integrable v μ) :
    KernelOperator.kernelPairing (μ := μ) (adjacencyKernel W) (fun _ => 1) v =
      ∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ := by
  rw [KernelOperator.kernelPairing_one_eq_row _ (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) v hv]
  apply integral_congr_ae
  filter_upwards [KernelOperator.onL2_coe (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ))] with x hx
  have hrow : KernelOperator.applyKernel (μ := μ) (adjacencyKernel W)
      (Lp.const 2 μ (1 : ℝ)) x = ∫ y, adjacencyKernel W x y ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with y hy
    simp only [hy, Function.const_apply, mul_one]
  change _ = KernelOperator.onL2 (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ)) x * v x
  rw [hx, hrow]

/-- The actual density polynomial, with its original adjacency-degree
linear coefficient and the original unhalved quadratic energy divided by two. -/
theorem density_integrableTilt (W : Model Ω μ) (v : Ω → ℝ) (hv : Integrable v μ)
    (hmean : (∫ x, v x ∂μ) = 0) (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    density (integrableTilt W v hv hmean hbelow t ht) = density W +
      t * (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) +
        t ^ 2 * KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) v / 2 := by
  rw [integrableTilt, density_integrableReweight]
  change KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) (fun x => 1 + t * v x) / 2 = _
  rw [KernelOperator.kernelEnergy_one_add_mul _ (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (adjacencyKernel_symm W) v hv,
    KernelOperator.kernelEnergy_one, adjacency_kernelPairing_one_eq_degree W v hv]
  unfold density adjacencyKernel
  ring

/-- The same original scalar shift acts linearly on arbitrary integrable
physical kernel energies. -/
theorem shifted_kernelEnergy (W : Model Ω μ) (m : ℝ) (v : Ω → ℝ) (hv : Integrable v μ) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v =
      KernelOperator.kernelEnergy (μ := μ) (chargeKernel W) v -
        m * KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) v := by
  have heq : shiftedKernel W m = fun x y => chargeKernel W x y - m * adjacencyKernel W x y := by
    funext x y
    exact shiftedMoment_eq W m (x, y)
  rw [heq]
  exact KernelOperator.kernelEnergy_sub_kernel _ _ (chargeKernel_measurable W)
    (adjacencyKernel_measurable W) (chargeKernel_bound W) (adjacencyKernel_bound W) v hv m

/-- Original stationarity annihilates the shifted mixed term of every
integrable mean-zero direction; no changed-law stationarity is asserted. -/
theorem FullStationaryClass.shifted_kernelPairing_one_eq_zero
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0) :
    KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) (fun _ => 1) v = 0 := by
  rw [KernelOperator.kernelPairing_one_eq_row _ (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) v hv]
  calc
    _ = ∫ x, (2 * (c - m * d)) * v x ∂μ := integral_congr_ae
      (hW.stationary.mono (fun x hx => by rw [hx]))
    _ = 0 := by rw [integral_const_mul, hmean, mul_zero]

/-- The original multiplier gives the exact actual shifted-objective
polynomial along every feasible integrable affine law. -/
theorem FullStationaryClass.objective_integrableTilt
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    objective (integrableTilt W v hv hmean hbelow t ht) = c +
      m * (density (integrableTilt W v hv hmean hbelow t ht) - d) +
        t ^ 2 * KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v / 2 := by
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hexp := KernelOperator.kernelEnergy_one_add_mul _ (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) hsym v hv t
  rw [hW.shifted_kernelPairing_one_eq_zero v hv hmean, mul_zero, add_zero] at hexp
  have hbase : KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (fun _ => 1) =
      2 * (c - m * d) := by
    rw [shifted_kernelEnergy W m _ (integrable_const 1), KernelOperator.kernelEnergy_one,
      KernelOperator.kernelEnergy_one]
    have hd := hW.density_eq
    have hc := hW.objective_eq
    unfold density at hd
    unfold objective at hc
    have hd' : (∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ) = 2 * d := by linarith
    have hc' : (∫ p, W.moment CappedColor.charge p ∂μ.prod μ) = 2 * c := by linarith
    change (∫ p, W.moment CappedColor.charge p ∂μ.prod μ) -
      m * (∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ) = _
    rw [hd', hc']
    ring
  rw [hbase] at hexp
  rw [integrableTilt, objective_integrableReweight, density_integrableReweight]
  change KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (integrableTiltWeight v t) = _ at hexp
  rw [shifted_kernelEnergy W m _ (integrableTiltWeight_integrable v hv t)] at hexp
  change KernelOperator.kernelEnergy (μ := μ) (chargeKernel W) (integrableTiltWeight v t) -
      m * KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) (integrableTiltWeight v t) = _ at hexp
  linarith

/-- Positive original shifted energy excludes any nonzero return to the
original density: the unchanged full-feasible dual would beat F(d). -/
theorem FullStationaryClass.no_density_return_of_positive_energy
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (henergy : 0 < KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (htpos : 0 < t) :
    density (integrableTilt W v hv hmean hbelow t ht) ≠ d := by
  intro hreturn
  have := integrableTilt_probability v hv hmean hbelow t ht
  have hbound := fullFeasible_objective_le_densityLimit _
    (fullFeasible_integrableTilt W hW.full v hv hmean hbelow t ht)
  rw [hreturn, ← hW.optimal] at hbound
  have hcost := hW.objective_integrableTilt v hv hmean hbelow t ht
  rw [hreturn, sub_self, mul_zero, add_zero] at hcost
  have hgain : 0 < t ^ 2 * KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v :=
    mul_pos (sq_pos_of_pos htpos) henergy
  linarith

/-- A quadratic endpoint strictly opposite to its nonzero initial slope
has an explicit interior return time. -/
theorem exists_quadratic_density_return (L A : ℝ) (hopp : L * (L + A) < 0) :
    ∃ t ∈ Ioo (0 : ℝ) 1, t * L + t ^ 2 * A = 0 := by
  have hAne : A ≠ 0 := by
    intro hz
    rw [hz, add_zero] at hopp
    exact (not_lt_of_ge (mul_self_nonneg L)) hopp
  have ht : -L / A ∈ Ioo (0 : ℝ) 1 := by
    rcases mul_neg_iff.mp hopp with h | h
    · have hA : A < 0 := by linarith [h.1, h.2]
      exact ⟨div_pos_of_neg_of_neg (neg_neg_of_pos h.1) hA,
        (div_lt_one_of_neg hA).mpr (by linarith [h.2])⟩
    · have hA : 0 < A := by linarith [h.1, h.2]
      exact ⟨div_pos (neg_pos.mpr h.1) hA, (div_lt_one hA).mpr (by linarith [h.2])⟩
  refine ⟨-L / A, ht, ?_⟩
  have hmul : (-L / A) * A = -L := div_mul_cancel₀ _ hAne
  calc
    _ = (-L / A) * (L + (-L / A) * A) := by ring
    _ = 0 := by rw [hmul]; ring

/-- Positive original shifted energy prevents the endpoint density from
being opposite to its original linear density coefficient. This is only
the positive-energy branch of the full density-return statement. -/
theorem FullStationaryClass.endpoint_density_sign_of_positive_energy
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (henergy : 0 < KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v) :
    0 ≤ (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) *
      (density (integrableTilt W v hv hmean hbelow 1 ⟨by norm_num, le_rfl⟩) - d) := by
  let L := ∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ
  let A := KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) v / 2
  have hpoly (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      density (integrableTilt W v hv hmean hbelow t ht) = d + t * L + t ^ 2 * A := by
    rw [density_integrableTilt, hW.density_eq]
    dsimp only [L, A]
    ring
  by_contra hnot
  have hopp : L * (L + A) < 0 := by
    have h := lt_of_not_ge hnot
    rw [hpoly 1 ⟨by norm_num, le_rfl⟩] at h
    change L * (d + 1 * L + 1 ^ 2 * A - d) < 0 at h
    nlinarith
  obtain ⟨t, ht, hzero⟩ := exists_quadratic_density_return L A hopp
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have heq := hpoly t htc
  apply hW.no_density_return_of_positive_energy v hv hmean hbelow henergy t htc ht0
  linarith

end Erdos1017.CappedModel

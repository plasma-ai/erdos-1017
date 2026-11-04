module

public import Erdos1017.Exclusions.Common.Flows.DiffuseFlowEnergyCredit

/-!
# Endpoint remainder of a diffuse rerouting

After a diffuse rerouting, the endpoint density on `C` is a uniform original-law
component plus a nonnegative remainder, and the endpoint recipient energy is
bounded by its uniform component plus eight times the endpoint mass times the
small-set error, so the full-flow energy covers it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original flow columns retained outside the rerouted source region. -/
def retainedSourceFlow (q : Ω × Ω → ℝ) (J : Set Ω) : Ω × Ω → ℝ :=
  (Prod.snd ⁻¹' Jᶜ).indicator q

omit [IsProbabilityMeasure μ] in
theorem integrable_retainedSourceFlow (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (J : Set Ω) (hJ : MeasurableSet J) :
    Integrable (retainedSourceFlow q J) (μ.prod μ) :=
  hq.indicator (hJ.compl.preimage measurable_snd)

omit [IsProbabilityMeasure μ] in
theorem retainedSourceFlow_nonnegative (q : Ω × Ω → ℝ)
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (J : Set Ω) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ retainedSourceFlow q J p := by
  filter_upwards [hq0] with p hp
  by_cases h : p.2 ∈ J <;> simp [retainedSourceFlow, h, hp]

omit [IsProbabilityMeasure μ] in
theorem receipt_retainedSourceFlow (q : Ω × Ω → ℝ) (J : Set Ω)
    (hJ : MeasurableSet J) (x : Ω) :
    receipt μ (retainedSourceFlow q J) x = ∫ y in Jᶜ, q (x, y) ∂μ := by
  change (∫ y, Jᶜ.indicator (fun y => q (x, y)) y ∂μ) = _
  rw [integral_indicator hJ.compl]

/-- Retaining only some source columns cannot increase actual receipt. -/
theorem receipt_retainedSourceFlow_le (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (J : Set Ω) (hJ : MeasurableSet J) :
    ∀ᵐ x ∂μ, receipt μ (retainedSourceFlow q J) x ≤ receipt μ q x := by
  filter_upwards [hq.prod_right_ae,
    (integrable_retainedSourceFlow q hq J hJ).prod_right_ae,
    Measure.ae_ae_of_ae_prod hq0] with x hx hr hn
  apply integral_mono_ae hr hx
  filter_upwards [hn] with y hy
  by_cases h : y ∈ J <;> simp [retainedSourceFlow, h, hy]

/-- The actual endpoint remainder contains the original recipient weight,
old receipt, and retained receipt, all on the original probability law. -/
def diffuseEndpointRemainder (μ : Measure Ω) (q : Ω × Ω → ℝ)
    (C J : Set Ω) (θ : ℝ) : Ω → ℝ :=
  C.indicator (fun x => 1 + (1 - θ) * receipt μ q x + θ * receipt μ (retainedSourceFlow q J) x)

theorem integrable_diffuseEndpointRemainder (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C J : Set Ω)
    (hC : MeasurableSet C) (hJ : MeasurableSet J) (θ : ℝ) :
    Integrable (diffuseEndpointRemainder μ q C J θ) μ :=
  (((integrable_const 1).add ((integrable_marginals hq).1.const_mul (1 - θ))).add
    ((integrable_marginals (integrable_retainedSourceFlow q hq J hJ)).1.const_mul θ)).indicator hC

theorem diffuseEndpointRemainder_nonnegative (q : Ω × Ω → ℝ)
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (C J : Set Ω)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, 0 ≤ diffuseEndpointRemainder μ q C J θ x := by
  filter_upwards [(nonnegative_marginals hq0).1,
    (nonnegative_marginals (retainedSourceFlow_nonnegative q hq0 J)).1] with x hx hr
  by_cases hC : x ∈ C
  · rw [diffuseEndpointRemainder, indicator_of_mem hC]
    exact add_nonneg (add_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr hθ.2) hx))
      (mul_nonneg hθ.1 hr)
  · rw [diffuseEndpointRemainder, indicator_of_notMem hC]

/-- The actual remainder mass is controlled by the original small-recipient
mass plus the old receipt, regardless of how large that receipt density is. -/
theorem integral_diffuseEndpointRemainder_le (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (∫ x, diffuseEndpointRemainder μ q C J θ x ∂μ) ≤
      μ.real C + ∫ x in C, receipt μ q x ∂μ := by
  have hle : ∀ᵐ x ∂μ, diffuseEndpointRemainder μ q C J θ x ≤
      C.indicator (fun x => 1 + receipt μ q x) x := by
    filter_upwards [receipt_retainedSourceFlow_le q hq hq0 J hJ] with x hx
    by_cases hCx : x ∈ C
    · simp only [diffuseEndpointRemainder, indicator_of_mem hCx]
      nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hx)]
    · simp only [diffuseEndpointRemainder, indicator_of_notMem hCx, le_refl]
  have hbound := integral_mono_ae (integrable_diffuseEndpointRemainder q hq C J hC hJ θ)
    (((integrable_const 1).add (integrable_marginals hq).1).indicator hC) hle
  rw [integral_indicator hC] at hbound
  change (∫ x, diffuseEndpointRemainder μ q C J θ x ∂μ) ≤
    (∫ x in C, 1 + receipt μ q x ∂μ) at hbound
  rw [integral_add (integrable_const 1)
    (integrable_marginals hq).1.restrict, setIntegral_const, smul_eq_mul, mul_one] at hbound
  exact hbound

end Erdos1017.MissingFlow

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- The current endpoint C-density is exactly a uniform original-law
component plus the constructed nonnegative original-law remainder. -/
theorem diffuse_endpoint_density_decomposition (hq : S.IsFullForwardFlow q)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0)
    (θ : ℝ) :
    C.indicator (integrableTiltWeight (MissingFlow.direction μ
      (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)) 1) =ᵐ[μ]
      fun x => (θ * μ.real J) * C.indicator (fun _ => 1 / μ.real C) x +
        MissingFlow.diffuseEndpointRemainder μ q C J θ x := by
  have hr := hq.redirect_diffuse C J hC hJ hpos hCD hCH hJL hJI hzero
  filter_upwards [hq.direction_affine hr θ, hq.supply, hr.supply,
    MissingFlow.receipt_redirect_decomposition q hq.integrable C J hJ] with x hd hs hsr hrec
  by_cases hx : x ∈ C
  · have hnL : x ∉ S.L := fun hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hCH hx) hL
    change MissingFlow.direction μ
      (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p) x =
      (1 - θ) * (MissingFlow.receipt μ q x - MissingFlow.supply μ q x) +
        θ * (MissingFlow.receipt μ (MissingFlow.redirect μ q C J) x -
          MissingFlow.supply μ (MissingFlow.redirect μ q C J) x) at hd
    simp only [hs, hsr, indicator_of_notMem hnL, sub_zero] at hd
    simp only [indicator_of_mem hx, integrableTiltWeight, one_mul,
      MissingFlow.diffuseEndpointRemainder]
    rw [hd, hrec, indicator_of_mem hx,
      MissingFlow.receipt_retainedSourceFlow q J hJ x]
    ring
  · simp only [MissingFlow.diffuseEndpointRemainder, indicator_of_notMem hx, mul_zero, add_zero]

/-- Integrating the actual endpoint density decomposition gives its exact
mass split into uniform supplied mass and the actual remainder mass. -/
theorem diffuse_endpoint_mass_split (hq : S.IsFullForwardFlow q)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (missingFlowEndpointLaw μ
      (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)).real C =
      θ * μ.real J + ∫ x, MissingFlow.diffuseEndpointRemainder μ q C J θ x ∂μ := by
  have hr := hq.redirect_diffuse C J hC hJ hpos hCD hCH hJL hJI hzero
  have ht := hq.convex hr θ hθ
  let v := MissingFlow.direction μ (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)
  have hv := MissingFlow.integrable_direction ht.integrable
  change (weightedMeasure (μ := μ) (integrableTiltWeight v 1)).real C = _
  rw [weightedMeasure_real_set _ (integrableTiltWeight_integrable v hv 1)
    (integrableTiltWeight_nonnegative v
      (MissingFlow.direction_ge_neg_one ht.nonnegative ht.supply_le_one) 1 ⟨by norm_num, le_rfl⟩) C hC,
    ← integral_indicator hC,
    integral_congr_ae (hq.diffuse_endpoint_density_decomposition C J hC hJ hpos hCD hCH hJL hJI hzero θ),
    integral_add (((integrable_const _).indicator hC).const_mul _)
      (MissingFlow.integrable_diffuseEndpointRemainder q hq.integrable C J hC hJ θ),
    integral_const_mul, integral_indicator hC, setIntegral_const, smul_eq_mul,
    mul_one_div, div_self hpos.ne', mul_one]

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded actual kernel pairs nonnegative L¹ densities by at most its
bound times their actual masses. No operator positivity is assumed. -/
theorem kernelPairing_le_bound_mul_integrals (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    kernelPairing (μ := μ) K f g ≤ B * (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
  have hle : kernelPairing (μ := μ) K f g ≤
      ∫ p : Ω × Ω, B * (g p.1 * f p.2) ∂μ.prod μ := by
    apply integral_mono_ae (integrable_kernel_bilinear hK hB hf hg)
      ((hg.mul_prod hf).const_mul B)
    filter_upwards [hB, Measure.quasiMeasurePreserving_fst.ae hg0,
      Measure.quasiMeasurePreserving_snd.ae hf0] with p hp hgx hfy
    have hk : K p.1 p.2 ≤ B := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hp)
    calc
      K p.1 p.2 * f p.2 * g p.1 ≤ B * f p.2 * g p.1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hfy) hgx
      _ = B * (g p.1 * f p.2) := by ring
  rw [integral_const_mul, integral_prod_mul] at hle
  nlinarith [hle]

/-- A small nonnegative L¹ remainder perturbs the uniform component's
actual energy by at most twice the kernel bound times total mass times
remainder mass. The reference density is normalized on the original law. -/
theorem kernelEnergy_add_remainder_le (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (ρ w : Ω → ℝ) (hρ : Integrable ρ μ) (hw : Integrable w μ)
    (hρ0 : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hmean : (∫ x, ρ x ∂μ) = 1) (a : ℝ) (ha : 0 ≤ a) :
    kernelEnergy (μ := μ) K (fun x => a * ρ x + w x) ≤
      a ^ 2 * kernelEnergy (μ := μ) K ρ +
        2 * B * (a + ∫ x, w x ∂μ) * (∫ x, w x ∂μ) := by
  have hcross := kernelPairing_le_bound_mul_integrals K hK hB (fun x => a * ρ x) w
    (hρ.const_mul a) hw (hρ0.mono (fun _ hx => mul_nonneg ha hx)) hw0
  rw [integral_const_mul, hmean, mul_one] at hcross
  have hself := kernelPairing_le_bound_mul_integrals K hK hB w w hw hw hw0 hw0
  change kernelEnergy (μ := μ) K w ≤ B * (∫ x, w x ∂μ) * (∫ x, w x ∂μ) at hself
  have heq : (fun x => a * ρ x + w x) = (fun x => a * ρ x - -1 * w x) :=
    funext (fun _ => by ring)
  rw [heq, kernelEnergy_sub_mul K hK hB hsym _ w (hρ.const_mul a) hw (-1), kernelEnergy_const_mul]
  nlinarith [mul_nonneg hB0 (sq_nonneg (∫ x, w x ∂μ))]

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Internal pair integrals under the current endpoint law are exactly
original-law energies of its actual restricted vertex density. -/
theorem endpoint_internal_kernel_integral (hq : S.IsFullForwardFlow q)
    (K : Ω → Ω → ℝ) (C : Set Ω) (hC : MeasurableSet C) :
    (∫ p : Ω × Ω in C ×ˢ C, K p.1 p.2 ∂(missingFlowEndpointLaw μ q).prod
      (missingFlowEndpointLaw μ q)) =
      KernelOperator.kernelEnergy (μ := μ) K
        (C.indicator (integrableTiltWeight (MissingFlow.direction μ q) 1)) := by
  let w := integrableTiltWeight (MissingFlow.direction μ q) 1
  have hw := integrableTiltWeight_integrable _ (MissingFlow.integrable_direction hq.integrable) 1
  have hw0 := integrableTiltWeight_nonnegative _
    (MissingFlow.direction_ge_neg_one hq.nonnegative hq.supply_le_one) 1 ⟨by norm_num, le_rfl⟩
  rw [← integral_indicator (hC.prod hC)]
  change (∫ p : Ω × Ω, (C ×ˢ C).indicator (fun p => K p.1 p.2) p
    ∂(weightedMeasure (μ := μ) w).prod (weightedMeasure (μ := μ) w)) = _
  rw [integral_weightedMeasure_prod w hw.aestronglyMeasurable.aemeasurable hw0
    (fun x y => (C ×ˢ C).indicator (fun p => K p.1 p.2) (x, y))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  by_cases hx : p.1 ∈ C <;> by_cases hy : p.2 ∈ C <;>
    simp [Set.mem_prod, hx, hy, w]

/-- The actual endpoint recipient energy is bounded by its uniform original-law
component plus eight times endpoint mass times the original small-set error.
The constant comes from the actual selected shifted-kernel bound of four. -/
theorem diffuse_endpoint_energy_remainder_bound (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (b : ℝ)
    (hmass : (missingFlowEndpointLaw μ
      (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)).real C = b) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (C.indicator (integrableTiltWeight (MissingFlow.direction μ
          (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)) 1)) ≤
      (θ * μ.real J) ^ 2 * KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (C.indicator (fun _ => 1 / μ.real C)) +
      8 * b * (μ.real C + ∫ x in C, MissingFlow.receipt μ q x ∂μ) := by
  let ρ := C.indicator (fun _ => 1 / μ.real C)
  let w := MissingFlow.diffuseEndpointRemainder μ q C J θ
  have hρ : Integrable ρ μ := (integrable_const _).indicator hC
  have hρ0 : ∀ᵐ x ∂μ, 0 ≤ ρ x := Eventually.of_forall
    (fun x => indicator_nonneg (fun _ _ => by positivity) x)
  have hmean : (∫ x, ρ x ∂μ) = 1 := by
    rw [integral_indicator hC, setIntegral_const, smul_eq_mul, mul_one_div, div_self hpos.ne']
  have hw := MissingFlow.integrable_diffuseEndpointRemainder q hq.integrable C J hC hJ θ
  have hw0 := MissingFlow.diffuseEndpointRemainder_nonnegative q hq.nonnegative C J θ hθ
  have hB : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hW.moment_mem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_of_nonneg hp.1]
    exact hp.2
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hp => hp.symm)
  have hbound := KernelOperator.kernelEnergy_add_remainder_le (shiftedKernel W m)
    (by norm_num : (0 : ℝ) ≤ 4) (shiftedKernel_measurable W m) hB hsym ρ w hρ hw hρ0 hw0
    hmean (θ * μ.real J) (mul_nonneg hθ.1 measureReal_nonneg)
  have hsplit : θ * μ.real J + (∫ x, w x ∂μ) = b :=
    (hq.diffuse_endpoint_mass_split C J hC hJ hpos hCD hCH hJL hJI hzero θ hθ).symm.trans hmass
  rw [hsplit] at hbound
  have hsmall := MissingFlow.integral_diffuseEndpointRemainder_le q hq.integrable hq.nonnegative
    C J hC hJ θ hθ
  have hb : 0 ≤ b := hmass ▸ measureReal_nonneg
  have herror : 2 * 4 * b * (∫ x, w x ∂μ) ≤
      8 * b * (μ.real C + ∫ x in C, MissingFlow.receipt μ q x ∂μ) := by
    nlinarith [mul_nonneg (show 0 ≤ 8 * b by positivity) (sub_nonneg.mpr hsmall)]
  rw [KernelOperator.kernelEnergy_congr_ae (shiftedKernel W m)
    (hq.diffuse_endpoint_density_decomposition C J hC hJ hpos hCD hCH hJL hJI hzero θ)]
  linarith

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The original full-flow energy covers the actual endpoint recipient's
internal shifted energy up to the controlled small-set error. No endpoint
stationarity or multiplier transfer is used. -/
theorem diffuse_endpoint_energy_le_flow_energy_add_error (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (b : ℝ)
    (hmass : (missingFlowEndpointLaw μ
      (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)).real C = b) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (C.indicator (integrableTiltWeight (MissingFlow.direction μ
          (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)) 1)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ
          (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)) +
      8 * b * (μ.real C + ∫ x in C, MissingFlow.receipt μ q x ∂μ) := by
  have herror := hq.diffuse_endpoint_energy_remainder_bound hW C J hC hJ hpos hCD hCH
    hJL hJI hzero θ hθ b hmass
  have hcredit := hq.diffuse_interpolation_energy_credit hW hd hgap C J hC hJ hpos hCD hCH
    hJL hJI hzero θ hθ
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

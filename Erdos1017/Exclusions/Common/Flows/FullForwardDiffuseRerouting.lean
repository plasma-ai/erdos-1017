module

public import Erdos1017.SelectedModel.Flows.FullForwardPeakAtom
public import Erdos1017.Exclusions.Common.Flows.SmallFlowRecipientSets

/-!
# Rerouting a full forward flow into a diffuse set

Rerouting a low atomic source region into a positive diffuse high set keeps full
forward membership when the rectangle is missing, keeps every avoided atom
avoided, and convex interpolations realize any recipient mass strictly between
the original endpoint mass and its source mass, including arbitrarily small
recipients.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Redirection into a general recipient retains all old receipt from
sources outside the replaced region. No exhaustion of old sources is assumed. -/
theorem receipt_redirect_decomposition (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C J : Set Ω) (hJ : MeasurableSet J) :
    ∀ᵐ x ∂μ, receipt μ (redirect μ q C J) x =
      μ.real J * C.indicator (fun _ => 1 / μ.real C) x + ∫ y in Jᶜ, q (x, y) ∂μ := by
  filter_upwards [hq.prod_right_ae] with x hx
  have heq : (fun y => redirect μ q C J (x, y)) =
      J.indicator (fun _ => C.indicator (fun _ => 1 / μ.real C) x) +
        Jᶜ.indicator (fun y => q (x, y)) := by
    funext y
    by_cases hy : y ∈ J <;> simp [redirect, hy]
  change (∫ y, redirect μ q C J (x, y) ∂μ) = _
  rw [heq]
  change (∫ y, J.indicator (fun _ => C.indicator (fun _ => 1 / μ.real C) x) y +
    Jᶜ.indicator (fun y => q (x, y)) y ∂μ) = _
  rw [integral_add ((integrable_const _).indicator hJ) (hx.indicator hJ.compl),
    integral_indicator hJ, integral_indicator hJ.compl, setIntegral_const, smul_eq_mul]

/-- A positive recipient obtains at least all replaced source mass; receipt
from unreplaced sources is nonnegative and is retained explicitly. -/
theorem integral_receipt_redirect_ge (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) :
    μ.real J ≤ ∫ x in C, receipt μ (redirect μ q C J) x ∂μ := by
  have hreceipt := receipt_redirect_decomposition q hq C J hJ
  have hle : ∀ᵐ x ∂μ.restrict C, μ.real J / μ.real C ≤ receipt μ (redirect μ q C J) x := by
    filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae hreceipt,
      ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hq0)] with x hx he hn
    rw [he, indicator_of_mem hx]
    have hnonneg : 0 ≤ ∫ y in Jᶜ, q (x, y) ∂μ :=
      integral_nonneg_of_ae (ae_restrict_of_ae hn)
    simp only [div_eq_mul_inv, one_mul]
    exact le_add_of_nonneg_right hnonneg
  have hbound := integral_mono_ae (integrable_const (μ.real J / μ.real C))
    ((integrable_marginals (integrable_redirect q hq C J hC hJ)).1.restrict) hle
  rw [setIntegral_const, smul_eq_mul, mul_div_cancel₀ _ hpos.ne'] at hbound
  exact hbound

end Erdos1017.MissingFlow

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The actual complete remainder is disjoint from every original atomic
whole-row fiber, pointwise by its defining complement identity. -/
theorem diffuse_disjoint_fiber (S : SelectedHighLowStructure W m) (i : S.I) :
    Disjoint S.D {x | S.ρ x = i} := by
  apply Set.disjoint_left.mpr
  intro x hx hxi
  rw [S.hDeq] at hx
  exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨i.property, hxi⟩⟩)

namespace IsFullForwardFlow

variable {S : SelectedHighLowStructure W m} {q r : Ω × Ω → ℝ}

/-- Actual endpoint masses of every measurable cell interpolate affinely
under the proved convex combination of actual full forward densities. -/
theorem endpoint_real_set_affine (hq : S.IsFullForwardFlow q) (hr : S.IsFullForwardFlow r)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (C : Set Ω) (hC : MeasurableSet C) :
    (missingFlowEndpointLaw μ (fun p => (1 - θ) * q p + θ * r p)).real C =
      (1 - θ) * (missingFlowEndpointLaw μ q).real C +
        θ * (missingFlowEndpointLaw μ r).real C := by
  have hmass (u : Ω × Ω → ℝ) (hu : S.IsFullForwardFlow u) :
      (missingFlowEndpointLaw μ u).real C = μ.real C + ∫ x in C, MissingFlow.direction μ u x ∂μ := by
    simpa only [missingFlowEndpointLaw, one_mul] using integrableTilt_real_set
      (MissingFlow.direction μ u) (MissingFlow.integrable_direction hu.integrable)
      (MissingFlow.direction_ge_neg_one hu.nonnegative hu.supply_le_one)
      1 ⟨by norm_num, le_rfl⟩ C hC
  rw [hmass _ (hq.convex hr θ hθ), hmass q hq, hmass r hr,
    integral_congr_ae (Measure.absolutelyContinuous_restrict.ae_le (hq.direction_affine hr θ)),
    integral_add ((MissingFlow.integrable_direction hq.integrable).restrict.const_mul _)
      ((MissingFlow.integrable_direction hr.integrable).restrict.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

/-- A HIGH recipient supplies nothing, so its actual endpoint mass is its
original mass plus actual receipt, even for unbounded receipt densities. -/
theorem endpoint_high_set_mass (hq : S.IsFullForwardFlow q)
    (C : Set Ω) (hC : MeasurableSet C) (hCH : C ⊆ S.H) :
    (missingFlowEndpointLaw μ q).real C =
      μ.real C + ∫ x in C, MissingFlow.receipt μ q x ∂μ := by
  apply MissingFlow.endpoint_real_set_eq_add_receipt q hq.integrable hq.nonnegative
    hq.supply_le_one C hC
  filter_upwards [hq.supply] with x hx hCx
  rw [hx, indicator_of_notMem]
  exact fun hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hCH hCx) hL

/-- Rerouting an actual LOW atomic source region into a positive diffuse
HIGH set preserves full forward membership when its actual rectangle is missing. -/
theorem redirect_diffuse (hq : S.IsFullForwardFlow q)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0) :
    S.IsFullForwardFlow (MissingFlow.redirect μ q C J) := by
  refine ⟨MissingFlow.integrable_redirect q hq.integrable C J hC hJ,
    MissingFlow.redirect_nonnegative q hq.nonnegative C J,
    MissingFlow.full_supply_redirect q C J S.L hC hpos hq.supply hJL, ?_⟩
  apply MissingFlow.support_redirect q C J
    {p | p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L} hq.support
  filter_upwards [hzero, Measure.quasiMeasurePreserving_snd.ae hJL,
    Measure.quasiMeasurePreserving_snd.ae hJI] with p hz hL hI hx hy
  refine ⟨⟨hz hx hy, ?_⟩, hCH hx, hL hy⟩
  intro heq
  exact Set.disjoint_left.mp (S.diffuse_disjoint_fiber ⟨S.ρ p.2, hI hy⟩) (hCD hx) heq

/-- Every original atom avoided by the old flow is still avoided after
rerouting into an actual diffuse recipient. -/
theorem redirect_diffuse_avoids (_hq : S.IsFullForwardFlow q)
    (C J : Set Ω) (hCD : C ⊆ S.D) (i : S.I)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    ∀ᵐ p ∂μ.prod μ, MissingFlow.redirect μ q C J p ≠ 0 → S.ρ p.1 ≠ i := by
  exact MissingFlow.avoids_redirect q C J {x | S.ρ x = i}
    ((S.diffuse_disjoint_fiber i).mono_left hCD) havoid

/-- The actual redirected endpoint contains at least the entire selected
source-region mass in its diffuse recipient; old receipt elsewhere remains. -/
theorem redirect_diffuse_endpoint_mass_ge (hq : S.IsFullForwardFlow q)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0) :
    μ.real J ≤ (missingFlowEndpointLaw μ (MissingFlow.redirect μ q C J)).real C := by
  rw [(hq.redirect_diffuse C J hC hJ hpos hCD hCH hJL hJI hzero).endpoint_high_set_mass C hC hCH]
  have hle := MissingFlow.integral_receipt_redirect_ge q hq.integrable hq.nonnegative C J hC hJ hpos
  linarith [measureReal_nonneg (μ := μ) (s := C)]

/-- An actual convex interpolation with diffuse redirection realizes any
recipient mass strictly between the old endpoint mass and the source mass.
Every original atomic label avoided by the old flow stays avoided. -/
theorem exists_diffuse_redirect_interpolation (hq : S.IsFullForwardFlow q)
    (C J : Set Ω) (hC : MeasurableSet C) (hJ : MeasurableSet J)
    (hpos : 0 < μ.real C) (hCD : C ⊆ S.D) (hCH : C ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0)
    (b : ℝ) (hstart : μ.real C + (∫ x in C, MissingFlow.receipt μ q x ∂μ) < b)
    (hfinish : b < μ.real J) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      S.IsFullForwardFlow (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p) ∧
      (missingFlowEndpointLaw μ
        (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)).real C = b ∧
      ∀ i : S.I, (∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) →
        ∀ᵐ p ∂μ.prod μ,
          (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p ≠ 0 → S.ρ p.1 ≠ i := by
  let r := MissingFlow.redirect μ q C J
  have hr := hq.redirect_diffuse C J hC hJ hpos hCD hCH hJL hJI hzero
  let a := (missingFlowEndpointLaw μ q).real C
  let z := (missingFlowEndpointLaw μ r).real C
  have hab : a < b := by
    dsimp only [a]
    rw [hq.endpoint_high_set_mass C hC hCH]
    exact hstart
  have hbz : b < z := hfinish.trans_le
    (hq.redirect_diffuse_endpoint_mass_ge C J hC hJ hpos hCD hCH hJL hJI hzero)
  have hza : 0 < z - a := by linarith
  let θ := (b - a) / (z - a)
  have hθ : θ ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hab) hza, (div_lt_one hza).mpr (by linarith)⟩
  refine ⟨θ, hθ, hq.convex hr θ ⟨hθ.1.le, hθ.2.le⟩, ?_, ?_⟩
  · rw [hq.endpoint_real_set_affine hr θ ⟨hθ.1.le, hθ.2.le⟩ C hC]
    change (1 - θ) * a + θ * z = b
    dsimp only [θ]
    field_simp
    ring
  · intro i havoid
    have havoidR := hq.redirect_diffuse_avoids C J hCD i havoid
    filter_upwards [havoid, havoidR] with p hp hpr hne hpi
    have hqzero : q p = 0 := by
      by_contra hqne
      exact hp hqne hpi
    have hrzero : MissingFlow.redirect μ q C J p = 0 := by
      by_contra hrne
      exact hpr hrne hpi
    apply hne
    rw [hqzero, hrzero]
    ring

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- An actual positive diffuse incidence region supplies arbitrarily small
recipients and genuine full-flow interpolations of prescribed endpoint mass.
Only the actual incidence rectangle is supplied at this intermediate layer. -/
theorem exists_small_diffuse_redirect_interpolation (hq : S.IsFullForwardFlow q)
    (C₀ J : Set Ω) (hC₀ : MeasurableSet C₀) (hJ : MeasurableSet J)
    (hpos : 0 < μ C₀) (hCD : C₀ ⊆ S.D) (hCH : C₀ ⊆ S.H)
    (hJL : ∀ᵐ y ∂μ, y ∈ J → y ∈ S.L)
    (hJI : ∀ᵐ y ∂μ, y ∈ J → S.ρ y ∈ S.I)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C₀ → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0)
    (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) (hfinish : b < μ.real J) :
    ∃ C ⊆ C₀, MeasurableSet C ∧ 0 < μ.real C ∧
      μ.real C + (∫ x in C, MissingFlow.receipt μ q x ∂μ) < ε ∧
      ∃ θ ∈ Ioo (0 : ℝ) 1,
        S.IsFullForwardFlow (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p) ∧
        (missingFlowEndpointLaw μ
          (fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p)).real C = b ∧
        ∀ i : S.I, (∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) →
          ∀ᵐ p ∂μ.prod μ,
            (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p ≠ 0 → S.ρ p.1 ≠ i := by
  obtain ⟨C, hCC, hC, hCp, hsmall⟩ := exists_positive_small_flow_recipient q hq.integrable
    C₀ hC₀ hpos (min ε b) (lt_min hε hb)
  have hzeroC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ J → shiftedKernel W m p.1 p.2 = 0 :=
    hzero.mono (fun _ hp hx hy => hp (hCC hx) hy)
  exact ⟨C, hCC, hC, hCp, hsmall.trans_le (min_le_left _ _),
    hq.exists_diffuse_redirect_interpolation C J hC hJ hCp (hCD.trans' hCC) (hCH.trans' hCC)
      hJL hJI hzeroC b (hsmall.trans_le (min_le_right _ _)) hfinish⟩

end IsFullForwardFlow

end Erdos1017.CappedModel.SelectedHighLowStructure

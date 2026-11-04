module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSourceDirection
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterHeadPrice
public import Erdos1017.Exclusions.Common.TwoCenter.TwoCenterSharedMassBound

/-!
# Schur energy bound of a two-center recovery

This module identifies the original conditional charge with the shifted
cross-head coefficient, derives the Schur quantitative premise from the guarded
head price, and applies the shared-source Schur argument on the recovered model
to bound the whole-source energy below by the shared credit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The original conditional old charge is identified with the original
shifted cross coefficient before any quantitative head-price substitution. -/
theorem original_headPrice_eq_headPairing (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    MultipartiteHeadPrice.headPrice W {x | S.ρ x = r.val} {x | S.ρ x = u.val} =
      S.headPairing r u + m * (if 0 < S.headPairing r u then 1 else 0) := by
  obtain ⟨q, _, hκ, hblock⟩ := S.exists_original_head_block r u hW
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = u.val}
  have hI := (S.hfibers r.val r.property).1
  have hJ := (S.hfibers u.val u.property).1
  have hprobI := PhysicalCliqueRepresentative.cellLaw_probability μ I (S.hfibers r.val r.property).2.1.ne'
  have hprobJ := PhysicalCliqueRepresentative.cellLaw_probability μ J (S.hfibers u.val u.property).2.1.ne'
  let := hprobI
  let := hprobJ
  have hy : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ J →
      chargeKernel W p.1 p.2 = q + m * (if 0 < q then 1 else 0) := by
    have hh := hblock.mono (fun _ hp => hp.2.2)
    rw [Measure.prod_restrict] at hh
    exact ((ae_restrict_iff' (hI.prod hJ)).mp hh).mono (fun _ hp hi hj => hp ⟨hi, hj⟩)
  have hc := ((PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous μ I).prod
    (PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous μ J)).ae_le hy
  have heq : (fun p : Ω × Ω => chargeKernel W p.1 p.2) =ᵐ[
      (MultipartiteHeadPrice.headLaw μ I).prod (MultipartiteHeadPrice.headLaw μ J)]
      fun _ => q + m * (if 0 < q then 1 else 0) := by
    filter_upwards [hc,
      Measure.quasiMeasurePreserving_fst.ae (MultipartiteHeadPrice.ae_mem_headLaw (μ := μ) hI),
      Measure.quasiMeasurePreserving_snd.ae (MultipartiteHeadPrice.ae_mem_headLaw (μ := μ) hJ)]
      with p hp hi hj
    exact hp hi hj
  change (∫ p, chargeKernel W p.1 p.2 ∂
    (MultipartiteHeadPrice.headLaw μ I).prod (MultipartiteHeadPrice.headLaw μ J)) = _
  rw [integral_congr_ae heq, hκ]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

namespace ReverseRecovery

variable (R : S.ReverseRecovery)
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Actual guarded original head price pays the Schur quantitative premise.
No price or cross-head coefficient hypothesis is used. -/
theorem headPairing_ge_two_stationary (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    2 * (2 * (c - m * d)) ≤ S.headPairing r u := by
  have hcard : R.plateau.card = 2 := by rw [hp, Finset.card_pair hru]
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hu : u ∈ R.plateau := by rw [hp]; simp
  have hprice := R.original_head_price_lower_bound hW hd hgap hcard hintercept r u hru hr hu
  rw [S.collapsedPartLabel_fiber, S.collapsedPartLabel_fiber,
    S.original_headPrice_eq_headPairing r u hW] at hprice
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨q, hq, hκ, _⟩ := S.exists_original_head_block r u hW
  have hnonnegative : 0 ≤ S.headPairing r u := hκ ▸ hq.1
  have hpositive : 0 < S.headPairing r u := by
    by_contra hn
    have hz : S.headPairing r u = 0 := le_antisymm (le_of_not_gt hn) hnonnegative
    rw [hz] at hprice
    norm_num at hprice
    linarith [hs.multiplier_neg, hs.gamma_pos]
  rw [ite_eq_left hpositive, mul_one] at hprice
  linarith only [hprice]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The actual shared/entire-source indicator pairing retains its literal
original kernel integral and original measure. -/
theorem shared_entire_pairing (r u : S.I) (hp : R.plateau = {r, u}) :
    schurForm W m (R.sharedMean r u hp) R.entireSourceMean =
      KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
        ((S.twoCenterShared r u).indicator (fun _ => 1))
        ((S.reverseCompulsorySource R.plateau).indicator (fun _ => 1)) := by
  rw [schurForm_eq_kernelPairing, KernelOperator.kernelPairing, KernelOperator.kernelPairing]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (R.sharedMean_coe r u hp),
    Measure.quasiMeasurePreserving_fst.ae R.entireSourceMean_coe] with p hs hc
  rw [hs, hc]

/-- The positive-shared-source Schur application derives all original Gram
entries and cone signs from the same physical recovered model. -/
theorem source_energy_ge_shared_of_headPairing (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) (hκ : 2 * (2 * (c - m * d)) ≤ S.headPairing r u)
    (hshared : 0 < μ (S.twoCenterShared r u)) :
    KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
        ((S.twoCenterShared r u).indicator (fun _ => 1))
        ((S.reverseCompulsorySource R.plateau).indicator (fun _ => 1)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow)) := by
  have hp' : R.plateau = {u, r} := by simpa only [Finset.pair_comm] using hp
  let ν := 2 * (c - m * d)
  have hν : 0 < ν := (hW.strict_gap_structure hd hgap).stationary_pos
  have hm := R.measurableSet_twoCenter_patterns r u hp
  have hmu := R.measurableSet_twoCenter_patterns u r hp'
  let c₁ := R.privateMean r u hp
  let c₂ := R.privateMean u r hp'
  let c₁₂ := R.sharedMean r u hp
  have hQ₁ : 0 ≤ schurForm W m c₁ c₁ := schurForm_indicator_nonnegative _ _ hW
  have hQ₂ : 0 ≤ schurForm W m c₂ c₂ := schurForm_indicator_nonnegative _ _ hW
  have hQ₁₂ : 0 ≤ schurForm W m c₁₂ c₁₂ := schurForm_indicator_nonnegative _ _ hW
  have hE₁ : schurForm W m (Lp.const 2 μ (1 : ℝ)) c₁ = ν * μ.real (S.twoCenterPrivate r u) :=
    schurForm_constant_indicator _ _ hW
  have hE₂ : schurForm W m (Lp.const 2 μ (1 : ℝ)) c₂ = ν * μ.real (S.twoCenterPrivate u r) :=
    schurForm_constant_indicator _ _ hW
  have hE₁₂ : 0 < schurForm W m (Lp.const 2 μ (1 : ℝ)) c₁₂ := by
    rw [show c₁₂ = indicatorVector _ hm.2.2 from rfl, schurForm_constant_indicator _ _ hW]
    exact mul_pos hν (ENNReal.toReal_pos hshared.ne' (measure_ne_top _ _))
  have hA₁ : schurForm W m (S.normalizedHead r) c₁ = 0 :=
    S.schurForm_head_indicator_zero_of_missing r _ hm.1 (fun _ hx => hx.1.2) hW
  have hB₂ : schurForm W m (S.normalizedHead u) c₂ = 0 :=
    S.schurForm_head_indicator_zero_of_missing u _ hmu.1 (fun _ hx => hx.1.2) hW
  have hA₁₂ : schurForm W m (S.normalizedHead r) c₁₂ = 0 :=
    S.schurForm_head_indicator_zero_of_missing r _ hm.2.2 (fun _ hx => hx.1.2) hW
  have hB₁₂ : schurForm W m (S.normalizedHead u) c₁₂ = 0 :=
    S.schurForm_head_indicator_zero_of_missing u _ hm.2.2 (fun _ hx => hx.2) hW
  have hcross₁ : c₁ ≠ 0 → 0 < schurForm W m c₁₂ c₁ :=
    fun hc => S.schurForm_shared_private_positive R r u hp hW hshared hc
  have hcross₂ : c₂ ≠ 0 → 0 < schurForm W m c₁₂ c₂ := by
    intro hc
    have hh := S.schurForm_shared_private_positive R u r hp' hW
      (by simpa only [S.twoCenterShared_comm u r] using hshared) hc
    change 0 < schurForm W m (R.sharedMean u r hp') (R.privateMean u r hp') at hh
    rw [R.sharedMean_comm r u hp] at hh
    exact hh
  have hr₁ : μ.real (S.twoCenterPrivate r u) ≤ R.headReceipt r u := by
    dsimp only [headReceipt]
    linarith only [R.sharedReceipt_nonnegative r u]
  have hr₂ : μ.real (S.twoCenterPrivate u r) ≤ R.headReceipt u r := by
    dsimp only [headReceipt]
    linarith only [R.sharedReceipt_nonnegative u r]
  have hbound := SchurHeadPlane.source_energy_ge_shared (schurForm W m)
    (fun f g => schurForm_symm f g) (schurForm_positiveIndexOn hW)
    (S.normalizedHead r) (S.normalizedHead u) (Lp.const 2 μ (1 : ℝ)) c₁ c₂ c₁₂
    ν (μ.real (S.twoCenterPrivate r u)) (μ.real (S.twoCenterPrivate u r))
    (R.headReceipt r u) (R.headReceipt u r) hν hκ
    (S.schurForm_head_self r) (S.schurForm_head_self u)
    (schurForm_constant_self hW) (S.schurForm_constant_head r hW) (S.schurForm_constant_head u hW)
    hE₁ hE₂ hE₁₂ hA₁ hB₂ hA₁₂ hB₁₂ hQ₁ hQ₂ hQ₁₂ hcross₁ hcross₂ hr₁ hr₂
  change schurForm W m (R.sharedMean r u hp) (R.privateMean r u hp + R.privateMean u r hp' + R.sharedMean r u hp) ≤
    schurForm W m
      (R.headReceipt r u • S.normalizedHead r + R.headReceipt u r • S.normalizedHead u -
        (R.privateMean r u hp + R.privateMean u r hp' + R.sharedMean r u hp))
      (R.headReceipt r u • S.normalizedHead r + R.headReceipt u r • S.normalizedHead u -
        (R.privateMean r u hp + R.privateMean u r hp' + R.sharedMean r u hp)) at hbound
  rw [R.sourceMeans_add r u hp] at hbound
  change schurForm W m (R.sharedMean r u hp) R.entireSourceMean ≤
    schurForm W m (R.sourceDirectionL2 r u) (R.sourceDirectionL2 r u) at hbound
  rw [R.shared_entire_pairing r u hp, R.sourceDirectionL2_energy r u hru hW hp] at hbound
  exact hbound

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Null shared patterns have zero original shared/entire-source pairing. -/
theorem shared_entire_pairing_zero_of_null (r u : S.I) (hp : R.plateau = {r, u})
    (hn : μ (S.twoCenterShared r u) = 0) :
    KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
      ((S.twoCenterShared r u).indicator (fun _ => 1))
      ((S.reverseCompulsorySource R.plateau).indicator (fun _ => 1)) = 0 := by
  rw [← R.shared_entire_pairing r u hp]
  have hz : R.sharedMean r u hp = 0 := indicatorVector_zero_of_null _ _ hn
  rw [hz, map_zero, LinearMap.zero_apply]

/-- Actual original head price and the paid Schur argument give the entire
source energy bound, including a null shared source. -/
theorem twoCenter_source_energy_ge_shared (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
        ((S.twoCenterShared r u).indicator (fun _ => 1))
        ((S.reverseCompulsorySource R.plateau).indicator (fun _ => 1)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow)) := by
  by_cases hs : 0 < μ (S.twoCenterShared r u)
  · exact R.source_energy_ge_shared_of_headPairing r u hru hW hd hgap hp
      (R.headPairing_ge_two_stationary r u hru hW hd hgap hp hintercept) hs
  · have hz : μ (S.twoCenterShared r u) = 0 := le_antisymm (le_of_not_gt hs) zero_le
    rw [R.shared_entire_pairing_zero_of_null r u hp hz]
    exact R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap R.measurableSet_source

/-- The actual recovered full energy pays both entire-source and shared
credits, on the same original model, multiplier and probability law. -/
theorem twoCenter_shared_energy_chain (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) ∧
    KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
        ((S.twoCenterShared r u).indicator (fun _ => 1))
        ((S.reverseCompulsorySource R.plateau).indicator (fun _ => 1)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow)) :=
  ⟨R.source_energy_le_full hW hd hgap,
    R.twoCenter_source_energy_ge_shared r u hru hW hd hgap hp hintercept⟩

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure

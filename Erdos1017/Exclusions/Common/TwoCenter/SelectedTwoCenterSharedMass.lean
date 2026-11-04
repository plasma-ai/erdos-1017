module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSchurEnergy

/-!
# Shared mass bound of a two-center recovery

This module bounds the shifted kernel by the color box, splits the constant mean
into heads, source and outside region, and turns the row estimates with the
Schur source energy into a reverse energy credit, so the shared mass is strictly
below the sharp original-slope bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

omit [IsProbabilityMeasure μ] in
/-- The actual compact color box pays the original shifted coefficient
upper bound; no coefficient-box hypothesis is used. -/
theorem shiftedKernel_le_one_sub (hm : m ≤ 1) (p : Ω × Ω) :
    shiftedKernel W m p.1 p.2 ≤ 1 - m := by
  have hy := charge_moment_le_adjacency W p
  have ha := adjacency_moment_mem W p
  have hmul := mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr hm)
  change shiftedMoment W m p ≤ 1 - m
  rw [shiftedMoment_eq]
  nlinarith only [hy, hmul]

private theorem indicator_coe (A : Set Ω) (hA : MeasurableSet A) :
    (indicatorVector (μ := μ) A hA : Ω → ℝ) =ᵐ[μ] A.indicator (fun _ => 1) := by
  change (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) : Ω → ℝ) =ᵐ[μ] _
  exact indicatorConstLp_coeFn

/-- Original indicator pairings are bounded by their original masses and
the derived pointwise color-box coefficient bound. -/
theorem schurForm_indicators_le_one_sub (A B : Set Ω) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hm : m ≤ 1) :
    schurForm W m (indicatorVector A hA) (indicatorVector B hB) ≤
      (1 - m) * μ.real A * μ.real B := by
  rw [schurForm_indicators]
  have hi : Integrable (fun p : Ω × Ω => shiftedKernel W m p.1 p.2) (μ.prod μ) :=
    (integrable_const _).mono' (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
  calc
    _ ≤ ∫ _ in B ×ˢ A, (1 - m) ∂μ.prod μ :=
      integral_mono_ae hi.integrableOn (integrable_const _)
        (Eventually.of_forall (fun p => shiftedKernel_le_one_sub hm p))
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, measureReal_prod_prod]
      ring

/-- The actual original head indicator is its original mass times its
normalized original head; no changed-law mass enters this identity. -/
theorem indicator_head_eq_mass_smul (r : S.I) :
    indicatorVector (μ := μ) {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 =
      μ.real {x | S.ρ x = r.val} • S.normalizedHead r := by
  have hn : μ.real {x | S.ρ x = r.val} ≠ 0 :=
    (ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top _ _)).ne'
  rw [normalizedHead, KernelOperator.normalizedSetL2, smul_smul, mul_inv_cancel₀ hn, one_smul]
  rfl

namespace ReverseRecovery

variable (R : S.ReverseRecovery)

/-- The remaining region's actual original indicator mean. -/
def outsideMean : Lp ℝ 2 μ := indicatorVector R.outsidePlateauSource R.measurableSet_outsidePlateauSource

/-- The original constant mean splits into original heads, entire source
and original outside region, using AE head/source disjointness correctly. -/
theorem original_partition_mean (r u : S.I) (hru : r ≠ u) (hp : R.plateau = {r, u}) :
    Lp.const 2 μ (1 : ℝ) =
      μ.real {x | S.ρ x = r.val} • S.normalizedHead r +
        μ.real {x | S.ρ x = u.val} • S.normalizedHead u + R.entireSourceMean + R.outsideMean := by
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = u.val}
  let ir := indicatorVector (μ := μ) I (S.hfibers r.val r.property).1
  let iu := indicatorVector (μ := μ) J (S.hfibers u.val u.property).1
  have hfun : ∀ᵐ x ∂μ, (1 : ℝ) = I.indicator (fun _ => 1) x + J.indicator (fun _ => 1) x +
      (S.reverseCompulsorySource R.plateau).indicator (fun _ => 1) x +
        R.outsidePlateauSource.indicator (fun _ => 1) x := by
    filter_upwards [R.ae_plateau_not_high] with x hx
    by_cases hr : S.ρ x = r.val
    · have hI : x ∈ I := hr
      have hnJ : x ∉ J := fun h => hru (Subtype.ext (hr.symm.trans h))
      have hregion : x ∈ R.plateauRegion := by rw [R.plateauRegion_eq_pair r u hp]; exact Or.inl hr
      have hnC : x ∉ S.reverseCompulsorySource R.plateau := fun h => hx hregion h.1
      have hnO : x ∉ R.outsidePlateauSource := fun h => h (Or.inl hregion)
      simp only [indicator_of_mem hI, indicator_of_notMem hnJ,
        indicator_of_notMem hnC, indicator_of_notMem hnO, add_zero]
    · by_cases hu : S.ρ x = u.val
      · have hnI : x ∉ I := hr
        have hJ : x ∈ J := hu
        have hregion : x ∈ R.plateauRegion := by rw [R.plateauRegion_eq_pair r u hp]; exact Or.inr hu
        have hnC : x ∉ S.reverseCompulsorySource R.plateau := fun h => hx hregion h.1
        have hnO : x ∉ R.outsidePlateauSource := fun h => h (Or.inl hregion)
        simp only [indicator_of_notMem hnI, indicator_of_mem hJ,
          indicator_of_notMem hnC, indicator_of_notMem hnO, zero_add, add_zero]
      · have hnI : x ∉ I := hr
        have hnJ : x ∉ J := hu
        have hnregion : x ∉ R.plateauRegion := by
          rw [R.plateauRegion_eq_pair r u hp]
          exact fun h => h.elim hr hu
        by_cases hc : x ∈ S.reverseCompulsorySource R.plateau
        · have hnO : x ∉ R.outsidePlateauSource := fun h => h (Or.inr hc)
          simp only [indicator_of_notMem hnI, indicator_of_notMem hnJ,
            indicator_of_mem hc, indicator_of_notMem hnO, zero_add, add_zero]
        · have hO : x ∈ R.outsidePlateauSource := fun h => h.elim hnregion hc
          simp only [indicator_of_notMem hnI, indicator_of_notMem hnJ,
            indicator_of_notMem hc, indicator_of_mem hO, zero_add]
  have heq : Lp.const 2 μ (1 : ℝ) = ir + iu + R.entireSourceMean + R.outsideMean := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ), Lp.coeFn_add (ir + iu + R.entireSourceMean) R.outsideMean,
      Lp.coeFn_add (ir + iu) R.entireSourceMean, Lp.coeFn_add ir iu,
      indicator_coe I (S.hfibers r.val r.property).1, indicator_coe J (S.hfibers u.val u.property).1,
      R.entireSourceMean_coe, indicator_coe R.outsidePlateauSource R.measurableSet_outsidePlateauSource,
      hfun] with x ha hb hc hd he hf hg hh hi
    change R.outsideMean x = _ at hh
    rw [ha, hb, Pi.add_apply, hc, Pi.add_apply, hd, Pi.add_apply, he, hf, hg, hh]
    exact hi
  rw [heq]
  change indicatorVector I _ + indicatorVector J _ + _ + _ = _
  rw [S.indicator_head_eq_mass_smul r, S.indicator_head_eq_mass_smul u]

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Flat original rows and the derived old color bound pay the shared
pairing by its original mass and the exact original outside mass. -/
theorem shared_pairing_linear_credit (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) :
    μ.real (S.twoCenterShared r u) *
        (2 * (1 - m) * R.height - 1 + (2 * (c - m * d) + m)) ≤
      KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
        ((S.twoCenterShared r u).indicator (fun _ => 1))
        ((S.reverseCompulsorySource R.plateau).indicator (fun _ => 1)) := by
  let ν := 2 * (c - m * d)
  let z := R.sharedMean r u hp
  have hmeas := (R.measurableSet_twoCenter_patterns r u hp).2.2
  have hzero₁ : schurForm W m z (S.normalizedHead r) = 0 :=
    (schurForm_symm _ _).trans (S.schurForm_head_indicator_zero_of_missing r _ hmeas
      (fun _ hx => hx.1.2) hW)
  have hzero₂ : schurForm W m z (S.normalizedHead u) = 0 :=
    (schurForm_symm _ _).trans (S.schurForm_head_indicator_zero_of_missing u _ hmeas
      (fun _ hx => hx.2) hW)
  have he : schurForm W m z (Lp.const 2 μ (1 : ℝ)) = ν * μ.real (S.twoCenterShared r u) :=
    (schurForm_symm _ _).trans (schurForm_constant_indicator _ _ hW)
  rw [R.original_partition_mean r u hru hp] at he
  simp only [map_add, map_smul, smul_eq_mul, hzero₁, hzero₂, mul_zero, zero_add] at he
  have hm : m ≤ 1 := by linarith [(hW.strict_gap_structure hd hgap).multiplier_neg]
  have hupper : schurForm W m z R.outsideMean ≤
      (1 - m) * μ.real (S.twoCenterShared r u) * μ.real R.outsidePlateauSource :=
    schurForm_indicators_le_one_sub _ _ hmeas R.measurableSet_outsidePlateauSource hm
  rw [R.outsidePlateauSource_mass r u hru hp] at hupper
  rw [← R.shared_entire_pairing r u hp]
  change μ.real (S.twoCenterShared r u) * (2 * (1 - m) * R.height - 1 + (ν + m)) ≤
    schurForm W m z R.entireSourceMean
  nlinarith only [he, hupper]

/-- The paid Schur source energy turns the original row/outside estimate
into an actual recovered full reverse energy credit. -/
theorem full_shared_linear_energy_credit (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    μ.real (S.twoCenterShared r u) *
        (2 * (1 - m) * R.height - 1 + (2 * (c - m * d) + m)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) := by
  have hchain := R.twoCenter_shared_energy_chain r u hru hW hd hgap hp hintercept
  exact (R.shared_pairing_linear_credit r u hru hW hd hgap hp).trans (hchain.2.trans hchain.1)

/-- The actual two-head recovery has shared mass strictly below the sharp
old-slope bound. All row, outside, head-price, Schur and energy premises
are derived from the same original model and physical recovery. -/
theorem twoCenter_shared_mass_lt (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hslope : (1 / 2 : ℝ) < -m) :
    μ.real (S.twoCenterShared r u) < (1 + m) / (4 * (-m)) ∧ (1 + m) / (4 * (-m)) < 1 / 4 := by
  have hcard : R.plateau.card = 2 := by rw [hp, Finset.card_pair hru]
  have hparameters := R.two_center_parameters hW hd hgap hcard hintercept
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hplateau : ∀ v ∈ R.plateau, S.reverseClassMass R.flow v = R.height :=
    fun v hv => (R.classMass_eq_iff hW v).mpr hv
  have hbudget := R.isFullReverseFlow.plateau_budget hW hd hgap R.plateau R.height
    (R.classMass_le hW) hplateau
  rw [hcard] at hbudget
  norm_num only [Nat.cast_ofNat] at hbudget
  have hpaid : (2 * (c - m * d) + m) +
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) ≤
        2 * (1 - (-m)) * R.height ^ 2 := by
    nlinarith only [hbudget.1, hbudget.2]
  have hlinear : μ.real (S.twoCenterShared r u) *
      (2 * (1 + (-m)) * R.height - 1 + (2 * (c - m * d) + m)) ≤
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) := by
    simpa only [sub_eq_add_neg] using R.full_shared_linear_energy_credit r u hru hW hd hgap hp hintercept
  have hbound := TwoCenterSharedMassBound.shared_mass_lt (-m) (2 * (c - m * d) + m)
    R.height (μ.real (S.twoCenterShared r u))
    (KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow))
    ⟨hslope, hparameters.2.1⟩ R.height_pos.le hparameters.2.2.2 measureReal_nonneg
    (by simpa only [sub_neg_eq_add] using hintercept) hE hlinear hpaid
  refine ⟨by simpa only [sub_neg_eq_add] using hbound, ?_⟩
  apply (div_lt_iff₀ (by positivity : 0 < 4 * (-m))).mpr
  linarith only [hslope]

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure

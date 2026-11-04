module

public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyPrimal

/-!
# Root charge rows in the zero-body branch

The stationary charge row is positive, and in the zero-body branch its only
positive contribution comes through the whole root, giving a quantitative lower
bound; the positive-cover root star is strictly positive almost everywhere off
its whole fiber.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original stationary charge row is positive. In the zero-body
branch its only positive contribution is through the original whole root,
which gives a quantitative lower bound on the actual averaged root star. -/
theorem ae_rootChargeRow_mass_lower_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val →
      2 * (c - m * d) + m ≤ μ.real {y | S.ρ y = r.val} * S.rootChargeRow r x := by
  have hs := hW.strict_gap_structure hd hgap
  let R := {x | S.ρ x = r.val}
  have hR : MeasurableSet R := (S.hfibers r.val r.property).1
  have hYint : Integrable (fun p : Ω × Ω => chargeKernel W p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hGint : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  have hroot : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → chargeKernel W p.1 p.2 = S.rootChargeRow r p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hr he hx
    exact he.symm.trans (hr hx)
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot
  have hcolumn : ∀ᵐ p ∂μ.prod μ, S.ρ p.2 = r.val → chargeKernel W p.1 p.2 = S.rootChargeRow r p.1 := by
    filter_upwards [hswap, chargeKernel_symm W] with p hp he hx
    exact he.trans (hp hx)
  filter_upwards [hW.stationary, hYint.prod_right_ae, hGint.prod_right_ae,
    Measure.ae_ae_of_ae_prod (S.zero_body_ae_charge_nonpositive r hzero),
    Measure.ae_ae_of_ae_prod hcolumn] with x hstat hYx hGx hbody hcol hx
  have hGle : (∫ y, adjacencyKernel W x y ∂μ) ≤ 1 := by
    have h := integral_mono_ae hGx (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun y => (adjacency_moment_mem W (x, y)).2))
    simpa using h
  have hMeq : (fun y => shiftedKernel W m x y) =
      fun y => chargeKernel W x y - m * adjacencyKernel W x y := by
    funext y
    exact shiftedMoment_eq W m (x, y)
  rw [hMeq, integral_sub hYx (hGx.const_mul m), integral_const_mul] at hstat
  have hmul := mul_le_mul_of_nonpos_left hGle hs.multiplier_neg.le
  have hlower : 2 * (c - m * d) + m ≤ ∫ y, chargeKernel W x y ∂μ := by
    nlinarith
  have hbound : ∀ᵐ y ∂μ, chargeKernel W x y ≤ R.indicator (fun _ => S.rootChargeRow r x) y := by
    filter_upwards [hbody, hcol] with y hb hc
    by_cases hy : y ∈ R
    · simpa only [indicator_of_mem hy] using (hc hy).le
    · simpa only [indicator_of_notMem hy] using hb hx hy
  have hupper := integral_mono_ae hYx ((integrable_const (S.rootChargeRow r x)).indicator hR) hbound
  rw [integral_indicator hR, setIntegral_const, smul_eq_mul] at hupper
  exact hlower.trans hupper

/-- The original positive-cover root star is strictly positive almost
everywhere off its literal whole fiber. -/
theorem ae_rootChargeRow_pos_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val → 0 < S.rootChargeRow r x := by
  have hs := hW.strict_gap_structure hd hgap
  filter_upwards [S.ae_rootChargeRow_mass_lower_of_zero_body r hW hd hgap hzero] with x hx hr
  have hp := lt_of_lt_of_le hs.gamma_pos (hx hr)
  by_contra hn
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (le_of_not_gt hn))) hp

end Erdos1017.CappedModel.SelectedHighLowStructure

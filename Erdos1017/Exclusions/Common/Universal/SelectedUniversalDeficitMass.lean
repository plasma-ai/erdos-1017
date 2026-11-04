module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitBudget
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitRows

/-!
# Universal atom mass below the saturated deficit ratio

A positive outside hole region of the saturated partner forces the universal
atom's mass below the saturated deficit ratio, using the original row and
missing mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.UniversalDeficit

private theorem deficit_gt_floor_of_mass_lt {A eta u a k D delta Delta : ℝ}
    (hdelta : 0 < delta) (hD : 0 ≤ D) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hcapacity : a + k ≤ eta + u - A)
    (hrow : delta * (eta + u - a) - Delta ≤ (eta + u - A - 2 * a - k) * D)
    (hmass : Delta < delta * A) : delta < D := by
  have hC : 0 ≤ eta + u - A - a := by linarith
  have hright : 0 < delta * (eta + u - a) - Delta := by
    nlinarith [mul_nonneg hdelta.le hC]
  have hcoef : 0 < eta + u - A - 2 * a - k := by
    by_contra hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hD
    linarith
  by_contra hn
  have hprod := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hcoef.le
  have hnonneg := mul_nonneg hdelta.le (add_nonneg ha hk)
  nlinarith

private theorem atom_mass_le_ratio_of_hole_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Set Ω) (hpos : 0 < μ H)
    (D a k : Ω → ℝ) (hD : IntegrableOn D H μ)
    {A u delta Delta : ℝ} (hdelta : 0 < delta)
    (hcap : (∫ x in H, D x ∂μ) ≤ Delta - delta * u)
    (hrows : ∀ᵐ x ∂μ.restrict H,
      0 ≤ D x ∧ 0 ≤ a x ∧ 0 ≤ k x ∧
        a x + k x ≤ μ.real H + u - A ∧
        delta * (μ.real H + u - a x) - Delta ≤
          (μ.real H + u - A - 2 * a x - k x) * D x) : A ≤ Delta / delta := by
  have hcapacity : A ≤ μ.real H + u := by
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' hrows
    linarith [hx.2.1, hx.2.2.1, hx.2.2.2.1]
  by_contra hn
  have hmass : Delta < delta * A := by
    have h := (div_lt_iff₀ hdelta).mp (lt_of_not_ge hn)
    nlinarith
  have hstrict : ∀ᵐ x ∂μ.restrict H, delta < D x := by
    filter_upwards [hrows] with x hx
    exact deficit_gt_floor_of_mass_lt hdelta hx.1 hx.2.1 hx.2.2.1
      hx.2.2.2.1 hx.2.2.2.2 hmass
  have hle : (fun _ : Ω => delta) ≤ᵐ[μ.restrict H] D :=
    hstrict.mono (fun _ hx => hx.le)
  have hbound : (∫ x : Ω in H, delta ∂μ) < ∫ x in H, D x ∂μ := by
    apply lt_of_le_of_ne (integral_mono_ae (integrable_const delta) hD hle)
    intro heq
    have hsame := (integral_eq_iff_of_ae_le (integrable_const delta) hD hle).mp heq
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
      (hstrict.and hsame)
    linarith [hx.1, hx.2]
  rw [setIntegral_const, smul_eq_mul] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hcapacity hdelta.le
  nlinarith

end Erdos1017.UniversalDeficit

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- A positive entire outside hole region of the actual saturated partner
forces the original universal atom below the saturated deficit ratio.
The original row, missing mass and score budgets are all derived. -/
theorem universal_atom_mass_le_saturated_deficit_ratio
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hholes : 0 < μ (S.universalPartnerHoleRegion r p)) :
    S.originalAtomMass r ≤ (1 - m - 4 * (c - m * d)) / (1 + m) := by
  refine UniversalDeficit.atom_mass_le_ratio_of_hole_rows
    (S.universalPartnerHoleRegion r p) hholes
    (S.universalRootDeficit r) (S.universalPartnerHoleMissingMass r p)
    (S.universalPartnerCommonMissingMass r p)
    (S.integrable_universalRootDeficit r).integrableOn (by linarith)
    (S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN) ?_
  filter_upwards [S.ae_universalPartnerHole_missing_capacity r p hpair hW hd hgap hell hN,
    S.ae_universalPartnerHole_deficit_row r p hpair hW hd hgap hell hN]
    with x hcapacity hrow
  refine ⟨(S.universalRootDeficit_mem_Icc r x).1,
    S.universalPartnerHoleMissingMass_nonneg r p x,
    S.universalPartnerCommonMissingMass_nonneg r p x, hcapacity, ?_⟩
  have hmissing := S.universalPartnerCommonMissingDeficit_ge_floor
    r p hpair hW hd hgap hell hN x
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure

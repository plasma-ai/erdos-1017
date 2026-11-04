module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateSourceBounds
public import Erdos1017.Exclusions.E2.Upper.E2PrivateTwoCenterScalar

/-!
# No largest atom in the first private source

A largest original atom cannot lie in the entire first private source of a
recovered two-center `E₂` plateau; the radius, source cover and reverse energy
budget are combined (`no_e2_private_largest_atom`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- A largest original atom cannot lie in the entire first private source of
an actual recovered two-center E2 plateau. The radius, source cover, and
reverse energy budget are derived from the same original selected model. -/
theorem no_e2_private_largest_atom (i r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.twoCenterPrivate r u)
    (hmax : ∀ k : S.I, S.originalAtomMass k ≤ S.originalAtomMass i)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  let γ := 2 * (c - m * d) + m
  let δ := 1 + m
  let κ := S.headPairing r u
  let ζ := S.twoCenterPrivateThreshold r u
  let A := S.originalAtomMass i
  let B := missingMassCapRadius d c m A
  let t := R.height
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  obtain ⟨hm, hell, hγfloor⟩ := hW.e2_gamma_floor hq hdq hgap hglobal
  have hδ : 0 < δ := by dsimp [δ]; linarith [hell.2]
  have hintercept := hW.e2_intercept_guard hq hdq hgap hglobal
  have hγquarter : δ / 4 < γ := by
    dsimp [δ, γ]
    linarith
  have hζ := R.private_threshold_pos_le_pairing r u hru hW hd hgap hp hintercept
  have hκlower := R.headPairing_ge_two_stationary r u hru hW hd hgap hp hintercept
  have hκupper : κ ≤ 1 - m := by
    have hr : r ∈ R.plateau := by rw [hp]; simp
    have hu : u ∈ R.plateau := by rw [hp]; simp
    have hprice := R.currentHeadPrice_le_one hW r u hr hu
    rw [R.current_head_price_eq_original hW r u hr hu,
      S.collapsedPartLabel_fiber, S.collapsedPartLabel_fiber,
      S.original_headPrice_eq_headPairing r u hW] at hprice
    have hκpos : 0 < κ := by
      dsimp [κ]
      linarith [hκlower, (hW.strict_gap_structure hd hgap).stationary_pos]
    change 0 < S.headPairing r u at hκpos
    simp only [ite_eq_left hκpos, mul_one] at hprice
    dsimp [κ]
    linarith
  have hradius := R.private_e2_radius_bounds i r u hru hp hprivate hmax
    hW hq hdq hgap hglobal
  have hBnonneg : 0 ≤ B := hradius.1
  have hBidentity : (-m) * B ^ 2 = (2 + m) * A ^ 2 - γ := hradius.2.1
  have hsource := R.e2_private_source_scalar_lower_bound i r u hru hp hprivate hmax
    hW hq hdq hgap hglobal
  have hsource' : ζ * (t / 2 + A - B / 2) ≤ κ - 4 * (c - m * d) := by
    convert hsource using 1; ring
  have henergy : γ ≤ 2 * δ * t ^ 2 := by
    have hcard : R.plateau.card = 2 := by rw [hp, Finset.card_pair hru]
    have hplateau : ∀ k ∈ R.plateau, S.reverseClassMass R.flow k = t :=
      fun k hk => (R.classMass_eq_iff hW k).mpr hk
    have hbudget := R.isFullReverseFlow.plateau_budget hW hd hgap R.plateau t
      (R.classMass_le hW) hplateau
    rw [hcard] at hbudget
    norm_num only [Nat.cast_ofNat] at hbudget
    have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
    dsimp [γ, δ, t]
    nlinarith [hbudget.1, hbudget.2]
  have hbudget : t / 2 + A - B / 2 ≤ 1 - 2 * γ / δ := by
    have hζpos : 0 < ζ := hζ.1
    have hnonneg : 0 ≤ 1 - κ - m := by linarith [hκupper]
    have hgap' : 0 < 4 * γ - δ := by linarith [hγquarter]
    have hprod : 0 ≤ (4 * γ - δ) * (1 - κ - m) :=
      mul_nonneg hgap'.le hnonneg
    have halgebra :
        ζ * (δ - 2 * γ) - δ * (κ - 4 * (c - m * d)) =
          (4 * γ - δ) * (1 - κ - m) := by
      dsimp [γ, δ, ζ, κ, twoCenterPrivateThreshold]
      ring
    have hscaled : δ * ζ * (t / 2 + A - B / 2) ≤ ζ * (δ - 2 * γ) := by
      nlinarith [hsource', hprod, halgebra, hδ]
    have hscaled' : ζ * (δ * (t / 2 + A - B / 2)) ≤ ζ * (δ - 2 * γ) := by
      nlinarith [hscaled]
    have hdiv : δ * (t / 2 + A - B / 2) ≤ δ - 2 * γ := by
      nlinarith [hscaled', hζpos]
    calc
      t / 2 + A - B / 2 ≤ (δ - 2 * γ) / δ :=
        (le_div_iff₀ hδ).mpr (by nlinarith [hdiv])
      _ = 1 - 2 * γ / δ := by field_simp
  have hA : 0 ≤ A := (S.originalAtomMass_summable).1 i
  have ht : 0 ≤ t := R.height_pos.le
  have hscalarIdentity : LowerE2Scalar.multiplier q * B ^ 2 =
      (2 - LowerE2Scalar.multiplier q) * A ^ 2 - γ := by
    simpa only [hm, neg_neg, sub_eq_add_neg] using hBidentity
  have hscalarEnergy : γ ≤ 2 * (1 - LowerE2Scalar.multiplier q) * t ^ 2 := by
    simpa only [δ, hm, sub_eq_add_neg] using henergy
  have hscalarBudget : 1 - 2 * γ / (1 - LowerE2Scalar.multiplier q) ≥
      t / 2 + A - B / 2 := by
    simpa only [δ, hm, sub_eq_add_neg] using hbudget
  exact LowerE2Scalar.private_two_center_scalar_contradiction hq
    (by simpa only [γ] using hγfloor) ht hA hBnonneg
    hscalarIdentity hscalarEnergy hscalarBudget

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

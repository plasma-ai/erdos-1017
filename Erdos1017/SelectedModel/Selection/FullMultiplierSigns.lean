module

public import Erdos1017.SelectedModel.Selection.FullNonnegativeBound
public import Erdos1017.Models.Capped.CappedGrowingLimit
public import Erdos1017.Models.Capped.CappedPositiveDirection

/-!
# Signs of the multipliers above the complement baseline

A fully feasible model above the complement-density baseline with nonnegative
shifted moment has negative `m` and positive source multiplier `ell = -m`, and
below density one half its stationary value is positive.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem charge_moment_nonnegative_of_nonnegative_multiplier (W : Model Ω μ) (m : ℝ)
    (hm : 0 ≤ m) (hM : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ W.moment CappedColor.charge p := by
  filter_upwards [hM] with p hp
  rw [shiftedMoment_eq] at hp
  have hprod := mul_nonneg hm (adjacency_moment_mem W p).1
  linarith

/-- A genuine fully feasible model above the complement-density baseline
has negative `m` whenever its shifted moment is nonnegative. The source
multiplier `ell=-m` is therefore positive. No multipartite lower envelope
is assumed by this statement. -/
theorem full_multiplier_neg_of_complement_excess (W : Model Ω μ) (hW : FullFeasible W)
    (m : ℝ) (hexcess : 1 / 2 - density W < objective W)
    (hM : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) : m < 0 := by
  by_contra hm
  have hY := charge_moment_nonnegative_of_nonnegative_multiplier W m (not_lt.mp hm) hM
  have hbound := full_moment_nonnegative_objective_add_density_le_half W hW hY
  linarith

/-- Below density one half, strict complement-baseline excess and a
nonnegative shifted kernel give positive stationary value, with all signs
derived from the actual full model. -/
theorem full_stationary_value_pos_of_complement_excess (W : Model Ω μ) (hW : FullFeasible W)
    (m ν : ℝ) (hexcess : 1 / 2 - density W < objective W)
    (hdhalf : density W < 1 / 2)
    (hM : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) : 0 < ν := by
  have hm := full_multiplier_neg_of_complement_excess W hW m hexcess hM
  have hc : 0 < objective W := by linarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg hm.le (density_mem W).1
  rw [shifted_stationary_value W m ν hrow]
  linarith

theorem full_source_multiplier_positive_of_complement_excess (W : Model Ω μ) (hW : FullFeasible W)
    (m : ℝ) (hexcess : 1 / 2 - density W < objective W)
    (hM : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) : 0 < -m :=
  neg_pos.mpr (full_multiplier_neg_of_complement_excess W hW m hexcess hM)

end Erdos1017.CappedModel

module

public import Erdos1017.Models.PhysicalPrimal.TupleSampling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# From a failed repeat test to a two-copy violation

Failure of the all-order tests gives a finite positive-measure violating event
under the independent product sampling law, above one half a violating repeat
count already has a two-copy violation, and the one-copy constraint turns it
into a strict lower bound on that copy's exterior incidence.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.FiniteArity

/-- Failure of actual all-order tests gives a finite positive-measure
violating event under the original independent product sampling law. -/
theorem exists_positive_violation_of_not_all_feasible
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hnot : ¬∀ n, 2 ≤ n → FeasibleOrder μ A Y n) :
    ∃ n, 2 ≤ n ∧ 0 < (Measure.pi (fun _ : Fin n => μ))
      {v | TupleClique A v ∧ 1 < tupleCharge Y v} := by
  classical
  push Not at hnot
  obtain ⟨n, hn, hbad⟩ := hnot
  refine ⟨n, hn, pos_iff_ne_zero.mpr ?_⟩
  intro hz
  apply hbad
  have hgood := (measure_eq_zero_iff_ae_notMem).mp hz
  filter_upwards [hgood] with v hv hc
  exact le_of_not_gt (fun hgt => hv ⟨hc, hgt⟩)

end Erdos1017.FiniteArity

namespace Erdos1017.CoveredRepeat

/-- Above one half, a violating finite repeat count already has a
two-copy violation when each copy's exterior incidence is at most one. -/
theorem two_copy_violation_of_repeat {ell base incidence : ℝ} {r : ℕ}
    (hell : 1 / 2 < ell) (hr : 2 ≤ r) (hincidence : incidence ≤ 1)
    (hbad : 1 < base + r * incidence - ell * r * ((r : ℝ) - 1) / 2) :
    1 < base + 2 * incidence - ell := by
  by_cases heq : r = 2
  · subst r
    norm_num at hbad
    linarith
  have hr3 : 3 ≤ (r : ℝ) := by exact_mod_cast (show 3 ≤ r by omega)
  have hell0 : 0 ≤ ell := by linarith
  have hmul := mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ r + 1 by linarith) hell0
  have hfactor : incidence - ell * ((r : ℝ) + 1) / 2 ≤ 0 := by linarith
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (r : ℝ) - 2 by linarith) hfactor
  have he : base + r * incidence - ell * r * ((r : ℝ) - 1) / 2 =
      base + 2 * incidence - ell +
        ((r : ℝ) - 2) * (incidence - ell * ((r : ℝ) + 1) / 2) := by ring
  rw [he] at hbad
  linarith

/-- The original one-copy constraint converts a genuine two-copy
violation into a strict lower bound on that copy's exterior incidence. -/
theorem incidence_gt_of_two_copy_violation {ell base incidence : ℝ}
    (hold : base + incidence ≤ 1)
    (hbad : 1 < base + 2 * incidence - ell) : ell < incidence := by
  linarith

end Erdos1017.CoveredRepeat

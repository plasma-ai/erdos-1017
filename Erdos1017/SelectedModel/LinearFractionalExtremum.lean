module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring

/-!
# Local constancy of a scalar quotient at a local minimum

For the scalar quotient `linearFractional` of a recorded multiplier along a
tilt, a local minimum forces the cross-product identity, so the quotient is
constant wherever the denominator is nonzero and equals its value at zero.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- The actual scalar quotient used for a recorded multiplier along a tilt. -/
def linearFractional (a b c d t : ℝ) : ℝ := (a + b * t) / (c + d * t)

/-- The denominator stays nonzero near zero by its actual continuity. -/
theorem linearFractional_eventually_ne_zero_den (c d : ℝ) (hc : c ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), c + d * t ≠ 0 := by
  have h : ContinuousAt (fun t : ℝ => c + d * t) 0 := by fun_prop
  exact h.eventually_ne (by simpa using hc)

/-- The rational derivative is derived from the numerator and denominator. -/
theorem linearFractional_hasDerivAt_zero (a b c d : ℝ) (hc : c ≠ 0) :
    HasDerivAt (linearFractional a b c d) ((b * c - a * d) / c ^ 2) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hn := (hi.const_mul b).const_add a
  have hd := (hi.const_mul d).const_add c
  convert hn.div hd (by simpa using hc) using 1
  · funext t
    rfl
  · simp

/-- Fermat at an actual local minimum forces the exact cross-product identity. -/
theorem linearFractional_cross_eq_of_local_min {a b c d : ℝ} (hc : c ≠ 0)
    (hmin : IsLocalMin (linearFractional a b c d) 0) : b * c = a * d := by
  have hzero := hmin.hasDerivAt_eq_zero (linearFractional_hasDerivAt_zero a b c d hc)
  have hnum : b * c - a * d = 0 := (div_eq_zero_iff.mp hzero).resolve_right (pow_ne_zero 2 hc)
  exact sub_eq_zero.mp hnum

/-- A zero cross-product derivative makes the quotient constant at every
point where its actual denominator is nonzero. -/
theorem linearFractional_eq_of_cross_eq {a b c d t : ℝ} (hc : c ≠ 0)
    (hcross : b * c = a * d) (ht : c + d * t ≠ 0) :
    linearFractional a b c d t = a / c := by
  unfold linearFractional
  apply (div_eq_div_iff ht hc).mpr
  calc
    (a + b * t) * c = a * c + (b * c) * t := by ring
    _ = a * (c + d * t) := by
      rw [hcross]
      ring

/-- The local extremum hypothesis derives constancy on the full nonzero
part of the denominator's domain. -/
theorem linearFractional_eq_of_local_min {a b c d t : ℝ} (hc : c ≠ 0)
    (hmin : IsLocalMin (linearFractional a b c d) 0) (ht : c + d * t ≠ 0) :
    linearFractional a b c d t = a / c :=
  linearFractional_eq_of_cross_eq hc (linearFractional_cross_eq_of_local_min hc hmin) ht

/-- The quotient equals its actual value at zero wherever the denominator
is nonzero, as a consequence of the local minimum. -/
theorem linearFractional_eq_at_zero_of_local_min {a b c d t : ℝ} (hc : c ≠ 0)
    (hmin : IsLocalMin (linearFractional a b c d) 0) (ht : c + d * t ≠ 0) :
    linearFractional a b c d t = linearFractional a b c d 0 := by
  simpa only [linearFractional, mul_zero, add_zero] using linearFractional_eq_of_local_min hc hmin ht

/-- Local constancy follows with no supplied neighborhood or denominator path. -/
theorem linearFractional_eventually_eq_of_local_min {a b c d : ℝ} (hc : c ≠ 0)
    (hmin : IsLocalMin (linearFractional a b c d) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), linearFractional a b c d t = a / c := by
  filter_upwards [linearFractional_eventually_ne_zero_den c d hc] with t ht
  exact linearFractional_eq_of_local_min hc hmin ht

end Erdos1017.Variation

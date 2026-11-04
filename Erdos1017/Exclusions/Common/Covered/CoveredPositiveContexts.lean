module

public import Erdos1017.Exclusions.Common.Covered.CoveredRepeatWitness

/-!
# Bare-root witnesses under positive `E`

With positive `E` and the strict star and penalty bounds, any of the three
witnessing contexts forces the bare-root context to witness, and two distinct
bare-root witnesses violate their joint rooted constraint when their cross
penalty is at most `ell`.
-/

@[expose] public section

namespace Erdos1017.CoveredRepeat

/-- With positive E and the actual strict star/penalty bounds, any of
the three witnessing contexts forces the bare-root context to witness. -/
theorem bare_witness_of_three_contexts {ell t h v z d : ℝ}
    (hell : 1 / 2 < ell) (hv : ell < v) (hz : (1 - ell) / 2 < z)
    (hR : t + h - z ≤ 1) (hE : t + v - d ≤ 1)
    (hwitness : ell < 2 * t - 1 ∨
      ell < 2 * t - 1 + h - 2 * z ∨ ell < 2 * t - 1 + v - 2 * d) :
    ell < 2 * t - 1 := by
  rcases hwitness with hbare | hRcopy | hEcopy
  · exact hbare
  · have hh : h < 1 - ell := by linarith
    linarith
  · have hsmall : 2 * t - 1 + v - 2 * d ≤ 1 - v := by linarith
    linarith

/-- Two distinct bare-root witnesses violate their actual original
joint rooted constraint when their cross penalty is at most ell. -/
theorem not_two_bare_witnesses {ell first second penalty : ℝ}
    (hfirst : ell < 2 * first - 1) (hsecond : ell < 2 * second - 1)
    (hjoint : first + second - penalty ≤ 1) (hpenalty : penalty ≤ ell) : False := by
  linarith

end Erdos1017.CoveredRepeat

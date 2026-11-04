module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleThresholds
public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleRpowRound

/-!
# Probability budget of a normalized nibble round

The explicit small-error inequalities of the normalized schedule imply the
simultaneous-round probability budget, uniformly in every larger order and
degree scale (`normalized_round_budget`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

/-- The normalized schedule's explicit small-error inequalities imply the actual
simultaneous-round probability budget, uniformly in every larger order and degree scale. -/
theorem normalized_round_budget (P C ε D N E : ℝ) (r T : ℕ)
    (hP : 0 < P) (hC : 0 < C) (hε : 0 < ε) (hD : 0 < D) (hN : 0 < N) (hr : 0 < r)
    (hE : E ≤ C * D * N)
    (hsmall : P * ε ^ (2 * T + 4) + P * (r : ℝ) ^ 2 * C ^ 2 * ε ^ (T + 2) < 1 / 4)
    (hlarge : P * C / (ε ^ 2 * N) < 1 / 4) :
    (P / D) * N * (C * D + N * (ε ^ (2 * T + 6) * D)) / (ε * N) ^ 2 +
      ((P / D) * (r * (ε ^ (2 * T + 6) * D)) * (r * (C * D)) * (C * D) * N /
        (ε * D) ^ 2) / (ε ^ (T + 2) * N) +
      ((P / D) ^ 2 * r ^ 2 * (C * D) * E) / (4 * P ^ 2 * r ^ 2 * C ^ 2 * N) < 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hpow1 : ε ^ (2 * T + 6) = ε ^ (2 * T + 4) * ε ^ 2 := by
    rw [← pow_add]
  have hpow2 : ε ^ (2 * T + 6) = ε ^ (T + 2) * ε ^ (T + 2) * ε ^ 2 := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hfirst : (P / D) * N * (C * D + N * (ε ^ (2 * T + 6) * D)) / (ε * N) ^ 2 =
      P * C / (ε ^ 2 * N) + P * ε ^ (2 * T + 4) := by
    rw [hpow1]
    field_simp
  have hsecond : ((P / D) * (r * (ε ^ (2 * T + 6) * D)) * (r * (C * D)) * (C * D) * N /
      (ε * D) ^ 2) / (ε ^ (T + 2) * N) = P * (r : ℝ) ^ 2 * C ^ 2 * ε ^ (T + 2) := by
    rw [hpow2]
    field_simp
  have hthird : ((P / D) ^ 2 * r ^ 2 * (C * D) * E) / (4 * P ^ 2 * r ^ 2 * C ^ 2 * N) =
      E / (4 * C * D * N) := by
    field_simp
  rw [hfirst, hsecond, hthird]
  have hlast : E / (4 * C * D * N) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith

end Erdos1017.HypergraphNibble

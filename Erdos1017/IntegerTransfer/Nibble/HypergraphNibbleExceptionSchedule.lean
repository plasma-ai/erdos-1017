module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleIdealSchedule

/-!
# Exception envelopes along a finite nibble schedule

Explicit envelopes absorb the amplification of earlier exceptions in every round
of a fixed finite schedule, the permitted initial exceptional fraction fits the
first envelope, and every envelope vanishes as the tolerance tends to zero,
including at the final round (`exception_envelope_limit`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

/-- Explicit envelopes absorb the amplification of old exceptions in every round of a
fixed finite schedule. The new-atypical fraction is chosen at a higher power of the tolerance. -/
theorem exception_envelope_step (ε R : ℝ) (T i : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hi : i < T) :
    ((R + 2) ^ i * ε ^ (T + 2 - i)) * (1 + R / ε) + ε ^ (T + 2) ≤
      (R + 2) ^ (i + 1) * ε ^ (T + 2 - (i + 1)) := by
  have hm : T + 2 - i = (T + 2 - (i + 1)) + 1 := by omega
  have hbase : 1 ≤ R + 2 := by linarith
  have hpow : 1 ≤ (R + 2) ^ i := one_le_pow₀ hbase
  have hsmall : ε ^ (T + 2) ≤ ε ^ (T + 2 - (i + 1)) :=
    pow_le_pow_of_le_one hε.le hε1 (by omega)
  have hnew : ε ^ (T + 2) ≤ (R + 2) ^ i * ε ^ (T + 2 - (i + 1)) := by
    have h := mul_le_mul_of_nonneg_right hpow (pow_nonneg hε.le (T + 2 - (i + 1)))
    exact hsmall.trans (by simpa using h)
  have hcoef : 0 ≤ (R + 2) ^ i * ε ^ (T + 2 - (i + 1)) := by positivity
  have hmain : ((R + 2) ^ i * ε ^ (T + 2 - i)) * (1 + R / ε) =
      ((R + 2) ^ i * ε ^ (T + 2 - (i + 1))) * (ε + R) := by
    rw [hm, pow_succ]
    field_simp
  rw [hmain, pow_succ (R + 2) i]
  have hmul := mul_le_mul_of_nonneg_left hε1 hcoef
  nlinarith

/-- The permitted initial exceptional fraction fits the envelope at the first round. -/
theorem initial_exception_envelope (ε : ℝ) (T : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ^ (2 * T + 6) ≤ ε ^ (T + 2) :=
  pow_le_pow_of_le_one hε hε1 (by omega)

/-- Every envelope vanishes as the tolerance tends to zero, including at the final round. -/
theorem exception_envelope_limit (R : ℝ) (T i : ℕ) (hi : i ≤ T) :
    Filter.Tendsto (fun ε : ℝ => (R + 2) ^ i * ε ^ (T + 2 - i)) (nhds 0) (nhds 0) := by
  have hpos : T + 2 - i ≠ 0 := by omega
  have hcont : Continuous (fun ε : ℝ => (R + 2) ^ i * ε ^ (T + 2 - i)) := by fun_prop
  simpa [hpos] using hcont.tendsto (0 : ℝ)

end Erdos1017.HypergraphNibble

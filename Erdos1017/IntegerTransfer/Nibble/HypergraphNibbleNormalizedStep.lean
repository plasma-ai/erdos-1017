module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleBudget

/-!
# One nibble round under the normalized schedule

This module instantiates the simultaneous nibble round with the fixed normalized
schedule, so that the bounds on active vertices and exceptions propagate to the
next explicit envelope (`exists_normalized_round`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Instantiate the actual simultaneous round with the fixed normalized schedule.
The bounds on active vertices and exceptions propagate to the next explicit envelope. -/
theorem exists_normalized_round (H : Finset (Finset V)) (U W : Finset V)
    (r T i : ℕ) (θ C ε D : ℝ) (hr : 0 < r) (hi : i < T)
    (hθ : 0 < θ) (hC : 0 < C) (hε : 0 < ε) (hε1 : ε ≤ 1) (hD : 0 < D)
    (hN : 0 < Fintype.card V)
    (hprob : (θ / idealDegree r θ i) / D < 1)
    (hsmall : smallErrorBudget r T θ C ε i < 1 / 4)
    (hlarge : (θ / idealDegree r θ i) * C / (ε ^ 2 * Fintype.card V) < 1 / 4)
    (hsupport : ∀ e ∈ H, e ⊆ U) (huniform : ∀ e ∈ H, e.card = r)
    (hmax : ∀ v, (degree H v : ℝ) ≤ C * D)
    (hcodegree : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ ε ^ (2 * T + 6) * D)
    (hregular : ∀ v ∈ U, v ∉ W →
      (degreeEnvelopes r T θ ε D i).1 * D ≤ (degree H v : ℝ) ∧
        (degree H v : ℝ) ≤ (degreeEnvelopes r T θ ε D i).2 * D)
    (hactive : (U.card : ℝ) ≤ activeEnvelope r T θ (r * C) ε D i * Fintype.card V)
    (hexceptions : (W.card : ℝ) ≤ (r * C + 2) ^ i * ε ^ (T + 2 - i) * Fintype.card V) :
    ∃ X : Finset V → Bool,
      ((survivors H X U).card : ℝ) ≤ activeEnvelope r T θ (r * C) ε D (i + 1) * Fintype.card V ∧
      ((nextExceptions H X U W ((θ / idealDegree r θ i) / D) (ε * D) (ε * D)).card : ℝ) ≤
        (r * C + 2) ^ (i + 1) * ε ^ (T + 2 - (i + 1)) * Fintype.card V ∧
      ((wasted H X U).card : ℝ) <
        4 * (θ / idealDegree r θ i) ^ 2 * r ^ 2 * C ^ 2 * Fintype.card V ∧
      (∀ v ∈ survivors H X U,
        v ∉ nextExceptions H X U W ((θ / idealDegree r θ i) / D) (ε * D) (ε * D) →
          (degreeEnvelopes r T θ ε D (i + 1)).1 * D ≤ (degree (residual H X) v : ℝ) ∧
            (degree (residual H X) v : ℝ) ≤ (degreeEnvelopes r T θ ε D (i + 1)).2 * D) := by
  classical
  let N : ℝ := Fintype.card V
  let P := θ / idealDegree r θ i
  let l := (degreeEnvelopes r T θ ε D i).1
  let d := (degreeEnvelopes r T θ ε D i).2
  have hNR : 0 < N := by dsimp [N]; exact_mod_cast hN
  have hP : 0 < P := div_pos hθ (Real.exp_pos _)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hE : (H.card : ℝ) ≤ C * D * N := by
    have hsum : (r : ℝ) * H.card = ∑ v : V, (degree H v : ℝ) := by
      exact_mod_cast (sum_degrees H r huniform).symm
    have hb : (∑ v : V, (degree H v : ℝ)) ≤ N * (C * D) := by
      calc
        _ ≤ ∑ _v : V, C * D := Finset.sum_le_sum (fun v _ => hmax v)
        _ = _ := by simp [N]
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hmul := mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg H.card : (0 : ℝ) ≤ H.card)
    rw [hsum] at hmul
    nlinarith
  have hbudget := normalized_round_budget P C ε D N H.card r T hP hC hε hD hNR hr hE hsmall hlarge
  obtain ⟨X, hlive, hbad, hwaste, _, _, hreg⟩ := exists_regular_rpow_round H U W
    (P / D) (l * D) (d * D) (C * D) (ε ^ (2 * T + 6) * D) (ε * D) (ε * N)
    (4 * P ^ 2 * r ^ 2 * C ^ 2 * N) (ε ^ (T + 2) * N) (ε * D) r
    (div_pos hP hD).le hprob (mul_pos hC hD).le (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hsupport huniform hmax hregular hcodegree hbudget
  refine ⟨X, ?_, ?_, hwaste, ?_⟩
  · have hfactor : 0 ≤ (1 - P / D) ^ (l * D) := (Real.rpow_pos_of_pos (by linarith [hprob]) _).le
    have hmul := mul_le_mul_of_nonneg_right hactive hfactor
    have hnext : activeEnvelope r T θ (r * C) ε D (i + 1) * N =
        (activeEnvelope r T θ (r * C) ε D i * N) * (1 - P / D) ^ (l * D) +
          ((r * C + 2) ^ i * ε ^ (T + 2 - i) * N) + ε * N := by
      simp only [activeEnvelope]
      dsimp [P, l]
      rw [mul_comm (degreeEnvelopes r T θ ε D i).1 D]
      ring
    rw [hnext]
    linarith
  · have hcoef : 0 ≤ 1 + (r : ℝ) * C / ε := by positivity
    have hmul := mul_le_mul_of_nonneg_right hexceptions hcoef
    have hstep := mul_le_mul_of_nonneg_right
      (exception_envelope_step ε (r * C) T i hε hε1 (by positivity) hi) hNR.le
    have hcancel : (r : ℝ) * (C * D) * W.card / (ε * D) = (W.card : ℝ) * (r * C / ε) := by field_simp
    rw [hcancel] at hbad
    nlinarith
  · intro v hv hvW
    have h := hreg v hv hvW
    have hloeq : (l * D - ε * D) * (1 - P / D) ^ (((r - 1 : ℕ) : ℝ) * (d * D)) - ε * D =
        (degreeEnvelopes r T θ ε D (i + 1)).1 * D := by
      simp only [degreeEnvelopes]
      dsimp [l, d, P]
      have he : ((r - 1 : ℕ) : ℝ) * ((degreeEnvelopes r T θ ε D i).2 * D) =
          D * (((r - 1 : ℕ) : ℝ) * (degreeEnvelopes r T θ ε D i).2) := by ring
      rw [he]
      ring
    have hhieq : d * D * (1 - P / D) ^
        (((r - 1 : ℕ) : ℝ) * (l * D - ε ^ (2 * T + 6) * D) -
          ((r - 1 : ℕ) : ℝ) ^ 2 * (ε ^ (2 * T + 6) * D)) + ε * D + ε * D =
        (degreeEnvelopes r T θ ε D (i + 1)).2 * D := by
      simp only [degreeEnvelopes]
      dsimp [l, d, P]
      have he : ((r - 1 : ℕ) : ℝ) * ((degreeEnvelopes r T θ ε D i).1 * D - ε ^ (2 * T + 6) * D) -
          ((r - 1 : ℕ) : ℝ) ^ 2 * (ε ^ (2 * T + 6) * D) =
          D * (((r - 1 : ℕ) : ℝ) * ((degreeEnvelopes r T θ ε D i).1 - ε ^ (2 * T + 6)) -
            ((r - 1 : ℕ) : ℝ) ^ 2 * ε ^ (2 * T + 6)) := by ring
      rw [he]
      ring
    rw [hloeq, hhieq] at h
    exact h

end Erdos1017.HypergraphNibble

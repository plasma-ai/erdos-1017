module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleNormalizedStep

/-!
# Running the nibble through a prescribed schedule

This module defines the residual hypergraph after a sequence of rounds, with
append lemmas for residuals, active sets and waste, and shows that finite
iteration selects sampling outcomes propagating the complete exceptional-vertex
and regularity invariant through every prescribed round
(`exists_scheduled_rounds`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def residualRounds (H : Finset (Finset V)) : List (Finset V → Bool) → Finset (Finset V)
  | [] => H
  | X :: xs => residualRounds (residual H X) xs

theorem residualRounds_subset (H : Finset (Finset V)) (xs : List (Finset V → Bool)) :
    residualRounds H xs ⊆ H := by
  induction xs generalizing H with
  | nil => exact Finset.Subset.refl _
  | cons X xs ih => exact (ih (residual H X)).trans (Finset.filter_subset _ _)

theorem residualRounds_supported (H : Finset (Finset V)) (U : Finset V)
    (xs : List (Finset V → Bool)) (hsupport : ∀ e ∈ H, e ⊆ U) :
    ∀ e ∈ residualRounds H xs, e ⊆ activeRounds H U xs := by
  induction xs generalizing H U with
  | nil => exact hsupport
  | cons X xs ih =>
    exact ih (residual H X) (survivors H X U)
      (residual_supported_on_survivors H X U hsupport)

theorem residualRounds_append (H : Finset (Finset V)) (xs : List (Finset V → Bool)) (X : Finset V → Bool) :
    residualRounds H (xs ++ [X]) = residual (residualRounds H xs) X := by
  induction xs generalizing H with
  | nil => rfl
  | cons Y xs ih => exact ih (residual H Y)

theorem activeRounds_append (H : Finset (Finset V)) (U : Finset V)
    (xs : List (Finset V → Bool)) (X : Finset V → Bool) :
    activeRounds H U (xs ++ [X]) = survivors (residualRounds H xs) X (activeRounds H U xs) := by
  induction xs generalizing H U with
  | nil => rfl
  | cons Y xs ih => exact ih (residual H Y) (survivors H Y U)

theorem wasteRounds_append (H : Finset (Finset V)) (U : Finset V)
    (xs : List (Finset V → Bool)) (X : Finset V → Bool) :
    wasteRounds H U (xs ++ [X]) = wasteRounds H U xs +
      (wasted (residualRounds H xs) X (activeRounds H U xs)).card := by
  induction xs generalizing H U with
  | nil => simp [wasteRounds, residualRounds, activeRounds]
  | cons Y xs ih => simp only [List.cons_append, wasteRounds, ih, residualRounds, activeRounds, Nat.add_assoc]

omit [Fintype V] in
private theorem degree_mono {H K : Finset (Finset V)} (h : K ⊆ H) (v : V) : degree K v ≤ degree H v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

omit [Fintype V] in
private theorem codegree_mono {H K : Finset (Finset V)} (h : K ⊆ H) (u v : V) : codegree K u v ≤ codegree H u v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Finite iteration selects actual sampling outcomes and propagates the complete
exceptional-vertex and regularity invariant through every prescribed round. -/
theorem exists_scheduled_rounds (H : Finset (Finset V)) (W : Finset V)
    (r T : ℕ) (θ C ε D : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hC : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hD : 0 < D) (hN : 0 < Fintype.card V)
    (huniform : ∀ e ∈ H, e.card = r) (hmax : ∀ v, (degree H v : ℝ) ≤ C * D)
    (hcodegree : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ ε ^ (2 * T + 6) * D)
    (hregular : ∀ v, v ∉ W → (1 - ε ^ (2 * T + 6)) * D ≤ (degree H v : ℝ) ∧
      (degree H v : ℝ) ≤ (1 + ε ^ (2 * T + 6)) * D)
    (hW : (W.card : ℝ) ≤ ε ^ (2 * T + 6) * Fintype.card V)
    (hprob : ∀ i : Fin T, (θ / idealDegree r θ i) / D < 1)
    (hsmall : ∀ i : Fin T, smallErrorBudget r T θ C ε i < 1 / 4)
    (hlarge : ∀ i : Fin T, (θ / idealDegree r θ i) * C / (ε ^ 2 * Fintype.card V) < 1 / 4) :
    ∃ xs : List (Finset V → Bool), xs.length = T ∧
      ((activeRounds H Finset.univ xs).card : ℝ) ≤ activeEnvelope r T θ (r * C) ε D T * Fintype.card V ∧
      (wasteRounds H Finset.univ xs : ℝ) ≤
        (∑ i ∈ Finset.range T, 4 * (θ / idealDegree r θ i) ^ 2 * r ^ 2 * C ^ 2) * Fintype.card V := by
  classical
  have hNR : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hind : ∀ i ≤ T, ∃ (xs : List (Finset V → Bool)) (W' : Finset V), xs.length = i ∧
      (∀ v ∈ activeRounds H Finset.univ xs, v ∉ W' →
        (degreeEnvelopes r T θ ε D i).1 * D ≤ (degree (residualRounds H xs) v : ℝ) ∧
          (degree (residualRounds H xs) v : ℝ) ≤ (degreeEnvelopes r T θ ε D i).2 * D) ∧
      ((activeRounds H Finset.univ xs).card : ℝ) ≤ activeEnvelope r T θ (r * C) ε D i * Fintype.card V ∧
      (W'.card : ℝ) ≤ (r * C + 2) ^ i * ε ^ (T + 2 - i) * Fintype.card V ∧
      (wasteRounds H Finset.univ xs : ℝ) ≤
        (∑ j ∈ Finset.range i, 4 * (θ / idealDegree r θ j) ^ 2 * r ^ 2 * C ^ 2) * Fintype.card V := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨[], W, rfl, ?_, ?_, ?_, ?_⟩
      · simpa only [activeRounds, residualRounds, degreeEnvelopes] using (fun v (_ : v ∈ Finset.univ) => hregular v)
      · simp [activeRounds, activeEnvelope]
      · simpa using hW.trans (mul_le_mul_of_nonneg_right (initial_exception_envelope ε T hε.le hε1) hNR)
      · simp [wasteRounds]
    | succ i ih =>
      intro hi
      have hiT : i < T := by omega
      obtain ⟨xs, W', hlen, hreg, hact, hexc, hwaste⟩ := ih (by omega)
      have hsub := residualRounds_subset H xs
      have hmax' : ∀ v, (degree (residualRounds H xs) v : ℝ) ≤ C * D := by
        intro v
        have hmono : (degree (residualRounds H xs) v : ℝ) ≤ degree H v := by exact_mod_cast degree_mono hsub v
        exact hmono.trans (hmax v)
      have hcode' : ∀ u v, u ≠ v → (codegree (residualRounds H xs) u v : ℝ) ≤ ε ^ (2 * T + 6) * D := by
        intro u v huv
        have hmono : (codegree (residualRounds H xs) u v : ℝ) ≤ codegree H u v := by exact_mod_cast codegree_mono hsub u v
        exact hmono.trans (hcodegree u v huv)
      obtain ⟨X, hact', hexc', hwaste', hreg'⟩ := exists_normalized_round (residualRounds H xs)
        (activeRounds H Finset.univ xs) W' r T i θ C ε D hr hiT hθ hC hε hε1 hD hN
        (hprob ⟨i, hiT⟩) (hsmall ⟨i, hiT⟩) (hlarge ⟨i, hiT⟩)
        (residualRounds_supported H Finset.univ xs (fun _ _ => Finset.subset_univ _))
        (fun e he => huniform e (hsub he)) hmax' hcode' hreg hact hexc
      refine ⟨xs ++ [X], nextExceptions (residualRounds H xs) X (activeRounds H Finset.univ xs)
        W' ((θ / idealDegree r θ i) / D) (ε * D) (ε * D), by simp [hlen], ?_, ?_, hexc', ?_⟩
      · simpa only [residualRounds_append, activeRounds_append] using hreg'
      · simpa only [activeRounds_append] using hact'
      · rw [wasteRounds_append, Nat.cast_add, Finset.sum_range_succ, add_mul]
        exact add_le_add hwaste hwaste'.le
  obtain ⟨xs, _, hlen, _, hact, _, hwaste⟩ := hind T le_rfl
  exact ⟨xs, hlen, hact, hwaste⟩

end Erdos1017.HypergraphNibble

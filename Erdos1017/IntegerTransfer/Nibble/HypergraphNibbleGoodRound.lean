module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleWaste

/-!
# Existence of a good nibble round

This module defines `badDegrees`, the vertices whose exposed next-round degree
differs substantially from its mean, and shows that a single sampling outcome
simultaneously controls the survivor count, the atypical exposed degrees and the
wasted vertices, with a budget computed from the proved moments
(`exists_good_round`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices whose exposed next-round degree differs substantially from its exact mean. -/
def badDegrees (H : Finset (Finset V)) (X : Finset V → Bool) (p t : ℝ) : Finset V :=
  Finset.univ.filter (fun v => t ≤ |prospectiveDegree H X v -
    ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card|)

/-- A single actual sampling outcome simultaneously controls survivor count, atypical
exposed degrees and wasted vertices. The budget is computed from the proved moments. -/
theorem exists_good_round (H : Finset (Finset V)) (p D c t s A B : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (ht : 0 < t) (hs : 0 < s) (hA : 0 < A) (hB : 0 < B)
    (huniform : ∀ e ∈ H, e.card = r) (hdegree : ∀ v, (degree H v : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c)
    (hbudget : p * Fintype.card V * (D + Fintype.card V * c) / s ^ 2 +
      (p * (r * c) * (r * D) * D * Fintype.card V / t ^ 2) / B +
      (p ^ 2 * r ^ 2 * D * H.card) / A < 1) :
    ∃ X : Finset V → Bool,
      |survivorCount H X - ∑ v, (1 - p) ^ degree H v| < s ∧
      ((badDegrees H X p t).card : ℝ) < B ∧
      ((wasted H X Finset.univ).card : ℝ) < A := by
  classical
  let Z (X : Finset V → Bool) : ℝ :=
    (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2 / s ^ 2 +
      ((badDegrees H X p t).card : ℝ) / B + ((wasted H X Finset.univ).card : ℝ) / A
  have hlive := survivorCount_variance_le_degree_codegree H p D c hp hp1 hc hdegree hcodegree
  have hbad := expected_bad_degree_count H p D c t r hp hp1 hD hc ht.le
    (fun e he => (huniform e he).le) hdegree hcodegree
  have hwaste := expected_waste_bound H p D r hp hp1 hD huniform hdegree
  have hbad' : (∑ X, CliqueSampling.weight (fun _ => p) X * ((badDegrees H X p t).card : ℝ)) ≤
      p * (r * c) * (r * D) * D * Fintype.card V / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    simpa only [badDegrees, mul_comm (t ^ 2)] using hbad
  have hEZ : (∑ X, CliqueSampling.weight (fun _ => p) X * Z X) < 1 := by
    have hl := div_le_div_of_nonneg_right hlive (sq_nonneg s)
    have hb := div_le_div_of_nonneg_right hbad' hB.le
    have hw := div_le_div_of_nonneg_right hwaste hA.le
    have hexpand : (∑ X, CliqueSampling.weight (fun _ => p) X * Z X) =
        (∑ X, CliqueSampling.weight (fun _ => p) X *
          (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2) / s ^ 2 +
        (∑ X, CliqueSampling.weight (fun _ => p) X * ((badDegrees H X p t).card : ℝ)) / B +
        (∑ X, CliqueSampling.weight (fun _ => p) X * ((wasted H X Finset.univ).card : ℝ)) / A := by
      simp only [Z, mul_add, mul_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hexpand]
    linarith
  have hexists : ∃ X, Z X < 1 := by
    by_contra h
    push Not at h
    have hsum : 1 ≤ ∑ X, CliqueSampling.weight (fun _ => p) X * Z X := by
      calc
        1 = ∑ X : Finset V → Bool, CliqueSampling.weight (fun _ => p) X :=
          (CliqueSampling.bernoulli_total (fun _ => p)).symm
        _ ≤ _ := Finset.sum_le_sum (fun X _ => by
          have hw := CliqueSampling.weight_nonneg (fun _ : Finset V => p) (fun _ => ⟨hp, hp1⟩) X
          simpa using mul_le_mul_of_nonneg_left (h X) hw)
    linarith
  obtain ⟨X, hX⟩ := hexists
  have h0 : 0 ≤ (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2 / s ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h1 : 0 ≤ ((badDegrees H X p t).card : ℝ) / B := div_nonneg (Nat.cast_nonneg _) hB.le
  have h2 : 0 ≤ ((wasted H X Finset.univ).card : ℝ) / A := div_nonneg (Nat.cast_nonneg _) hA.le
  change _ + _ + _ < 1 at hX
  refine ⟨X, ?_, ?_, ?_⟩
  · have hsq : (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2 < s ^ 2 := by
      have hratio : (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2 / s ^ 2 < 1 := by linarith
      exact (div_lt_one (sq_pos_of_pos hs)).mp hratio
    nlinarith [sq_abs (survivorCount H X - ∑ v, (1 - p) ^ degree H v),
      abs_nonneg (survivorCount H X - ∑ v, (1 - p) ^ degree H v)]
  · exact (div_lt_one hB).mp (by linarith)
  · exact (div_lt_one hA).mp (by linarith)

end Erdos1017.HypergraphNibble

module

public import Erdos1017.IntegerTransfer.ThinningBaseSelection
public import Erdos1017.IntegerTransfer.BernoulliReindex

/-!
# Centered sampling score for thinning

This module defines the centered sampling score, which centers the
deterministic-exception count so that every score budget vanishes with the part
size, and proves its first-moment bound, nonnegativity, and that a score below
one controls both counts and the retained square sum
(`centeredSamplingScore_controls`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- The exact selected count mean for a deterministic family of edge bases. -/
def retainedBaseMean (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (B : Finset (Fin 2 → A)) (α : ℝ) : ℝ :=
  B.card * baseProbability (t := 2) (normalizedProbability G α)

/-- Centering the deterministic-exception count makes every score budget
vanish with the part size, allowing arbitrarily many finite clique types. -/
def centeredSamplingScore (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (B : Finset (Fin 2 → A)) (α a b c : ℝ) (X : Coordinate (2 + u) A → Bool) : ℝ :=
  (((retainedBases (MultipartiteExtension.bases (t := 2) G) X).card : ℝ) -
      α * (Fintype.card A : ℝ) ^ 2) ^ 2 / a ^ 2 +
    (((retainedBases B X).card : ℝ) - retainedBaseMean G B α) ^ 2 / b ^ 2 +
    retainedSquaredError (extensions G) (partProbability (normalizedProbability G α)) X / c

/-- The first two score terms both have variance at most n². -/
def centeredSamplingBudget (n u : ℕ) (α δ a b c : ℝ) : ℝ :=
  (n : ℝ) ^ 2 / a ^ 2 + (n : ℝ) ^ 2 / b ^ 2 +
    ((α / δ) * (n : ℝ) ^ 2 * ((n : ℝ) ^ u * ((u : ℝ) * (n : ℝ) ^ (u - 1)))) / c

/-- The centered score has an explicit first-moment bound with no fixed
exception-probability term. -/
theorem centeredSamplingScore_expectation
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    {α δ : ℝ} (hα : 0 ≤ α) (hαδ : α ≤ δ) (hδ : 0 < δ)
    (hd : ∀ i j : Fin (2 + u), i < j → δ ≤ pairDensity G (i, j))
    (B : Finset (Fin 2 → A)) (a b c : ℝ) (hc : 0 < c) :
    (∑ X, CliqueSampling.weight (partProbability (normalizedProbability G α)) X *
      centeredSamplingScore G B α a b c X) ≤
      centeredSamplingBudget (Fintype.card A) u α δ a b c := by
  let q := normalizedProbability G α
  let p : Coordinate (2 + u) A → ℝ := partProbability q
  let n : ℝ := Fintype.card A
  let Q := MultipartiteExtension.bases (t := 2) G
  have hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1 := fun v => normalizedProbability_bounds G hα hαδ hδ hd _
  have hQcard : (Q.card : ℝ) ≤ n ^ 2 := by
    dsimp only [n]
    exact_mod_cast family_card_le Q
  have hBcard : (B.card : ℝ) ≤ n ^ 2 := by
    dsimp only [n]
    exact_mod_cast family_card_le B
  have hmeanQ : BernoulliFamily.mean Q (baseSupport (u := u)) p = α * n ^ 2 := by
    rw [← BernoulliFamily.expectation]
    exact normalized_retainedBases_expectation G α (hδ.trans_le (hd _ _ (by change (0 : ℕ) < 1; omega)))
  have hmeanB : BernoulliFamily.mean B (baseSupport (u := u)) p = retainedBaseMean G B α := by
    simp only [BernoulliFamily.mean, p, q, baseSupport_probability, Finset.sum_const, nsmul_eq_mul, retainedBaseMean]
  have horder := (retainedBases_variance_le Q p hp).trans hQcard
  rw [hmeanQ] at horder
  have hbad := (retainedBases_variance_le B p hp).trans hBcard
  rw [hmeanB] at hbad
  have hpbase := normalized_baseProbability_le G hα hδ (hd _ _ (by change (0 : ℕ) < 1; omega))
  have hsquare := retainedSquaredError_expectation_le (extensions G) q
    (fun e => normalizedProbability_bounds G hα hαδ hδ hd e)
  have hsquare' : (∑ X, CliqueSampling.weight p X * retainedSquaredError (extensions G) p X) ≤
      (α / δ) * n ^ 2 * (n ^ u * ((u : ℝ) * n ^ (u - 1))) := by
    apply hsquare.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpbase (by positivity)) (by positivity)
  have h1 := div_le_div_of_nonneg_right horder (sq_nonneg a)
  have h2 := div_le_div_of_nonneg_right hbad (sq_nonneg b)
  have h3 := div_le_div_of_nonneg_right hsquare' hc.le
  have hexpand : (∑ X, CliqueSampling.weight p X * centeredSamplingScore G B α a b c X) =
      (∑ X, CliqueSampling.weight p X * (((retainedBases Q X).card : ℝ) - α * n ^ 2) ^ 2) / a ^ 2 +
      (∑ X, CliqueSampling.weight p X * (((retainedBases B X).card : ℝ) - retainedBaseMean G B α) ^ 2) / b ^ 2 +
      (∑ X, CliqueSampling.weight p X * retainedSquaredError (extensions G) p X) / c := by
    simp only [centeredSamplingScore, mul_add, mul_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rfl
  rw [hexpand]
  exact add_le_add (add_le_add h1 h2) h3

omit [Nonempty A] in
/-- Centered scores remain nonnegative for every actual outcome. -/
theorem centeredSamplingScore_nonneg
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (B : Finset (Fin 2 → A)) (α a b c : ℝ) (hc : 0 ≤ c)
    (X : Coordinate (2 + u) A → Bool) : 0 ≤ centeredSamplingScore G B α a b c X := by
  apply add_nonneg (add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  apply div_nonneg _ hc
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (sq_nonneg _)
  unfold BernoulliPresence.present
  split_ifs <;> norm_num

omit [Nonempty A] in
/-- A centered score below one controls both counts and the actual retained
square sum. The deterministic exception mean is stated explicitly. -/
theorem centeredSamplingScore_controls
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (B : Finset (Fin 2 → A)) (α a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (X : Coordinate (2 + u) A → Bool) (hscore : centeredSamplingScore G B α a b c X < 1) :
    |((retainedBases (MultipartiteExtension.bases (t := 2) G) X).card : ℝ) -
      α * (Fintype.card A : ℝ) ^ 2| < a ∧
    ((retainedBases B X).card : ℝ) < retainedBaseMean G B α + b ∧
    retainedSquaredError (extensions G) (partProbability (normalizedProbability G α)) X < c := by
  let z := (((retainedBases (MultipartiteExtension.bases (t := 2) G) X).card : ℝ) - α * (Fintype.card A : ℝ) ^ 2)
  let y := (((retainedBases B X).card : ℝ) - retainedBaseMean G B α)
  have h0 : 0 ≤ z ^ 2 / a ^ 2 := by positivity
  have h1 : 0 ≤ y ^ 2 / b ^ 2 := by positivity
  have h2 : 0 ≤ retainedSquaredError (extensions G) (partProbability (normalizedProbability G α)) X / c := by
    apply div_nonneg _ hc.le
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (sq_nonneg _)
    unfold BernoulliPresence.present
    split_ifs <;> norm_num
  change z ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + _ < 1 at hscore
  have hz : z ^ 2 < a ^ 2 := (div_lt_one (sq_pos_of_pos ha)).mp (by linarith)
  have hy : y ^ 2 < b ^ 2 := (div_lt_one (sq_pos_of_pos hb)).mp (by linarith)
  refine ⟨?_, ?_, (div_lt_one hc).mp (by linarith)⟩
  · change |z| < a
    nlinarith [sq_abs z, abs_nonneg z]
  · have hylt : y < b := by nlinarith [sq_abs y, abs_nonneg y]
    dsimp only [y] at hylt
    linarith only [hylt]

end Erdos1017.TransversalThinning

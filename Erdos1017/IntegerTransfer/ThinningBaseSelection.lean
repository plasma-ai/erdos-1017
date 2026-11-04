module

public import Erdos1017.IntegerTransfer.RetainedBaseCounts

/-!
# Base sampling score for simultaneous thinning control

A single nonnegative score (`baseSamplingScore`) with an explicit first-moment
budget controls retained order, deterministic exceptions and aggregate degree
error on one thinning sample, and one outcome controls all three at once
(`exists_base_sampling_control`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

omit [DecidableEq A] [Nonempty A] in
/-- The single-edge base retention probability is at most α/δ, with the
allocation factor α retained explicitly. -/
theorem normalized_baseProbability_le (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    (hd : δ ≤ pairDensity G (Fin.castAdd u 0, Fin.castAdd u 1)) :
    baseProbability (t := 2) (normalizedProbability G α) ≤ α / δ := by
  have hcomplete : MultipartiteExtension.completeEdges 2 = {(0, 1)} := by decide
  have hne : Fin.castAdd u (0 : Fin 2) ≠ Fin.castAdd u 1 := by
    intro h
    have hval := congrArg Fin.val h
    change (0 : ℕ) = 1 at hval
    omega
  simp only [baseProbability, hcomplete, Finset.prod_singleton, normalizedProbability, ite_eq_right hne]
  apply (div_le_div_iff₀ (hδ.trans_le hd) hδ).mpr
  nlinarith [mul_nonneg hα (sub_nonneg.mpr hd)]

/-- One nonnegative score controls retained order, deterministic exceptions
and aggregate degree error on the same actual sample. -/
def baseSamplingScore (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (B : Finset (Fin 2 → A)) (α a b c : ℝ) (X : Coordinate (2 + u) A → Bool) : ℝ :=
  (((retainedBases (MultipartiteExtension.bases (t := 2) G) X).card : ℝ) -
      α * (Fintype.card A : ℝ) ^ 2) ^ 2 / a ^ 2 +
    ((retainedBases B X).card : ℝ) / b +
    retainedSquaredError (extensions G) (partProbability (normalizedProbability G α)) X / c

/-- The explicit first-moment budget for that score. -/
def baseSamplingBudget (n u : ℕ) (α δ ζ a b c : ℝ) : ℝ :=
  (n : ℝ) ^ 2 / a ^ 2 + ((α / δ) * ζ * (n : ℝ) ^ 2) / b +
    ((α / δ) * (n : ℝ) ^ 2 * ((n : ℝ) ^ u * ((u : ℝ) * (n : ℝ) ^ (u - 1)))) / c

/-- The score expectation is bounded before selecting an outcome. -/
theorem baseSamplingScore_expectation
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    {α δ ζ : ℝ} (hα : 0 ≤ α) (hαδ : α ≤ δ) (hδ : 0 < δ)
    (hd : ∀ i j : Fin (2 + u), i < j → δ ≤ pairDensity G (i, j))
    (B : Finset (Fin 2 → A)) (hB : (B.card : ℝ) ≤ ζ * (Fintype.card A : ℝ) ^ 2)
    (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (∑ X, CliqueSampling.weight (partProbability (normalizedProbability G α)) X *
      baseSamplingScore G B α a b c X) ≤
      baseSamplingBudget (Fintype.card A) u α δ ζ a b c := by
  classical
  let q := normalizedProbability G α
  let p : Coordinate (2 + u) A → ℝ := partProbability q
  let n : ℝ := Fintype.card A
  let Q := MultipartiteExtension.bases (t := 2) G
  let Z (X : Coordinate (2 + u) A → Bool) : ℝ :=
    (((retainedBases Q X).card : ℝ) - α * n ^ 2) ^ 2 / a ^ 2 +
      ((retainedBases B X).card : ℝ) / b + retainedSquaredError (extensions G) p X / c
  have hprob : ∀ v, 0 ≤ p v ∧ p v ≤ 1 := fun v => normalizedProbability_bounds G hα hαδ hδ hd _
  have hd0 := hd (Fin.castAdd u 0) (Fin.castAdd u 1) (by change (0 : ℕ) < 1; omega)
  have hpbase := normalized_baseProbability_le G hα hδ hd0
  have hmean : BernoulliFamily.mean Q (baseSupport (u := u)) p = α * n ^ 2 := by
    rw [← BernoulliFamily.expectation]
    exact normalized_retainedBases_expectation G α (hδ.trans_le hd0)
  have horder := retainedBases_variance_le Q p hprob
  rw [hmean] at horder
  have hQ : (Q.card : ℝ) ≤ n ^ 2 := by
    have h := Finset.card_le_card (Finset.subset_univ Q)
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
      (show (Q.card : ℝ) ≤ Fintype.card (Fin 2 → A) by exact_mod_cast h)
  have horder := horder.trans hQ
  have hbad : (∑ X, CliqueSampling.weight p X * ((retainedBases B X).card : ℝ)) ≤
      (α / δ) * ζ * n ^ 2 := by
    rw [retainedBases_expectation]
    have hmul := mul_le_mul_of_nonneg_left hpbase (Nat.cast_nonneg B.card : (0 : ℝ) ≤ B.card)
    have hmul' := mul_le_mul_of_nonneg_right hB (div_nonneg hα hδ.le)
    dsimp only [q, n] at *
    nlinarith
  have hsquare := retainedSquaredError_expectation_le (extensions G) q
    (fun e => normalizedProbability_bounds G hα hαδ hδ hd e)
  have hsquare' : (∑ X, CliqueSampling.weight p X * retainedSquaredError (extensions G) p X) ≤
      (α / δ) * n ^ 2 * (n ^ u * ((u : ℝ) * n ^ (u - 1))) := by
    apply hsquare.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpbase (by positivity)) (by positivity)
  change (∑ X, CliqueSampling.weight p X * Z X) ≤ _
  have hEZ : (∑ X, CliqueSampling.weight p X * Z X) ≤
      n ^ 2 / a ^ 2 + ((α / δ) * ζ * n ^ 2) / b +
        ((α / δ) * n ^ 2 * (n ^ u * ((u : ℝ) * n ^ (u - 1)))) / c := by
    have h1 := div_le_div_of_nonneg_right horder (sq_nonneg a)
    have h2 := div_le_div_of_nonneg_right hbad hb.le
    have h3 := div_le_div_of_nonneg_right hsquare' hc.le
    have hexpand : (∑ X, CliqueSampling.weight p X * Z X) =
        (∑ X, CliqueSampling.weight p X * (((retainedBases Q X).card : ℝ) - α * n ^ 2) ^ 2) / a ^ 2 +
        (∑ X, CliqueSampling.weight p X * ((retainedBases B X).card : ℝ)) / b +
        (∑ X, CliqueSampling.weight p X * retainedSquaredError (extensions G) p X) / c := by
      simp only [Z, mul_add, mul_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hexpand]
    exact add_le_add (add_le_add h1 h2) h3
  exact hEZ

/-- A single actual thinning outcome simultaneously controls retained order,
retained deterministic exceptions and aggregate retained degree error. -/
theorem exists_base_sampling_control
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    {α δ ζ : ℝ} (hα : 0 ≤ α) (hαδ : α ≤ δ) (hδ : 0 < δ)
    (hd : ∀ i j : Fin (2 + u), i < j → δ ≤ pairDensity G (i, j))
    (B : Finset (Fin 2 → A)) (hB : (B.card : ℝ) ≤ ζ * (Fintype.card A : ℝ) ^ 2)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbudget : (Fintype.card A : ℝ) ^ 2 / a ^ 2 +
      ((α / δ) * ζ * (Fintype.card A : ℝ) ^ 2) / b +
      ((α / δ) * (Fintype.card A : ℝ) ^ 2 *
        ((Fintype.card A : ℝ) ^ u * ((u : ℝ) * (Fintype.card A : ℝ) ^ (u - 1)))) / c < 1) :
    ∃ X : Coordinate (2 + u) A → Bool,
      |((retainedBases (MultipartiteExtension.bases (t := 2) G) X).card : ℝ) -
        α * (Fintype.card A : ℝ) ^ 2| < a ∧
      ((retainedBases B X).card : ℝ) < b ∧
      retainedSquaredError (extensions G) (partProbability (normalizedProbability G α)) X < c := by
  classical
  let q := normalizedProbability G α
  let p : Coordinate (2 + u) A → ℝ := partProbability q
  let n : ℝ := Fintype.card A
  let Q := MultipartiteExtension.bases (t := 2) G
  let Z (X : Coordinate (2 + u) A → Bool) : ℝ :=
    (((retainedBases Q X).card : ℝ) - α * n ^ 2) ^ 2 / a ^ 2 +
      ((retainedBases B X).card : ℝ) / b + retainedSquaredError (extensions G) p X / c
  have hprob : ∀ v, 0 ≤ p v ∧ p v ≤ 1 := fun v => normalizedProbability_bounds G hα hαδ hδ hd _
  have hEZ : (∑ X, CliqueSampling.weight p X * Z X) < 1 :=
    (baseSamplingScore_expectation G hα hαδ hδ hd B hB a b c hb hc).trans_lt hbudget
  obtain ⟨X, hX⟩ : ∃ X, Z X < 1 := by
    by_contra h
    push Not at h
    have hsum : 1 ≤ ∑ X, CliqueSampling.weight p X * Z X := by
      calc
        1 = ∑ X, CliqueSampling.weight p X := (CliqueSampling.bernoulli_total p).symm
        _ ≤ _ := Finset.sum_le_sum (fun X _ => by
          simpa using mul_le_mul_of_nonneg_left (h X) (CliqueSampling.weight_nonneg p hprob X))
    exact (not_lt_of_ge hsum) hEZ
  have h0 : 0 ≤ (((retainedBases Q X).card : ℝ) - α * n ^ 2) ^ 2 / a ^ 2 := by positivity
  have h1 : 0 ≤ ((retainedBases B X).card : ℝ) / b := by positivity
  have h2 : 0 ≤ retainedSquaredError (extensions G) p X / c := by
    apply div_nonneg _ hc.le
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (sq_nonneg _)
    unfold BernoulliPresence.present
    split_ifs <;> norm_num
  change _ + _ + _ < 1 at hX
  refine ⟨X, ?_, ?_, ?_⟩
  · have hsq : (((retainedBases Q X).card : ℝ) - α * n ^ 2) ^ 2 < a ^ 2 :=
      (div_lt_one (sq_pos_of_pos ha)).mp (by linarith)
    nlinarith [sq_abs (((retainedBases Q X).card : ℝ) - α * n ^ 2),
      abs_nonneg (((retainedBases Q X).card : ℝ) - α * n ^ 2)]
  · exact (div_lt_one hb).mp (by linarith)
  · exact (div_lt_one hc).mp (by linarith)

end Erdos1017.TransversalThinning

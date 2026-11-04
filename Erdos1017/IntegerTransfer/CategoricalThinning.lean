module

public import Erdos1017.IntegerTransfer.FiniteCategoricalSampling
public import Erdos1017.IntegerTransfer.BernoulliRestriction
public import Erdos1017.IntegerTransfer.CenteredThinningScore
public import Erdos1017.IntegerTransfer.FinitePositiveSelection

/-!
# One categorical sample controlling many embedded clique problems

A label restricted to any embedded coordinate family has its exact independent
Bernoulli marginal law, and one mutually exclusive categorical sample
simultaneously controls any finite family of embedded regular clique problems,
including different ranks (`exists_embedded_controls`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CategoricalSampling

open scoped BigOperators

variable {V W J : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype J] [DecidableEq J]

/-- A label restricted to any embedded coordinate family has its exact
independent Bernoulli marginal law. -/
theorem projection_embedding_expectation (q : W → J → ℝ) (hq : ∀ w, ∑ j, q w j = 1)
    (j : J) (e : V ↪ W) (f : (V → Bool) → ℝ) :
    (∑ X : W → J, weight q X * f (fun v => projection j X (e v))) =
      ∑ Y : V → Bool, CliqueSampling.weight (fun v => q (e v) j) Y * f Y := by
  calc
    _ = ∑ B : W → Bool, CliqueSampling.weight (fun w => q w j) B * f (fun v => B (e v)) :=
      projection_expectation q hq j (fun B => f (fun v => B (e v)))
    _ = _ := CliqueSampling.expectation_embedding e (fun w => q w j) f

/-- One mutually exclusive categorical sample simultaneously controls any
finite family of embedded regular clique problems, including different ranks.
The input probabilities are explicit marginals; no successful outcome is assumed. -/
theorem exists_embedded_controls {I : Type*} [Fintype I]
    (n : ℕ) (hn : 0 < n) (u : I → ℕ)
    (G : ∀ i, SimpleGraph (Fin (2 + u i) × Fin n)) [∀ i, DecidableRel (G i).Adj]
    (q : W → J → ℝ) (hq : ∀ w j, 0 ≤ q w j) (htotal : ∀ w, ∑ j, q w j = 1)
    (label : I → J) (e : ∀ i, TransversalThinning.Coordinate (2 + u i) (Fin n) ↪ W)
    (α δ : I → ℝ) (hα : ∀ i, 0 ≤ α i) (hαδ : ∀ i, α i ≤ δ i) (hδ : ∀ i, 0 < δ i)
    (hd : ∀ i j l, j < l → δ i ≤ TransversalThinning.pairDensity (G i) (j, l))
    (hprob : ∀ i v, q (e i v) (label i) =
      TransversalThinning.partProbability (TransversalThinning.normalizedProbability (G i) (α i)) v)
    (B : I → Finset (Fin 2 → Fin n)) (a b c : I → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hbudget : (∑ i, TransversalThinning.centeredSamplingBudget n (u i) (α i) (δ i) (a i) (b i) (c i)) < 1) :
    ∃ X : W → J, 0 < weight q X ∧ ∀ i,
      let Y := fun v => projection (label i) X (e i v)
      |((TransversalThinning.retainedBases (MultipartiteExtension.bases (t := 2) (G i)) Y).card : ℝ) -
        α i * (n : ℝ) ^ 2| < a i ∧
      ((TransversalThinning.retainedBases (B i) Y).card : ℝ) <
        TransversalThinning.retainedBaseMean (G i) (B i) (α i) + b i ∧
      TransversalThinning.retainedSquaredError (TransversalThinning.extensions (G i))
        (TransversalThinning.partProbability (TransversalThinning.normalizedProbability (G i) (α i))) Y < c i := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨X, hwX, hX⟩ := FiniteSampling.exists_positive_all_scores_lt_one (weight q)
    (weight_nonneg q hq) (total q htotal)
    (fun i X => TransversalThinning.centeredSamplingScore (G i) (B i) (α i) (a i) (b i) (c i)
      (fun v => projection (label i) X (e i v)))
    (fun i X => TransversalThinning.centeredSamplingScore_nonneg (G i) (B i) (α i) (a i) (b i) (c i) (hc i).le _)
    (fun i => TransversalThinning.centeredSamplingBudget n (u i) (α i) (δ i) (a i) (b i) (c i))
    (by
      intro i
      rw [projection_embedding_expectation q htotal (label i) (e i)]
      have hfun : (fun v => q (e i v) (label i)) =
          TransversalThinning.partProbability (TransversalThinning.normalizedProbability (G i) (α i)) := funext (hprob i)
      rw [hfun]
      simpa only [Fintype.card_fin] using TransversalThinning.centeredSamplingScore_expectation (G i)
        (hα i) (hαδ i) (hδ i) (hd i) (B i) (a i) (b i) (c i) (hc i)) hbudget
  exact ⟨X, hwX, fun i => by
    simpa only [Fintype.card_fin] using TransversalThinning.centeredSamplingScore_controls (G i)
      (B i) (α i) (a i) (b i) (c i) (ha i) (hb i) (hc i) _ (hX i)⟩

end Erdos1017.CategoricalSampling

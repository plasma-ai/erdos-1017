module

public import Erdos1017.IntegerTransfer.CleanedGraphRounding
public import Erdos1017.IntegerTransfer.LabelledFractionalTruncation

/-!
# Rounding the fractional value on cleaned graphs

The attained unrestricted fractional value rounds on every sufficiently large
equal-part cleaned graph, with no bounded-support weights assumed
(`exists_cleaned_value_rounding_tolerance`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

/-- The attained unrestricted fractional value rounds on every sufficiently
large equal-part cleaned graph, with no bounded-support weights assumed. -/
theorem exists_cleaned_value_rounding_tolerance (δ τ : ℝ)
    (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (p C : ℕ), 0 < C → 1 ≤ (C : ℝ) * δ →
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ p →
        ∀ (G : SimpleGraph (Fin ℓ × Fin n)) [DecidableRel G.Adj],
          (∀ i (a z : Fin n), ¬G.Adj (i, a) (i, z)) →
          ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
          (∀ i j : Fin ℓ, i < j → (∀ a z : Fin n, ¬G.Adj (i, a) (j, z)) ∨
            (G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j) ∧
              δ ≤ G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j))) →
          ∀ (N : ℕ) (f : (Fin ℓ × Fin n) ↪ Fin N),
            (cliquePartitionNumber (G.map f) : ℝ) ≤ FractionalGraph.value (G.map f) + τ * (ℓ * n : ℕ) ^ 2 := by
  have hhalf : 0 < τ / 2 := by linarith
  obtain ⟨b, hb, hweights⟩ := exists_uniform_bounded_labelled_partition (τ / 2) hhalf
  obtain ⟨ε₀, hε₀, hround⟩ := exists_cleaned_rounding_tolerance b hb δ (τ / 2) hδ hhalf (by linarith)
  refine ⟨ε₀, hε₀, ?_⟩
  intro p C hC hscale
  obtain ⟨n₀, hn₀, hsize⟩ := hround p C hC hscale
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn ℓ hℓ hℓp G _ hparts ε hε hsmall hclean N f
  obtain ⟨w, hw, hsupport, hbalance, hcost⟩ := hweights ℓ n N G f
  have h := hsize n hn ℓ hℓ hℓp G hparts w hw hsupport hbalance ε hε hsmall hclean N f
  linarith only [h, hcost]

end Erdos1017.MultipartiteAllocation

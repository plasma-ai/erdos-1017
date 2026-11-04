module

public import Erdos1017.FinalAssembly

/-!
# Proof of the uniform asymptotic formula for Erdős Problem 1017

Comparator checks this theorem against the Mathlib-only statement in
`Challenge.lean`.
-/

@[expose] public section

namespace Erdos1017

/-- The clique partition extremum converges uniformly to the benchmark
over every feasible edge count. -/
theorem uniform_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, k ≤ n.choose 2 →
        |(f n k : ℝ) / (n : ℝ) ^ 2 - benchmark ((k : ℝ) / (n : ℝ) ^ 2)| < ε :=
  uniform_asymptotic_proved

end Erdos1017

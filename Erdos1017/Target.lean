module

public import Erdos1017.Statement
public import Erdos1017.Benchmark

/-!
# The uniform asymptotic formula

This module defines `UniformAsymptotic`: for every `ε > 0` there is `N` such
that `|f(n, k)/n² - B(k/n²)| < ε` for all `n ≥ N` and all `k ≤ n choose 2`.
`FinalAssembly` proves it as `uniform_asymptotic_proved`.
-/

@[expose] public section

namespace Erdos1017

/-- The uniform additive limit, expressed without a finite maximum.
The quantifier over all feasible edge counts is inside the eventual bound on `n`.
Densities and partition counts are both normalized by `n²`.
The proposition is proved by `uniform_asymptotic_proved` in `FinalAssembly`. -/
def UniformAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n.choose 2 →
    |(f n k : ℝ) / (n : ℝ) ^ 2 - benchmark ((k : ℝ) / (n : ℝ) ^ 2)| < ε

end Erdos1017

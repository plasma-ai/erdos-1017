module

public import Erdos1017.IntegerTransfer.CliquePackingSampling

/-!
# Reindexing independent Bernoulli laws

Independent Bernoulli laws transport exactly along a coordinate equivalence
(`expectation_reindex`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CliqueSampling

open scoped BigOperators

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Independent Bernoulli laws transport exactly along a coordinate equivalence. -/
theorem expectation_reindex (e : V ≃ W) (p : W → ℝ) (f : (V → Bool) → ℝ) :
    (∑ X : W → Bool, weight p X * f (fun v => X (e v))) =
      ∑ Y : V → Bool, weight (fun v => p (e v)) Y * f Y := by
  let E := Equiv.arrowCongr e.symm (Equiv.refl Bool)
  apply Fintype.sum_equiv E
  intro X
  have hweight : weight p X = weight (fun v => p (e v)) (E X) := by
    apply Fintype.prod_equiv e.symm
    intro w
    simp only [E, Equiv.arrowCongr_apply, Equiv.symm_symm, Function.comp_apply, Equiv.refl_apply, Equiv.apply_symm_apply]
  have heq : E X = fun v => X (e v) := by rfl
  rw [hweight, heq]

end Erdos1017.CliqueSampling

module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleExceptions

/-!
# Updated exceptions after a round

This module defines `nextExceptions`, the surviving vertices that were
exceptional, damaged by earlier exceptions, or had atypical sampled exposure,
and bounds its size by the earlier exceptions, the quantified damage and the
atypical exposures (`nextExceptions_card_bound`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The next exceptional set includes the old exceptions, vertices damaged by them,
and vertices whose sampled exposure is atypical. It is restricted to actual survivors. -/
def nextExceptions (H : Finset (Finset V)) (X : Finset V → Bool) (U W : Finset V)
    (p t a : ℝ) : Finset V :=
  survivors H X U ∩ (W ∪ damaged H W a ∪ badDegrees H X p t)

/-- The number of exceptions in the next round is bounded by old exceptions,
quantified damage, and the actual number of atypical exposures. -/
theorem nextExceptions_card_bound (H : Finset (Finset V)) (X : Finset V → Bool)
    (U W : Finset V) (p t a M : ℝ) (r : ℕ) (ha : 0 < a)
    (huniform : ∀ e ∈ H, e.card = r) (hdegree : ∀ v, (degree H v : ℝ) ≤ M) :
    ((nextExceptions H X U W p t a).card : ℝ) ≤
      W.card + r * M * W.card / a + (badDegrees H X p t).card := by
  have hdamage := damaged_count_bound H W a M r huniform hdegree
  have hdamage' : ((damaged H W a).card : ℝ) ≤ r * M * W.card / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm a] using hdamage
  have hcard : (nextExceptions H X U W p t a).card ≤
      W.card + (damaged H W a).card + (badDegrees H X p t).card := by
    exact (Finset.card_le_card Finset.inter_subset_right).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcast : ((nextExceptions H X U W p t a).card : ℝ) ≤
      W.card + (damaged H W a).card + (badDegrees H X p t).card := by exact_mod_cast hcard
  linarith

end Erdos1017.HypergraphNibble

module

public import Erdos1017.IntegerTransfer.BernoulliReindex
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Prod

/-!
# Restricting independent sampling to a coordinate group

Ignoring a disjoint group of independent coordinates does not change the law on
the retained group, and independent sampling restricts exactly along any
coordinate embedding, even when the ambient sample includes other clique types
and unused coordinates (`expectation_embedding`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CliqueSampling

open scoped BigOperators

variable {V W U : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype U] [DecidableEq U]

/-- Ignoring a disjoint group of independent coordinates does not change the
law on the retained coordinate group. -/
theorem expectation_inl (p : V ⊕ U → ℝ) (f : (V → Bool) → ℝ) :
    (∑ X : V ⊕ U → Bool, weight p X * f (fun v => X (Sum.inl v))) =
      ∑ Y : V → Bool, weight (fun v => p (Sum.inl v)) Y * f Y := by
  let E := Equiv.sumArrowEquivProdArrow V U Bool
  have hsplit : (∑ X : V ⊕ U → Bool, weight p X * f (fun v => X (Sum.inl v))) =
      ∑ c : (V → Bool) × (U → Bool),
        weight (fun v => p (Sum.inl v)) c.1 * weight (fun v => p (Sum.inr v)) c.2 * f c.1 := by
    apply Fintype.sum_equiv E
    intro X
    simp only [weight, Fintype.prod_sum_type]
    rfl
  rw [hsplit, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro Y _
  calc
    _ = (weight (fun v => p (Sum.inl v)) Y * f Y) * ∑ Z : U → Bool, weight (fun v => p (Sum.inr v)) Z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Z _
      ring
    _ = _ := by rw [bernoulli_total, mul_one]

/-- Independent sampling restricts exactly along any coordinate embedding.
The ambient sample can include other clique types and unused coordinates. -/
theorem expectation_embedding (e : V ↪ W) (p : W → ℝ) (f : (V → Bool) → ℝ) :
    (∑ X : W → Bool, weight p X * f (fun v => X (e v))) =
      ∑ Y : V → Bool, weight (fun v => p (e v)) Y * f Y := by
  classical
  let C := (Set.range e)ᶜ
  let E : (V ⊕ C) ≃ W :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl C)).trans
      (Equiv.Set.sumCompl (Set.range e))
  have hE (v : V) : E (Sum.inl v) = e v := by
    simp only [E, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  calc
    _ = ∑ Z : V ⊕ C → Bool, weight (fun v => p (E v)) Z * f (fun v => Z (Sum.inl v)) := by
      simpa only [hE] using expectation_reindex E p (fun Z => f (fun v => Z (Sum.inl v)))
    _ = _ := by simpa only [hE] using expectation_inl (fun v => p (E v)) f

end Erdos1017.CliqueSampling

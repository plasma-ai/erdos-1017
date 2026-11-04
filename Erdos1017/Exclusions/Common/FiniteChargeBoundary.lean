module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# First boundary point of a charge segment

A segment from finitely many strictly interior lower charges toward a
lower-bound violation has a first boundary point, with every coordinate still in
the closed charge box.
-/

@[expose] public section

open Set

namespace Erdos1017

/-- A segment from finitely many strictly interior lower charges toward
a lower-bound violation has a first boundary point. Every coordinate is
still in the closed charge box there, and one attains its lower endpoint. -/
theorem exists_finite_charge_boundary {ι : Type*} [Finite ι]
    (y₀ y₁ : ι → ℝ) (L U : ℝ)
    (h₀ : ∀ i, L < y₀ i ∧ y₀ i ≤ U) (h₁ : ∀ i, y₁ i ≤ U)
    (hbad : ∃ i, y₁ i ≤ L) :
    ∃ t ∈ Ioc (0 : ℝ) 1,
      (∀ i, (1 - t) * y₀ i + t * y₁ i ∈ Icc L U) ∧
      ∃ i, (1 - t) * y₀ i + t * y₁ i = L := by
  let S := {i | y₁ i ≤ L}
  let time := fun i => (y₀ i - L) / (y₀ i - y₁ i)
  have hS : S.Nonempty := hbad
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image time (Set.toFinite S) hS
  have hden (j : ι) (hj : j ∈ S) : 0 < y₀ j - y₁ j := by
    have hj' : y₁ j ≤ L := hj
    linarith [(h₀ j).1]
  have htimepos : 0 < time i := div_pos (sub_pos.mpr (h₀ i).1) (hden i hi)
  have htimeone : time i ≤ 1 := by
    apply (div_le_one (hden i hi)).mpr
    have hi' : y₁ i ≤ L := hi
    linarith
  refine ⟨time i, ⟨htimepos, htimeone⟩, ?_, i, ?_⟩
  · intro j
    constructor
    · by_cases hj : j ∈ S
      · have htime : time i * (y₀ j - y₁ j) ≤ y₀ j - L :=
          (le_div_iff₀ (hden j hj)).mp (hmin j hj)
        nlinarith only [htime]
      · have hj' : L < y₁ j := lt_of_not_ge hj
        have hleft := mul_nonneg (sub_nonneg.mpr htimeone)
          (sub_nonneg.mpr (h₀ j).1.le)
        have hright := mul_nonneg htimepos.le (sub_nonneg.mpr hj'.le)
        nlinarith only [hleft, hright]
    · have hleft := mul_nonneg (sub_nonneg.mpr htimeone) (sub_nonneg.mpr (h₀ j).2)
      have hright := mul_nonneg htimepos.le (sub_nonneg.mpr (h₁ j))
      nlinarith only [hleft, hright]
  · have heq : time i * (y₀ i - y₁ i) = y₀ i - L :=
      div_mul_cancel₀ _ (hden i hi).ne'
    nlinarith only [heq]

end Erdos1017

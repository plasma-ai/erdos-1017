module

public import Erdos1017.FractionalLimit.FractionalGraph
public import Mathlib.Data.Fintype.BigOperators

/-!
# Aggregating clique weights by part profile

This module defines the profile of a vertex set (its part labels) and the
aggregated mass `typeMass` per profile, shows that independent parts force each
clique to use each part at most once, and proves that aggregation preserves
total weight and the load on each part pair (`typeMass_pair_sum`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The set of part labels used by an actual vertex set. -/
def profile (S : Finset (Fin ℓ × A)) : Finset (Fin ℓ) := S.image Prod.fst

/-- The actual vertices of S in one part, recorded by their within-part labels. -/
def fibre (S : Finset (Fin ℓ × A)) (i : Fin ℓ) : Finset A :=
  Finset.univ.filter (fun a => (i, a) ∈ S)

omit [Fintype A] in
/-- Independent parts force each graph clique to use each part at most once. -/
theorem profile_injOn (G : SimpleGraph (Fin ℓ × A))
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (S : Finset (Fin ℓ × A)) (hS : G.IsClique (S : Set (Fin ℓ × A))) :
    Set.InjOn Prod.fst (S : Set (Fin ℓ × A)) := by
  rintro ⟨i, a⟩ hv ⟨j, b⟩ hw hrole
  change i = j at hrole
  subst j
  by_contra hne
  exact hparts i a b (hS hv hw hne)

omit [Fintype A] [DecidableEq A] in
/-- A transversal profile has the same cardinality as its actual clique. -/
theorem profile_card (S : Finset (Fin ℓ × A)) (hS : Set.InjOn Prod.fst (S : Set (Fin ℓ × A))) :
    (profile S).card = S.card := Finset.card_image_of_injOn hS

/-- A transversal has one vertex in a used part and none in an unused part. -/
theorem fibre_card (S : Finset (Fin ℓ × A)) (hS : Set.InjOn Prod.fst (S : Set (Fin ℓ × A))) (i : Fin ℓ) :
    (fibre S i).card = if i ∈ profile S then 1 else 0 := by
  by_cases hi : i ∈ profile S
  · obtain ⟨⟨j, a⟩, ha, hja⟩ := Finset.mem_image.mp hi
    change j = i at hja
    subst j
    have heq : fibre S i = {a} := by
      ext b
      simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hb
        exact congrArg Prod.snd (hS hb ha rfl)
      · rintro rfl
        exact ha
    simp only [heq, Finset.card_singleton, ite_eq_left hi]
  · have heq : fibre S i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hi (Finset.mem_image.mpr ⟨(i, a), (Finset.mem_filter.mp ha).2, rfl⟩)
    simp only [heq, Finset.card_empty, ite_eq_right hi]

/-- Fractional mass aggregated over one actual part profile. -/
def typeMass (w : Finset (Fin ℓ × A) → ℝ) (K : Finset (Fin ℓ)) : ℝ :=
  ∑ S, if profile S = K then w S else 0

omit [DecidableEq A] in
/-- Exact pushforward of arbitrary signed weights from vertex sets to profiles. -/
theorem sum_typeMass (w : Finset (Fin ℓ × A) → ℝ) (f : Finset (Fin ℓ) → ℝ) :
    (∑ K, typeMass w K * f K) = ∑ S, w S * f (profile S) := by
  simp only [typeMass, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp

omit [DecidableEq A] in
/-- Nonnegative actual clique weights give nonnegative profile masses. -/
theorem typeMass_nonneg (w : Finset (Fin ℓ × A) → ℝ) (hw : ∀ S, 0 ≤ w S)
    (K : Finset (Fin ℓ)) : 0 ≤ typeMass w K := by
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact hw S
  · exact le_rfl

/-- A transversal contributes once to a role pair precisely when both roles occur. -/
theorem transversal_pair_sum (S : Finset (Fin ℓ × A)) (hS : Set.InjOn Prod.fst (S : Set (Fin ℓ × A)))
    (i j : Fin ℓ) (z : ℝ) :
    (∑ a : A, ∑ b : A, if (i, a) ∈ S ∧ (j, b) ∈ S then z else 0) =
      if i ∈ profile S ∧ j ∈ profile S then z else 0 := by
  have heq : (∑ a : A, ∑ b : A, if (i, a) ∈ S ∧ (j, b) ∈ S then z else 0) =
      ∑ a ∈ fibre S i, ∑ b ∈ fibre S j, z := by
    simp only [fibre, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : (i, a) ∈ S <;> simp [ha]
  rw [heq]
  simp only [Finset.sum_const, nsmul_eq_mul, fibre_card S hS]
  by_cases hi : i ∈ profile S <;> by_cases hj : j ∈ profile S <;> simp [hi, hj]

/-- Exact pair load for generic labelled finite vertex sets. -/
def pairLoad (w : Finset (Fin ℓ × A) → ℝ) (v z : Fin ℓ × A) : ℝ :=
  ∑ S, if v ∈ S ∧ z ∈ S then w S else 0

/-- Profile aggregation preserves the actual total load on each part pair. -/
theorem typeMass_pair_sum (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → Set.InjOn Prod.fst (S : Set (Fin ℓ × A))) (i j : Fin ℓ) :
    (∑ K, if i ∈ K ∧ j ∈ K then typeMass w K else 0) =
      ∑ a : A, ∑ b : A, pairLoad w (i, a) (j, b) := by
  have hpush := sum_typeMass w (fun K => if i ∈ K ∧ j ∈ K then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at hpush
  rw [hpush]
  have hrhs : (∑ a : A, ∑ b : A, pairLoad w (i, a) (j, b)) =
      ∑ S : Finset (Fin ℓ × A), ∑ a : A, ∑ b : A,
        if (i, a) ∈ S ∧ (j, b) ∈ S then w S else 0 := by
    simp only [pairLoad]
    calc
      _ = ∑ a : A, ∑ S : Finset (Fin ℓ × A), ∑ b : A,
          if (i, a) ∈ S ∧ (j, b) ∈ S then w S else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hz : w S = 0
  · simp [hz]
  · exact (transversal_pair_sum S (hsupport S hz) i j (w S)).symm

end Erdos1017.MultipartiteAllocation

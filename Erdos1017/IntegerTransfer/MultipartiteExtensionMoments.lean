module

public import Erdos1017.IntegerTransfer.SharedBaseAssignments

/-!
# Extension moments as pattern counts

The first extension moment is the complete-pattern count and the second is the
shared-base doubled-pattern count, so regular pairs determine both moments with
explicit error (`first_moment_error`, `second_moment_error`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteExtension

open scoped BigOperators

variable {A : Type*} [Fintype A] {t u : ℕ}

/-- A complete transversal with one vertex from each labelled part. -/
def Realizes (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (X : Fin (t + u) → A) : Prop :=
  ∀ i j : Fin (t + u), i < j → G.Adj (i, X i) (j, X j)
deriving Decidable

/-- Actual extensions of a base assignment to a complete transversal. -/
def extensionRelation (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (x : Fin t → A) (y : Fin u → A) : Prop := Realizes G (Fin.addCases x y)
deriving Decidable

/-- Increasing pairs representing the complete graph on the role labels. -/
def completeEdges (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun e => e.1 < e.2)

/-- The actual first extension moment is the complete-pattern count. -/
theorem first_moment (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] :
    (∑ x : Fin t → A, CliqueExtension.count (extensionRelation G) x) =
      ∑ X : Fin (t + u) → A, ∏ e ∈ completeEdges (t + u),
        if G.Adj (e.1, X e.1) (e.2, X e.2) then (1 : ℝ) else 0 := by
  rw [SharedBasePattern.sum_split t u]
  simp only [CliqueExtension.count_eq_sum, Finset.prod_boole]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have heq : (∀ e ∈ completeEdges (t + u),
      G.Adj (e.1, (Fin.addCases x y : Fin (t + u) → A) e.1)
        (e.2, (Fin.addCases x y : Fin (t + u) → A) e.2)) ↔ extensionRelation G x y := by
    simp [completeEdges, extensionRelation, Realizes]
  simp only [heq]

/-- The actual second extension moment is the shared-base doubled-pattern count. -/
theorem second_moment (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] :
    (∑ x : Fin t → A, CliqueExtension.count (extensionRelation G) x ^ 2) =
      ∑ X : Fin (t + u + u) → A, ∏ e ∈ SharedBasePattern.edges t u,
        if G.Adj (SharedBasePattern.label t u e.1, X e.1)
          (SharedBasePattern.label t u e.2, X e.2) then (1 : ℝ) else 0 := by
  rw [SharedBasePattern.sum_split (t + u) u, SharedBasePattern.sum_split t u]
  simp only [CliqueExtension.count_sq, Finset.prod_boole]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  have heq := SharedBasePattern.realizes_iff t u G
    (Fin.addCases (Fin.addCases x y) z)
  simp only [SharedBasePattern.addCases_left, SharedBasePattern.addCases_right] at heq
  change (if extensionRelation G x y ∧ extensionRelation G x z then (1 : ℝ) else 0) = _
  change _ ↔ extensionRelation G x y ∧ extensionRelation G x z at heq
  by_cases h : extensionRelation G x y ∧ extensionRelation G x z
  · simp only [ite_eq_left h, ite_eq_left (heq.mpr h)]
  · simp only [ite_eq_right h, ite_eq_right (fun hr => h (heq.mp hr))]

/-- Regular pairs determine the actual first extension moment, with explicit error. -/
theorem first_moment_error [DecidableEq A] [Nonempty A]
    (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hreg : ∀ i j : Fin (t + u), i < j →
      G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j)) :
    |(∑ x : Fin t → A, CliqueExtension.count (extensionRelation G) x) -
      (Fintype.card A : ℝ) ^ (t + u) * ∏ e ∈ completeEdges (t + u),
        (G.edgeDensity (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2) : ℝ)| ≤
      (completeEdges (t + u)).card * ε * (Fintype.card A : ℝ) ^ (t + u) := by
  rw [first_moment]
  exact MultipartiteCounting.labelled_pattern_error G id (completeEdges (t + u)) hε
    (fun _ he => (Finset.mem_filter.mp he).2)
    (fun _ he => hreg _ _ (Finset.mem_filter.mp he).2)

/-- Regular pairs also determine the actual shared-base second extension moment. -/
theorem second_moment_error [DecidableEq A] [Nonempty A]
    (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hreg : ∀ i j : Fin (t + u), i < j →
      G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j)) :
    |(∑ x : Fin t → A, CliqueExtension.count (extensionRelation G) x ^ 2) -
      (Fintype.card A : ℝ) ^ (t + u + u) * ∏ e ∈ SharedBasePattern.edges t u,
        (G.edgeDensity (MultipartiteCounting.part (SharedBasePattern.label t u e.1))
          (MultipartiteCounting.part (SharedBasePattern.label t u e.2)) : ℝ)| ≤
      (SharedBasePattern.edges t u).card * ε * (Fintype.card A : ℝ) ^ (t + u + u) := by
  rw [second_moment]
  exact MultipartiteCounting.labelled_pattern_error G (SharedBasePattern.label t u)
    (SharedBasePattern.edges t u) hε (fun _ he => (Finset.mem_filter.mp he).2.1)
    (fun _ he => hreg _ _ (SharedBasePattern.label_lt_of_mem t u he))

end Erdos1017.MultipartiteExtension

module

public import Erdos1017.IntegerTransfer.SharedBaseProducts

/-!
# Base transversals and their moment restrictions

This module defines the complete base transversals with their base and extension
density products, shows that restricting the first and second extension moments
to base cliques loses no mass, and counts the base transversals as the zeroth
moment (`base_count_error`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteExtension

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] {t u : ℕ}

/-- The actual complete transversals of the base parts. -/
def bases (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] : Finset (Fin t → A) :=
  Finset.univ.filter (fun x => ∀ i j : Fin t, i < j →
    G.Adj (Fin.castAdd u i, x i) (Fin.castAdd u j, x j))

/-- The density product for the base edges. -/
def baseDensity (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] : ℝ :=
  ∏ e ∈ SharedBasePattern.baseEdges t u,
    (G.edgeDensity (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2) : ℝ)

/-- The density product for edges touching an extension vertex. -/
def extensionDensity (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] : ℝ :=
  ∏ e ∈ SharedBasePattern.extensionEdges t u,
    (G.edgeDensity (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2) : ℝ)

omit [DecidableEq A] in
/-- A base which has an extension must itself be a complete transversal. -/
theorem mem_bases_of_extension (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (x : Fin t → A) (y : Fin u → A) (h : extensionRelation G x y) : x ∈ bases G := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i j hij
  have hh := h (Fin.castAdd u i) (Fin.castAdd u j) hij
  simpa only [Fin.addCases_left] using hh

omit [DecidableEq A] in
/-- Invalid bases have no complete extensions. -/
theorem count_eq_zero_of_not_base (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (x : Fin t → A) (hx : x ∉ bases G) : CliqueExtension.count (extensionRelation G) x = 0 := by
  rw [CliqueExtension.count_eq_sum]
  apply Finset.sum_eq_zero
  intro y _
  exact ite_eq_right (fun h => hx (mem_bases_of_extension G x y h))

omit [DecidableEq A] in
/-- Restricting the first moment to actual base cliques loses no mass. -/
theorem sum_bases_count (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] :
    (∑ x ∈ bases G, CliqueExtension.count (extensionRelation G) x) =
      ∑ x : Fin t → A, CliqueExtension.count (extensionRelation G) x := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  exact count_eq_zero_of_not_base G x hx

omit [DecidableEq A] in
/-- The same holds for the actual second extension moment. -/
theorem sum_bases_count_sq (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] :
    (∑ x ∈ bases G, CliqueExtension.count (extensionRelation G) x ^ 2) =
      ∑ x : Fin t → A, CliqueExtension.count (extensionRelation G) x ^ 2 := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  rw [count_eq_zero_of_not_base G x hx]
  norm_num

/-- Counting the actual complete base transversals supplies the zeroth moment. -/
theorem base_count_error [Nonempty A]
    (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hreg : ∀ i j : Fin (t + u), i < j →
      G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j)) :
    |((bases G).card : ℝ) - (Fintype.card A : ℝ) ^ t * baseDensity G| ≤
      (completeEdges t).card * ε * (Fintype.card A : ℝ) ^ t := by
  have h := MultipartiteCounting.labelled_pattern_error G (Fin.castAdd u) (completeEdges t) hε
    (fun _ he => (Finset.mem_filter.mp he).2)
    (fun _ he => hreg _ _ (Finset.mem_filter.mp he).2)
  have hcard : ((bases G).card : ℝ) = ∑ x : Fin t → A, ∏ e ∈ completeEdges t,
      if G.Adj (Fin.castAdd u e.1, x e.1) (Fin.castAdd u e.2, x e.2) then (1 : ℝ) else 0 := by
    simp only [Finset.prod_boole, bases, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro x _
    have heq : (∀ e ∈ completeEdges t,
        G.Adj (Fin.castAdd u e.1, x e.1) (Fin.castAdd u e.2, x e.2)) ↔
        ∀ i j : Fin t, i < j → G.Adj (Fin.castAdd u i, x i) (Fin.castAdd u j, x j) := by
      simp [completeEdges]
    by_cases hx : ∀ i j : Fin t, i < j → G.Adj (Fin.castAdd u i, x i) (Fin.castAdd u j, x j)
    · simp only [ite_eq_left hx, ite_eq_left (heq.mpr hx)]
    · simp only [ite_eq_right hx, ite_eq_right (fun hr => hx (heq.mp hr))]
  rw [hcard, baseDensity, SharedBasePattern.product_base]
  exact h

end Erdos1017.MultipartiteExtension

module

public import Erdos1017.IntegerTransfer.CliqueExtensionMoments

/-!
# The doubled pattern over a shared base

This module defines the doubled pattern formed by two complete patterns that
share a base and use separate extension blocks, keeping the original part
labels, and shows that realizing it is exactly realizing both copies, with
shared-base edges occurring only once (`realizes_iff`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.SharedBasePattern

variable (t u : ℕ)

/-- Both extension copies retain their original part labels. -/
def label (i : Fin (t + u + u)) : Fin (t + u) :=
  if h : i.val < t + u then ⟨i.val, h⟩ else ⟨i.val - u, by omega⟩

/-- The first complete pattern uses the initial base and extension blocks. -/
def left (i : Fin (t + u)) : Fin (t + u + u) := Fin.castAdd u i

/-- The second complete pattern shares the base and uses the last extension block. -/
def right (i : Fin (t + u)) : Fin (t + u + u) :=
  if h : i.val < t then ⟨i.val, by omega⟩ else ⟨i.val + u, by omega⟩

/-- Edges of two complete patterns glued along their first `t` vertices.
There are no edges between the two extension copies. -/
def edges : Finset (Fin (t + u + u) × Fin (t + u + u)) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧
    ((e.1.val < t + u ∧ e.2.val < t + u) ∨
      ((e.1.val < t ∨ t + u ≤ e.1.val) ∧ (e.2.val < t ∨ t + u ≤ e.2.val))))

@[simp] theorem label_left (i : Fin (t + u)) : label t u (left t u i) = i := by
  apply Fin.ext
  simp [label, left, i.isLt]

@[simp] theorem label_right (i : Fin (t + u)) : label t u (right t u i) = i := by
  by_cases hi : i.val < t
  · simp [right, hi, label, i.isLt]
  · have htotal : ¬ i.val + u < t + u := by omega
    simp [right, hi, label, htotal]

theorem left_strictMono : StrictMono (left t u) := by
  intro i j hij
  exact hij

theorem right_strictMono : StrictMono (right t u) := by
  intro i j hij
  simp only [right]
  split_ifs <;> simp_all <;> omega

/-- Every doubled-pattern edge joins distinct original labels in increasing order. -/
theorem label_lt_of_mem {e : Fin (t + u + u) × Fin (t + u + u)}
    (he : e ∈ edges t u) : label t u e.1 < label t u e.2 := by
  have he := (Finset.mem_filter.mp he).2
  change (label t u e.1).val < (label t u e.2).val
  simp only [label]
  split_ifs <;> dsimp only at * <;> omega

theorem left_edge_mem {i j : Fin (t + u)} (hij : i < j) :
    (left t u i, left t u j) ∈ edges t u := by
  simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and, left, Fin.val_castAdd]
  exact ⟨hij, Or.inl ⟨i.isLt, j.isLt⟩⟩

theorem right_edge_mem {i j : Fin (t + u)} (hij : i < j) :
    (right t u i, right t u j) ∈ edges t u := by
  have hmono := right_strictMono t u hij
  simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hmono, Or.inr ?_⟩
  constructor <;> simp only [right] <;> split_ifs <;> simp_all

theorem left_label_of_lt (i : Fin (t + u + u)) (hi : i.val < t + u) :
    left t u (label t u i) = i := by
  apply Fin.ext
  simp [left, label, hi]

theorem right_label_of_right (i : Fin (t + u + u))
    (hi : i.val < t ∨ t + u ≤ i.val) : right t u (label t u i) = i := by
  apply Fin.ext
  simp only [right, label]
  split_ifs <;> dsimp only at * <;> omega

/-- Every edge belongs to one of the two complete copies. -/
theorem edge_copies {e : Fin (t + u + u) × Fin (t + u + u)} (he : e ∈ edges t u) :
    (left t u (label t u e.1) = e.1 ∧ left t u (label t u e.2) = e.2) ∨
      (right t u (label t u e.1) = e.1 ∧ right t u (label t u e.2) = e.2) := by
  rcases (Finset.mem_filter.mp he).2.2 with hleft | hright
  · exact Or.inl ⟨left_label_of_lt t u e.1 hleft.1, left_label_of_lt t u e.2 hleft.2⟩
  · exact Or.inr ⟨right_label_of_right t u e.1 hright.1,
      right_label_of_right t u e.2 hright.2⟩

/-- Realizing the doubled pattern is exactly realizing both original complete
patterns. Shared-base edges occur only once in the edge set. -/
theorem realizes_iff {A : Type*} (G : SimpleGraph (Fin (t + u) × A))
    (X : Fin (t + u + u) → A) :
    (∀ e ∈ edges t u, G.Adj (label t u e.1, X e.1) (label t u e.2, X e.2)) ↔
      (∀ i j : Fin (t + u), i < j → G.Adj (i, X (left t u i)) (j, X (left t u j))) ∧
      (∀ i j : Fin (t + u), i < j → G.Adj (i, X (right t u i)) (j, X (right t u j))) := by
  constructor
  · intro h
    constructor
    · intro i j hij
      simpa only [label_left] using h _ (left_edge_mem t u hij)
    · intro i j hij
      simpa only [label_right] using h _ (right_edge_mem t u hij)
  · rintro ⟨hl, hr⟩ e he
    have hlt := label_lt_of_mem t u he
    rcases edge_copies t u he with hcopy | hcopy
    · simpa only [hcopy.1, hcopy.2] using hl _ _ hlt
    · simpa only [hcopy.1, hcopy.2] using hr _ _ hlt

end Erdos1017.SharedBasePattern

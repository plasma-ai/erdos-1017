module

public import Erdos1017.IntegerTransfer.RegularPairSlicing
public import Mathlib.Tactic.Positivity

/-!
# Typical degrees into a regular pair

In a regular pair, all but at most `2ε|s|` vertices of the first part have the
predicted degree into the second part up to an additive error `ε|t|`
(`atypical_degree_card_le`), and the same holds simultaneously for a finite
family of regular partner sets.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.RegularPair

open Finset

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edge counts are the sum of the degrees into the second part. -/
theorem interedges_card_eq_sum (s t : Finset V) :
    (G.interedges s t).card = ∑ x ∈ s, (t.filter (G.Adj x)).card := by
  simp only [SimpleGraph.interedges, Rel.interedges, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

/-- In a regular pair, at most an ε fraction of the first part has degree
below the density prediction by more than ε times the second part's size. -/
theorem low_degree_card_le {s t : Finset V} {ε : ℝ}
    (h : G.IsUniform ε s t) (hε : ε ≤ 1) :
    ((s.filter (fun x => ((t.filter (G.Adj x)).card : ℝ) <
      ((G.edgeDensity s t : ℝ) - ε) * t.card)).card : ℝ) ≤ s.card * ε := by
  let B := s.filter (fun x => ((t.filter (G.Adj x)).card : ℝ) <
    ((G.edgeDensity s t : ℝ) - ε) * t.card)
  change (B.card : ℝ) ≤ s.card * ε
  by_contra! hB
  have hBpos : 0 < (B.card : ℝ) := (mul_nonneg (Nat.cast_nonneg _) h.pos.le).trans_lt hB
  have hsum : ((G.interedges B t).card : ℝ) ≤
      B.card * (((G.edgeDensity s t : ℝ) - ε) * t.card) := by
    rw [interedges_card_eq_sum, Nat.cast_sum]
    exact (Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2.le)).trans_eq
      (by simp)
  have hclose := h (Finset.filter_subset _ _) Finset.Subset.rfl hB.le
    (mul_le_of_le_one_right (Nat.cast_nonneg _) hε)
  have htpos : 0 < (t.card : ℝ) := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hBpos)
    have hxt := (Finset.mem_filter.mp hx).2
    by_contra! ht
    have htzero : t.card = 0 := by exact_mod_cast le_antisymm ht (Nat.cast_nonneg _)
    simp [Finset.card_eq_zero.mp htzero] at hxt
  have hdensity : (G.edgeDensity B t : ℝ) ≤ (G.edgeDensity s t : ℝ) - ε := by
    rw [G.edgeDensity_def B t]
    push_cast
    apply (div_le_iff₀ (mul_pos hBpos htpos)).mpr
    nlinarith [hsum]
  have := (abs_sub_lt_iff.mp hclose).2
  linarith

/-- The corresponding upper-tail estimate for degrees into a regular pair. -/
theorem high_degree_card_le {s t : Finset V} {ε : ℝ}
    (h : G.IsUniform ε s t) (hε : ε ≤ 1) :
    ((s.filter (fun x => ((G.edgeDensity s t : ℝ) + ε) * t.card <
      ((t.filter (G.Adj x)).card : ℝ))).card : ℝ) ≤ s.card * ε := by
  let B := s.filter (fun x => ((G.edgeDensity s t : ℝ) + ε) * t.card <
    ((t.filter (G.Adj x)).card : ℝ))
  change (B.card : ℝ) ≤ s.card * ε
  by_contra! hB
  have hBpos : 0 < (B.card : ℝ) := (mul_nonneg (Nat.cast_nonneg _) h.pos.le).trans_lt hB
  have hsum : B.card * (((G.edgeDensity s t : ℝ) + ε) * t.card) ≤
      ((G.interedges B t).card : ℝ) := by
    rw [interedges_card_eq_sum, Nat.cast_sum]
    calc
      _ = ∑ _x ∈ B, (((G.edgeDensity s t : ℝ) + ε) * t.card) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2.le)
  have hclose := h (Finset.filter_subset _ _) Finset.Subset.rfl hB.le
    (mul_le_of_le_one_right (Nat.cast_nonneg _) hε)
  have htpos : 0 < (t.card : ℝ) := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hBpos)
    have hxt := (Finset.mem_filter.mp hx).2
    by_contra! ht
    have htzero : t.card = 0 := by exact_mod_cast le_antisymm ht (Nat.cast_nonneg _)
    simp [Finset.card_eq_zero.mp htzero] at hxt
  have hdensity : (G.edgeDensity s t : ℝ) + ε ≤ (G.edgeDensity B t : ℝ) := by
    rw [G.edgeDensity_def B t]
    push_cast
    apply (le_div_iff₀ (mul_pos hBpos htpos)).mpr
    nlinarith [hsum]
  have := (abs_sub_lt_iff.mp hclose).1
  linarith

variable [DecidableEq V]

/-- All but at most `2ε|s|` vertices have the predicted degree, with additive
error `ε|t|`. Both tails are controlled by the actual regular pair. -/
theorem atypical_degree_card_le {s t : Finset V} {ε : ℝ}
    (h : G.IsUniform ε s t) (hε : ε ≤ 1) :
    ((s.filter (fun x => ¬
      (((G.edgeDensity s t : ℝ) - ε) * t.card ≤ (t.filter (G.Adj x)).card ∧
       ((t.filter (G.Adj x)).card : ℝ) ≤ ((G.edgeDensity s t : ℝ) + ε) * t.card))).card : ℝ)
      ≤ 2 * ε * s.card := by
  have heq : s.filter (fun x => ¬
      (((G.edgeDensity s t : ℝ) - ε) * t.card ≤ (t.filter (G.Adj x)).card ∧
       ((t.filter (G.Adj x)).card : ℝ) ≤ ((G.edgeDensity s t : ℝ) + ε) * t.card)) =
      (s.filter (fun x => ((t.filter (G.Adj x)).card : ℝ) <
        ((G.edgeDensity s t : ℝ) - ε) * t.card)) ∪
      (s.filter (fun x => ((G.edgeDensity s t : ℝ) + ε) * t.card <
        ((t.filter (G.Adj x)).card : ℝ))) := by
    ext x
    simp only [mem_filter, mem_union, not_and_or, not_le, and_or_left]
  rw [heq]
  have hc := Finset.card_union_le
    (s.filter (fun x => ((t.filter (G.Adj x)).card : ℝ) <
      ((G.edgeDensity s t : ℝ) - ε) * t.card))
    (s.filter (fun x => ((G.edgeDensity s t : ℝ) + ε) * t.card <
      ((t.filter (G.Adj x)).card : ℝ)))
  have hcr := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcr
  linarith [low_degree_card_le G h hε, high_degree_card_le G h hε]

/-- Simultaneous typical degrees into a finite family of regular partner sets.
This is the exceptional-vertex estimate in the clique-counting induction. -/
theorem atypical_family_card_le {ι : Type*} (I : Finset ι)
    (s : Finset V) (t : ι → Finset V) {ε : ℝ}
    (h : ∀ i ∈ I, G.IsUniform ε s (t i)) (hε : ε ≤ 1) :
    ((s.filter (fun x => ∃ i ∈ I, ¬
      (((G.edgeDensity s (t i) : ℝ) - ε) * (t i).card ≤ ((t i).filter (G.Adj x)).card ∧
       (((t i).filter (G.Adj x)).card : ℝ) ≤
         ((G.edgeDensity s (t i) : ℝ) + ε) * (t i).card))).card : ℝ)
      ≤ 2 * I.card * ε * s.card := by
  classical
  let B := fun i => s.filter (fun x => ¬
    (((G.edgeDensity s (t i) : ℝ) - ε) * (t i).card ≤ ((t i).filter (G.Adj x)).card ∧
     (((t i).filter (G.Adj x)).card : ℝ) ≤
       ((G.edgeDensity s (t i) : ℝ) + ε) * (t i).card))
  have heq : s.filter (fun x => ∃ i ∈ I, ¬
      (((G.edgeDensity s (t i) : ℝ) - ε) * (t i).card ≤ ((t i).filter (G.Adj x)).card ∧
       (((t i).filter (G.Adj x)).card : ℝ) ≤
         ((G.edgeDensity s (t i) : ℝ) + ε) * (t i).card)) = I.biUnion B := by
    ext x
    simp only [mem_filter, mem_biUnion, B]
    aesop
  rw [heq]
  calc
    ((I.biUnion B).card : ℝ) ≤ ∑ i ∈ I, ((B i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, 2 * ε * s.card :=
      Finset.sum_le_sum (fun i hi => atypical_degree_card_le G (h i hi) hε)
    _ = _ := by simp; ring

end Erdos1017.RegularPair

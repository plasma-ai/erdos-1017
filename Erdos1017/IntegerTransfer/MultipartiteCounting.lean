module

public import Erdos1017.IntegerTransfer.CliqueCountingPattern
public import Erdos1017.IntegerTransfer.RegularPairDiscrepancy

/-!
# Pattern counting in regular labeled parts

This module counts the assignments realizing a pattern in regular labeled parts,
with an explicit additive error for every pattern edge
(`graph_pattern_discrepancy`) and a relative error that follows from a positive
lower bound on the pair densities with a tolerance independent of the part size
(`assignments_relative_error`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCounting

open scoped BigOperators

variable {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The actual vertex set of a labelled part. -/
def part (i : Fin k) : Finset (Fin k × A) :=
  Finset.univ.map ⟨fun a => (i, a), Prod.mk_right_injective i⟩

omit [DecidableEq A] in
/-- Regularity of two labelled parts gives the rectangle discrepancy required
by the bounded-pattern counting theorem. -/
theorem part_discrepancy (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    {i j : Fin k} {ε : ℝ} (h : G.IsUniform ε (part i) (part j))
    (X Y : A → Bool) :
    |∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) *
      ((if G.Adj (i, a) (j, b) then (1 : ℝ) else 0) - G.edgeDensity (part i) (part j))|
      ≤ ε * (Fintype.card A : ℝ) ^ 2 := by
  let a := (Finset.univ.filter (fun a => X a = true)).map
    ⟨fun a => (i, a), Prod.mk_right_injective i⟩
  let b := (Finset.univ.filter (fun b => Y b = true)).map
    ⟨fun b => (j, b), Prod.mk_right_injective j⟩
  have ha : a ⊆ part i := Finset.map_subset_map.mpr (Finset.filter_subset _ _)
  have hb : b ⊆ part j := Finset.map_subset_map.mpr (Finset.filter_subset _ _)
  have hc := RegularPair.rectangle_sum_discrepancy G h ha hb
  rw [WeightedRectangle.indicator_sum_eq]
  simpa only [a, b, part, Finset.sum_map, Function.Embedding.coeFn_mk,
    Finset.card_map, Finset.card_univ, pow_two, mul_assoc] using hc

/-- Actual graph pattern counts in regular labelled parts, with an explicit
additive error for every pattern edge. Repeated labels are not introduced. -/
theorem graph_pattern_discrepancy (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (E : Finset (Fin k × Fin k)) {ε : ℝ} (hε : 0 ≤ ε)
    (horder : ∀ e ∈ E, e.1 < e.2)
    (hreg : ∀ e ∈ E, G.IsUniform ε (part e.1) (part e.2)) :
    (Fintype.card A : ℝ) ^ 2 *
      |(∑ X : Fin k → A, ∏ e ∈ E, if G.Adj (e.1, X e.1) (e.2, X e.2) then (1 : ℝ) else 0) -
        Fintype.card (Fin k → A) * ∏ e ∈ E, (G.edgeDensity (part e.1) (part e.2) : ℝ)| ≤
      E.card * Fintype.card (Fin k → A) * (ε * (Fintype.card A : ℝ) ^ 2) := by
  apply CliqueCounting.pattern_discrepancy E
    (fun e a b => if G.Adj (e.1, a) (e.2, b) then 1 else 0)
    (fun e => (G.edgeDensity (part e.1) (part e.2) : ℝ))
    (ε * (Fintype.card A : ℝ) ^ 2) (by positivity) horder
  · intro e _ a b
    split_ifs <;> constructor <;> norm_num
  · intro e _
    constructor
    · exact_mod_cast G.edgeDensity_nonneg (part e.1) (part e.2)
    · exact_mod_cast G.edgeDensity_le_one (part e.1) (part e.2)
  · intro e he X Y
    exact part_discrepancy G (hreg e he) X Y

/-- Actual assignments realizing every edge of the pattern. -/
def assignments (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (E : Finset (Fin k × Fin k)) : Finset (Fin k → A) :=
  Finset.univ.filter (fun X => ∀ e ∈ E, G.Adj (e.1, X e.1) (e.2, X e.2))

omit [DecidableEq A] in
/-- The product expression counts actual pattern assignments. -/
theorem assignments_card (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (E : Finset (Fin k × Fin k)) :
    ((assignments G E).card : ℝ) =
      ∑ X : Fin k → A, ∏ e ∈ E,
        if G.Adj (e.1, X e.1) (e.2, X e.2) then (1 : ℝ) else 0 := by
  simp only [Finset.prod_boole, assignments, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro X _
  split_ifs <;> rfl

/-- Absolute counting error for actual assignments in nonempty equal-sized parts. -/
theorem assignments_error [Nonempty A]
    (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (E : Finset (Fin k × Fin k)) {ε : ℝ} (hε : 0 ≤ ε)
    (horder : ∀ e ∈ E, e.1 < e.2)
    (hreg : ∀ e ∈ E, G.IsUniform ε (part e.1) (part e.2)) :
    |((assignments G E).card : ℝ) -
      (Fintype.card A : ℝ) ^ k * ∏ e ∈ E, (G.edgeDensity (part e.1) (part e.2) : ℝ)| ≤
      E.card * ε * (Fintype.card A : ℝ) ^ k := by
  have h := graph_pattern_discrepancy G E hε horder hreg
  rw [← assignments_card] at h
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  apply le_of_mul_le_mul_left (a := (Fintype.card A : ℝ) ^ 2) ?_ (sq_pos_of_pos hn)
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- Relative counting error follows from a positive lower bound on the pair
densities. The tolerance is explicit and independent of the part size. -/
theorem assignments_relative_error [Nonempty A]
    (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (E : Finset (Fin k × Fin k)) {ε δ γ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (htolerance : E.card * ε ≤ γ * δ ^ E.card)
    (horder : ∀ e ∈ E, e.1 < e.2)
    (hreg : ∀ e ∈ E, G.IsUniform ε (part e.1) (part e.2))
    (hdensity : ∀ e ∈ E, δ ≤ G.edgeDensity (part e.1) (part e.2)) :
    |((assignments G E).card : ℝ) -
      (Fintype.card A : ℝ) ^ k * ∏ e ∈ E, (G.edgeDensity (part e.1) (part e.2) : ℝ)| ≤
      γ * ((Fintype.card A : ℝ) ^ k * ∏ e ∈ E,
        (G.edgeDensity (part e.1) (part e.2) : ℝ)) := by
  have hprod : δ ^ E.card ≤ ∏ e ∈ E, (G.edgeDensity (part e.1) (part e.2) : ℝ) := by
    simpa only [Finset.prod_const] using
      Finset.prod_le_prod₀ (fun e (_ : e ∈ E) => hδ) hdensity
  have he := assignments_error G E hε horder hreg
  have hmul := mul_le_mul_of_nonneg_right htolerance
    (pow_nonneg (Nat.cast_nonneg (Fintype.card A)) k)
  have hmul' := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg hγ (pow_nonneg (Nat.cast_nonneg (Fintype.card A)) k))
  nlinarith

end Erdos1017.MultipartiteCounting

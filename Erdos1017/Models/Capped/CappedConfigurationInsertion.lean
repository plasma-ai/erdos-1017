module

public import Erdos1017.Models.Capped.CappedColorConfiguration

/-!
# Filling absent pairs of a sampled configuration

Missing sampled pair colors are exactly the missing edges of the sampled finite
graph, and filling each absent outcome at the repair charge `-3` (`insertColor`)
proves the clique inequality by the finite fractional cost-four repair.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.CappedModel

variable {n : ℕ}

open scoped Classical in
def missingPairs (c : CliquePair n → CappedColor) : Finset (CliquePair n) :=
  Finset.univ.filter (fun p => CappedColor.adjacency (c p) ≠ 1)

/-- Missing sampled pair colors are exactly the missing unordered edges of
the actual sampled finite graph. -/
theorem missingPairs_card (c : CliquePair n → CappedColor) :
    (missingPairs c).card =
      (FractionalGraph.finiteEdges (⊤ : SimpleGraph (Fin n)) \
        FractionalGraph.finiteEdges (configurationGraph c)).card := by
  classical
  apply Finset.card_bij (fun p _ => s(p.val.1, p.val.2))
  · intro p hp
    simp only [Finset.mem_sdiff, FractionalGraph.mem_finiteEdges, SimpleGraph.top_adj]
    refine ⟨p.property.ne, ?_⟩
    change CappedColor.adjacency (pairColor c p.val.1 p.val.2) ≠ 1
    rw [pairColor_lt _ _ _ p.property]
    exact (Finset.mem_filter.mp hp).2
  · intro p hp q hq hpq
    rcases Sym2.eq_iff.mp hpq with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have hlt := p.property
      rw [h.1, h.2] at hlt
      exact False.elim (lt_asymm hlt q.property)
  · intro z hz
    induction z using Sym2.ind with
    | h i j =>
      have hz' := hz
      simp only [Finset.mem_sdiff, FractionalGraph.mem_finiteEdges, SimpleGraph.top_adj] at hz'
      rcases lt_or_gt_of_ne hz'.1 with hij | hij
      · let p : CliquePair n := ⟨(i, j), hij⟩
        refine ⟨p, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hno := hz'.2
        change CappedColor.adjacency (pairColor c i j) ≠ 1 at hno
        rw [pairColor_lt c i j hij] at hno
        exact hno
      · let p : CliquePair n := ⟨(j, i), hij⟩
        refine ⟨p, ?_, Sym2.eq_swap⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hno : CappedColor.adjacency (pairColor c j i) ≠ 1 := by
          rw [pairColor_symm]
          exact hz'.2
        simpa [p, pairColor_lt c j i hij] using hno

def negativeThree : CappedColor := CappedColor.present (-3) ⟨le_rfl, by norm_num⟩

@[simp] theorem adjacency_negativeThree : CappedColor.adjacency negativeThree = 1 := rfl

@[simp] theorem charge_negativeThree : CappedColor.charge negativeThree = -3 := rfl

open scoped Classical in
/-- Fill each absent outcome at the cost-four repair charge `-3`. -/
def insertColor (c : CappedColor) : CappedColor :=
  if CappedColor.adjacency c = 1 then c else negativeThree

theorem sum_insertColor (c : CliquePair n → CappedColor) :
    (∑ p, CappedColor.charge (insertColor (c p))) =
      (∑ p, CappedColor.charge (c p)) - 3 * ((missingPairs c).card : ℝ) := by
  classical
  have hpoint (p : CliquePair n) : CappedColor.charge (insertColor (c p)) =
      CappedColor.charge (c p) - 3 * (if CappedColor.adjacency (c p) ≠ 1 then 1 else 0) := by
    by_cases hp : CappedColor.adjacency (c p) = 1
    · simp [insertColor, hp]
    · simp [insertColor, color_eq_absent_of_not_present (c p) hp]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  rfl

/-- The finite fractional cost-four repair proves the clique inequality
after filling absent sampled outcomes at charge `-3`. -/
theorem sum_insertColor_le_one (c : CliquePair n → CappedColor) (hn : 2 ≤ n)
    (htests : ∀ k, 2 ≤ k → k ≤ n → ∀ e : Fin k ↪o Fin n,
      violation (fun p => c (pairEmbedding e p)) = 0) :
    (∑ p, CappedColor.charge (insertColor (c p))) ≤ 1 := by
  have h := WeightedGraph.dual_charge_minus_three_missing_le_one (configurationGraph c) hn
    (chargeMatrix c) (configuration_dualFeasible c htests)
  rw [chargeMatrix_objective, ← missingPairs_card] at h
  rwa [sum_insertColor]

end Erdos1017.CappedModel

module

public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Completing the cut of an independent positive cover

The adjacency `completeCrossAdjacency` completes the cut between an independent
positive-charge cover and its complement, and completing every cross edge at
zero charge preserves all finite clique tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.FiniteArity

/-- Complete the cut between an independent positive-charge cover and its
complement, retaining all old incidences on each side. -/
def completeCrossAdjacency {Ω : Type*} (A : Ω → Ω → Bool) (H : Set Ω)
    [DecidablePred (· ∈ H)] (x y : Ω) : Bool :=
  if (x ∈ H ∧ y ∉ H) ∨ (y ∈ H ∧ x ∉ H) then true else A x y

private theorem pairCharge_le_filter {α : Type*} [Fintype α] [DecidableEq α]
    (Y : α → α → ℝ) (P : α → Prop) [DecidablePred P]
    (hdrop : ∀ i j, ¬(P i ∧ P j) → Y i j ≤ 0) :
    pairCharge Finset.univ Y ≤ pairCharge (Finset.univ.filter P) Y := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold crossSum
  calc
    _ ≤ ∑ i, ∑ j, if P i ∧ P j then Y i j else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : P i ∧ P j
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        exact hdrop i j h
    _ = _ := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i <;> simp [hi]

/-- Completing every cross edge at zero charge preserves all actual finite
clique tests. A completed clique has at most one cover vertex; deleting its
old nonneighbors removes only nonpositive charges. -/
theorem feasibleOrder_complete_cross_of_independent_positive_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (H : Set Ω) [DecidablePred (· ∈ H)]
    (hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ H → p.2 ∈ H → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ H → p.2 ∉ H → Y p.1 p.2 ≤ 0)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FeasibleOrder μ A Y n) (n : ℕ) :
    FeasibleOrder μ (completeCrossAdjacency A H) Y n := by
  classical
  have hpairs := ae_all_pairs μ n _ (hind.and (hbody.and hzero))
  have hsub := ae_all_subtuples μ n n
    (fun _ v => TupleClique A v → tupleCharge Y v ≤ 1) (fun r _ => hfull r)
  filter_upwards [hpairs, hsub] with v hp hv hclique
  by_cases hex : ∃ r, v r ∈ H
  · obtain ⟨r, hr⟩ := hex
    have hout {i : Fin n} (hi : i ≠ r) : v i ∉ H := by
      intro hiH
      have ha := hclique i r hi
      have hz := (hp i r hi).1 hiH hr
      simp only [completeCrossAdjacency, hiH, hr, not_true_eq_false,
        and_false, or_self, ite_false, hz, Bool.false_eq_true] at ha
    let P : Fin n → Prop := fun i => i = r ∨ A (v r) (v i) = true
    let T := Finset.univ.filter P
    let e := (T.orderEmbOfFin rfl).toEmbedding
    have he (i : Fin T.card) : P (e i) := by
      exact (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl i)).2
    have hold : TupleClique A (fun i => v (e i)) := by
      intro i j hij
      change A (v (e i)) (v (e j)) = true
      have heij : e i ≠ e j := fun h => hij (e.injective h)
      by_cases hi : e i = r
      · rw [hi]
        exact (he j).resolve_left (fun h => heij (hi.trans h.symm))
      · by_cases hj : e j = r
        · rw [hj, hAsym]
          exact (he i).resolve_left hi
        · simpa only [completeCrossAdjacency, hout hi, hout hj, false_and,
            or_self, ite_false] using hclique (e i) (e j) heij
    have ht := hv T.card (by simpa using Finset.card_le_univ T) e hold
    rw [tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ T rfl] at ht
    change pairCharge Finset.univ (fun i j => if i = j then 0 else Y (v i) (v j)) ≤ 1
    refine (pairCharge_le_filter _ P ?_).trans ht
    have hrow {i : Fin n} (hi : ¬P i) (j : Fin n) :
        (if i = j then 0 else Y (v i) (v j)) ≤ 0 := by
      by_cases hij : i = j
      · simp only [hij, ite_true, le_refl]
      · rw [ite_eq_right hij]
        have hir : i ≠ r := fun h => hi (Or.inl h)
        by_cases hjr : j = r
        · subst j
          have ha : A (v r) (v i) = false :=
            Bool.eq_false_iff.mpr (fun h => hi (Or.inr h))
          rw [hYsym, (hp r i hir.symm).2.2 ha]
        · exact (hp i j hij).2.1 (hout hir) (hout hjr)
    intro i j hij
    by_cases hi : P i
    · have hj : ¬P j := fun hj => hij ⟨hi, hj⟩
      have h := hrow hj i
      simpa only [eq_comm, hYsym] using h
    · exact hrow hi j
  · have hout (i : Fin n) : v i ∉ H := fun hi => hex ⟨i, hi⟩
    have hold : TupleClique A v := by
      intro i j hij
      simpa only [completeCrossAdjacency, hout i, hout j, false_and,
        or_self, ite_false] using hclique i j hij
    exact hv n le_rfl (Function.Embedding.refl _) hold

end Erdos1017.FiniteArity

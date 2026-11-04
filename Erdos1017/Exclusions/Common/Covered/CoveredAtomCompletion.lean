module

public import Erdos1017.SelectedModel.DiffuseCompletionFeasibility
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Completing an independent cell under one root

Repeated vertices of a completed independent cell can be deleted when its
internal penalty pays for its only possible positive root incidence, and
completing the cell at penalty `ell` preserves every clique test when the
positive incidences are covered by one independent root.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.FiniteArity

private theorem pairCharge_erase {α : Type*} [DecidableEq α]
    (U : Finset α) (a : α) (ha : a ∈ U) (Y : α → α → ℝ)
    (hdiag : ∀ i, Y i i = 0) (hsym : ∀ i j, Y i j = Y j i) :
    pairCharge U Y = pairCharge (U.erase a) Y + ∑ b ∈ U.erase a, Y a b := by
  have hU : {a} ∪ U.erase a = U := by ext b; simp; grind
  have hdisj : Disjoint ({a} : Finset α) (U.erase a) := by simp
  nth_rw 1 [← hU]
  rw [pairCharge_union _ _ hdisj]
  simp only [pairCharge, crossSum, Finset.sum_singleton, hdiag, zero_div, zero_add]
  simp_rw [hsym a]
  ring

/-- Repeated vertices in a completed independent cell can be deleted when
its internal penalty pays for its only possible positive root incidence.
Every retained test is an actual subset test with at most one cell vertex. -/
theorem pairCharge_le_of_single_root_deletion {α : Type*} [DecidableEq α]
    (U : Finset α) (Y : α → α → ℝ) (R D : Set α) (ell : ℝ)
    (hdiag : ∀ i, Y i i = 0) (hsym : ∀ i j, Y i j = Y j i)
    (hdisj : ∀ a ∈ D, a ∉ R)
    (hroot : ∀ a ∈ U, ∀ b ∈ U, a ∈ R → b ∈ R → a = b)
    (hDD : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → a ∈ D → b ∈ D → Y a b = -ell)
    (hstar : ∀ a ∈ U, ∀ b ∈ U, a ∈ D → b ∈ R → Y a b ≤ ell)
    (hbody : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → a ∈ D → b ∉ R → Y a b ≤ 0)
    (htest : ∀ S ⊆ U, (∀ a ∈ S, ∀ b ∈ S, a ∈ D → b ∈ D → a = b) →
      pairCharge S Y ≤ 1) : pairCharge U Y ≤ 1 := by
  have hall : ∀ S : Finset α, S ⊆ U → pairCharge S Y ≤ 1 := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hS
    by_cases hsingle : ∀ a ∈ S, ∀ b ∈ S, a ∈ D → b ∈ D → a = b
    · exact htest S hS hsingle
    · push Not at hsingle
      obtain ⟨a, ha, b, hb, haD, hbD, hab⟩ := hsingle
      have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
      have hrow : (∑ k ∈ S.erase a, Y a k) ≤ 0 := by
        by_cases hex : ∃ r ∈ S.erase a, r ∈ R
        · obtain ⟨r, hr, hrR⟩ := hex
          have hbr : b ≠ r := fun heq => hdisj b hbD (heq.symm ▸ hrR)
          calc
            _ ≤ ∑ k ∈ S.erase a, ((if k = b then -ell else 0) + (if k = r then ell else 0)) := by
              apply Finset.sum_le_sum
              intro k hk
              have hkS := Finset.mem_of_mem_erase hk
              by_cases hkb : k = b
              · subst k
                simp only [ite_true, hbr, ite_false, add_zero]
                exact (hDD a (hS ha) b (hS hb) hab haD hbD).le
              · by_cases hkr : k = r
                · subst k
                  simp only [hkb, ite_false, ite_true, zero_add]
                  exact hstar a (hS ha) r (hS hkS) haD hrR
                · simp only [hkb, hkr, ite_false, add_zero]
                  apply hbody a (hS ha) k (hS hkS) (Finset.ne_of_mem_erase hk).symm haD
                  intro hkR
                  exact hkr (hroot k (hS hkS) r (hS (Finset.mem_of_mem_erase hr)) hkR hrR)
            _ = 0 := by simp [Finset.sum_add_distrib, hb', hr]
        · apply Finset.sum_nonpos
          intro k hk
          exact hbody a (hS ha) k (hS (Finset.mem_of_mem_erase hk))
            (Finset.ne_of_mem_erase hk).symm haD (fun hkR => hex ⟨k, hk, hkR⟩)
      rw [pairCharge_erase S a ha Y hdiag hsym]
      have hle := ih (S.erase a) (Finset.erase_ssubset ha)
        (Finset.Subset.trans (Finset.erase_subset _ _) hS)
      linarith
  exact hall U Finset.Subset.rfl

/-- Completing an independent cell at penalty `ell` preserves every actual
clique test when its positive incidences are covered by one independent
root and each such incidence is at most `ell`. The subset tests come from
the original product laws; completed tests are not assumptions. -/
theorem feasibleOrder_complete_of_single_root
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (R D : Set Ω) [DecidablePred (· ∈ D)] (hdisj : Disjoint R D)
    (ell : ℝ) (hell : 0 ≤ ell)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → A p.1 p.2 = false)
    (hcell : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0)
    (hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ R → Y p.1 p.2 ≤ ell)
    (hfull : ∀ n, FeasibleOrder μ A Y n) (n : ℕ) :
    FeasibleOrder μ (completeAdjacency A D) (completeCharge A Y D ell) n := by
  classical
  have hpairs := ae_all_pairs μ n _ (hroot.and (hcell.and (hbody.and hstar)))
  have hsub := ae_all_subtuples μ n n
    (fun _ v => TupleClique A v → tupleCharge Y v ≤ 1) (fun r _ => hfull r)
  filter_upwards [hpairs, hsub] with v hp hv hclique
  let Z := completeCharge A Y D ell
  let z (i j : Fin n) : ℝ := if i = j then 0 else Z (v i) (v j)
  have hsep {x : Ω} (hx : x ∈ D) : x ∉ R := fun hr => Set.disjoint_left.mp hdisj hr hx
  have hZsym (x y : Ω) : Z x y = Z y x := by
    simp only [Z, completeCharge, hAsym x y, hYsym x y]
    congr 1
    exact propext (by tauto)
  have hzsym (i j : Fin n) : z i j = z j i := by
    by_cases hij : i = j
    · simp [z, hij]
    · simp [z, hij, Ne.symm hij, hZsym]
  change pairCharge Finset.univ z ≤ 1
  apply pairCharge_le_of_single_root_deletion Finset.univ z (v ⁻¹' R) (v ⁻¹' D) ell
    (fun i => by simp [z]) hzsym (fun i hi => hsep hi)
  · intro i _ j _ hi hj
    by_contra hij
    have hA := (hp i j hij).1 hi hj
    have hvi := hsep (x := v i)
    have he := hclique i j hij
    simp only [completeAdjacency] at he
    split_ifs at he with hDD
    · exact hvi hDD.1 hi
    · rw [hA] at he
      contradiction
  · intro i _ j _ hij hi hj
    change v i ∈ D at hi
    change v j ∈ D at hj
    have hA := (hp i j hij).2.1 hi hj
    simp [z, Z, completeCharge, hij, hi, hj, hA]
  · intro i _ j _ hi hj
    have hij : i ≠ j := fun he => hsep hi (he ▸ hj)
    have hnot : v j ∉ D := fun hjD => hsep hjD hj
    simpa [z, Z, completeCharge, hij, hnot] using (hp i j hij).2.2.2 hi hj
  · intro i _ j _ hij hi hj
    dsimp only [z, Z]
    rw [ite_eq_right hij]
    unfold completeCharge
    split_ifs
    · exact neg_nonpos.mpr hell
    · exact (hp i j hij).2.2.1 (hsep hi) hj
  · intro T _ hsingle
    let e := (T.orderEmbOfFin rfl).toEmbedding
    have he (i : Fin T.card) : e i ∈ T := T.orderEmbOfFin_mem rfl i
    have hn : T.card ≤ n := by simpa using Finset.card_le_univ T
    have hnot {i j : Fin n} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j) :
        ¬(v i ∈ D ∧ v j ∈ D) := fun h => hij (hsingle i hi j hj h.1 h.2)
    have hold : TupleClique A (fun i => v (e i)) := by
      intro i j hij
      have heij : e i ≠ e j := fun h => hij (e.injective h)
      have h := hclique (e i) (e j) heij
      simpa only [completeAdjacency, ite_eq_right (hnot (he i) (he j) heij)] using h
    have ht := hv T.card hn e hold
    rw [tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ T rfl] at ht
    convert ht using 1
    unfold pairCharge crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · simp [z, hij]
    · simp only [z, hij, ite_false, Z, completeCharge]
      rw [ite_eq_right (fun h => hnot hi hj hij ⟨h.1, h.2.1⟩)]

end Erdos1017.FiniteArity

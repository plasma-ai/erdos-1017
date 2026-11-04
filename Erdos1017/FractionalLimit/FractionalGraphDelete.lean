module

public import Erdos1017.FractionalLimit.FractionalGraphEdit
public import Erdos1017.FractionalLimit.Selector

/-!
# Deleting one edge from a fractional graph

Deleting a present edge raises the fractional optimum by at most three
(`value_delete_edge_le`): each original clique weight is transported through an
explicit deletion kernel built from sampling measures on vertex subsets
(`deleteEdgeWeights`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n : ℕ} {Ω : Type*} [Fintype Ω]

/-- Push a finite sampling measure to vertex subsets, omitting edgeless outcomes. -/
def sampleWeights (μ : Ω → ℝ) (F : Ω → Finset (Fin n)) (S : Finset (Fin n)) : ℝ :=
  if 2 ≤ S.card then ∑ ω, if F ω = S then μ ω else 0 else 0

theorem sampleWeights_expectation (μ : Ω → ℝ) (F : Ω → Finset (Fin n))
    (h : Finset (Fin n) → ℝ) (hsmall : ∀ S, S.card < 2 → h S = 0) :
    (∑ S, sampleWeights μ F S * h S) = ∑ ω, μ ω * h (F ω) := by
  have hterm (S : Finset (Fin n)) : sampleWeights μ F S * h S =
      (∑ ω, if F ω = S then μ ω else 0) * h S := by
    by_cases hS : 2 ≤ S.card
    · simp [sampleWeights, hS]
    · simp [sampleWeights, hS, hsmall S (by omega)]
  simp_rw [hterm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul, Finset.sum_ite_eq]

theorem sampleWeights_nonneg (μ : Ω → ℝ) (F : Ω → Finset (Fin n))
    (hμ : ∀ ω, 0 ≤ μ ω) (S : Finset (Fin n)) : 0 ≤ sampleWeights μ F S := by
  unfold sampleWeights
  split_ifs
  · exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp_all)
  · exact le_rfl

theorem sampleWeights_cost_le (μ : Ω → ℝ) (F : Ω → Finset (Fin n))
    (hμ : ∀ ω, 0 ≤ μ ω) : (∑ S, sampleWeights μ F S) ≤ ∑ ω, μ ω := by
  have hterm (S : Finset (Fin n)) : sampleWeights μ F S ≤
      ∑ ω, if F ω = S then μ ω else 0 := by
    unfold sampleWeights
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp_all)
  calc
    (∑ S, sampleWeights μ F S) ≤ ∑ S, ∑ ω, if F ω = S then μ ω else 0 :=
      Finset.sum_le_sum (fun S _ => hterm S)
    _ = ∑ ω, μ ω := by rw [Finset.sum_comm]; simp

theorem sampleWeights_pairLoad (μ : Ω → ℝ) (F : Ω → Finset (Fin n))
    (a b : Fin n) (hab : a ≠ b) : pairLoad (sampleWeights μ F) a b =
      ∑ ω, μ ω * (if a ∈ F ω ∧ b ∈ F ω then 1 else 0) := by
  have h := sampleWeights_expectation μ F
    (fun S => if a ∈ S ∧ b ∈ S then 1 else 0) (by
      intro S hS
      have hnot : ¬(a ∈ S ∧ b ∈ S) := by
        intro h
        have hsub : ({a, b} : Finset (Fin n)) ⊆ S := by
          simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact h
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_pair hab] at hcard
        omega
      simp [hnot])
  simpa [pairLoad, mul_ite] using h

def selectedSet (X : Selector.Selection n) : Finset (Fin n) :=
  Finset.univ.filter fun i => X i = true

theorem selectedSet_pair (X : Selector.Selection n) (a b : Fin n) :
    (if a ∈ selectedSet X ∧ b ∈ selectedSet X then (1 : ℝ) else 0) =
      Selector.bit (X a) * Selector.bit (X b) := by
  simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  cases X a <;> cases X b <;> norm_num [Selector.bit]

/-- Choose one deleted-edge endpoint, and independently retain each other vertex with
probability one half. Vertices outside the original clique are always discarded. -/
def repairSelection (S : Finset (Fin n)) (u v : Fin n) (b : Bool)
    (X : Selector.Selection n) : Selector.Selection n :=
  fun k => if k = u then b else if k = v then !b else X k && decide (k ∈ S)

def repairMass (ω : Bool × Selector.Selection n) : ℝ :=
  2 * Selector.bernoulliWeight (fun _ => 1 / 2) ω.2

def repairKernel (S : Finset (Fin n)) (u v : Fin n) : Finset (Fin n) → ℝ :=
  sampleWeights repairMass (fun ω => selectedSet (repairSelection S u v ω.1 ω.2))

theorem repairMass_nonneg (ω : Bool × Selector.Selection n) : 0 ≤ repairMass ω := by
  apply mul_nonneg (by norm_num)
  exact Selector.bernoulliWeight_nonneg _ (by intro i; norm_num) _

theorem repairMass_total : (∑ ω : Bool × Selector.Selection n, repairMass ω) = 4 := by
  simp only [repairMass, Fintype.sum_prod_type, ← Finset.mul_sum,
    Selector.bernoulli_total]
  norm_num

theorem repairKernel_cost (S : Finset (Fin n)) (u v : Fin n) :
    (∑ T, repairKernel S u v T) ≤ 4 := by
  have h := sampleWeights_cost_le repairMass
    (fun ω => selectedSet (repairSelection S u v ω.1 ω.2)) repairMass_nonneg
  exact h.trans_eq repairMass_total

theorem repairSelection_subset (S : Finset (Fin n)) (u v : Fin n)
    (hu : u ∈ S) (hv : v ∈ S) (b : Bool) (X : Selector.Selection n) :
    selectedSet (repairSelection S u v b X) ⊆ S := by
  intro k hk
  simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  unfold repairSelection at hk
  split_ifs at hk with hku hkv
  · simpa [hku] using hu
  · simpa [hkv] using hv
  · simp at hk
    exact hk.2

theorem repairSelection_not_both (S : Finset (Fin n)) (u v : Fin n)
    (huv : u ≠ v) (b : Bool) (X : Selector.Selection n) :
    ¬(u ∈ selectedSet (repairSelection S u v b X) ∧
      v ∈ selectedSet (repairSelection S u v b X)) := by
  cases b <;> simp [selectedSet, repairSelection, Ne.symm huv]

/-- Every surviving edge of a repaired clique has sampling load exactly one. -/
theorem repair_pair_expectation (S : Finset (Fin n)) (u v a b : Fin n)
    (huv : u ≠ v) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hnot : ¬((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    (∑ ω : Bool × Selector.Selection n, repairMass ω *
      (Selector.bit (repairSelection S u v ω.1 ω.2 a) *
        Selector.bit (repairSelection S u v ω.1 ω.2 b))) = 1 := by
  have hfirst (k : Fin n) :
      (∑ X : Selector.Selection n, Selector.bernoulliWeight (fun _ => 1 / 2) X * Selector.bit (X k)) = 1 / 2 :=
    Selector.bernoulli_first_moment _ k
  have hpair := Selector.bernoulli_pair_moment (fun _ : Fin n => (1 : ℝ) / 2) a b hab
  have htrue : Selector.bit true = 1 := rfl
  have hfalse : Selector.bit false = 0 := rfl
  simp only [repairMass, Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases hau : a = u <;> by_cases hav : a = v <;>
    by_cases hbu : b = u <;> by_cases hbv : b = v <;>
    simp_all only [ne_self_iff_false, not_true_eq_false, and_self, or_self, not_false_eq_true, false_and,
      and_false, false_or, or_false, repairSelection, ite_true, ite_false,
      decide_true, Bool.and_true, Bool.not_true, Bool.not_false,
      mul_one, one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  all_goals
    simp only [mul_assoc, ← Finset.mul_sum, hfirst, hpair]
    norm_num

theorem repairKernel_pairLoad (S : Finset (Fin n)) (u v a b : Fin n)
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (hab : a ≠ b)
    (hnot : ¬((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    pairLoad (repairKernel S u v) a b = if a ∈ S ∧ b ∈ S then 1 else 0 := by
  unfold repairKernel
  rw [sampleWeights_pairLoad _ _ a b hab]
  by_cases hmem : a ∈ S ∧ b ∈ S
  · rw [ite_eq_left hmem]
    simp_rw [selectedSet_pair]
    exact repair_pair_expectation S u v a b huv hab hmem.1 hmem.2 hnot
  · rw [ite_eq_right hmem]
    apply Finset.sum_eq_zero
    intro ω _
    have hsubset := repairSelection_subset S u v hu hv ω.1 ω.2
    have hpair : ¬(a ∈ selectedSet (repairSelection S u v ω.1 ω.2) ∧
        b ∈ selectedSet (repairSelection S u v ω.1 ω.2)) :=
      fun h => hmem ⟨hsubset h.1, hsubset h.2⟩
    simp [hpair]

theorem clique_delete_edge (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u v : Fin n)
    (hS : G.IsClique (S : Set (Fin n))) (hnot : ¬(u ∈ S ∧ v ∈ S)) :
    (G.deleteEdges {s(u, v)}).IsClique (S : Set (Fin n)) := by
  intro a ha b hb hab
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hS ha hb hab, ?_⟩
  intro heq
  have heq' := Sym2.eq_iff.mp (Set.mem_singleton_iff.mp heq)
  rcases heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hnot ⟨ha, hb⟩
  · exact hnot ⟨hb, ha⟩

theorem sampleWeights_supported (G : SimpleGraph (Fin n)) (μ : Ω → ℝ)
    (F : Ω → Finset (Fin n)) (hF : ∀ ω, G.IsClique (F ω : Set (Fin n)))
    (T : Finset (Fin n)) (hT : sampleWeights μ F T ≠ 0) :
    2 ≤ T.card ∧ G.IsClique (T : Set (Fin n)) := by
  by_cases hcard : 2 ≤ T.card
  · refine ⟨hcard, ?_⟩
    by_contra hclique
    apply hT
    rw [sampleWeights, ite_eq_left hcard]
    apply Finset.sum_eq_zero
    intro ω _
    split_ifs with heq
    · exact (hclique (heq ▸ hF ω)).elim
    · rfl
  · exact (hT (by simp [sampleWeights, hcard])).elim

theorem repairKernel_supported (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u v : Fin n)
    (hS : G.IsClique (S : Set (Fin n))) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (T : Finset (Fin n)) (hT : repairKernel S u v T ≠ 0) :
    2 ≤ T.card ∧ (G.deleteEdges {s(u, v)}).IsClique (T : Set (Fin n)) := by
  apply sampleWeights_supported _ repairMass _ _ T hT
  intro ω
  apply clique_delete_edge G _ u v
  · apply SimpleGraph.IsClique.subset _ hS
    exact repairSelection_subset S u v hu hv ω.1 ω.2
  · exact repairSelection_not_both S u v huv ω.1 ω.2

/-- Leave unaffected cliques in place and repair precisely those using the deleted edge. -/
def deletionKernel (S : Finset (Fin n)) (u v : Fin n) (T : Finset (Fin n)) : ℝ :=
  if u ∈ S ∧ v ∈ S then repairKernel S u v T else if T = S then 1 else 0

theorem deletionKernel_nonneg (S : Finset (Fin n)) (u v : Fin n) (T : Finset (Fin n)) :
    0 ≤ deletionKernel S u v T := by
  unfold deletionKernel
  split_ifs
  · exact sampleWeights_nonneg _ _ repairMass_nonneg T
  · norm_num
  · exact le_rfl

theorem deletionKernel_supported (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u v : Fin n)
    (hS : 2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) (huv : u ≠ v)
    (T : Finset (Fin n)) (hT : deletionKernel S u v T ≠ 0) :
    2 ≤ T.card ∧ (G.deleteEdges {s(u, v)}).IsClique (T : Set (Fin n)) := by
  by_cases hcontains : u ∈ S ∧ v ∈ S
  · apply repairKernel_supported G S u v hS.2 hcontains.1 hcontains.2 huv T
    simpa [deletionKernel, hcontains] using hT
  · have hTS : T = S := by
      by_contra h
      exact hT (by simp [deletionKernel, hcontains, h])
    subst T
    exact ⟨hS.1, clique_delete_edge G S u v hS.2 hcontains⟩

theorem deletionKernel_pairLoad (S : Finset (Fin n)) (u v a b : Fin n)
    (huv : u ≠ v) (hab : a ≠ b)
    (hnot : ¬((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    pairLoad (deletionKernel S u v) a b = if a ∈ S ∧ b ∈ S then 1 else 0 := by
  unfold deletionKernel
  by_cases hcontains : u ∈ S ∧ v ∈ S
  · simpa only [deletionKernel, ite_eq_left hcontains] using
      repairKernel_pairLoad S u v a b hcontains.1 hcontains.2 huv hab hnot
  · simpa only [deletionKernel, ite_eq_right hcontains] using pairLoad_single S 1 a b

theorem deletionKernel_cost (S : Finset (Fin n)) (u v : Fin n) :
    (∑ T, deletionKernel S u v T) ≤ 1 + 3 * (if u ∈ S ∧ v ∈ S then 1 else 0) := by
  by_cases hcontains : u ∈ S ∧ v ∈ S
  · simpa only [deletionKernel, ite_eq_left hcontains, mul_one,
      show (1 : ℝ) + 3 = 4 by norm_num] using repairKernel_cost S u v
  · simp [deletionKernel, hcontains]

/-- Transport every old clique weight through its explicit deletion kernel. -/
def deleteEdgeWeights (w : Finset (Fin n) → ℝ) (u v : Fin n) (T : Finset (Fin n)) : ℝ :=
  ∑ S, w S * deletionKernel S u v T

theorem pairLoad_sum_mul (w : Finset (Fin n) → ℝ)
    (K : Finset (Fin n) → Finset (Fin n) → ℝ) (a b : Fin n) :
    pairLoad (fun T => ∑ S, w S * K S T) a b = ∑ S, w S * pairLoad (K S) a b := by
  have hterm (T : Finset (Fin n)) :
      (if a ∈ T ∧ b ∈ T then ∑ S, w S * K S T else 0) =
        ∑ S, w S * (if a ∈ T ∧ b ∈ T then K S T else 0) := by
    split_ifs <;> simp
  unfold pairLoad
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem deleteEdgeWeights_feasible (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G w) (u v : Fin n) (huv : u ≠ v) :
    SubsetFeasible (G.deleteEdges {s(u, v)}) (deleteEdgeWeights w u v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T
    exact Finset.sum_nonneg (fun S _ => mul_nonneg (hw.1 S) (deletionKernel_nonneg S u v T))
  · intro T hT
    obtain ⟨S, _, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    have hparts := mul_ne_zero_iff.mp hS
    exact deletionKernel_supported G S u v (hw.2.1 S hparts.1) huv T hparts.2
  · intro a b hab
    have hbase := (SimpleGraph.deleteEdges_adj.mp hab).1
    have hnot : ¬((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
      intro h
      apply (SimpleGraph.deleteEdges_adj.mp hab).2
      exact Set.mem_singleton_iff.mpr (Sym2.eq_iff.mpr h)
    unfold deleteEdgeWeights
    rw [pairLoad_sum_mul]
    simp_rw [deletionKernel_pairLoad _ u v a b huv hbase.ne hnot]
    simpa [pairLoad, mul_ite] using hw.2.2 a b hbase

theorem deleteEdgeWeights_cost (w : Finset (Fin n) → ℝ) (hw : ∀ S, 0 ≤ w S)
    (u v : Fin n) :
    (∑ T, deleteEdgeWeights w u v T) ≤ (∑ S, w S) + 3 * pairLoad w u v := by
  unfold deleteEdgeWeights
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    (∑ S, w S * ∑ T, deletionKernel S u v T) ≤
        ∑ S, w S * (1 + 3 * (if u ∈ S ∧ v ∈ S then 1 else 0)) :=
      Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (deletionKernel_cost S u v) (hw S))
    _ = _ := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib]
      congr 1
      unfold pairLoad
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring

/-- Deleting a present edge raises the actual fractional optimum by at most three. -/
theorem value_delete_edge_le (G : SimpleGraph (Fin n)) (u v : Fin n) (huv : G.Adj u v) :
    value (G.deleteEdges {s(u, v)}) ≤ value G + 3 := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  have hext := extendWeights_feasible G w hw
  have hnew := deleteEdgeWeights_feasible G (extendWeights G w) hext u v huv.ne
  have hbound := (value_le_subset_cost _ _ hnew).trans
    (deleteEdgeWeights_cost (extendWeights G w) hext.1 u v)
  rw [hext.2.2 u v huv] at hbound
  have hcost : (∑ S, extendWeights G w S) = FinitePrimal.cost w := by
    simpa [FinitePrimal.cost] using extendWeights_sum G w (fun _ => 1)
  rw [hcost, ← value_eq_optimal G w hw hmin] at hbound
  simpa using hbound

end Erdos1017.FractionalGraph

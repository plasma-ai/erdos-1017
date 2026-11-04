module

public import Erdos1017.FractionalLimit.FractionalGraphBlowup

/-!
# Projecting a blowup back to the original graph

This module projects clique weights of a blowup back to the original graph
(`projectionWeights`) and concludes that uniform independent cloning multiplies
the fractional partition number exactly by `t²` (`value_blowup`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n t : ℕ}

def projectSet (S : Finset (Fin (n * t))) : Finset (Fin n) :=
  S.image (fun z => (finProdFinEquiv.symm z).1)

theorem projectSet_clique (G : SimpleGraph (Fin n)) (K : Clique (blowup G t)) :
    G.IsClique (projectSet K.val : Set _) := by
  intro i hi j hj hij
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
  exact K.property.2 hu hv (fun h => hij (congrArg (fun z => (finProdFinEquiv.symm z).1) h))

theorem clone_in_clique_unique (G : SimpleGraph (Fin n)) (K : Clique (blowup G t))
    (i : Fin n) (a b : Fin t)
    (ha : finProdFinEquiv (i, a) ∈ K.val) (hb : finProdFinEquiv (i, b) ∈ K.val) : a = b := by
  by_contra hab
  have hne : finProdFinEquiv (i, a) ≠ finProdFinEquiv (i, b) := by
    intro heq
    exact hab (congrArg Prod.snd (finProdFinEquiv.injective heq))
  have h := K.property.2 ha hb hne
  change G.Adj (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, b))).1 at h
  simp only [Equiv.symm_apply_apply] at h
  exact G.irrefl h

theorem projectSet_mem_iff (S : Finset (Fin (n * t))) (i : Fin n) :
    i ∈ projectSet S ↔ ∃ a : Fin t, finProdFinEquiv (i, a) ∈ S := by
  constructor
  · intro hi
    obtain ⟨u, hu, hi⟩ := Finset.mem_image.mp hi
    obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective u
    simp only [Equiv.symm_apply_apply] at hi
    subst j
    exact ⟨a, hu⟩
  · rintro ⟨a, ha⟩
    exact Finset.mem_image.mpr ⟨finProdFinEquiv (i, a), ha, by simp only [Equiv.symm_apply_apply]⟩

theorem clone_indicator_sum (G : SimpleGraph (Fin n)) (K : Clique (blowup G t))
    (i : Fin n) :
    (∑ a : Fin t, if finProdFinEquiv (i, a) ∈ K.val then (1 : ℝ) else 0) =
      if i ∈ projectSet K.val then 1 else 0 := by
  by_cases hi : i ∈ projectSet K.val
  · obtain ⟨a, ha⟩ := (projectSet_mem_iff K.val i).mp hi
    rw [Finset.sum_eq_single a]
    · simp [ha, hi]
    · intro b _ hba
      have hb : finProdFinEquiv (i, b) ∉ K.val := by
        intro hb
        exact hba (clone_in_clique_unique G K i b a hb ha)
      simp [hb]
    · simp
  · have hnone (a : Fin t) : finProdFinEquiv (i, a) ∉ K.val := by
      intro ha
      exact hi ((projectSet_mem_iff K.val i).mpr ⟨a, ha⟩)
    simp [hnone, hi]

theorem clone_pair_indicator_sum (G : SimpleGraph (Fin n)) (K : Clique (blowup G t))
    (i j : Fin n) :
    (∑ a : Fin t, ∑ b : Fin t,
      if finProdFinEquiv (i, a) ∈ K.val ∧ finProdFinEquiv (j, b) ∈ K.val
        then (1 : ℝ) else 0) =
      if i ∈ projectSet K.val ∧ j ∈ projectSet K.val then 1 else 0 := by
  have hterm (a b : Fin t) :
      (if finProdFinEquiv (i, a) ∈ K.val ∧ finProdFinEquiv (j, b) ∈ K.val
        then (1 : ℝ) else 0) =
      (if finProdFinEquiv (i, a) ∈ K.val then (1 : ℝ) else 0) *
        (if finProdFinEquiv (j, b) ∈ K.val then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, clone_indicator_sum]
  split_ifs <;> simp_all

def projectionWeights (G : SimpleGraph (Fin n)) (w : Clique (blowup G t) → ℝ) :
    Finset (Fin n) → ℝ :=
  sampleWeights (fun K => w K / (t : ℝ) ^ 2) (fun K => projectSet K.val)

theorem projectionWeights_cost_le (G : SimpleGraph (Fin n))
    (w : Clique (blowup G t) → ℝ) (hw : ∀ K, 0 ≤ w K) :
    (∑ S, projectionWeights G w S) ≤ FinitePrimal.cost w / (t : ℝ) ^ 2 := by
  apply (sampleWeights_cost_le _ _ (fun K => div_nonneg (hw K) (sq_nonneg _))).trans_eq
  simp only [FinitePrimal.cost, Finset.sum_div]

theorem projectionWeights_feasible (G : SimpleGraph (Fin n))
    (w : Clique (blowup G t) → ℝ) (hw : Feasible (blowup G t) w) (ht : 0 < t) :
    SubsetFeasible G (projectionWeights G w) := by
  refine ⟨sampleWeights_nonneg _ _ (fun K => div_nonneg (hw.1 K) (sq_nonneg _)), ?_, ?_⟩
  · exact sampleWeights_supported _ _ _ (projectSet_clique G)
  · intro i j hij
    rw [projectionWeights, sampleWeights_pairLoad _ _ _ _ hij.ne]
    have hpair (a b : Fin t) :
        (∑ K : Clique (blowup G t), w K *
          (if finProdFinEquiv (i, a) ∈ K.val ∧ finProdFinEquiv (j, b) ∈ K.val
            then (1 : ℝ) else 0)) = 1 := by
      have hab : (blowup G t).Adj (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) := by
        change G.Adj (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
          (finProdFinEquiv.symm (finProdFinEquiv (j, b))).1
        simpa only [Equiv.symm_apply_apply] using hij
      let e : Edge (blowup G t) := ⟨s(finProdFinEquiv (i, a), finProdFinEquiv (j, b)),
        (SimpleGraph.mem_edgeSet _).mpr hab⟩
      have h := (moment_apply _ w e).symm.trans (congrFun hw.2 e)
      simpa [column, e, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] using h
    simp_rw [← clone_pair_indicator_sum G, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Eq.trans ?_ (show (∑ _a : Fin t, ∑ _b : Fin t, (1 : ℝ) / (t : ℝ) ^ 2) = 1 by
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
      simp
      field_simp)
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, hpair]

theorem value_le_blowup_div (G : SimpleGraph (Fin n)) (ht : 0 < t) :
    value G ≤ value (blowup G t) / (t : ℝ) ^ 2 := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal (blowup G t)
  rw [value_eq_optimal _ w hw hmin]
  exact (value_le_subset_cost _ _ (projectionWeights_feasible G w hw ht)).trans
    (projectionWeights_cost_le G w hw.1)

/-- Uniform independent cloning multiplies the fractional partition number by `t²`. -/
theorem value_blowup (G : SimpleGraph (Fin n)) (ht : 0 < t) :
    value (blowup G t) = (t : ℝ) ^ 2 * value G := by
  apply le_antisymm (value_blowup_le G ht)
  have ht' : 0 < (t : ℝ) ^ 2 := pow_pos (by exact_mod_cast ht) _
  have h := (le_div_iff₀ ht').mp (value_le_blowup_div G ht)
  simpa [mul_comm] using h

end Erdos1017.FractionalGraph

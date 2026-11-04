module

public import Erdos1017.Models.FractionalBoundedDual

/-!
# The capped fractional clique LP of a finite graph

Cliques of orders between two and the cap carry weights at most one under the
unit edge-load constraint, the optimum is attained, and the capped dual
constraints are imposed only on cliques of order at most `N`, with an optimal
dual (`exists_optimal_dual`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalCappedGraph

open scoped BigOperators
open FractionalGraph (Edge)

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-- Actual graph cliques of orders between two and the imposed cap. -/
def Clique (G : SimpleGraph (Fin n)) (N : ℕ) :=
  {K : FractionalGraph.Clique G // K.val.card ≤ N}

instance (G : SimpleGraph (Fin n)) (N : ℕ) : Fintype (Clique G N) := by
  unfold Clique
  exact Fintype.ofFinite _

instance (G : SimpleGraph (Fin n)) (N : ℕ) : DecidableEq (Clique G N) :=
  inferInstanceAs (DecidableEq (Subtype _))

def column (G : SimpleGraph (Fin n)) (N : ℕ) (K : Clique G N) : Edge G → ℝ :=
  FractionalGraph.column G K.val

def Feasible (G : SimpleGraph (Fin n)) (N : ℕ) (w : Clique G N → ℝ) : Prop :=
  FinitePrimal.Feasible (column G N) (fun _ => 1) w

def value (G : SimpleGraph (Fin n)) (N : ℕ) : ℝ :=
  sInf {c | ∃ w, Feasible G N w ∧ FinitePrimal.cost w = c}

def edgeClique (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) (e : Edge G) : Clique G N :=
  ⟨FractionalGraph.edgeClique G e, by
    change e.val.toFinset.card ≤ N
    rw [FractionalGraph.edge_toFinset_card]
    exact hN⟩

theorem column_edgeClique (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) (e : Edge G) :
    column G N (edgeClique G N hN e) = Pi.single e 1 :=
  FractionalGraph.column_edgeClique G e

/-- A uniform small weight on every clique, corrected by edge columns. -/
def positiveWeight (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) (K : Clique G N) : ℝ :=
  let ε : ℝ := 1 / (2 * (Fintype.card (Clique G N) + 1))
  ε + ∑ e : Edge G,
    (if K = edgeClique G N hN e then
      1 - ε * ∑ L : Clique G N, column G N L e else 0)

theorem column_le_one (G : SimpleGraph (Fin n)) (N : ℕ) (K : Clique G N) (e : Edge G) :
    column G N K e ≤ 1 := by
  exact FractionalGraph.column_le_one G K.val e

theorem positiveWeight_pos (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) (K : Clique G N) :
    0 < positiveWeight G N hN K := by
  let ε : ℝ := 1 / (2 * (Fintype.card (Clique G N) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsum (e : Edge G) : 0 ≤ 1 - ε * ∑ L : Clique G N, column G N L e := by
    have hcount : (∑ L : Clique G N, column G N L e) ≤ Fintype.card (Clique G N) := by
      calc
        (∑ L : Clique G N, column G N L e) ≤ ∑ _ : Clique G N, (1 : ℝ) :=
          Finset.sum_le_sum (fun L _ => column_le_one G N L e)
        _ = Fintype.card (Clique G N) := by simp
    have hcast : (0 : ℝ) ≤ Fintype.card (Clique G N) := Nat.cast_nonneg _
    have hden : (0 : ℝ) < 2 * (Fintype.card (Clique G N) + 1) := by positivity
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hden).mpr
    nlinarith
  unfold positiveWeight
  apply add_pos_of_pos_of_nonneg hε
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact hsum e
  · exact le_rfl

theorem positiveWeight_moment (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) :
    FinitePrimal.moment (column G N) (positiveWeight G N hN) = (fun _ => 1) := by
  classical
  funext q
  simp only [FinitePrimal.moment, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let ε : ℝ := 1 / (2 * (Fintype.card (Clique G N) + 1))
  change (∑ K : Clique G N, (ε + ∑ e : Edge G,
    if K = edgeClique G N hN e then 1 - ε * ∑ L : Clique G N, column G N L e else 0) *
      column G N K q) = 1
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (e : Edge G) :
      (∑ K : Clique G N,
        (if K = edgeClique G N hN e then
          1 - ε * ∑ L : Clique G N, column G N L e else 0) * column G N K q) =
        (1 - ε * ∑ L : Clique G N, column G N L e) * column G N (edgeClique G N hN e) q := by
    simp
  simp_rw [hterm, column_edgeClique]
  simp only [Pi.single_apply]
  have hsum : (∑ e : Edge G,
      (1 - ε * ∑ L : Clique G N, column G N L e) *
        (if q = e then (1 : ℝ) else 0)) =
      1 - ε * ∑ L : Clique G N, column G N L q := by
    rw [Finset.sum_eq_single q]
    · simp
    · intro e _ he
      simp [Ne.symm he]
    · simp
  rw [hsum, ← Finset.mul_sum]
  ring

theorem columns_span (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) :
    Submodule.span ℝ (Set.range (column G N)) = ⊤ := by
  apply top_unique
  intro v _
  have hbasis (e : Edge G) :
      Pi.single e (1 : ℝ) ∈ Submodule.span ℝ (Set.range (column G N)) := by
    rw [← column_edgeClique G N hN e]
    exact Submodule.subset_span ⟨edgeClique G N hN e, rfl⟩
  have hv := (Pi.basisFun ℝ (Edge G)).sum_repr v
  rw [← hv]
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  simpa only [Pi.basisFun_apply] using hbasis e

/-- The restricted finite LP has attained primal and signed-dual optima. -/
theorem exists_linear_primal_dual (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) :
    ∃ w : Clique G N → ℝ, Feasible G N w ∧
      ∃ y : (Edge G → ℝ) →L[ℝ] ℝ,
        (∀ K, y (column G N K) ≤ 1) ∧
        y (fun _ => 1) = FinitePrimal.cost w ∧
        ∀ v, Feasible G N v → FinitePrimal.cost w ≤ FinitePrimal.cost v :=
  FiniteLinearProgram.exists_primal_dual (column G N) (fun _ => 1)
    (positiveWeight G N hN) (positiveWeight_pos G N hN)
    (positiveWeight_moment G N hN) (columns_span G N hN)

theorem exists_optimal (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) :
    ∃ w, Feasible G N w ∧ ∀ v, Feasible G N v → FinitePrimal.cost w ≤ FinitePrimal.cost v := by
  obtain ⟨w, hw, _, _, _, hmin⟩ := exists_linear_primal_dual G N hN
  exact ⟨w, hw, hmin⟩

theorem value_eq_optimal (G : SimpleGraph (Fin n)) (N : ℕ) (w : Clique G N → ℝ)
    (hw : Feasible G N w)
    (hmin : ∀ v, Feasible G N v → FinitePrimal.cost w ≤ FinitePrimal.cost v) :
    value G N = FinitePrimal.cost w := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro c ⟨v, hv, rfl⟩
      exact Finset.sum_nonneg (fun K _ => hv.1 K)
    · exact ⟨w, hw, rfl⟩
  · refine le_csInf (s := {c | ∃ v, Feasible G N v ∧ FinitePrimal.cost v = c})
      ⟨FinitePrimal.cost w, w, hw, rfl⟩ ?_
    rintro c ⟨v, hv, rfl⟩
    exact hmin v hv

theorem value_nonneg (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) : 0 ≤ value G N := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G N hN
  rw [value_eq_optimal G N w hw hmin]
  exact Finset.sum_nonneg (fun K _ => hw.1 K)

theorem moment_apply (G : SimpleGraph (Fin n)) (N : ℕ) (w : Clique G N → ℝ) (e : Edge G) :
    FinitePrimal.moment (column G N) w e = ∑ K, w K * column G N K e := by
  simp only [FinitePrimal.moment, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Every actual capped clique weight is at most one, by any edge of that
clique and the exact unit edge-load constraint. -/
theorem weight_mem_Icc (G : SimpleGraph (Fin n)) (N : ℕ) (w : Clique G N → ℝ)
    (hw : Feasible G N w) (K : Clique G N) : w K ∈ Set.Icc 0 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := (Finset.one_lt_card (s := K.val.val)).mp
    (by have := K.val.property.1; omega)
  have hadj : G.Adj u v := K.val.property.2 hu hv huv
  let e : Edge G := ⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr hadj⟩
  have hcol : column G N K e = 1 := by
    simp [column, FractionalGraph.column, e, Sym2.toFinset_mk_eq,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, hu, hv]
  have hnonneg (L : Clique G N) : 0 ≤ column G N L e := by
    unfold column FractionalGraph.column
    split_ifs <;> norm_num
  have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun L => w L * column G N L e)
    (fun L _ => mul_nonneg (hw.1 L) (hnonneg L)) (Finset.mem_univ K)
  have hmoment : (∑ L, w L * column G N L e) = 1 :=
    (moment_apply G N w e).symm.trans (congrFun hw.2 e)
  rw [hcol, mul_one, hmoment] at hsum
  exact ⟨hw.1 K, hsum⟩

end Erdos1017.FractionalCappedGraph

namespace Erdos1017.WeightedGraph

variable {n : ℕ}

/-- Signed dual constraints are imposed only on actual cliques of order at
most N; all entries still vanish off the graph and are symmetric. -/
def CappedDualFeasible (G : SimpleGraph (Fin n)) (N : ℕ) (y : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, y i j = y j i) ∧ (∀ i j, ¬G.Adj i j → y i j = 0) ∧
    ∀ S : Finset (Fin n), S.card ≤ N → G.IsClique (S : Set (Fin n)) → charge y S ≤ 1

end Erdos1017.WeightedGraph

namespace Erdos1017.FractionalCappedGraph

open FractionalGraph (Edge)

variable {n : ℕ}

/-- The actual supporting functional gives a matrix satisfying precisely
the capped clique constraints, including the vacuous small-set tests. -/
theorem functionalMatrix_cappedDualFeasible (G : SimpleGraph (Fin n)) (N : ℕ)
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (hy : ∀ K, y (column G N K) ≤ 1) :
    WeightedGraph.CappedDualFeasible G N (FractionalGraph.functionalMatrix G y) := by
  refine ⟨FractionalGraph.functionalMatrix_symm G y, FractionalGraph.functionalMatrix_nonedge G y, ?_⟩
  intro S hSN hS
  by_cases hcard : 2 ≤ S.card
  · let K : Clique G N := ⟨⟨S, hcard, hS⟩, hSN⟩
    exact (FractionalGraph.functionalMatrix_charge G y K.val).trans_le (hy K)
  · rw [FractionalGraph.functionalMatrix_charge_small G y S (by omega)]
    norm_num

theorem exists_optimal_dual (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) :
    ∃ y : Fin n → Fin n → ℝ, WeightedGraph.CappedDualFeasible G N y ∧
      WeightedGraph.objective (fun _ => 1) y = value G N := by
  obtain ⟨w, hw, y, hy, hcost, hmin⟩ := exists_linear_primal_dual G N hN
  refine ⟨FractionalGraph.functionalMatrix G y, functionalMatrix_cappedDualFeasible G N y hy, ?_⟩
  rw [FractionalGraph.functionalMatrix_objective, hcost, value_eq_optimal G N w hw hmin]

end Erdos1017.FractionalCappedGraph

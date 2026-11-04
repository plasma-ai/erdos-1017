module

public import Erdos1017.Models.FractionalDualBounds
public import Erdos1017.Models.FiniteLinearProgram
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bounded fractional duals of finite graphs

Every finite graph has an attained fractional dual with bounded signed edge
charges (`exists_bounded_dual`), built from a functional matrix that is
symmetric, vanishes off edges and is dual feasible.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-- The two-vertex clique corresponding to an actual graph edge. -/
def edgeClique (G : SimpleGraph (Fin n)) (e : Edge G) : Clique G := by
  rcases e with ⟨e, he⟩
  refine ⟨e.toFinset, ?_⟩
  induction e using Sym2.ind with
  | h u v =>
    have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp he
    rw [Sym2.toFinset_mk_eq, Finset.card_pair huv.ne, Finset.coe_pair]
    exact ⟨le_rfl, SimpleGraph.isClique_pair.mpr (fun _ => huv)⟩

theorem edge_toFinset_card (G : SimpleGraph (Fin n)) (e : Edge G) :
    e.val.toFinset.card = 2 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
    have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp he
    simp [Sym2.toFinset_mk_eq, Finset.card_pair huv.ne]

theorem column_edgeClique (G : SimpleGraph (Fin n)) (e : Edge G) :
    column G (edgeClique G e) = Pi.single e 1 := by
  funext q
  by_cases h : q = e
  · subst q
    have hsub : e.val.toFinset ⊆ (edgeClique G e).val := Finset.Subset.rfl
    simp [column, hsub]
  · have hnot : ¬q.val.toFinset ⊆ e.val.toFinset := by
      intro hsub
      have heq : q.val.toFinset = e.val.toFinset :=
        Finset.eq_of_subset_of_card_le hsub (by
          rw [edge_toFinset_card G q, edge_toFinset_card G e])
      rcases q with ⟨q, hq⟩
      induction q using Sym2.ind with
      | h u v =>
        have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp hq
        have hu : u ∈ e.val := by
          rw [← Sym2.mem_toFinset, ← heq]
          simp
        have hv : v ∈ e.val := by
          rw [← Sym2.mem_toFinset, ← heq]
          simp
        exact h (Subtype.ext ((Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩).symm)
    have hsub : ¬q.val.toFinset ⊆ (edgeClique G e).val := hnot
    simp [column, hsub, h]

/-- A uniform small weight on every clique, corrected by edge columns. -/
def positiveWeight (G : SimpleGraph (Fin n)) (K : Clique G) : ℝ :=
  let ε : ℝ := 1 / (2 * (Fintype.card (Clique G) + 1))
  ε + ∑ e : Edge G,
    (if K = edgeClique G e then
      1 - ε * ∑ L : Clique G, column G L e else 0)

theorem column_le_one (G : SimpleGraph (Fin n)) (K : Clique G) (e : Edge G) :
    column G K e ≤ 1 := by
  unfold column
  split_ifs <;> norm_num

theorem positiveWeight_pos (G : SimpleGraph (Fin n)) (K : Clique G) :
    0 < positiveWeight G K := by
  let ε : ℝ := 1 / (2 * (Fintype.card (Clique G) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsum (e : Edge G) : 0 ≤ 1 - ε * ∑ L : Clique G, column G L e := by
    have hcount : (∑ L : Clique G, column G L e) ≤ Fintype.card (Clique G) := by
      calc
        (∑ L : Clique G, column G L e) ≤ ∑ _ : Clique G, (1 : ℝ) :=
          Finset.sum_le_sum (fun L _ => column_le_one G L e)
        _ = Fintype.card (Clique G) := by simp
    have hcast : (0 : ℝ) ≤ Fintype.card (Clique G) := Nat.cast_nonneg _
    have hden : (0 : ℝ) < 2 * (Fintype.card (Clique G) + 1) := by positivity
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

theorem positiveWeight_moment (G : SimpleGraph (Fin n)) :
    FinitePrimal.moment (column G) (positiveWeight G) = (fun _ => 1) := by
  classical
  funext q
  simp only [FinitePrimal.moment, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let ε : ℝ := 1 / (2 * (Fintype.card (Clique G) + 1))
  change (∑ K : Clique G, (ε + ∑ e : Edge G,
    if K = edgeClique G e then 1 - ε * ∑ L : Clique G, column G L e else 0) *
      column G K q) = 1
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (e : Edge G) :
      (∑ K : Clique G,
        (if K = edgeClique G e then
          1 - ε * ∑ L : Clique G, column G L e else 0) * column G K q) =
        (1 - ε * ∑ L : Clique G, column G L e) * column G (edgeClique G e) q := by
    simp
  simp_rw [hterm, column_edgeClique]
  simp only [Pi.single_apply]
  have hsum : (∑ e : Edge G,
      (1 - ε * ∑ L : Clique G, column G L e) *
        (if q = e then (1 : ℝ) else 0)) =
      1 - ε * ∑ L : Clique G, column G L q := by
    rw [Finset.sum_eq_single q]
    · simp
    · intro e _ he
      simp [Ne.symm he]
    · simp
  rw [hsum, ← Finset.mul_sum]
  ring

theorem columns_span (G : SimpleGraph (Fin n)) :
    Submodule.span ℝ (Set.range (column G)) = ⊤ := by
  apply top_unique
  intro v _
  have hbasis (e : Edge G) :
      Pi.single e (1 : ℝ) ∈ Submodule.span ℝ (Set.range (column G)) := by
    rw [← column_edgeClique G e]
    exact Submodule.subset_span ⟨edgeClique G e, rfl⟩
  have hv := (Pi.basisFun ℝ (Edge G)).sum_repr v
  rw [← hv]
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  simpa only [Pi.basisFun_apply] using hbasis e

/-- The finite clique LP has an attained supporting functional. -/
theorem exists_linear_primal_dual (G : SimpleGraph (Fin n)) :
    ∃ w : Clique G → ℝ, Feasible G w ∧
      ∃ y : (Edge G → ℝ) →L[ℝ] ℝ,
        (∀ K, y (column G K) ≤ 1) ∧
        y (fun _ => 1) = FinitePrimal.cost w ∧
        ∀ v, Feasible G v → FinitePrimal.cost w ≤ FinitePrimal.cost v := by
  exact FiniteLinearProgram.exists_primal_dual (column G) (fun _ => 1)
    (positiveWeight G) (positiveWeight_pos G) (positiveWeight_moment G) (columns_span G)

theorem ordered_edge_sum (G : SimpleGraph (Fin n)) (f : Edge G → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      if h : G.Adj i j then f ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h⟩ else 0) =
      2 * ∑ e : Edge G, f e := by
  classical
  let edgeOfDart (d : G.Dart) : Edge G := ⟨d.edge, d.edge_mem⟩
  have hfiber (e : Edge G) :
      (∑ d : G.Dart with edgeOfDart d = e, f e) = 2 * f e := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun d : G.Dart => edgeOfDart d = e).card = 2 := by
      convert G.dart_edge_fiber_card e.val e.property using 1
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => congrArg Subtype.val h
      · exact fun h => Subtype.ext h
    simp [hcard]
  have hgroup : (∑ d : G.Dart, f (edgeOfDart d)) = 2 * ∑ e : Edge G, f e := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (g := edgeOfDart) (by simp)
      (f := fun d => f (edgeOfDart d))]
    have hterm (e : Edge G) :
        (∑ d : G.Dart with edgeOfDart d = e, f (edgeOfDart d)) = 2 * f e := by
      calc
        _ = ∑ d : G.Dart with edgeOfDart d = e, f e := by
          apply Finset.sum_congr rfl
          intro d hd
          exact congrArg f (Finset.mem_filter.mp hd).2
        _ = 2 * f e := hfiber e
    simp_rw [hterm]
    rw [Finset.mul_sum]
  rw [← hgroup]
  let F (p : Fin n × Fin n) : ℝ :=
    if h : G.Adj p.1 p.2 then f ⟨s(p.1, p.2), (SimpleGraph.mem_edgeSet G).mpr h⟩ else 0
  let dartEquiv : G.Dart ≃ {p : Fin n × Fin n // G.Adj p.1 p.2} :=
    { toFun := fun d => ⟨d.toProd, d.adj⟩
      invFun := fun p => ⟨p.val, p.property⟩
      left_inv := by intro d; cases d; rfl
      right_inv := by intro p; cases p; rfl }
  have hsub := Finset.sum_subtype (p := fun p : Fin n × Fin n => G.Adj p.1 p.2)
    (F := inferInstance) (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2))
    (by simp) F
  rw [Finset.sum_filter] at hsub
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      if h : G.Adj i j then f ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h⟩ else 0) =
        ∑ p : Fin n × Fin n, F p := by
      rw [Fintype.sum_prod_type]
    (∑ p : Fin n × Fin n, F p) = ∑ d : G.Dart, F d.toProd := by
      have hfilter : (∑ p : Fin n × Fin n, F p) =
          ∑ p : Fin n × Fin n, if G.Adj p.1 p.2 then F p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases h : G.Adj p.1 p.2 <;> simp [F, h]
      rw [hfilter, hsub]
      rw [← Equiv.sum_comp dartEquiv]
      rfl
    _ = ∑ d : G.Dart, f (edgeOfDart d) := by
      apply Finset.sum_congr rfl
      intro d _
      simp [F, edgeOfDart, SimpleGraph.Dart.edge, d.adj]

/-- The coefficient of each unordered edge under the supporting functional. -/
def functionalMatrix (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (i j : Fin n) : ℝ :=
  if h : G.Adj i j then
    y (Pi.single (⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h⟩ : Edge G) 1) else 0

theorem functionalMatrix_symm (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (i j : Fin n) :
    functionalMatrix G y i j = functionalMatrix G y j i := by
  by_cases h : G.Adj i j
  · have h' : G.Adj j i := h.symm
    have heq : (⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h⟩ : Edge G) =
        (⟨s(j, i), (SimpleGraph.mem_edgeSet G).mpr h'⟩ : Edge G) :=
      Subtype.ext Sym2.eq_swap
    simp only [functionalMatrix, dite_eq_left h, dite_eq_left h']
    rw [heq]
  · have h' : ¬G.Adj j i := fun hji => h hji.symm
    simp [functionalMatrix, h, h']

theorem functionalMatrix_nonedge (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (i j : Fin n) (h : ¬G.Adj i j) :
    functionalMatrix G y i j = 0 := by
  simp [functionalMatrix, h]

theorem functional_eq_edge_sum (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (v : Edge G → ℝ) :
    y v = ∑ e : Edge G, v e * y (Pi.single e 1) := by
  have hv := (Pi.basisFun ℝ (Edge G)).sum_repr v
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_apply, Pi.basisFun_repr]

theorem functionalMatrix_objective (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) :
    WeightedGraph.objective (fun _ => 1) (functionalMatrix G y) = y (fun _ => 1) := by
  have hsum := ordered_edge_sum G (fun e => y (Pi.single e 1))
  simp only [WeightedGraph.objective, mul_one] at *
  change (∑ i : Fin n, ∑ j : Fin n, functionalMatrix G y i j) =
    2 * ∑ e : Edge G, y (Pi.single e 1) at hsum
  rw [hsum, functional_eq_edge_sum G y (fun _ => 1)]
  simp

theorem functionalMatrix_charge (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (K : Clique G) :
    WeightedGraph.charge (functionalMatrix G y) K.val = y (column G K) := by
  let f : Edge G → ℝ := fun e =>
    if e.val.toFinset ⊆ K.val then y (Pi.single e 1) else 0
  have hterm (i j : Fin n) :
      (if i ∈ K.val ∧ j ∈ K.val then functionalMatrix G y i j else 0) =
        if h : G.Adj i j then f ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h⟩ else 0 := by
    by_cases h : G.Adj i j
    · have hsubset : s(i, j).toFinset ⊆ K.val ↔ i ∈ K.val ∧ j ∈ K.val := by
        simp [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff]
      simp only [functionalMatrix, f, dite_eq_left h]
      by_cases hmem : i ∈ K.val ∧ j ∈ K.val
      · simp [hmem, hsubset]
      · simp [hmem, hsubset]
    · simp [functionalMatrix, h]
  calc
    WeightedGraph.charge (functionalMatrix G y) K.val =
        (∑ i : Fin n, ∑ j : Fin n,
          if h : G.Adj i j then f ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h⟩ else 0) / 2 := by
      unfold WeightedGraph.charge
      simp_rw [hterm]
    _ = ∑ e : Edge G, f e := by rw [ordered_edge_sum]; ring
    _ = y (column G K) := by
      rw [functional_eq_edge_sum]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : e.val.toFinset ⊆ K.val <;> simp [f, column, h]

theorem functionalMatrix_charge_small (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (S : Finset (Fin n)) (hS : S.card < 2) :
    WeightedGraph.charge (functionalMatrix G y) S = 0 := by
  unfold WeightedGraph.charge
  have hzero : (∑ i : Fin n, ∑ j : Fin n,
      if i ∈ S ∧ j ∈ S then functionalMatrix G y i j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · have hij : i = j := by
        by_contra hne
        have hsub : ({i, j} : Finset (Fin n)) ⊆ S := by
          simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at hcard
        omega
      subst j
      have hno : ¬G.Adj i i := fun h => G.irrefl h
      simp [hi, functionalMatrix_nonedge G y i i hno]
    · simp [hj]
    · simp [hi]
    · simp [hi]
  rw [hzero]
  norm_num

theorem functionalMatrix_dualFeasible (G : SimpleGraph (Fin n))
    (y : (Edge G → ℝ) →L[ℝ] ℝ) (hy : ∀ K, y (column G K) ≤ 1) :
    WeightedGraph.DualFeasible G (functionalMatrix G y) := by
  refine ⟨functionalMatrix_symm G y, functionalMatrix_nonedge G y, ?_⟩
  intro S hS
  by_cases hcard : 2 ≤ S.card
  · let K : Clique G := ⟨S, hcard, hS⟩
    simpa only [K] using (functionalMatrix_charge G y K).trans_le (hy K)
  · rw [functionalMatrix_charge_small G y S (by omega)]
    norm_num

/-- Every finite graph has an attained fractional dual with bounded signed edge charges. -/
theorem exists_bounded_dual (G : SimpleGraph (Fin n)) :
    ∃ y : Fin n → Fin n → ℝ,
      WeightedGraph.DualFeasible G y ∧
      (∀ i j, y i j ∈ Set.Icc (-3 : ℝ) 1) ∧
      WeightedGraph.objective (fun _ => 1) y = value G := by
  obtain ⟨w, hw, y, hy, hvalue, hmin⟩ := exists_linear_primal_dual G
  let z := functionalMatrix G y
  have hz : WeightedGraph.DualFeasible G z := functionalMatrix_dualFeasible G y hy
  have hopt : WeightedGraph.objective (fun _ => 1) z = value G := by
    rw [functionalMatrix_objective, hvalue, value_eq_optimal G w hw hmin]
  exact ⟨z, hz, fun i j => WeightedGraph.optimal_dual_mem_Icc G z hz hopt i j, hopt⟩

end Erdos1017.FractionalGraph

module

public import Erdos1017.IntegerTransfer.NormalizedThinningRoles

/-!
# Edge charts of transversal assignments

A role permutation moves any ordered pair into the first two positions
(`pairRoleEquiv`), each increasing edge coordinate is recovered from its chart,
and chart transport bounds nonnegative edge sums without counting an edge twice.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- A role permutation putting any prescribed ordered pair into the first two
positions. It fixes the assignment values within every part. -/
def pairRoleEquiv (i j : Fin (2 + u)) : Equiv.Perm (Fin (2 + u)) :=
  let a := Fin.castAdd u (0 : Fin 2)
  let b := Fin.castAdd u (1 : Fin 2)
  (Equiv.swap a i).trans (Equiv.swap (Equiv.swap a i b) j)

/-- The second designated role always maps to the requested endpoint. -/
theorem pairRoleEquiv_second (i j : Fin (2 + u)) :
    pairRoleEquiv i j (Fin.castAdd u 1) = j := by simp [pairRoleEquiv]

/-- Distinct requested endpoints ensure that the first designated role is preserved. -/
theorem pairRoleEquiv_first (i j : Fin (2 + u)) (hij : i ≠ j) :
    pairRoleEquiv i j (Fin.castAdd u 0) = i := by
  let a := Fin.castAdd u (0 : Fin 2)
  let b := Fin.castAdd u (1 : Fin 2)
  have hab : a ≠ b := by intro h; have hv := congrArg Fin.val h; change (0 : ℕ) = 1 at hv; omega
  have hne : i ≠ Equiv.swap a i b := by
    have h : Equiv.swap a i a ≠ Equiv.swap a i b := (Equiv.swap a i).injective.ne hab
    simpa only [Equiv.swap_apply_left] using h
  simp only [pairRoleEquiv, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne hne hij

/-- Endpoint values viewed as a two-role base assignment. -/
def edgeBase (v : Coordinate (2 + u) A) : Fin 2 → A :=
  fun i => if i = 0 then v.1.2 else v.2.2

/-- A chart consists of a role permutation and a base assignment. -/
def edgeChart (v : Coordinate (2 + u) A) :
    Equiv.Perm (Fin (2 + u)) × (Fin 2 → A) :=
  (pairRoleEquiv v.1.1 v.2.1, edgeBase v)

/-- The original graph-edge coordinate represented by a chart. -/
def chartEdge (c : Equiv.Perm (Fin (2 + u)) × (Fin 2 → A)) : Coordinate (2 + u) A :=
  roleCoordinateEquiv c.1 (baseEdge c.2)

omit [Fintype A] [DecidableEq A] in
/-- Every increasing edge coordinate is recovered exactly from its chart. -/
theorem chartEdge_edgeChart (v : Coordinate (2 + u) A) (hv : v.1.1 < v.2.1) :
    chartEdge (edgeChart v) = v := by
  change roleCoordinate (pairRoleEquiv v.1.1 v.2.1) (baseEdge (edgeBase v)) = v
  rw [roleCoordinate_of_lt _ _ (by change (0 : ℕ) < 1; omega)]
  simp [baseEdge, pairRoleEquiv_first _ _ hv.ne, pairRoleEquiv_second, hv, edgeBase]

/-- Finite chart transport bounds any nonnegative edge sum by the full chart
sum. This permits dependent events to be combined without counting an edge twice. -/
theorem sum_chart_le (U : Finset (Coordinate (2 + u) A))
    (hU : ∀ v ∈ U, v.1.1 < v.2.1)
    (f : Equiv.Perm (Fin (2 + u)) → (Fin 2 → A) → ℝ) (hf : ∀ σ x, 0 ≤ f σ x) :
    (∑ v ∈ U, f (edgeChart v).1 (edgeChart v).2) ≤
      ∑ σ : Equiv.Perm (Fin (2 + u)), ∑ x : Fin 2 → A, f σ x := by
  have hinj : Set.InjOn (edgeChart (u := u) (A := A)) U := by
    intro v hv w hw h
    have heq := congrArg chartEdge h
    simpa only [chartEdge_edgeChart v (hU v hv), chartEdge_edgeChart w (hU w hw)] using heq
  have hprod : (∑ c : Equiv.Perm (Fin (2 + u)) × (Fin 2 → A), f c.1 c.2) =
      ∑ σ : Equiv.Perm (Fin (2 + u)), ∑ x : Fin 2 → A, f σ x :=
    Fintype.sum_prod_type (fun c => f c.1 c.2)
  rw [← hprod]
  rw [← Finset.sum_image (f := fun c => f c.1 c.2) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => hf c.1 c.2)

omit [Fintype A] [DecidableEq A] in
/-- Base retention for graph edges is exactly the one sampled edge bit. -/
theorem baseRetained_two_iff (x : Fin 2 → A) (X : Coordinate (2 + u) A → Bool) :
    BaseRetained x X ↔ X (baseEdge x) = true := by
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact h | (simp only [Fin.lt_def] at hij; omega)

omit [DecidableEq A] in
/-- Each selected actual graph edge has a retained base in its chart. -/
theorem edgeChart_base_retained (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (X : Coordinate (2 + u) A → Bool) (v : Coordinate (2 + u) A)
    (hv : v ∈ graphEdges (thinned G X)) :
    BaseRetained (edgeChart v).2 (fun w => X (roleCoordinateEquiv (edgeChart v).1 w)) := by
  have hv := (Finset.mem_filter.mp hv).2
  apply (baseRetained_two_iff _ _).mpr
  rw [← chartEdge, chartEdge_edgeChart v hv.1]
  exact ((thinned_adj_iff G X hv.1 _ _).mp hv.2).2

omit [DecidableEq A] in
/-- Each actual graph edge has an original complete base in its chart. -/
theorem edgeChart_mem_bases (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (v : Coordinate (2 + u) A) (hv : v ∈ graphEdges G) :
    (edgeChart v).2 ∈ MultipartiteExtension.bases
      (G.comap (MultipartiteCounting.roleEquiv (edgeChart v).1)) := by
  have hv := (Finset.mem_filter.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try { simp only [Fin.lt_def] at hij; omega }
  change G.Adj ((edgeChart v).1 (Fin.castAdd u 0), edgeBase v 0)
    ((edgeChart v).1 (Fin.castAdd u 1), edgeBase v 1)
  simpa [edgeChart, edgeBase, pairRoleEquiv_first _ _ hv.1.ne, pairRoleEquiv_second] using hv.2

/-- Chart degree is the actual extension count in the corresponding relabelled
sampled graph; both use the original physical edge-retention bits. -/
theorem degree_edgeChart (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (X : Coordinate (2 + u) A → Bool) (v : Coordinate (2 + u) A)
    (hv : v.1.1 < v.2.1) :
    HypergraphNibble.degree (hypergraph (thinned G X)) v =
      (extensions (thinned (G.comap (MultipartiteCounting.roleEquiv (edgeChart v).1))
        (fun w => X (roleCoordinateEquiv (edgeChart v).1 w))) (edgeChart v).2).card := by
  have h := degree_role (thinned G X) (edgeChart v).1 (baseEdge (edgeChart v).2)
  have heq : roleCoordinateEquiv (edgeChart v).1 (baseEdge (edgeChart v).2) = v := chartEdge_edgeChart v hv
  simpa only [thinned_role_comap, degree_baseEdge, heq] using h.symm

end Erdos1017.TransversalClique

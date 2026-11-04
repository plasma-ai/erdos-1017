module

public import Erdos1017.IntegerTransfer.TransversalEdgeCharts

/-!
# Chart means and squared degree error of the thinned graph

This module defines the conditional thinned degree mean `chartMean` at a graph
edge and the atypical edges, bounds the mean uniformly in `α`, and controls the
global squared degree error and the atypical edge count by the retained-base
errors over all role charts, losing no inverse allocation factor.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The actual conditional thinned degree mean at an arbitrary graph edge,
computed in the edge's designated two-role chart. -/
def chartMean (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (α : ℝ) (v : Coordinate (2 + u) A) : ℝ :=
  let H := G.comap (MultipartiteCounting.roleEquiv (edgeChart v).1)
  BernoulliFamily.mean (extensions H (edgeChart v).2) (support (edgeChart v).2)
    (partProbability (normalizedProbability H α))

/-- Selected graph edges whose original base is not typical in its chart. -/
def atypicalEdges (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (γ : ℝ) (X : Coordinate (2 + u) A → Bool) : Finset (Coordinate (2 + u) A) :=
  (graphEdges (thinned G X)).filter (fun v => (edgeChart v).2 ∉
    typicalBases (G.comap (MultipartiteCounting.roleEquiv (edgeChart v).1)) γ)

/-- Retained edge bases are exactly original bases with their one coordinate retained. -/
theorem mem_retainedBases_iff (B : Finset (Fin 2 → A)) (x : Fin 2 → A)
    (Y : Coordinate (2 + u) A → Bool) :
    x ∈ retainedBases B Y ↔ x ∈ B ∧ BaseRetained x Y := by
  simp only [retainedBases, BernoulliFamily.retained, Finset.mem_filter,
    baseSupport_two, Finset.mem_singleton, forall_eq, baseRetained_two_iff]

/-- The mean bound is uniform over every graph edge and every allocation α. -/
theorem chartMean_le [Nonempty A]
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    (hd : ∀ i j : Fin (2 + u), i < j → δ ≤ pairDensity G (i, j))
    (v : Coordinate (2 + u) A) :
    chartMean G α v ≤ (1 + (δ ^ (SharedBasePattern.extensionEdges 2 u).card)⁻¹) *
      degreeScale (Fintype.card A) u (SharedBasePattern.extensionEdges 2 u).card α := by
  apply mean_le_uniform_multiplier _ hα hδ
  intro i j hij
  exact MultipartiteCounting.role_density G (edgeChart v).1 δ hd i j hij

/-- A typical chart gives an α-independent relative approximation to the common degree scale. -/
theorem chartMean_close (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    {α δ γ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    (hd : ∀ i j : Fin (2 + u), i < j → δ ≤ pairDensity G (i, j))
    (v : Coordinate (2 + u) A)
    (hv : (edgeChart v).2 ∈ typicalBases (G.comap (MultipartiteCounting.roleEquiv (edgeChart v).1)) γ) :
    |chartMean G α v - degreeScale (Fintype.card A) u (SharedBasePattern.extensionEdges 2 u).card α| ≤
      γ * degreeScale (Fintype.card A) u (SharedBasePattern.extensionEdges 2 u).card α := by
  apply typical_mean_close _ α γ hα _ _ hv
  intro i j hij
  exact hδ.trans_le (MultipartiteCounting.role_density G (edgeChart v).1 δ hd i j hij)

/-- The global degree squared error over actually selected graph edges is
bounded by the sum of the retained-base errors over all role charts. -/
theorem degree_squared_error_le
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (α : ℝ) (X : Coordinate (2 + u) A → Bool) :
    (∑ v ∈ graphEdges (thinned G X),
      ((HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - chartMean G α v) ^ 2) ≤
      ∑ σ : Equiv.Perm (Fin (2 + u)),
        retainedSquaredError (extensions (G.comap (MultipartiteCounting.roleEquiv σ)))
          (partProbability (normalizedProbability (G.comap (MultipartiteCounting.roleEquiv σ)) α))
          (fun v => X (roleCoordinateEquiv σ v)) := by
  let f (σ : Equiv.Perm (Fin (2 + u))) (x : Fin 2 → A) : ℝ :=
    let H := G.comap (MultipartiteCounting.roleEquiv σ)
    let Y := fun v => X (roleCoordinateEquiv σ v)
    BernoulliPresence.present Y (baseSupport x) *
      (((BernoulliFamily.retained (extensions H x) (support x) Y).card : ℝ) -
        BernoulliFamily.mean (extensions H x) (support x) (partProbability (normalizedProbability H α))) ^ 2
  have hpoint (v : Coordinate (2 + u) A) (hv : v ∈ graphEdges (thinned G X)) :
      ((HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - chartMean G α v) ^ 2 =
        f (edgeChart v).1 (edgeChart v).2 := by
    have hbase := edgeChart_base_retained G X v hv
    have hpres : BernoulliPresence.present (fun w => X (roleCoordinateEquiv (edgeChart v).1 w))
        (baseSupport (edgeChart v).2) = 1 := by rw [present_baseSupport, ite_eq_left hbase]
    dsimp only [f, chartMean]
    rw [hpres, one_mul]
    rw [← extensions_thinned _ _ _ hbase, degree_edgeChart G X v (Finset.mem_filter.mp hv).2.1]
  rw [Finset.sum_congr rfl hpoint]
  apply sum_chart_le _ (fun v hv => (Finset.mem_filter.mp hv).2.1) f
  intro σ x
  dsimp only [f]
  apply mul_nonneg _ (sq_nonneg _)
  unfold BernoulliPresence.present
  split_ifs <;> norm_num

/-- Original regularity exceptions are counted after their physical graph edges
are retained, so no inverse allocation factor is lost. -/
theorem atypicalEdges_card_le
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (γ : ℝ) (X : Coordinate (2 + u) A → Bool) :
    ((atypicalEdges G γ X).card : ℝ) ≤
      ∑ σ : Equiv.Perm (Fin (2 + u)),
        ((retainedBases ((MultipartiteExtension.bases (t := 2)
          (G.comap (MultipartiteCounting.roleEquiv σ))) \
            typicalBases (G.comap (MultipartiteCounting.roleEquiv σ)) γ)
          (fun v => X (roleCoordinateEquiv σ v))).card : ℝ) := by
  let f (σ : Equiv.Perm (Fin (2 + u))) (x : Fin 2 → A) : ℝ :=
    if x ∈ retainedBases ((MultipartiteExtension.bases (t := 2)
      (G.comap (MultipartiteCounting.roleEquiv σ))) \
        typicalBases (G.comap (MultipartiteCounting.roleEquiv σ)) γ)
      (fun v => X (roleCoordinateEquiv σ v)) then 1 else 0
  have hpoint (v : Coordinate (2 + u) A) (hv : v ∈ atypicalEdges G γ X) :
      f (edgeChart v).1 (edgeChart v).2 = 1 := by
    obtain ⟨hvG, hvbad⟩ := Finset.mem_filter.mp hv
    have hvOriginal : v ∈ graphEdges G := by
      obtain ⟨hlt, hadj⟩ := (Finset.mem_filter.mp hvG).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, (thinned_le G X) hadj⟩
    apply ite_eq_left
    apply (mem_retainedBases_iff _ _ _).mpr
    exact ⟨Finset.mem_sdiff.mpr ⟨edgeChart_mem_bases G v hvOriginal, hvbad⟩,
      edgeChart_base_retained G X v hvG⟩
  have hsum := sum_chart_le (atypicalEdges G γ X)
    (fun v hv => (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.1) f
    (fun σ x => by dsimp only [f]; split_ifs <;> norm_num)
  have hleft : (∑ v ∈ atypicalEdges G γ X, f (edgeChart v).1 (edgeChart v).2) =
      ((atypicalEdges G γ X).card : ℝ) := by simp only [Finset.sum_congr rfl hpoint, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hleft] at hsum
  simpa only [f, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] using hsum

end Erdos1017.TransversalClique

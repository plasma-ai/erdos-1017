module

public import Erdos1017.IntegerTransfer.TransversalCliqueMatching
public import Erdos1017.IntegerTransfer.RetainedExtensionMoments

/-!
# Base edges and degrees of transversal assignments

A two-role base assignment specifies one graph-edge coordinate (`baseEdge`),
complete assignments are exactly the transversal cliques, and the hypergraph
degree of a base edge is the number of assignments completing its two endpoints.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open TransversalThinning

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The actual graph-edge coordinate specified by a two-role base assignment. -/
def baseEdge (x : Fin 2 → A) : Coordinate (2 + u) A :=
  ((Fin.castAdd u 0, x 0), (Fin.castAdd u 1, x 1))

omit [DecidableEq A] in
/-- Complete assignments are exactly the actual transversal graph cliques. -/
theorem mem_assignments_iff {k : ℕ} (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (X : Fin k → A) : X ∈ assignments G ↔
      ∀ i j : Fin k, i < j → G.Adj (i, X i) (j, X j) := by
  simp only [assignments, MultipartiteCounting.assignments, Finset.mem_filter,
    Finset.mem_univ, true_and, MultipartiteExtension.completeEdges]
  constructor
  · intro h i j hij
    exact h (i, j) hij
  · intro h e he
    exact h e.1 e.2 he

omit [Fintype A] in
/-- Membership of the base edge fixes exactly its two endpoint values. -/
theorem baseEdge_mem_iff (x : Fin 2 → A) (X : Fin (2 + u) → A) :
    baseEdge x ∈ edges X ↔ ∀ i : Fin 2, X (Fin.castAdd u i) = x i := by
  rw [mem_edges_iff]
  constructor
  · rintro ⟨_, h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1
  · intro h
    exact ⟨by change (0 : ℕ) < 1; omega, h 0, h 1⟩

/-- Actual hypergraph degree equals the actual number of completing assignments
for the two graph-edge endpoints. -/
theorem degree_baseEdge (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (x : Fin 2 → A) :
    HypergraphNibble.degree (hypergraph G) (baseEdge x) = (extensions G x).card := by
  rw [degree_eq (by omega)]
  symm
  apply Finset.card_bij (fun y _ => (Fin.addCases x y : Fin (2 + u) → A))
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨(mem_assignments_iff G _).mpr (Finset.mem_filter.mp hy).2, ?_⟩
    exact (baseEdge_mem_iff x _).mpr (fun i => by simp only [Fin.addCases_left])
  · intro y _ z _ h
    funext i
    have heq := congrArg (fun X => X (Fin.natAdd 2 i)) h
    simpa only [Fin.addCases_right] using heq
  · intro X hX
    have hbase := (baseEdge_mem_iff x X).mp (Finset.mem_filter.mp hX).2
    let y : Fin u → A := fun i => X (Fin.natAdd 2 i)
    have heq : (Fin.addCases x y : Fin (2 + u) → A) = X := by
      funext i
      have h := Fin.addCases_castAdd_natAdd X i
      simpa only [hbase] using h
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    change MultipartiteExtension.Realizes G (Fin.addCases x y)
    rw [heq]
    exact (mem_assignments_iff G X).mp (Finset.mem_filter.mp hX).1

omit [Fintype A] in
/-- The graph-edge base support is a singleton, so it uses one independent bit. -/
theorem baseSupport_two (x : Fin 2 → A) :
    baseSupport (u := u) x = {baseEdge x} := by
  have h : MultipartiteExtension.completeEdges 2 = {(0, 1)} := by decide
  simp only [baseSupport, h, Finset.image_singleton, baseEdge]

omit [Fintype A] [DecidableEq A] in
/-- Distinct endpoint assignments give distinct graph edges. -/
theorem baseEdge_injective : Function.Injective (baseEdge (u := u) (A := A)) := by
  intro x y h
  funext i
  fin_cases i
  · exact congrArg (fun v => v.1.2) h
  · exact congrArg (fun v => v.2.2) h

end Erdos1017.TransversalClique

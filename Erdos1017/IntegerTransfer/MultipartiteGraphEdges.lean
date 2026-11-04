module

public import Erdos1017.IntegerTransfer.EmbeddedCliquePacking

/-!
# Counting unordered edges by increasing part labels

Increasing part-label coordinates count each unordered graph edge exactly once
(`graphEdges_card_eq_edgeFinset`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

variable {ℓ : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- Increasing part-label coordinates count each actual unordered edge once. -/
theorem graphEdges_card_eq_edgeFinset (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b)) :
    (graphEdges G).card = G.edgeFinset.card := by
  apply Finset.card_bij (fun v _ => s(v.1, v.2))
  · intro v hv
    exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hv).2.2
  · intro v hv w hw heq
    rcases Sym2.mk_eq_mk_iff.mp heq with heq | heq
    · exact heq
    · have hvlt := (Finset.mem_filter.mp hv).2.1
      have hwlt := (Finset.mem_filter.mp hw).2.1
      rw [heq] at hvlt
      exact (not_lt_of_ge hwlt.le hvlt).elim
  · intro e he
    induction e using Sym2.ind with
    | h v w =>
      have hadj : G.Adj v w := by simpa using he
      have hroles : v.1 ≠ w.1 := by
        intro h
        apply hparts v.1 v.2 w.2
        convert hadj using 1
        exact Prod.ext h rfl
      rcases lt_or_gt_of_ne hroles with hlt | hlt
      · exact ⟨(v, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hadj⟩, rfl⟩
      · exact ⟨(w, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hadj.symm⟩, Sym2.eq_swap⟩

end Erdos1017.TransversalClique

module

public import Erdos1017.Statement
public import Erdos1017.FractionalLimit.FinitePrimal
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The fractional clique partition value of a finite graph

This module defines the fractional clique partition linear program of a finite
graph, with cliques as columns of unit cost, and proves that it is feasible,
that its optimum is attained (`exists_optimal`), and that its value is at most
the integer clique partition number (`value_le_cliquePartitionNumber`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n : ℕ}

/-- Only actual graph cliques with at least one edge may receive partition weight. -/
def Clique (G : SimpleGraph (Fin n)) :=
  {s : Finset (Fin n) // 2 ≤ s.card ∧ G.IsClique (s : Set (Fin n))}

instance (G : SimpleGraph (Fin n)) : Fintype (Clique G) := by
  unfold Clique
  exact Fintype.ofFinite _

instance (G : SimpleGraph (Fin n)) : DecidableEq (Clique G) := inferInstanceAs (DecidableEq (Subtype _))

def Edge (G : SimpleGraph (Fin n)) := {e : Sym2 (Fin n) // e ∈ G.edgeSet}

instance (G : SimpleGraph (Fin n)) : Fintype (Edge G) := by
  unfold Edge
  exact Fintype.ofFinite _

instance (G : SimpleGraph (Fin n)) : DecidableEq (Edge G) := inferInstanceAs (DecidableEq (Subtype _))

/-- The incidence column of a clique in the finite edge space. -/
def column (G : SimpleGraph (Fin n)) (K : Clique G) : Edge G → ℝ :=
  fun e => if e.val.toFinset ⊆ K.val then 1 else 0

def Feasible (G : SimpleGraph (Fin n)) (w : Clique G → ℝ) : Prop :=
  FinitePrimal.Feasible (column G) (fun _ => 1) w

def value (G : SimpleGraph (Fin n)) : ℝ :=
  sInf {c | ∃ w, Feasible G w ∧ FinitePrimal.cost w = c}

/-- An ordinary clique partition gives a fractional partition by assigning unit weights. -/
def partitionWeight (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (K : Clique G) : ℝ := if K.val ∈ P then 1 else 0

theorem partition_feasible (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (hP : G.IsCliqueEdgePartition P) : Feasible G (partitionWeight G P) := by
  classical
  refine ⟨fun K => by unfold partitionWeight; split_ifs <;> norm_num, ?_⟩
  funext e
  simp only [FinitePrimal.moment, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ K : Clique G, partitionWeight G P K * column G K e) = 1
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h u v =>
    have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp he
    obtain ⟨s, ⟨hs, hu, hv⟩, hunique⟩ := hP.2 u v huv
    let K : Clique G := ⟨s, hP.1 s hs⟩
    rw [Finset.sum_eq_single K]
    · have hsubset : s(u, v).toFinset ⊆ s := by
        rw [Sym2.toFinset_mk_eq]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hu
        · exact hv
      simp [partitionWeight, column, K, hs, hsubset]
    · intro L _ hLK
      by_cases hL : L.val ∈ P
      · have hnot : ¬s(u, v).toFinset ⊆ L.val := by
          intro hsubset
          have hlu : u ∈ L.val := hsubset (by simp)
          have hlv : v ∈ L.val := hsubset (by simp)
          have heq : L.val = s := hunique L.val ⟨hL, hlu, hlv⟩
          exact hLK (Subtype.ext heq)
        simp [column, hnot]
      · simp [partitionWeight, hL]
    · simp

theorem partition_cost (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (hP : G.IsCliqueEdgePartition P) : FinitePrimal.cost (partitionWeight G P) = P.card := by
  classical
  let e : {K : Clique G // K.val ∈ P} ≃ {s : Finset (Fin n) // s ∈ P} :=
    { toFun := fun K => ⟨K.val.val, K.property⟩
      invFun := fun s => ⟨⟨s.val, hP.1 s.val s.property⟩, s.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_subtype] at hcard
  simpa [FinitePrimal.cost, partitionWeight] using congrArg (fun k : ℕ => (k : ℝ)) hcard

/-- Edge-by-edge partitions ensure that the fractional LP is always feasible. -/
theorem exists_feasible (G : SimpleGraph (Fin n)) : ∃ w, Feasible G w := by
  classical
  obtain ⟨P, hP, _⟩ := G.exists_isCliqueEdgePartition_card_eq
  exact ⟨partitionWeight G P, partition_feasible G P hP⟩

/-- The fractional optimum is attained, including in the edgeless graph. -/
theorem exists_optimal (G : SimpleGraph (Fin n)) :
    ∃ w, Feasible G w ∧ ∀ v, Feasible G v → FinitePrimal.cost w ≤ FinitePrimal.cost v := by
  obtain ⟨w₀, hw₀⟩ := exists_feasible G
  obtain ⟨w, hw, _, hmin⟩ := FinitePrimal.exists_optimal (column G) (fun _ => 1) w₀ hw₀
  exact ⟨w, hw, hmin⟩

theorem value_eq_optimal (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (hw : Feasible G w) (hmin : ∀ v, Feasible G v → FinitePrimal.cost w ≤ FinitePrimal.cost v) :
    value G = FinitePrimal.cost w := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro c ⟨v, hv, rfl⟩
      exact Finset.sum_nonneg (fun K _ => hv.1 K)
    · exact ⟨w, hw, rfl⟩
  · refine le_csInf (s := {c | ∃ v, Feasible G v ∧ FinitePrimal.cost v = c})
      ⟨FinitePrimal.cost w, w, hw, rfl⟩ ?_
    rintro c ⟨v, hv, rfl⟩
    exact hmin v hv

theorem value_nonneg (G : SimpleGraph (Fin n)) : 0 ≤ value G := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  rw [value_eq_optimal G w hw hmin]
  exact Finset.sum_nonneg (fun K _ => hw.1 K)

/-- Fractional partitions relax the original integer clique-partition problem. -/
theorem value_le_cliquePartitionNumber (G : SimpleGraph (Fin n)) :
    value G ≤ cliquePartitionNumber G := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  obtain ⟨P, hP, hcard⟩ := partition_card_le_cliquePartitionNumber G
  rw [value_eq_optimal G w hw hmin]
  calc
    FinitePrimal.cost w ≤ FinitePrimal.cost (partitionWeight G P) :=
      hmin _ (partition_feasible G P hP)
    _ = (P.card : ℝ) := partition_cost G P hP
    _ ≤ cliquePartitionNumber G := by exact_mod_cast hcard

end Erdos1017.FractionalGraph

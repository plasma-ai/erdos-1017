/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted from google-deepmind/formal-conjectures at revision
7bdc4a42f24c0316f81c73b26121794b2bed96a3: `SimpleGraph.IsCliqueEdgePartition`
and `SimpleGraph.exists_isCliqueEdgePartition_card_eq` from
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Chordal.lean, and
`Erdos1017.f` with its proved API from FormalConjectures/ErdosProblems/1017.lean.
Their category attributes and umbrella imports are removed. The definition
`cliquePartitionNumber` and the theorems about it at the end of this file are
local additions.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Lean.Elab.Tactic.Omega

/-!
# Statement of Erdős Problem 1017

`SimpleGraph.IsCliqueEdgePartition` and `f` are the definitions of Formal
Conjectures, and `Challenge.lean` repeats them; Comparator requires them to
agree exactly. The open answer placeholders and open theorems of the Formal
Conjectures entry are not included. `cliquePartitionNumber`, the least number
of cliques in an edge partition of a single graph, and its theorems are local
additions.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- `P` is a partition of the edges of `G` into cliques: each member of `P` is a clique
of `G` with at least two vertices, and every edge of `G` is contained in exactly one
member of `P`. -/
def IsCliqueEdgePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, 2 ≤ s.card ∧ G.IsClique (s : Set V)) ∧
  ∀ u v : V, G.Adj u v → ∃! s, s ∈ P ∧ u ∈ s ∧ v ∈ s

/-- Every finite graph has a clique edge partition consisting of its edges. -/
theorem exists_isCliqueEdgePartition_card_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P : Finset (Finset V), G.IsCliqueEdgePartition P ∧ P.card = G.edgeFinset.card := by
  refine ⟨G.edgeFinset.image Sym2.toFinset, ⟨?_, ?_⟩, ?_⟩
  · simp only [Finset.mem_image, mem_edgeFinset]
    rintro s ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he
      rw [Sym2.toFinset_mk_eq, Finset.card_pair he.ne, Finset.coe_pair]
      exact ⟨le_rfl, isClique_pair.mpr (fun _ => he)⟩
  · intro u v huv
    refine ⟨s(u, v).toFinset,
      ⟨Finset.mem_image.mpr ⟨s(u, v), by simpa using huv, rfl⟩, by simp, by simp⟩, ?_⟩
    rintro s ⟨hs, hu, hv⟩
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Sym2.mem_toFinset] at hu hv
    rw [(Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩]
  · apply Finset.card_image_of_injOn
    intro e he e' _ h
    simp only [mem_edgeFinset, Finset.mem_coe] at he
    induction e using Sym2.ind with
    | h a b =>
      have hab := (mem_edgeSet G).mp he
      have ha : a ∈ e'.toFinset := by rw [← h]; simp
      have hb : b ∈ e'.toFinset := by rw [← h]; simp
      rw [Sym2.mem_toFinset] at ha hb
      exact ((Sym2.mem_and_mem_iff hab.ne).mp ⟨ha, hb⟩).symm

end SimpleGraph

namespace Erdos1017

open SimpleGraph

/-- The least uniform bound on the number of cliques in an edge partition of an
$n$-vertex, $k$-edge graph. For infeasible parameters the value is zero. -/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = k →
    ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ m}

/-- Partitioning into individual edges gives the bound $f(n,k) \le k$. -/
theorem f_le (n k : ℕ) : f n k ≤ k := by
  classical
  apply Nat.sInf_le
  intro G hG
  obtain ⟨P, hP, hcard⟩ := G.exists_isCliqueEdgePartition_card_eq
  refine ⟨P, hP, ?_⟩
  simpa [hcard, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hG.le

/-- The infimum defining $f$ is an attained uniform bound. -/
theorem partition_card_le_f (n k : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.edgeSet.ncard = k) :
    ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ f n k := by
  classical
  have hne : {m : ℕ | ∀ H : SimpleGraph (Fin n), H.edgeSet.ncard = k →
      ∃ P : Finset (Finset (Fin n)), H.IsCliqueEdgePartition P ∧ P.card ≤ m}.Nonempty := by
    refine ⟨k, ?_⟩
    intro H hH
    obtain ⟨P, hP, hcard⟩ := H.exists_isCliqueEdgePartition_card_eq
    refine ⟨P, hP, ?_⟩
    simpa [hcard, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hH.le
  exact Nat.sInf_mem hne G hG

/-- A graph with no edges needs no cliques in its edge partition. -/
theorem f_zero (n : ℕ) : f n 0 = 0 := Nat.eq_zero_of_le_zero (f_le n 0)

/-- A proposed uniform bound is valid exactly when it is at least $f(n,k)$. -/
theorem f_le_iff (n k m : ℕ) : f n k ≤ m ↔
    ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = k →
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ m := by
  constructor
  · intro h G hG
    obtain ⟨P, hP, hcard⟩ := partition_card_le_f n k G hG
    exact ⟨P, hP, hcard.trans h⟩
  · intro h
    apply Nat.sInf_le
    exact h

/-- Impossible edge counts give the vacuous value zero and are excluded from the question. -/
theorem f_eq_zero_of_infeasible (n k : ℕ) (hk : n.choose 2 < k) : f n k = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [f_le_iff]
  intro G hG
  have hcard := G.card_edgeFinset_le_card_choose_two
  have : G.edgeFinset.card = k := by
    simpa [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hG
  simp only [Fintype.card_fin, this] at hcard
  omega

/-! Local additions, not part of Formal Conjectures. -/

/-- The minimum number of cliques in an edge partition of an individual graph. -/
noncomputable def cliquePartitionNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ m}

/-- The minimum for an individual graph is attained by an actual edge partition. -/
theorem partition_card_le_cliquePartitionNumber {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ P : Finset (Finset (Fin n)),
      G.IsCliqueEdgePartition P ∧ P.card ≤ cliquePartitionNumber G := by
  classical
  have hne : {m : ℕ | ∃ P : Finset (Finset (Fin n)),
      G.IsCliqueEdgePartition P ∧ P.card ≤ m}.Nonempty := by
    obtain ⟨P, hP, hcard⟩ := G.exists_isCliqueEdgePartition_card_eq
    exact ⟨G.edgeFinset.card, P, hP, hcard.le⟩
  exact Nat.sInf_mem hne

/-- This characterization ensures the minimum definition expresses graph partitions. -/
theorem cliquePartitionNumber_le_iff {n m : ℕ} (G : SimpleGraph (Fin n)) :
    cliquePartitionNumber G ≤ m ↔
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ m := by
  constructor
  · intro h
    obtain ⟨P, hP, hcard⟩ := partition_card_le_cliquePartitionNumber G
    exact ⟨P, hP, hcard.trans h⟩
  · intro h
    exact Nat.sInf_le h

/-- The official extremal function is exactly the least bound on individual minima. -/
theorem f_le_iff_cliquePartitionNumber (n k m : ℕ) :
    f n k ≤ m ↔ ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard = k → cliquePartitionNumber G ≤ m := by
  simp only [f_le_iff, cliquePartitionNumber_le_iff]

end Erdos1017

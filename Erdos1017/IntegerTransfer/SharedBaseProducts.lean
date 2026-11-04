module

public import Erdos1017.IntegerTransfer.MultipartiteExtensionMoments

/-!
# Density products of the shared-base pattern

This module factors the density products of the complete and doubled patterns:
the first-moment density is base density times extension density, and the
second-moment density has one base factor and two extension factors
(`product_double_factor`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.SharedBasePattern

open scoped BigOperators
open MultipartiteExtension

variable (t u : ℕ)

def leftPair : (Fin (t + u) × Fin (t + u)) ↪ (Fin (t + u + u) × Fin (t + u + u)) where
  toFun e := (left t u e.1, left t u e.2)
  inj' := by
    intro e f h
    exact Prod.ext ((left_strictMono t u).injective (congrArg Prod.fst h))
      ((left_strictMono t u).injective (congrArg Prod.snd h))

def rightPair : (Fin (t + u) × Fin (t + u)) ↪ (Fin (t + u + u) × Fin (t + u + u)) where
  toFun e := (right t u e.1, right t u e.2)
  inj' := by
    intro e f h
    exact Prod.ext ((right_strictMono t u).injective (congrArg Prod.fst h))
      ((right_strictMono t u).injective (congrArg Prod.snd h))

/-- Original edges having at least one extension endpoint. -/
def extensionEdges : Finset (Fin (t + u) × Fin (t + u)) :=
  (completeEdges (t + u)).filter (fun e => t ≤ e.2.val)

theorem right_eq_left_of_lt (i : Fin (t + u)) (hi : i.val < t) :
    right t u i = left t u i := by
  apply Fin.ext
  simp [right, left, hi]

/-- The doubled pattern contains the whole first copy and exactly the
non-base edges of the second copy. -/
theorem edges_decomposition : edges t u =
    (completeEdges (t + u)).map (leftPair t u) ∪ (extensionEdges t u).map (rightPair t u) := by
  ext e
  constructor
  · intro he
    have hord := label_lt_of_mem t u he
    have hfull : (label t u e.1, label t u e.2) ∈ completeEdges (t + u) := by
      simp only [completeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hord
    rcases edge_copies t u he with hc | hc
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr
        ⟨(label t u e.1, label t u e.2), hfull, Prod.ext hc.1 hc.2⟩)
    · by_cases hbase : (label t u e.2).val < t
      · have hbase' : (label t u e.1).val < t := by omega
        have hl1 := right_eq_left_of_lt t u (label t u e.1) hbase'
        have hl2 := right_eq_left_of_lt t u (label t u e.2) hbase
        exact Finset.mem_union_left _ (Finset.mem_map.mpr
          ⟨(label t u e.1, label t u e.2), hfull,
            Prod.ext (hl1.symm.trans hc.1) (hl2.symm.trans hc.2)⟩)
      · exact Finset.mem_union_right _ (Finset.mem_map.mpr
          ⟨(label t u e.1, label t u e.2), Finset.mem_filter.mpr ⟨hfull, Nat.le_of_not_gt hbase⟩,
            Prod.ext hc.1 hc.2⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
      exact left_edge_mem t u (Finset.mem_filter.mp hf).2
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
      exact right_edge_mem t u (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2

theorem copies_disjoint : Disjoint ((completeEdges (t + u)).map (leftPair t u))
    ((extensionEdges t u).map (rightPair t u)) := by
  apply Finset.disjoint_left.mpr
  intro e hl hr
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hl
  obtain ⟨b, hb, hb'⟩ := Finset.mem_map.mp hr
  have hbase := (Finset.mem_filter.mp hb).2
  have hn : ¬ b.2.val < t := by omega
  have heq := congrArg (fun e => e.2.val) (ha.trans hb'.symm)
  simp only [leftPair, rightPair, Function.Embedding.coeFn_mk, left, right, hn,
    ↓reduceDIte, Fin.val_castAdd] at heq
  have hlt := a.2.isLt
  omega

/-- Exact density product of the actual shared-base doubled edge set. -/
theorem product_double (D : Fin (t + u) × Fin (t + u) → ℝ) :
    (∏ e ∈ edges t u, D (label t u e.1, label t u e.2)) =
      (∏ e ∈ completeEdges (t + u), D e) * (∏ e ∈ extensionEdges t u, D e) := by
  rw [edges_decomposition, Finset.prod_union (copies_disjoint t u)]
  simp only [Finset.prod_map, leftPair, rightPair, Function.Embedding.coeFn_mk,
    label_left, label_right]

/-- Original edges whose two endpoints lie in the shared base. -/
def baseEdges : Finset (Fin (t + u) × Fin (t + u)) :=
  (completeEdges (t + u)).filter (fun e => e.2.val < t)

def basePair : (Fin t × Fin t) ↪ (Fin (t + u) × Fin (t + u)) where
  toFun e := (Fin.castAdd u e.1, Fin.castAdd u e.2)
  inj' := by
    intro e f h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun e => e.1.val) h
    · apply Fin.ext
      exact congrArg (fun e => e.2.val) h

/-- The shared-base edge family is exactly the embedded complete base graph. -/
theorem baseEdges_eq_map : baseEdges t u = (completeEdges t).map (basePair t u) := by
  ext e
  constructor
  · intro he
    obtain ⟨hfull, hbase⟩ := Finset.mem_filter.mp he
    have hlt := (Finset.mem_filter.mp hfull).2
    have hi : e.1.val < t := by omega
    refine Finset.mem_map.mpr ⟨(⟨e.1.val, hi⟩, ⟨e.2.val, hbase⟩), ?_, ?_⟩
    · simp only [completeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt
    · apply Prod.ext <;> apply Fin.ext <;> rfl
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    have hlt := (Finset.mem_filter.mp hf).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, f.2.isLt⟩

/-- First-moment density factors into base density and extension density. -/
theorem product_complete (D : Fin (t + u) × Fin (t + u) → ℝ) :
    (∏ e ∈ completeEdges (t + u), D e) =
      (∏ e ∈ baseEdges t u, D e) * (∏ e ∈ extensionEdges t u, D e) := by
  simpa only [baseEdges, extensionEdges, not_lt] using
    (Finset.prod_filter_mul_prod_filter_not (completeEdges (t + u))
      (fun e => e.2.val < t) D).symm

/-- Second-moment density has one base factor and two extension factors. -/
theorem product_double_factor (D : Fin (t + u) × Fin (t + u) → ℝ) :
    (∏ e ∈ edges t u, D (label t u e.1, label t u e.2)) =
      (∏ e ∈ baseEdges t u, D e) * (∏ e ∈ extensionEdges t u, D e) ^ 2 := by
  rw [product_double, product_complete]
  ring

/-- The base density factor in the actual base counting theorem. -/
theorem product_base (D : Fin (t + u) × Fin (t + u) → ℝ) :
    (∏ e ∈ baseEdges t u, D e) =
      ∏ e ∈ completeEdges t, D (Fin.castAdd u e.1, Fin.castAdd u e.2) := by
  rw [baseEdges_eq_map, Finset.prod_map]
  rfl

end Erdos1017.SharedBasePattern

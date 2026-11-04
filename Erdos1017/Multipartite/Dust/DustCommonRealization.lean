module

public import Erdos1017.Multipartite.Dust.DustPaddedCells
public import Erdos1017.Multipartite.Physical.PhysicalCellCollapse

/-!
# Common physical realization across cell counts

Merging every artificial cell into one dust component (`merge`) preserves
completed blocks in both pair orientations, the merged vertex masses are the
original heads and total dust mass, and every admissible cell count realizes the
same fixed physical graph demand.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.DustCommonRealization

open MeasureTheory PhysicalCellLift
open scoped BigOperators

/-- One anchor, the fixed heads, and one physical dust component. -/
abbrev Label (m : ℕ) := Option (Fin m) ⊕ Unit

local instance (k : ℕ) : MeasurableSpace (Option (Fin k)) := ⊤
local instance (m : ℕ) : MeasurableSpace (Label m) := ⊤

/-- These physical component masses do not depend on the number of artificial cells. -/
def masses {m : ℕ} (p : Fin m → ℝ) (s : ℝ) : Label m → ℝ :=
  Sum.elim (Multipartite.anchorMasses p) (fun _ => s)

/-- Merge every artificial cell into the same dust component, retaining all heads. -/
def merge (m n : ℕ) : Option (Fin (m + n)) → Label m
  | none => .inl none
  | some i => Fin.addCases (fun j => .inl (some j)) (fun _ => .inr ()) i

theorem merge_anchor (m n : ℕ) : merge m n none = .inl none := rfl

theorem merge_head (m n : ℕ) (i : Fin m) : merge m n (some (Fin.castAdd n i)) = .inl (some i) := by
  simp [merge]

theorem merge_cell (m n : ℕ) (i : Fin n) : merge m n (some (Fin.natAdd m i)) = .inr () := by
  simp [merge]

/-- The label merge preserves every completed block, including both pair orientations. -/
theorem merge_blocks (m n : ℕ) (i j : Option (Fin (m + n))) :
    (i ≠ j ∨ i ∈ (DustPaddedCells.cells m n).image some) ↔
      (merge m n i ≠ merge m n j ∨ merge m n i ∈ ({.inr ()} : Finset (Label m))) := by
  cases i with
  | none =>
    cases j with
    | none => simp [merge]
    | some j =>
      induction j using Fin.addCases <;> simp [merge_head, merge_cell, merge_anchor]
  | some i =>
    induction i using Fin.addCases with
    | left i =>
      cases j with
      | none => simp [merge_head, merge_anchor]
      | some j =>
        induction j using Fin.addCases with
        | left j => simp [merge_head, DustPaddedCells.castAdd_not_mem_cells]
        | right j =>
          have hne : Fin.castAdd n i ≠ Fin.natAdd m j := by
            intro h
            exact DustPaddedCells.castAdd_not_mem_cells m n i
              (h ▸ DustPaddedCells.natAdd_mem_cells m n j)
          simp [merge_head, merge_cell, hne]
    | right i => simp [merge_cell, DustPaddedCells.natAdd_mem_cells]

/-- The merged vertex masses are precisely the original heads and total dust mass. -/
theorem grouped_masses {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (n : ℕ) (hn : 0 < n) :
    groupedMass (merge m n) (Multipartite.anchorMasses (DustPaddedCells.target p s n)) = masses p s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  funext k
  rcases k with h | u
  · cases h with
    | none =>
      simp [groupedMass, Fin.sum_univ_add, merge_head, merge_cell, merge_anchor,
        masses, Multipartite.anchorMasses]
    | some i =>
      simp [groupedMass, Fin.sum_univ_add, merge_head, merge_cell, merge_anchor,
        DustPaddedCells.target_head, masses, Multipartite.anchorMasses]
  · cases u
    simp [groupedMass, Fin.sum_univ_add, merge_head, merge_cell, merge_anchor,
      DustPaddedCells.target_cell, masses, Multipartite.anchorMasses]
    field_simp

/-- The physical vertex measure after merging is independent of the artificial cell count. -/
theorem map_vertices {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) (ν : Measure Ω) :
    (vertexMeasure (fun _ : Option (Fin (m + n)) => ν)
      (Multipartite.anchorMasses (DustPaddedCells.target p s n))).map (collapse (merge m n)) =
      vertexMeasure (fun _ : Label m => ν) (masses p s) := by
  have ha : ∀ i, 0 ≤ Multipartite.anchorMasses (DustPaddedCells.target p s n) i := by
    intro i
    cases i with
    | none => norm_num [Multipartite.anchorMasses]
    | some i => exact (DustPaddedCells.target_cube p hp s hs n hn hsn i).1
  rw [map_vertexMeasure (merge m n) (measurable_of_countable _) ν _ ha, grouped_masses p s n hn]

/-- Every admissible cell count realizes the same fixed physical graph demand.
Both ordered pair orientations are preserved by the common-law dust merge. -/
theorem exists_fixed_partition {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω]
    {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) (ν : Measure Ω)
    [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∃ w : Multipartite.Selection (Option (Fin (m + n))) → ℝ,
      TransportedFeasible ν (Multipartite.anchorMasses (DustPaddedCells.target p s n)) w
        ((DustPaddedCells.cells m n).image some) (merge m n) {.inr ()} ∧
      (occupation (fun _ : Option (Fin (m + n)) => ν)
        (Multipartite.anchorMasses (DustPaddedCells.target p s n)) w
        ((DustPaddedCells.cells m n).image some)).map
          (Prod.map (collapse (merge m n)) (collapse (merge m n))) =
        ((vertexMeasure (fun _ : Label m => ν) (masses p s)).prod
          (vertexMeasure (fun _ : Label m => ν) (masses p s))).restrict (edgeSet {.inr ()}) ∧
      cost (fun _ : Option (Fin (m + n)) => ν)
        (Multipartite.anchorMasses (DustPaddedCells.target p s n)) w
        ((DustPaddedCells.cells m n).image some) ≤ MultipartiteDust.value p s + s ^ 2 / (n : ℝ) := by
  obtain ⟨w, hw, _, hcost⟩ := DustPaddedCells.exists_physical_lift p hp s hs n hn hsn
    (fun _ => ν)
  have ha : ∀ i, 0 ≤ Multipartite.anchorMasses (DustPaddedCells.target p s n) i := by
    intro i
    cases i with
    | none => norm_num [Multipartite.anchorMasses]
    | some i => exact (DustPaddedCells.target_cube p hp s hs n hn hsn i).1
  have hfeasible := transported_feasible ν _ ha w hw ((DustPaddedCells.cells m n).image some)
    (merge m n) (measurable_of_countable _) {.inr ()} (merge_blocks m n)
  refine ⟨w, hfeasible, ?_, hcost⟩
  have hbalance := hfeasible.2.2.2
  rw [grouped_masses p s n hn] at hbalance
  rw [hbalance, demand_eq_restrict_product]
  intro i
  rcases i with h | u
  · cases h with
    | none => norm_num [masses, Multipartite.anchorMasses]
    | some i => exact (hp i).1
  · exact hs

end Erdos1017.DustCommonRealization

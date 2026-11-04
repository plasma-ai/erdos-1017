module

public import Erdos1017.Multipartite.Dust.DustZeroHead
public import Erdos1017.Multipartite.Dust.DustPhysicalLift

/-!
# Padding a head profile with equal dust cells

A finite collection of equal dust cells is appended to a fixed head vector
(`target`); the fixed-head value is approximated for every admissible positive
cell count, and atomless cells give physical clique laws with full edge balance
and the explicit approximation cost.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.DustPaddedCells

open MeasureTheory
open scoped BigOperators

/-- The new cell labels after the fixed finite head profile. -/
def cells (m n : ℕ) : Finset (Fin (m + n)) := Finset.univ.map (Fin.natAddEmb m)

theorem cells_card (m n : ℕ) : (cells m n).card = n := by simp [cells]

theorem cells_nonempty (m n : ℕ) (hn : 0 < n) : (cells m n).Nonempty := by
  apply Finset.card_pos.mp
  simpa [cells_card] using hn

theorem natAdd_mem_cells (m n : ℕ) (i : Fin n) : Fin.natAdd m i ∈ cells m n :=
  Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem castAdd_not_mem_cells (m n : ℕ) (i : Fin m) : Fin.castAdd n i ∉ cells m n := by
  rintro h
  obtain ⟨j, _, heq⟩ := Finset.mem_map.mp h
  have hv := congrArg Fin.val heq
  simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

/-- Append a finite collection of equal dust cells to a fixed head vector. -/
def target {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (n : ℕ) : Fin (m + n) → ℝ :=
  fun i => Fin.append p (fun _ : Fin n => 0) i + s * Selector.uniformCellWeights (cells m n) i

theorem target_head {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (n : ℕ) (i : Fin m) :
    target p s n (Fin.castAdd n i) = p i := by
  simp [target, Selector.uniformCellWeights, castAdd_not_mem_cells]

theorem target_cell {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (n : ℕ) (i : Fin n) :
    target p s n (Fin.natAdd m i) = s / (n : ℝ) := by
  simp [target, Selector.uniformCellWeights, natAdd_mem_cells, cells_card, div_eq_mul_inv]

theorem padded_zero {m n : ℕ} (p : Fin m → ℝ) :
    ∀ i ∈ cells m n, Fin.append p (fun _ : Fin n => 0) i = 0 := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact Fin.append_right _ _ j

theorem target_cube {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) :
    ∀ i, 0 ≤ target p s n i ∧ target p s n i ≤ 1 := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [target_head] using hp i
  | right i =>
    rw [target_cell]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact ⟨div_nonneg hs hn'.le, (div_le_one hn').mpr hsn⟩

/-- The same fixed-head value is approximated for every admissible positive cell count. -/
theorem finite_cell_value_error {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) :
    0 ≤ Selector.value (target p s n) - MultipartiteDust.value p s ∧
      Selector.value (target p s n) - MultipartiteDust.value p s ≤ s ^ 2 / (2 * (n : ℝ)) := by
  unfold target
  have h := DustCellRestriction.finite_cell_value_error (cells m n) (cells_nonempty m n hn)
    (Fin.append p (fun _ : Fin n => 0)) s (padded_zero p) (target_cube p hp s hs n hn hsn)
  simpa only [target, MultipartiteDust.value_append_zero, cells_card] using h

/-- Actual cell-sampled laws with internal edge repair approximate the fixed-head dust value. -/
theorem exists_physical_lift {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 0 < n) (hsn : s ≤ n)
    (μ : Option (Fin (m + n)) → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ w : Multipartite.Selection (Option (Fin (m + n))) → ℝ,
      Multipartite.PrimalFeasible (Multipartite.anchorMasses (target p s n)) w ∧
      (∀ i j, PhysicalCellLift.completedPairLoad μ (Multipartite.anchorMasses (target p s n))
        w ((cells m n).image some) i j =
        if i ≠ j ∨ i ∈ (cells m n).image some then
          ENNReal.ofReal (Multipartite.anchorMasses (target p s n) i *
            Multipartite.anchorMasses (target p s n) j) • (μ i).prod (μ j) else 0) ∧
      PhysicalCellLift.cost μ (Multipartite.anchorMasses (target p s n)) w ((cells m n).image some) ≤
        MultipartiteDust.value p s + s ^ 2 / (n : ℝ) := by
  unfold target
  have h := DustPhysicalLift.exists_uniform_cell_lift (cells m n) (cells_nonempty m n hn)
    (Fin.append p (fun _ : Fin n => 0)) s (padded_zero p) (target_cube p hp s hs n hn hsn) μ
  simpa only [target, MultipartiteDust.value_append_zero, cells_card] using h

/-- Atomless cells give genuine physical clique laws, with full edge balance
and the explicit fixed-head approximation cost. -/
theorem exists_physical_partition {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω]
    {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 0 < n) (hsn : s ≤ n)
    (μ : Option (Fin (m + n)) → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)] :
    let : MeasurableSpace (Option (Fin (m + n))) := ⊤
    ∃ w : Multipartite.Selection (Option (Fin (m + n))) → ℝ,
      PhysicalCellLift.Feasible μ (Multipartite.anchorMasses (target p s n))
        ((cells m n).image some) w ∧
      PhysicalCellLift.cost μ (Multipartite.anchorMasses (target p s n)) w ((cells m n).image some) ≤
        MultipartiteDust.value p s + s ^ 2 / (n : ℝ) := by
  let : MeasurableSpace (Option (Fin (m + n))) := ⊤
  obtain ⟨w, hw, _, hcost⟩ := exists_physical_lift p hp s hs n hn hsn μ
  exact ⟨w, PhysicalCellLift.feasible_lift μ _ w hw _, hcost⟩

end Erdos1017.DustPaddedCells

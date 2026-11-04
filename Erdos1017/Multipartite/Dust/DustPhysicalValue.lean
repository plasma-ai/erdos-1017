module

public import Erdos1017.Multipartite.Dust.DustPhysicalDuality
public import Erdos1017.Multipartite.Physical.PhysicalTupleLift

/-!
# Physical infimum equals the coefficient value

`infimum` ranges over all finite-component clique laws at all orders, allowing
singular joint measures; the finite-cell partitions are feasible members with
arbitrarily accurate cost, so the finite-head homogeneous coefficient value
equals the infimum over all physical clique laws on the fixed atomless graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.PhysicalPrimal

/-- The infimum over all finite-component clique laws at all orders. Singular
joint measures and infinitely many nonzero orders are allowed. -/
def infimum {V : Type*} [MeasurableSpace V] (A : V → V → Prop)
    (demand : Measure (V × V)) : ℝ :=
  sInf {c | ∃ μ : Laws V, (∀ n, IsFiniteMeasure (μ n)) ∧ Feasible A demand μ ∧ cost μ = c}

end Erdos1017.PhysicalPrimal

namespace Erdos1017.DustCommonRealization

open PhysicalCellLift

local instance (k : ℕ) : MeasurableSpace (Option (Fin k)) := ⊤
local instance (m : ℕ) : MeasurableSpace (Label m) := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω] {m : ℕ}

/-- The previously constructed finite-cell partitions are actual feasible
members of the unrestricted all-orders physical primal. -/
theorem exists_unrestricted_partition (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) (ν : Measure Ω)
    [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∃ μ : PhysicalPrimal.Laws (Label m × Ω), (∀ k, IsFiniteMeasure (μ k)) ∧
      PhysicalPrimal.Feasible (Adj ({.inr ()} : Finset (Label m)))
        (((vertexMeasure (fun _ => ν) (masses p s)).prod
          (vertexMeasure (fun _ => ν) (masses p s))).restrict
          (edgeSet ({.inr ()} : Finset (Label m)))) μ ∧
      PhysicalPrimal.cost μ ≤ MultipartiteDust.value p s + s ^ 2 / (n : ℝ) := by
  obtain ⟨w, hw, hbalance, hcost⟩ := exists_fixed_partition p hp s hs n hn hsn ν
  let a := Multipartite.anchorMasses (DustPaddedCells.target p s n)
  let S := (DustPaddedCells.cells m n).image some
  let μ := tuplePartition (merge m n) (fun _ => ν) a w S
  have he : Measurable (merge m n) := measurable_of_countable _
  have hμ := tuplePartition_feasible (merge m n) he ν a w S {.inr ()} hw
  refine ⟨μ, fun k => tuplePartition_finite _ _ _ _ _ k, ?_, ?_⟩
  · refine ⟨hμ.1, hμ.2.1, hμ.2.2.1, ?_⟩
    rw [tuplePartition_occupation (merge m n) he]
    exact hbalance
  · rw [tuplePartition_cost]
    exact hcost

/-- Arbitrarily accurate upper approximants in the unrestricted physical
primal, on the same fixed graph and probability space. -/
theorem exists_unrestricted_near_value (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) (ν : Measure Ω)
    [IsProbabilityMeasure ν] [NullSingletonClass ν] (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : PhysicalPrimal.Laws (Label m × Ω), (∀ k, IsFiniteMeasure (μ k)) ∧
      PhysicalPrimal.Feasible (Adj ({.inr ()} : Finset (Label m)))
        (((vertexMeasure (fun _ => ν) (masses p s)).prod
          (vertexMeasure (fun _ => ν) (masses p s))).restrict
          (edgeSet ({.inr ()} : Finset (Label m)))) μ ∧
      PhysicalPrimal.cost μ < MultipartiteDust.value p s + ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (max 0 (s ^ 2 / ε)))
  have hn₀ : (0 : ℝ) < n := lt_of_le_of_lt ((le_max_left 0 _).trans (le_max_right s _)) hn
  have hsn : s ≤ n := (le_max_left s _).trans hn.le
  have hnε : s ^ 2 / ε < n := lt_of_le_of_lt ((le_max_right 0 _).trans (le_max_right s _)) hn
  have herr : s ^ 2 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hn₀).mpr
    have h := (div_lt_iff₀ hε).mp hnε
    simpa [mul_comm] using h
  obtain ⟨μ, hf, hμ, hc⟩ := exists_unrestricted_partition p hp s hs n
    (by exact_mod_cast hn₀) hsn ν
  exact ⟨μ, hf, hμ, lt_of_le_of_lt hc (add_lt_add_right herr _)⟩

/-- The finite-head homogeneous coefficient value equals the infimum over
all physical clique laws on the actual fixed atomless graph. -/
theorem physical_infimum_eq_value (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) (ν : Measure Ω)
    [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    PhysicalPrimal.infimum (Adj ({.inr ()} : Finset (Label m)))
      (((vertexMeasure (fun _ => ν) (masses p s)).prod
        (vertexMeasure (fun _ => ν) (masses p s))).restrict
        (edgeSet ({.inr ()} : Finset (Label m)))) = MultipartiteDust.value p s := by
  let A := Adj ({.inr ()} : Finset (Label m)) (Ω := Ω)
  let demand := ((vertexMeasure (fun _ => ν) (masses p s)).prod
    (vertexMeasure (fun _ => ν) (masses p s))).restrict (edgeSet ({.inr ()} : Finset (Label m)))
  let costs : Set ℝ := {c | ∃ μ : PhysicalPrimal.Laws (Label m × Ω),
    (∀ n, IsFiniteMeasure (μ n)) ∧ PhysicalPrimal.Feasible A demand μ ∧ PhysicalPrimal.cost μ = c}
  have hlower : ∀ c ∈ costs, MultipartiteDust.value p s ≤ c := by
    rintro c ⟨μ, hf, hμ, rfl⟩
    have : ∀ n, IsFiniteMeasure (μ n) := hf
    exact value_le_restricted_physical_cost ν p (fun i => (hp i).1) s hs μ hμ
  have hbounded : BddBelow costs := ⟨MultipartiteDust.value p s, hlower⟩
  have hnonempty : costs.Nonempty := by
    obtain ⟨μ, hf, hμ, hc⟩ := exists_unrestricted_near_value p hp s hs ν 1 (by norm_num)
    exact ⟨PhysicalPrimal.cost μ, μ, hf, hμ, rfl⟩
  change sInf costs = MultipartiteDust.value p s
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨μ, hf, hμ, hc⟩ := exists_unrestricted_near_value p hp s hs ν ε hε
    exact lt_of_le_of_lt (csInf_le hbounded ⟨μ, hf, hμ, rfl⟩) hc
  · exact le_csInf hnonempty hlower

end Erdos1017.DustCommonRealization

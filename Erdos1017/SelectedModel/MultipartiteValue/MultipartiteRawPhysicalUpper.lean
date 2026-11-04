module

public import Erdos1017.Multipartite.MultipartiteCountableIntegral
public import Erdos1017.Multipartite.MultipartiteDensitySelection

/-!
# Physical upper bound for a raw anchored profile

For every raw summable anchored profile, finite-head near-primal laws on the
fixed countable carrier approach the countable coefficient value
(`exists_partition_near_countable_value`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Erdos1017.MultipartiteCountableDual

/-- A finite genuine-dust prefix is bounded by the actual countable value,
without a sorted profile or square-moment hypothesis. -/
theorem prefix_dust_value_le_value (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (s : ℝ) (n : ℕ) :
    MultipartiteDust.value (fun i : Fin n => p i.val) s ≤ value p s := by
  obtain ⟨D, hD, hvalue⟩ := MultipartiteDust.exists_value_eq (fun i : Fin n => p i.val) s
  rw [hvalue, ← objective_extendZero D p s]
  apply le_csSup
  · exact (feasible_isCompact.image_of_continuousOn
      ((objective_continuousOn p hp hsum s).mono Set.inter_subset_left)).bddAbove
  · exact ⟨extendZero D, extendZero_feasible hD, rfl⟩

end Erdos1017.MultipartiteCountableDual

namespace Erdos1017.MultipartiteCountableMeasure

local instance rawPhysicalLabelMeasurable : MeasurableSpace Label := ⊤
local instance rawPhysicalFiniteHeadMeasurable (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤
local instance rawPhysicalFiniteDustMeasurable (n : ℕ) : MeasurableSpace (DustCommonRealization.Label n) := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω]

/-- Actual finite-head near-primal laws on the fixed countable carrier,
with raw summable masses and only the genuine dust retained. -/
theorem exists_raw_prefix_partition (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : PhysicalPrimal.Laws (Label × Ω), (∀ k, IsFiniteMeasure (ρ k)) ∧
      PhysicalPrimal.Feasible (fun a b => (a, b) ∈ edgeSet)
        (PhysicalPrimal.graphDemand (prefixMeasure ν p s n) edgeSet) ρ ∧
      PhysicalPrimal.cost ρ < MultipartiteDust.value (fun i : Fin n => p i.val) s + ε := by
  obtain ⟨ρ, hfinite, hρ, hcost⟩ := DustCommonRealization.exists_unrestricted_near_value
    (fun i : Fin n => p i.val) (fun i => hp i.val) s hs ν ε hε
  let (k : ℕ) : IsFiniteMeasure (ρ k) := hfinite k
  refine ⟨PhysicalPrimal.mapLaws (embedVertex n) ρ,
    fun k => PhysicalPrimal.mapLaws_finite _ _ k, ?_, ?_⟩
  · have h := PhysicalPrimal.mapLaws_feasible (embedVertex_measurable n) ρ _
      (fun a b => (a, b) ∈ edgeSet) _ hρ edgeSet_measurable
      (fun a b hab => (embedVertex_adj n a b).mpr hab)
    have hmap := map_finite_graphDemand ν p s n
    dsimp only [PhysicalPrimal.graphDemand] at hmap
    rw [hmap] at h
    exact h
  · rw [PhysicalPrimal.cost_mapLaws (embedVertex_measurable n)]
    exact hcost

/-- Genuine canonical all-order physical laws approach the actual countable
coefficient value for every raw summable anchored profile. The sorted
compact-profile square constraint is not a hidden hypothesis. -/
theorem exists_partition_near_countable_value (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : PhysicalPrimal.Laws (Label × Ω), (∀ k, IsFiniteMeasure (ρ k)) ∧
      PhysicalPrimal.Feasible (fun a b => (a, b) ∈ edgeSet)
        (PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet) ρ ∧
      PhysicalPrimal.cost ρ < MultipartiteCountableDual.value p s + ε := by
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp i).1
  let η := vertexMeasure ν p s
  have hlimit : Tendsto (fun n => η.real Set.univ * (tailMeasure ν p n).real Set.univ)
      atTop (𝓝 0) := by
    simpa using (tailMeasure_mass_tendsto_zero ν p hp0 hsum).const_mul (η.real Set.univ)
  obtain ⟨n, hn⟩ := (hlimit.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith)).exists
  obtain ⟨ρ, hfinite, hρ, hcost⟩ := exists_raw_prefix_partition ν p hp s hs n (ε / 2) (by linarith)
  let (k : ℕ) : IsFiniteMeasure (ρ k) := hfinite k
  have := prefixMeasure_finite ν p hsum s n
  have := tailMeasure_finite ν p hsum n
  have : IsFiniteMeasure (PhysicalPrimal.tailDemand
      (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet) := by
    unfold PhysicalPrimal.tailDemand
    infer_instance
  have hrepair := PhysicalPrimal.pairRepair_graph (prefixMeasure ν p s n) (tailMeasure ν p n)
    edgeSet edgeSet_measurable edgeSet_swap ρ hρ
  have hmass : (prefixMeasure ν p s n).real Set.univ + (tailMeasure ν p n).real Set.univ =
      η.real Set.univ := by
    rw [prefixMeasure_mass ν p hp0 s hs, tailMeasure_mass ν p hp0 hsum n,
      vertexMeasure_mass ν p hp0 hsum s hs]
    ring
  rw [hmass] at hrepair
  refine ⟨PhysicalPrimal.pairRepair ρ (PhysicalPrimal.tailDemand
    (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet),
    fun k => PhysicalPrimal.pairRepair_finite ρ _ k, ?_, ?_⟩
  · rw [vertexMeasure_eq_prefix_add_tail ν p s n]
    exact hrepair.1
  · have hv := MultipartiteCountableDual.prefix_dust_value_le_value p hp0 hsum s n
    linarith [hrepair.2]

end Erdos1017.MultipartiteCountableMeasure

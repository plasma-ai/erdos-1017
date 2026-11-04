module

public import Erdos1017.Multipartite.MultipartitePrefixEmbedding
public import Erdos1017.Multipartite.MultipartiteCountableValue

/-!
# Near-optimal partitions of the countable graph

The common carrier's graph (`edgeSet`) has independent head components and
complete dust; finite-head near-optimal partitions live on the fixed countable
carrier, and finite-prefix partitions with pair repair give arbitrarily
near-optimal partitions of the full countable physical graph.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableMeasure

open MeasureTheory
open scoped BigOperators

local instance : MeasurableSpace Label := ⊤
local instance (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤
local instance (n : ℕ) : MeasurableSpace (DustCommonRealization.Label n) := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω]

/-- The common carrier's graph has independent head components and complete dust. -/
def edgeSet : Set ((Label × Ω) × (Label × Ω)) :=
  PhysicalCellLift.edgeSet ({.inr ()} : Finset Label)

theorem edgeSet_measurable : MeasurableSet (edgeSet (Ω := Ω)) :=
  PhysicalCellLift.edgeSet_measurable _

omit [MeasurableSpace Ω] [MeasurableEq Ω] in
theorem edgeSet_swap : Prod.swap ⁻¹' edgeSet (Ω := Ω) = edgeSet := by
  ext z
  simp only [edgeSet, PhysicalCellLift.edgeSet, PhysicalCellLift.Adj,
    Set.mem_preimage, Set.mem_ofPred_eq, Prod.swap, Finset.mem_singleton]
  constructor <;> rintro ⟨hneq, hlabels | hdust⟩
  · exact ⟨Ne.symm hneq, Or.inl (Ne.symm hlabels)⟩
  · refine ⟨Ne.symm hneq, ?_⟩
    by_cases h : z.1.1 = z.2.1
    · exact Or.inr (h.trans hdust)
    · exact Or.inl h
  · exact ⟨Ne.symm hneq, Or.inl (Ne.symm hlabels)⟩
  · refine ⟨Ne.symm hneq, ?_⟩
    by_cases h : z.2.1 = z.1.1
    · exact Or.inr (h.trans hdust)
    · exact Or.inl h

/-- Actual finite-head near-optimal partitions live on the fixed countable carrier. -/
theorem exists_prefix_partition (ν : Measure Ω) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    {L : ℝ} {x : MultipartiteProfiles.Profile} (hx : x ∈ MultipartiteProfiles.space L)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : PhysicalPrimal.Laws (Label × Ω), (∀ k, IsFiniteMeasure (μ k)) ∧
      PhysicalPrimal.Feasible (fun a b => (a, b) ∈ edgeSet)
        (PhysicalPrimal.graphDemand (prefixMeasure ν x.2 (MultipartiteProfiles.dust x) n) edgeSet) μ ∧
      PhysicalPrimal.cost μ < MultipartiteProfiles.actualDustValue n x + ε := by
  obtain ⟨μ, hf, hμ, hc⟩ := DustCommonRealization.exists_unrestricted_near_value
    (fun i : Fin n => x.2 i.val) (fun i => ⟨hx.1.1.2 i.val, hx.1.2.2 i.val⟩)
    (MultipartiteProfiles.dust x) (MultipartiteProfiles.dust_nonneg hx) ν ε hε
  let (k : ℕ) : IsFiniteMeasure (μ k) := hf k
  refine ⟨PhysicalPrimal.mapLaws (embedVertex n) μ, fun k => PhysicalPrimal.mapLaws_finite _ _ k,
    ?_, ?_⟩
  · have h := PhysicalPrimal.mapLaws_feasible (embedVertex_measurable n) μ _
      (fun a b => (a, b) ∈ edgeSet) _ hμ edgeSet_measurable
      (fun a b hab => (embedVertex_adj n a b).mpr hab)
    have hmap := map_finite_graphDemand ν x.2 (MultipartiteProfiles.dust x) n
    dsimp only [PhysicalPrimal.graphDemand] at hmap
    rw [hmap] at h
    exact h
  · rw [PhysicalPrimal.cost_mapLaws (embedVertex_measurable n)]
    exact hc

/-- Finite-prefix partitions and actual pair repair give arbitrarily near-optimal
partitions of the full countable physical graph. -/
theorem exists_partition_near_limit (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : PhysicalPrimal.Laws (Label × Ω), (∀ k, IsFiniteMeasure (μ k)) ∧
      PhysicalPrimal.Feasible (fun a b => (a, b) ∈ edgeSet)
        (PhysicalPrimal.graphDemand (vertexMeasure ν x.2 (MultipartiteProfiles.dust x))
          edgeSet) μ ∧
      PhysicalPrimal.cost μ < MultipartiteProfiles.limitValue x + ε := by
  have hp : ∀ i, 0 ≤ x.2 i := fun i => hx.1.1.2 i
  have hsum := MultipartiteProfiles.atoms_summable hx
  have hs := MultipartiteProfiles.dust_nonneg hx
  let η := vertexMeasure ν x.2 (MultipartiteProfiles.dust x)
  have hmass (n : ℕ) :
      (prefixMeasure ν x.2 (MultipartiteProfiles.dust x) n).real Set.univ +
        (tailMeasure ν x.2 n).real Set.univ = η.real Set.univ := by
    rw [prefixMeasure_mass ν x.2 hp _ hs, tailMeasure_mass ν x.2 hp hsum,
      vertexMeasure_mass ν x.2 hp hsum _ hs]
    ring
  have hlimit : Filter.Tendsto (fun n => MultipartiteProfiles.actualDustValue n x +
      η.real Set.univ * (tailMeasure ν x.2 n).real Set.univ)
      Filter.atTop (nhds (MultipartiteProfiles.limitValue x)) := by
    simpa using (MultipartiteProfiles.actualDustValue_tendsto hx).add
      ((tailMeasure_mass_tendsto_zero ν x.2 hp hsum).const_mul (η.real Set.univ))
  obtain ⟨n, hn⟩ := (hlimit.eventually_lt_const
    (show MultipartiteProfiles.limitValue x < MultipartiteProfiles.limitValue x + ε / 2 by
      linarith)).exists
  obtain ⟨μ, hf, hμ, hc⟩ := exists_prefix_partition ν hx n (ε / 2) (by linarith)
  let (k : ℕ) : IsFiniteMeasure (μ k) := hf k
  have := prefixMeasure_finite ν x.2 hsum (MultipartiteProfiles.dust x) n
  have := tailMeasure_finite ν x.2 hsum n
  have : IsFiniteMeasure (PhysicalPrimal.tailDemand
      (prefixMeasure ν x.2 (MultipartiteProfiles.dust x) n) (tailMeasure ν x.2 n) edgeSet) := by
    unfold PhysicalPrimal.tailDemand
    infer_instance
  have hrepair := PhysicalPrimal.pairRepair_graph
    (prefixMeasure ν x.2 (MultipartiteProfiles.dust x) n) (tailMeasure ν x.2 n)
    edgeSet edgeSet_measurable edgeSet_swap μ hμ
  refine ⟨PhysicalPrimal.pairRepair μ (PhysicalPrimal.tailDemand
    (prefixMeasure ν x.2 (MultipartiteProfiles.dust x) n) (tailMeasure ν x.2 n) edgeSet),
    fun k => PhysicalPrimal.pairRepair_finite μ _ k, ?_, ?_⟩
  · rw [vertexMeasure_eq_prefix_add_tail ν x.2 (MultipartiteProfiles.dust x) n]
    exact hrepair.1
  · rw [hmass] at hrepair
    linarith [hrepair.2]

end Erdos1017.MultipartiteCountableMeasure

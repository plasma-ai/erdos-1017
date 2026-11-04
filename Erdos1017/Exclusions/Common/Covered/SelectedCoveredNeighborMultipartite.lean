module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteModelComparison

/-!
# The `E`-null boundary is a multipartite model

This module defines the neighbor code merging all atoms other than `B` into one
class and marking the diffuse remainder as clique dust; under `E`-nullity the
model is bounded by the multipartite theorem and cannot be a full stationary
optimum with benchmark excess.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

local instance : MeasurableSpace (Option (Fin 2)) := ⊤

/-- B retains class zero, all other original atoms merge into class one,
and the actual diffuse remainder receives the clique-dust marker. -/
def coveredNeighborCode (S : SelectedHighLowStructure W m) (r : S.I) :
    S.I ⊕ Bool → Option (Fin 2)
  | Sum.inl u => some (if u = r then 0 else 1)
  | Sum.inr _ => none

def coveredNeighborLabel (S : SelectedHighLowStructure W m) (r a : S.I) (x : Ω) :
    Option (Fin 2) := S.coveredNeighborCode r (S.coveredLabel a x)

theorem measurable_coveredNeighborLabel (S : SelectedHighLowStructure W m) (r a : S.I) :
    Measurable (S.coveredNeighborLabel r a) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (measurable_of_countable (S.coveredNeighborCode r)).comp (S.measurable_coveredLabel a)

/-- Genuine singleton labels keep diffuse dust a clique, including when
the entire diffuse part is null. The unused left none label never occurs. -/
def coveredNeighborPart (S : SelectedHighLowStructure W m) (r a : S.I) (x : Ω) :
    Option (Fin 2) ⊕ Ω :=
  if S.coveredNeighborLabel r a x = none then Sum.inr x
  else Sum.inl (S.coveredNeighborLabel r a x)

theorem measurable_coveredNeighborPart (S : SelectedHighLowStructure W m) (r a : S.I) :
    Measurable (S.coveredNeighborPart r a) := by
  exact Measurable.ite ((S.measurable_coveredNeighborLabel r a) (measurableSet_singleton none))
    measurable_inr (measurable_inl.comp (S.measurable_coveredNeighborLabel r a))

/-- The root class is the original B whole fiber, without merging it
with the optional exterior atom or with the saturated A head. -/
theorem coveredNeighborLabel_root_fiber (S : SelectedHighLowStructure W m) (r a : S.I) :
    S.coveredNeighborLabel r a ⁻¹' {some 0} = {x | S.ρ x = r.val} := by
  have hc (i : S.I ⊕ Bool) : S.coveredNeighborCode r i = some 0 ↔ i = Sum.inl r := by
    cases i with
    | inl u => by_cases h : u = r <;> simp [coveredNeighborCode, h]
    | inr b => simp [coveredNeighborCode]
  ext x
  exact (hc (S.coveredLabel a x)).trans (S.coveredLabel_eq_inl_iff a r x)

/-- The merged independent class consists exactly of the original atomic
points outside B. Under the stated exhaustion these are A and optional C. -/
theorem coveredNeighborLabel_merged_fiber (S : SelectedHighLowStructure W m) (r a : S.I) :
    S.coveredNeighborLabel r a ⁻¹' {some 1} = {x | S.ρ x ∈ S.I ∧ S.ρ x ≠ r.val} := by
  have hc (i : S.I ⊕ Bool) : S.coveredNeighborCode r i = some 1 ↔
      ∃ u : S.I, u ≠ r ∧ i = Sum.inl u := by
    cases i with
    | inl u => by_cases h : u = r <;> simp [coveredNeighborCode, h]
    | inr b => simp [coveredNeighborCode]
  ext x
  change S.coveredNeighborCode r (S.coveredLabel a x) = some 1 ↔ _
  rw [hc]
  constructor
  · rintro ⟨u, hu, hx⟩
    have he := (S.coveredLabel_eq_inl_iff a u x).mp hx
    exact ⟨he.symm ▸ u.property, fun h => hu (Subtype.ext (he.symm.trans h))⟩
  · rintro ⟨hin, hne⟩
    let u : S.I := ⟨S.ρ x, hin⟩
    refine ⟨u, fun h => hne (congrArg Subtype.val h), ?_⟩
    exact (S.coveredLabel_eq_inl_iff a u x).mpr rfl

/-- Only the actual original diffuse remainder is assigned the dust marker. -/
theorem coveredNeighborLabel_dust_fiber (S : SelectedHighLowStructure W m) (r a : S.I) :
    S.coveredNeighborLabel r a ⁻¹' {none} = S.D := by
  have hc (i : S.I ⊕ Bool) : S.coveredNeighborCode r i = none ↔ ∃ b, i = Sum.inr b := by
    cases i <;> simp [coveredNeighborCode]
  ext x
  change S.coveredNeighborCode r (S.coveredLabel a x) = none ↔ x ∈ S.D
  rw [hc]
  simp [S.coveredLabel_eq_inr_iff]

private theorem neighbor_part_ne_iff (S : SelectedHighLowStructure W m) (r a : S.I)
    {x y : Ω} (hxy : x ≠ y) :
    S.coveredNeighborPart r a x ≠ S.coveredNeighborPart r a y ↔
      S.coveredNeighborLabel r a x ≠ S.coveredNeighborLabel r a y ∨
        S.coveredNeighborLabel r a x = none := by
  cases hx : S.coveredNeighborLabel r a x <;>
    cases hy : S.coveredNeighborLabel r a y <;>
      simp [coveredNeighborPart, hx, hy, hxy]

private theorem coveredGraph_eq_neighborCode (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z)
    (i j : S.I ⊕ Bool) (hi : i ≠ Sum.inr false) (hj : j ≠ Sum.inr false) :
    (if S.coveredGraph r a i j = true then (1 : ℝ) else 0) =
      if S.coveredNeighborCode r i ≠ S.coveredNeighborCode r j ∨
        S.coveredNeighborCode r i = none then 1 else 0 := by
  cases i with
  | inl u =>
    cases j with
    | inl v =>
      rcases hatoms u with hu | hu | hu <;>
        rcases hatoms v with hv | hv | hv <;>
          rw [hu, hv] <;> by_cases hzr : z = r <;> by_cases hza : z = a <;>
            simp_all [coveredGraph, coveredNeighborCode] <;> first
            | exact Ne.symm hra
            | exact Ne.symm hzr
    | inr b => cases b <;> simp_all [coveredGraph, coveredNeighborCode]
  | inr b =>
    cases j with
    | inl u => cases b <;> simp_all [coveredGraph, coveredNeighborCode]
    | inr c => cases b <;> cases c <;> simp_all [coveredGraph, coveredNeighborCode]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- E-nullity makes the original A and optional C graph twins. The actual
covered topology and atom exhaustion give the two-class/dust support. -/
theorem ae_coveredNeighbor_support (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if S.coveredNeighborLabel r a p.1 ≠ S.coveredNeighborLabel r a p.2 ∨
        S.coveredNeighborLabel r a p.1 = none then 1 else 0 := by
  have hn : ∀ᵐ x ∂μ, S.coveredLabel a x ≠ Sum.inr false := by
    apply measure_eq_zero_iff_ae_notMem.mp
    change μ (S.coveredLabel a ⁻¹' {Sum.inr false}) = 0
    rw [S.coveredLabel_fiber_false]
    exact hE
  filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
    Measure.quasiMeasurePreserving_fst.ae hn,
    Measure.quasiMeasurePreserving_snd.ae hn] with p hp hi hj
  change adjacencyKernel W p.1 p.2 = _
  rw [hp]
  exact S.coveredGraph_eq_neighborCode r a z hpair.1 hatoms _ _ hi hj

/-- The actual singleton-dust partition has conditional color adjacency
exactly on different partition classes, on the same original law. -/
theorem ae_coveredNeighbor_partition_support (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ w ∂W.kernel p,
      CappedColor.adjacency w = 1 ↔
        S.coveredNeighborPart r a p.1 ≠ S.coveredNeighborPart r a p.2 := by
  filter_upwards [S.ae_coveredNeighbor_support r a z hW hd hgap hpair hzero hE hatoms,
    HalfGraphMultipartite.ae_coordinates_ne (μ := μ)] with p hp hne
  simp only [← S.neighbor_part_ne_iff r a hne] at hp
  by_cases hpart : S.coveredNeighborPart r a p.1 ≠ S.coveredNeighborPart r a p.2
  · rw [ite_eq_left hpart] at hp
    filter_upwards [ae_adjacency_one_of_moment_one W p hp] with w hw
    exact ⟨fun _ => hpart, fun _ => hw⟩
  · rw [ite_eq_right hpart] at hp
    filter_upwards [ae_adjacency_zero_of_moment_zero W p hp] with w hw
    exact iff_of_false (by simp [hw]) hpart

/-- The original E-null zero/one-exterior model is bounded by the actual
multipartite theorem after constructing its genuine measurable partition. -/
theorem coveredNeighbor_objective_le_benchmark
    (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    objective W ≤ benchmark (density W) :=
  objective_le_benchmark_of_partition_support W hW.full (S.coveredNeighborPart r a)
    (S.ae_coveredNeighbor_partition_support r a z hW hd hgap hpair hzero hE hatoms)

/-- Zero/one-C atom exhaustion and E-nullity are incompatible with
the same original full stationary optimum's genuine benchmark excess. -/
theorem not_coveredNeighbor_boundary (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) : False := by
  have h := S.coveredNeighbor_objective_le_benchmark r a z hW hd hgap hpair hzero hE hatoms
  rw [hW.objective_eq, hW.density_eq] at h
  exact (not_le_of_gt hgap) h

end Erdos1017.CappedModel.SelectedHighLowStructure

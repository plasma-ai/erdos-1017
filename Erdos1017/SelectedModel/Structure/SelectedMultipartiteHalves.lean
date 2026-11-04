module

public import Erdos1017.SelectedModel.Structure.SelectedHighLowClassification
public import Erdos1017.SelectedModel.Structure.HalfGraphMultipartiteSupport
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteLawRestriction

/-!
# Multipartite structure of the selected halves

This module defines the two selected halves (high plus neutral, low plus
neutral) with collapsed and singleton-dust part labels; a probability law or
integrable reweighting supported on a half inherits multipartite color support
and is bounded by the benchmark, so neither ordered class is null.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

local instance : MeasurableSpace (Lp ℝ 2 μ) := borel _
local instance : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

namespace SelectedHighLowStructure

variable {W : Model Ω μ} {m : ℝ}

/-- The two actual selected halves: true is HIGH plus neutral, and false
is LOW plus neutral. Both retain the same original whole-row classes. -/
def half (S : SelectedHighLowStructure W m) (b : Bool) : Set Ω :=
  if b then S.H ∪ S.N else S.L ∪ S.N

/-- Original atomic labels with one collapsed marker for clique dust. -/
def collapsedPartLabel (S : SelectedHighLowStructure W m) : Ω → Option S.I :=
  HalfGraphMultipartite.collapsedLabel S.ρ S.I

/-- Genuine multipartite labels: each diffuse point keeps its own singleton. -/
def atomicDustPartLabel (S : SelectedHighLowStructure W m) : Ω → S.I ⊕ Ω :=
  HalfGraphMultipartite.atomicDustLabel S.ρ S.I

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_half (S : SelectedHighLowStructure W m) (b : Bool) :
    MeasurableSet (S.half b) := by
  cases b
  · exact S.hpartition.2.1.union S.hpartition.2.2.1
  · exact S.hpartition.1.union S.hpartition.2.2.1

theorem measurable_collapsedPartLabel (S : SelectedHighLowStructure W m) :
    @Measurable Ω (Option S.I) _ ⊤ S.collapsedPartLabel :=
  HalfGraphMultipartite.measurable_collapsedLabel S.ρ S.hρ.measurable S.I S.hI

theorem measurable_atomicDustPartLabel (S : SelectedHighLowStructure W m) :
    Measurable S.atomicDustPartLabel :=
  HalfGraphMultipartite.measurable_atomicDustLabel S.ρ S.hρ.measurable S.I S.hI

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The selected structure itself supplies every independence, zero-coverage
and crossing premise for collapsed clique-dust support on either half. -/
theorem ae_collapsed_half_support (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool) :
    ∀ᵐ p ∂(μ.restrict (S.half b)).prod (μ.restrict (S.half b)),
      W.moment CappedColor.adjacency p =
        if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
        then 1 else 0 := by
  have hcross : ∀ᵐ p ∂μ.prod μ, p ∈ actualZeroRelation W m S.ρ →
      (p.1 ∈ S.H ∧ p.2 ∈ S.L) ∨ (p.2 ∈ S.H ∧ p.1 ∈ S.L) :=
    S.hrelation.mono (fun _ hp hz => (hp hz).elim
      (fun h => Or.inl ⟨h.1, h.2.1⟩) (fun h => Or.inr ⟨h.1, h.2.1⟩))
  have hs := HalfGraphMultipartite.ae_collapsed_support_on_halves
    (shiftedKernel W m) (adjacencyKernel W) S.ρ S.hρ.measurable S.I S.hI
    (fun r hr => (S.hfibers r hr).2.2.1)
    (hW.moment_mem.mono (fun _ hp => hp.1)) (hW.strict_gap_structure hd hgap).strict_support
    (actualZeroRelation W m S.ρ) S.hcoverage S.H S.L S.N
    S.hpartition.1 S.hpartition.2.1 S.hpartition.2.2.1
    S.hpartition.2.2.2.2.1 S.hpartition.2.2.2.2.2.1 S.hpartition.2.2.2.2.2.2 hcross
  cases b
  · filter_upwards [hs.2] with p hp
    split_ifs at hp ⊢ <;> first | exact hp | contradiction
  · filter_upwards [hs.1] with p hp
    split_ifs at hp ⊢ <;> first | exact hp | contradiction

/-- The derived null physical diagonal makes the genuine atomic/singleton
labels an ordinary multipartite support on either actual selected half. -/
theorem ae_atomicDust_half_support (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool) :
    ∀ᵐ p ∂(μ.restrict (S.half b)).prod (μ.restrict (S.half b)),
      W.moment CappedColor.adjacency p =
        if S.atomicDustPartLabel p.1 ≠ S.atomicDustPartLabel p.2 then 1 else 0 := by
  have hcollapsed := S.ae_collapsed_half_support hW hd hgap b
  have hs := HalfGraphMultipartite.ae_atomicDust_support_on_set (μ := μ)
    (adjacencyKernel W) S.ρ S.I (S.half b)
    (by
      filter_upwards [hcollapsed] with p hp
      split_ifs at hp ⊢ <;> first | exact hp | contradiction)
  filter_upwards [hs] with p hp
  split_ifs at hp ⊢ <;> first | exact hp | contradiction

/-- A probability law supported on either original half inherits actual
conditional clique-dust color support, including every dust-dust pair. -/
theorem ae_collapsed_color_support_of_half_ac (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool)
    {ν : Measure Ω} [IsProbabilityMeasure ν] (hν : ν ≪ μ.restrict (S.half b)) :
    ∀ᵐ p ∂ν.prod ν, ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔
      S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none :=
  ae_color_adjacency_of_restricted_moment W (S.half b) hν _
    (S.ae_collapsed_half_support hW hd hgap b)

/-- The same actual new law has genuine conditional multipartite support;
no conditional color assertion is supplied as a premise. -/
theorem ae_atomicDust_color_support_of_half_ac (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool)
    {ν : Measure Ω} [IsProbabilityMeasure ν] (hν : ν ≪ μ.restrict (S.half b)) :
    ∀ᵐ p ∂ν.prod ν, ∀ᵐ z ∂W.kernel p, CappedColor.adjacency z = 1 ↔
      S.atomicDustPartLabel p.1 ≠ S.atomicDustPartLabel p.2 :=
  ae_color_adjacency_of_restricted_moment W (S.half b) hν _
    (S.ae_atomicDust_half_support hW hd hgap b)

/-- Full feasibility and the derived genuine labels bound the actual
unchanged kernel at the density of any probability law supported on a half. -/
theorem objective_changeMeasure_le_benchmark_of_half_ac (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool)
    {ν : Measure Ω} [IsProbabilityMeasure ν] (hν : ν ≪ μ.restrict (S.half b)) :
    objective (W.changeMeasure (hν.trans Measure.absolutelyContinuous_restrict)) ≤
      benchmark (density (W.changeMeasure (hν.trans Measure.absolutelyContinuous_restrict))) :=
  objective_changeMeasure_le_benchmark_of_restricted_partition W hW.full (S.half b) hν
    S.atomicDustPartLabel (by
      filter_upwards [S.ae_atomicDust_half_support hW hd hgap b] with p hp
      split_ifs at hp ⊢ <;> exact hp)

/-- Every actual integrable probability weight supported on a selected
half inherits its conditional collapsed clique-dust support. -/
theorem ae_collapsed_color_support_integrableReweight (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool)
    (w : Ω → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw1 : (∫ x, w x ∂μ) = 1) (hzero : ∀ᵐ x ∂μ, x ∉ S.half b → w x = 0) :
    ∀ᵐ p ∂(weightedMeasure (μ := μ) w).prod (weightedMeasure (μ := μ) w),
      ∀ᵐ z ∂(integrableReweight W w hw hw0 hw1).kernel p, CappedColor.adjacency z = 1 ↔
        S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none := by
  let := weightedMeasure_probability hw hw0 hw1
  exact S.ae_collapsed_color_support_of_half_ac hW hd hgap b
    (weightedMeasure_ac_restrict_of_ae_zero w (S.half b) (S.measurableSet_half b) hzero)

/-- Actual probability reweighting on a half also has genuine multipartite
labels, including separate labels for all original diffuse points. -/
theorem ae_atomicDust_color_support_integrableReweight (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool)
    (w : Ω → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw1 : (∫ x, w x ∂μ) = 1) (hzero : ∀ᵐ x ∂μ, x ∉ S.half b → w x = 0) :
    ∀ᵐ p ∂(weightedMeasure (μ := μ) w).prod (weightedMeasure (μ := μ) w),
      ∀ᵐ z ∂(integrableReweight W w hw hw0 hw1).kernel p, CappedColor.adjacency z = 1 ↔
        S.atomicDustPartLabel p.1 ≠ S.atomicDustPartLabel p.2 := by
  let := weightedMeasure_probability hw hw0 hw1
  exact S.ae_atomicDust_color_support_of_half_ac hW hd hgap b
    (weightedMeasure_ac_restrict_of_ae_zero w (S.half b) (S.measurableSet_half b) hzero)

/-- The unchanged fully feasible model under every such actual reweighting
is bounded by the benchmark at its actual new density. -/
theorem objective_integrableReweight_le_benchmark_of_half (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : Bool)
    (w : Ω → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hw1 : (∫ x, w x ∂μ) = 1) (hzero : ∀ᵐ x ∂μ, x ∉ S.half b → w x = 0) :
    objective (integrableReweight W w hw hw0 hw1) ≤
      benchmark (density (integrableReweight W w hw hw0 hw1)) := by
  let := weightedMeasure_probability hw hw0 hw1
  exact S.objective_changeMeasure_le_benchmark_of_half_ac hW hd hgap b
    (weightedMeasure_ac_restrict_of_ae_zero w (S.half b) (S.measurableSet_half b) hzero)

/-- Neither selected ordered class can be null. Otherwise the original
probability law is concentrated on the opposite multipartite half and its
unchanged full-feasible model contradicts the original strict benchmark gap. -/
theorem high_low_mass_pos (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < μ S.H ∧ 0 < μ S.L := by
  have hcover (x : Ω) : x ∈ S.H ∨ x ∈ S.L ∨ x ∈ S.N := by
    have hx : x ∈ S.H ∪ S.L ∪ S.N := by rw [S.hpartition.2.2.2.1]; exact mem_univ x
    rcases hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  have hpos (b : Bool) : 0 < μ (if b then S.H else S.L) := by
    by_contra hnot
    have hnull : μ (if b then S.H else S.L) = 0 := le_antisymm (le_of_not_gt hnot) zero_le
    have hconcentrated : ∀ᵐ x ∂μ, x ∈ S.half (!b) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
      have hc := hcover x
      cases b
      · change x ∉ S.L at hx
        exact hc.elim (fun h => Or.inl h) (fun h => h.elim (fun h => (hx h).elim) Or.inr)
      · change x ∉ S.H at hx
        exact hc.elim (fun h => (hx h).elim) (fun h => h)
    have hac : μ ≪ μ.restrict (S.half (!b)) := by
      rw [Measure.restrict_eq_self_of_ae_mem hconcentrated]
    have hbound := S.objective_changeMeasure_le_benchmark_of_half_ac hW hd hgap (!b) hac
    change objective W ≤ benchmark (density W) at hbound
    rw [hW.objective_eq, hW.density_eq] at hbound
    exact (not_le_of_gt hgap) hbound
  exact ⟨hpos true, hpos false⟩

end SelectedHighLowStructure

end Erdos1017.CappedModel

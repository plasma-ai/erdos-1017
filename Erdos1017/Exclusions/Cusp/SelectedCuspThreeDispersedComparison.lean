module

public import Erdos1017.Exclusions.Cusp.DispersedMissingEditValues
public import Erdos1017.Exclusions.Cusp.MarkedMissingEditVariation
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeNeighborhoodTrace

/-!
# Dispersed-edit comparison at the low-slope third cusp

The dispersed edit of the entire original missing region, under the same law, is
compared at its changed density to the selected global excess maximum; the
low-slope third-cusp value equals its reciprocal split value, and the edit gives
the edited-value input of the dispersed body ratio.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

/-- The actual dispersed edit of the entire original missing region, under
the same original law, is compared at its exact changed density to the same
selected global excess maximum. It deletes every missing-region edge, fills
every missing region-neighborhood pair at zero charge and pays the entire
original positive neighborhood body. No body sign or edited test is assumed. -/
theorem cusp_three_dispersed_edit_excess (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    let J := S.cuspThreeMissingRegion i
    let N := S.rootNeighborhood i
    let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
    let v := ∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
    let YJJ := ∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂μ.prod μ
    let L := ∫ p : Ω × Ω, IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
      Nᶜ p.1 p.2 ∂μ.prod μ
    c - YJJ / 2 - L / 2 - benchmark (d + v - z) ≤ c - benchmark d := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let J := S.cuspThreeMissingRegion i
  let N := S.rootNeighborhood i
  let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
  let v := ∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  let YJJ := ∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂μ.prod μ
  let L := ∫ p : Ω × Ω, IndependentAtomCopy.positiveBody Y Nᶜ p.1 p.2 ∂μ.prod μ
  have hstructure := hW.strict_gap_structure hd hgap
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hJ : MeasurableSet J := S.measurableSet_cuspThreeMissingRegion i
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood i
  have hdis : Disjoint J N := disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  have hAsym := PhysicalRepresentative.adjacency_symm W m
  have hYsym := PhysicalRepresentative.charge_symm W m
  -- Original missing incidences from the region outside the neighborhood lie in the peak.
  have hmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∉ J ∪ N → A p.1 p.2 = false := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (S.ae_root_adjacency i hW hd hgap)] with p hp hx hy
    have hi : S.ρ p.2 = i.val := by
      by_contra hi
      exact hy (Or.inl ⟨hi, fun hn => hy (Or.inr hn)⟩)
    apply Bool.eq_false_iff.mpr
    intro ha
    have ha' : A p.2 p.1 = true := (hAsym _ _).trans ha
    exact hx.2 ((hp hi).mp ha')
  have hfull := PhysicalRepresentative.full_feasible W hW.full m hstructure.strict_support
    hW.deterministic
  have hArep := PhysicalRepresentative.adjacency_moment_ae_eq W m hstructure.strict_support
  have hYrep := PhysicalRepresentative.charge_ae_eq W m hstructure.strict_support
  have hvalues := DispersedMissingEdit.objective_le_densityLimit_values A Y J N hA hY hJ hN hdis
    hAsym hYsym 3 (by norm_num) (PhysicalRepresentative.charge_bound W m)
    (PhysicalRepresentative.charge_zero_of_nonedge W m) hmiss hfull μ
    Measure.AbsolutelyContinuous.rfl
  -- Identify every edited density and value term with the original integrals.
  have hdold := (PhysicalRepresentative.density_eq W m hstructure.strict_support).trans
    hW.density_eq
  have hcold := (PhysicalRepresentative.objective_eq W m hstructure.strict_support).trans
    hW.objective_eq
  have hcross : (∫ p, (J ×ˢ N).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) p
      ∂μ.prod μ) = v := by
    rw [integral_indicator (hJ.prod hN)]
    apply integral_congr_ae
    exact (ae_restrict_of_ae hArep).mono (fun _ hp => congrArg (fun x : ℝ => 1 - x) hp.symm)
  have hsquare : (∫ p, (J ×ˢ J).indicator (fun p => if A p.1 p.2 = true then 1 else 0) p
      ∂μ.prod μ) / 2 = z := by
    rw [integral_indicator (hJ.prod hJ)]
    congr 1
    exact integral_congr_ae ((ae_restrict_of_ae hArep).mono (fun _ hp => hp.symm))
  have hcharge : (∫ p, (J ×ˢ J).indicator (Function.uncurry Y) p ∂μ.prod μ) = YJJ := by
    rw [integral_indicator (hJ.prod hJ)]
    exact integral_congr_ae (ae_restrict_of_ae hYrep)
  have hbody : (∫ p, (N ×ˢ N).indicator (fun p => max (Y p.1 p.2) 0) p ∂μ.prod μ) = L := by
    congr 1
    funext p
    by_cases hx : p.1 ∈ N <;> by_cases hy : p.2 ∈ N <;>
      simp [IndependentAtomCopy.positiveBody, Set.indicator, hx, hy]
  rw [hcold, hcross, hsquare, hcharge, hbody, hdold] at hvalues
  -- The same exact edited density is attained by an actual fully feasible model.
  have hdenmem := FiniteCappedSamplingCost.physicalDensity_mem_Icc (μ := μ)
    (DispersedMissingEdit.adjacency A J N) (DispersedMissingEdit.adjacency_symm A J N hAsym)
    (DispersedMissingEdit.measurable_adjacency A J N hA hJ hN)
  rw [DispersedMissingEdit.density_eq A J N hA hJ hN hdis hAsym, hdold, hcross, hsquare]
    at hdenmem
  obtain ⟨V, hV, hdV, hcV⟩ := exists_fullFeasible_at_density (μ := μ) _ hdenmem
  have hbound := hglobal μ V hV
  rw [hcV, hdV, hW.objective_eq, hW.density_eq] at hbound
  change c - YJJ / 2 - L / 2 - benchmark (d + v - z) ≤ c - benchmark d
  linarith only [hvalues, hbound]

/-- The low-slope third cusp value is exactly its reciprocal split value. -/
theorem benchmark_cusp_three : benchmark (4 / 9) = 2 / 27 := by
  have hband : (4 / 9 : ℝ) ∈ Ioo (1 / 2 - Benchmark.epsilonStar) (1 / 2) := by
    have h := Benchmark.split_cusp_mem_band 3 (by norm_num)
    norm_num at h ⊢
    exact h
  have hsqrt : Real.sqrt (1 - 2 * (4 / 9 : ℝ)) = 1 / ((3 : ℕ) : ℝ) := by
    rw [show 1 - 2 * (4 / 9 : ℝ) = (1 / ((3 : ℕ) : ℝ)) ^ 2 by norm_num,
      Real.sqrt_sq (by positivity)]
  rw [(Benchmark.benchmark_split_eventually hband).eq_of_nhds, hsqrt,
    Benchmark.splitValue_reciprocal 3 (by norm_num)]
  norm_num

/-- At the low-slope third cusp the actual dispersed edit gives the
edited-value input of the dispersed body ratio. -/
theorem cusp_three_dispersed_edit_value (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    let J := S.cuspThreeMissingRegion i
    let N := S.rootNeighborhood i
    let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
    let v := ∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
    let YJJ := ∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂μ.prod μ
    let L := ∫ p : Ω × Ω, IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
      Nᶜ p.1 p.2 ∂μ.prod μ
    2 / 27 - YJJ / 2 - L / 2 ≤ benchmark (4 / 9 + v - z) := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hexcess := S.cusp_three_dispersed_edit_excess i hW hd hgap hglobal
  dsimp only at hexcess ⊢
  rw [hdk, benchmark_cusp_three] at hexcess
  linarith only [hexcess]

end Erdos1017.CappedModel.SelectedHighLowStructure

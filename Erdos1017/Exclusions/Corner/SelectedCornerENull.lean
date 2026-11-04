module

public import Erdos1017.Exclusions.Common.Covered.CoveredHalfSlopeBoundaryGates
public import Erdos1017.Exclusions.Corner.SelectedCornerAtomGuards
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoNeighborCounts
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNeighborMultipartite
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredBoundaryRepeat
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNullDiffuseDensity

/-!
# Exclusion of the `E`-null corner zero-body boundary

The `E`-null saturated zero-body boundary at the corner is excluded, without a
supplied `R`-positivity or exterior-cardinality certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The original E-null corner saturated zero-body case is excluded
when exactly two exterior atoms remain and R has positive mass. The
actual entry and every active child dual's own one-sided corner slope
are constructed. -/
private theorem no_corner_zero_body_two_neighbor
    (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) : False := by
  obtain ⟨hy, V, hV, hmom, hphysical, _⟩ :=
    S.exists_covered_two_neighbor_entry r a z1 z2 hW hd hgap hpair hzero hE hR
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hslope (U : Model Ω μ) (m' : ℝ) (hU : FullStationaryClass d c U m') :
      1 / 2 < -m' := by
    have hglobalU : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
        FullFeasible T → objective T - benchmark (density T) ≤
          objective U - benchmark (density U) := by
      intro ν _ T hT
      simpa only [hW.objective_eq, hW.density_eq, hU.objective_eq, hU.density_eq] using
        hglobal ν T hT
    have hell := (hU.corner_contact_parameters hd hgap he heq hglobalU).1
    linarith [hell.1]
  have hD : 0 < μ S.D := hR.trans_le (measure_mono inter_subset_left)
  exact CoveredTwoExteriorNeighbor.no_optimum_of_own_half_slope hV hd hgap hslope hphysical
    (S.coveredTwoBoundaryLabel r a z1) (S.measurable_coveredTwoBoundaryLabel r a z1)
    (S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1
      hz1r hz1a hz2r hz2a hz12 hatoms hD)
    (S.coveredTwoBoundaryEntry r a z1) hy hmom

/-- The original E-null/R-positive corner saturated zero-body case is
excluded without any supplied bound on the number of exterior atoms. -/
private theorem no_corner_zero_body_E_null_of_R_positive
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a)) : False := by
  obtain ⟨hell, _, _, hratio, _⟩ :=
    S.corner_atom_contact_guards r hW hd hgap he heq hglobal
  have hD : 0 < μ S.D := hR.trans_le (measure_mono inter_subset_left)
  by_cases hfirst : ∃ z1 : S.I, z1 ≠ r ∧ z1 ≠ a
  · obtain ⟨z1, hz1r, hz1a⟩ := hfirst
    by_cases hsecond : ∃ z2 : S.I, z2 ≠ r ∧ z2 ≠ a ∧ z2 ≠ z1
    · obtain ⟨z2, hz2r, hz2a, hz21⟩ := hsecond
      have hatoms := S.covered_boundary_atoms_eq_four true r a z1 z2 hW hd hgap hpair
        hzero hD (by simpa using hE) hell.1 hratio
        (Ne.symm hz1r) (Ne.symm hz1a) (Ne.symm hz2r) (Ne.symm hz2a) (Ne.symm hz21)
      exact S.no_corner_zero_body_two_neighbor r a z1 z2 hW hd hgap he heq hglobal
        hpair hzero hE hR hz1r hz1a hz2r hz2a (Ne.symm hz21) hatoms
    · have hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 := by
        intro u
        by_cases hur : u = r
        · exact Or.inl hur
        by_cases hua : u = a
        · exact Or.inr (Or.inl hua)
        have huz : u = z1 := by
          by_contra hn
          exact hsecond ⟨u, hur, hua, hn⟩
        exact Or.inr (Or.inr huz)
      exact S.not_coveredNeighbor_boundary r a z1 hW hd hgap hpair hzero hE hatoms
  · have hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = r := by
      intro u
      by_cases hur : u = r
      · exact Or.inl hur
      have hua : u = a := by
        by_contra hn
        exact hfirst ⟨u, hur, hn⟩
      exact Or.inr (Or.inl hua)
    exact S.not_coveredNeighbor_boundary r a r hW hd hgap hpair hzero hE hatoms

/-- The actual E-null corner saturated zero-body boundary is excluded
without a supplied R-positivity or exterior-cardinality certificate. -/
theorem no_corner_zero_body_E_null
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0) : False := by
  by_cases hR : μ (S.D ∩ S.rootNeighborhood a) = 0
  · obtain ⟨hell, _, _, hratio, _⟩ :=
      S.corner_atom_contact_guards r hW hd hgap he heq hglobal
    have hD : μ S.D = 0 := by
      have hparts : S.D = (S.D ∩ S.rootNeighborhood a) ∪
          (S.D \ S.rootNeighborhood a) := (inter_union_sdiff _ _).symm
      apply le_antisymm _ zero_le
      calc
        μ S.D = μ ((S.D ∩ S.rootNeighborhood a) ∪ (S.D \ S.rootNeighborhood a)) :=
          congrArg μ hparts
        _ ≤ μ (S.D ∩ S.rootNeighborhood a) + μ (S.D \ S.rootNeighborhood a) :=
          measure_union_le _ _
        _ = 0 := by rw [hR, hE, add_zero]
    exact S.not_covered_null_diffuse r a hW hd hgap hpair hell.1 hzero hD hratio
  · exact S.no_corner_zero_body_E_null_of_R_positive r a hW hd hgap he heq hglobal
      hpair hzero hE (pos_iff_ne_zero.mpr hR)

end Erdos1017.CappedModel.SelectedHighLowStructure

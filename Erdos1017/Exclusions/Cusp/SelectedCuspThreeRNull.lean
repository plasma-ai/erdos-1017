module

public import Erdos1017.Exclusions.Common.Covered.CoveredHalfSlopeBoundaryGates
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeZeroExterior
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredOneExteriorCounts
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoExteriorCounts
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeENull

/-!
# The `R`-null saturated zero-body case at the third cusp

The `R`-null third-cusp saturated zero-body boundary is excluded, with the
`E`-null and `E`-positive cases derived internally: with positive `E` mass,
exactly one or exactly two remaining exterior atoms are ruled out first, then
any number of them.
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

/-- The original R-null third-cusp saturated zero-body case is excluded
when exactly one exterior atom remains and E has positive mass. The
actual entry and every optimal child dual's own data are constructed. -/
theorem no_cusp_three_zero_body_one_exterior
    (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  obtain ⟨hy, V, hV, hmom, hphysical, _⟩ :=
    S.exists_covered_one_exterior_entry r a z hW hd hgap hpair hzero hR hE hzr hza hatoms
  have hslope (U : Model Ω μ) (m' : ℝ) (hU : FullStationaryClass d c U m') :
      1 / 2 < -m' := by
    have hglobalU : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
        FullFeasible T → objective T - benchmark (density T) ≤
          objective U - benchmark (density U) := by
      intro ν _ T hT
      simpa only [hW.objective_eq, hW.density_eq, hU.objective_eq, hU.density_eq] using
        hglobal ν T hT
    obtain ⟨_, _, hell, _⟩ := hU.cusp_contact_parameters 3 (by omega)
      (by norm_num; exact hdk) hgap hglobalU
    linarith [hell.1]
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  exact CoveredOneExterior.no_optimum_of_own_half_slope hV hd hgap hslope hphysical
    (S.coveredBoundaryLabel r a) (S.measurable_coveredBoundaryLabel r a)
    (S.coveredBoundaryLabel_fibers_positive r a z hpair.1 hzr hza hatoms hD)
    (S.coveredBoundaryEntry r a) hy hmom

/-- The original R-null third-cusp saturated zero-body case is excluded
when exactly two exterior atoms remain and E has positive mass. The
actual entry and every optimal child dual's own data are constructed. -/
theorem no_cusp_three_zero_body_two_exterior
    (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  obtain ⟨hy, V, hV, hmom, hphysical, _⟩ :=
    S.exists_covered_two_exterior_entry r a z1 z2 hW hd hgap hpair hzero hR hE
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hslope (U : Model Ω μ) (m' : ℝ) (hU : FullStationaryClass d c U m') :
      1 / 2 < -m' := by
    have hglobalU : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
        FullFeasible T → objective T - benchmark (density T) ≤
          objective U - benchmark (density U) := by
      intro ν _ T hT
      simpa only [hW.objective_eq, hW.density_eq, hU.objective_eq, hU.density_eq] using
        hglobal ν T hT
    obtain ⟨_, _, hell, _⟩ := hU.cusp_contact_parameters 3 (by omega)
      (by norm_num; exact hdk) hgap hglobalU
    linarith [hell.1]
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  exact CoveredTwoExterior.no_optimum_of_own_half_slope hV hd hgap hslope hphysical
    (S.coveredTwoBoundaryLabel r a z1) (S.measurable_coveredTwoBoundaryLabel r a z1)
    (S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1
      hz1r hz1a hz2r hz2a hz12 hatoms hD)
    (S.coveredTwoBoundaryEntry r a z1) hy hmom

/-- The original R-null/E-positive third-cusp saturated zero-body case is
excluded without any supplied bound on the number of exterior atoms. -/
theorem no_cusp_three_zero_body_R_null_of_E_positive
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  obtain ⟨_, hell, _, _, _, _, hratio, _⟩ :=
    S.cusp_atom_contact_guards r hW 3 (by omega) (by norm_num; exact hdk) hgap hglobal
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  by_cases hfirst : ∃ z1 : S.I, z1 ≠ r ∧ z1 ≠ a
  · obtain ⟨z1, hz1r, hz1a⟩ := hfirst
    by_cases hsecond : ∃ z2 : S.I, z2 ≠ r ∧ z2 ≠ a ∧ z2 ≠ z1
    · obtain ⟨z2, hz2r, hz2a, hz21⟩ := hsecond
      have hatoms := S.covered_boundary_atoms_eq_four false r a z1 z2 hW hd hgap hpair
        hzero hD (by simpa using hR) (by linarith [hell.1]) hratio
        (Ne.symm hz1r) (Ne.symm hz1a) (Ne.symm hz2r) (Ne.symm hz2a) (Ne.symm hz21)
      exact S.no_cusp_three_zero_body_two_exterior r a z1 z2 hW hdk hgap hglobal
        hpair hzero hR hE hz1r hz1a hz2r hz2a (Ne.symm hz21) hatoms
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
      exact S.no_cusp_three_zero_body_one_exterior r a z1 hW hdk hgap hglobal
        hpair hzero hR hE hz1r hz1a hatoms
  · have hatoms : ∀ u : S.I, u = r ∨ u = a := by
      intro u
      by_cases hur : u = r
      · exact Or.inl hur
      have hua : u = a := by
        by_contra hn
        exact hfirst ⟨u, hur, hn⟩
      exact Or.inr hua
    exact S.no_cusp_three_zero_body_zero_exterior r a hW hdk hgap hglobal
      hpair hzero hR hE hatoms

/-- The original R-null third-cusp saturated zero-body boundary is excluded
with both E-null and E-positive cases derived internally. -/
theorem no_cusp_three_zero_body_R_null
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0) : False := by
  by_cases hE : μ (S.D \ S.rootNeighborhood a) = 0
  · exact S.no_cusp_three_zero_body_E_null r a hW hdk hgap hglobal
      hpair hzero hE
  · exact S.no_cusp_three_zero_body_R_null_of_E_positive r a hW hdk hgap hglobal
      hpair hzero hR (pos_iff_ne_zero.mpr hE)

end Erdos1017.CappedModel.SelectedHighLowStructure

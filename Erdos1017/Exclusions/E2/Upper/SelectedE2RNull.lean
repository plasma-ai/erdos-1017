module

public import Erdos1017.Exclusions.E2.Upper.CoveredE2ExteriorGates
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredZeroExteriorCounts
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredOneExteriorCounts
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoExteriorCounts
public import Erdos1017.Exclusions.E2.Upper.SelectedE2ENull

/-!
# `R`-null zero-body case at the `E₂` contact

The `R`-null `E₂` saturated zero-body boundary is excluded with both `E`-null
and `E`-positive cases derived internally (`no_e2_zero_body_R_null`): the
zero-exterior case by an explicit constructed optimum, the one- and two-exterior
cases with positive `E`, and then positive `E` without any bound on the number
of exterior atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

/-- An actual one-head integer contact with own slope between one half
and one must use the second count interval. -/
private theorem integer_contact_eq_two_of_penalty_lt_one {j : ℕ} {b e ell : ℝ}
    (hj : 1 ≤ j) (hb : 0 < b)
    (hell : ell ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hfirst : ((j : ℝ) - 1) * b ≤ e)
    (hfloor : 2 / ((j : ℝ) * (j + 1)) < ell)
    (hrow : b * (1 - 2 / ((j : ℝ) + 1)) =
      e * (ell - 2 / ((j : ℝ) * (j + 1)))) : j = 2 := by
  have hjne : j ≠ 1 := by
    rintro rfl
    norm_num at hfloor
    linarith [hell.2]
  by_contra hne
  have hjthree : 3 ≤ j := by omega
  have hJ : (3 : ℝ) ≤ j := by exact_mod_cast hjthree
  have hJ0 : (0 : ℝ) < j := by linarith
  have hJ1 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hden : (0 : ℝ) < (j : ℝ) * (j + 1) := mul_pos hJ0 hJ1
  have hrow' : b * (j : ℝ) * (j - 1) =
      e * ((j : ℝ) * (j + 1) * ell - 2) := by
    have h := congrArg (fun x : ℝ => x * ((j : ℝ) * (j + 1))) hrow
    field_simp at h
    nlinarith only [h]
  have hcoef : (j : ℝ) < (j : ℝ) * (j + 1) * ell - 2 := by
    have hstrict := mul_lt_mul_of_pos_left hell.1 hden
    have hquad : (4 : ℝ) < (j : ℝ) * (j - 1) := by nlinarith [sq_nonneg ((j : ℝ) - 3)]
    nlinarith only [hstrict, hquad]
  have hleft : 0 < ((j : ℝ) - 1) * b := mul_pos (by linarith) hb
  have hbound := mul_le_mul_of_nonneg_right hfirst
    (show 0 ≤ (j : ℝ) * (j + 1) * ell - 2 by linarith)
  have hstrict := mul_lt_mul_of_pos_left hcoef hleft
  nlinarith only [hrow', hbound, hstrict]

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The actual zero-exterior R-null E2 boundary is excluded by its
constructed explicit optimum, that model's own contact multiplier and rows.
No scalar profile, count contact or new stationary record is assumed. -/
theorem no_e2_zero_body_zero_exterior
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hbenchmark : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    hdq ▸ LowerE2Scalar.contact_density_mem hq
  obtain ⟨j, hj, hlo, _, V, m', hV, hmom, _⟩ :=
    S.exists_covered_zero_explicit_optimum r a hW hd hgap hpair hzero hR hE hatoms
  let label := S.coveredZeroBoundaryLabel r a
  let B := μ.real (label ⁻¹' {1})
  let E := μ.real (label ⁻¹' {2})
  have hlabel := S.measurable_coveredZeroBoundaryLabel r a
  have hpos := S.coveredZeroBoundaryLabel_fibers_positive r a hpair.1 hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  obtain ⟨_, hB, hD⟩ := S.coveredZeroBoundaryLabel_fibers r a hpair.1 hatoms
  have hb : 0 < B := ENNReal.toReal_pos (hpos 1).ne' (measure_ne_top _ _)
  have hfirst : ((j : ℝ) - 1) * B ≤ E := by simpa only [B, E, label, hB, hD] using hlo
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  obtain ⟨hm, hell, _⟩ :=
    hV.e2_general_contact_parameters hq hdq hbenchmark hderiv hgap hglobalV
  have hfloor := CoveredZeroExterior.penalty_lt_own_multiplier hV hd hgap label hpos
    (CoveredZeroExterior.explicitDual j) hmom
  obtain ⟨hAE, _⟩ := CoveredZeroExterior.stationary_row_differences hV label hlabel hpos
    (CoveredZeroExterior.explicitDual j) hmom
  have hjtwo : j = 2 := integer_contact_eq_two_of_penalty_lt_one hj hb hell hfirst hfloor hAE
  subst j
  have hmult : (2 / 3 : ℝ) < LowerE2Scalar.multiplier q := by
    unfold LowerE2Scalar.multiplier
    apply (lt_div_iff₀ (by linarith [hq.1] : 0 < 2 + q)).mpr
    linarith [hq.2]
  have hstrong : (2 / 3 : ℝ) < -m' := by
    rw [hm, neg_neg]
    exact hmult
  have hBE : B ≤ E := by
    norm_num at hfirst
    exact hfirst
  have hEpos : 0 < E := hb.trans_le hBE
  have hprod := mul_pos hEpos (sub_pos.mpr hstrong)
  norm_num [CoveredZeroExterior.explicitDual] at hAE
  change B * (1 / 3) = E * (-m' - 1 / 3) at hAE
  nlinarith only [hAE, hBE, hprod]

/-- The original R-null E2 saturated zero-body case is excluded
when exactly one exterior atom remains and E has positive mass. The
actual entry and every optimal child dual's own data are constructed. -/
theorem no_e2_zero_body_one_exterior
    (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hbenchmark : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
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
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    hdq ▸ LowerE2Scalar.contact_density_mem hq
  obtain ⟨hy, V, hV, hmom, hphysical, _⟩ :=
    S.exists_covered_one_exterior_entry r a z hW hd hgap hpair hzero hR hE hzr hza hatoms
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  exact CoveredOneExterior.no_e2_one_exterior hV hd hgap hq hdq hbenchmark hderiv
    hglobalV hphysical
    (S.coveredBoundaryLabel r a) (S.measurable_coveredBoundaryLabel r a)
    (S.coveredBoundaryLabel_fibers_positive r a z hpair.1 hzr hza hatoms hD)
    (S.coveredBoundaryEntry r a) hy hmom

/-- The original R-null E2 saturated zero-body case is excluded
when exactly two exterior atoms remain and E has positive mass. The
actual entry and every optimal child dual's own data are constructed. -/
theorem no_e2_zero_body_two_exterior
    (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hbenchmark : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
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
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    hdq ▸ LowerE2Scalar.contact_density_mem hq
  obtain ⟨hy, V, hV, hmom, hphysical, _⟩ :=
    S.exists_covered_two_exterior_entry r a z1 z2 hW hd hgap hpair hzero hR hE
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  exact CoveredTwoExterior.no_e2_five_region hV hd hgap hq hdq hbenchmark hderiv
    hglobalV hphysical
    (S.coveredTwoBoundaryLabel r a z1) (S.measurable_coveredTwoBoundaryLabel r a z1)
    (S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1
      hz1r hz1a hz2r hz2a hz12 hatoms hD)
    (S.coveredTwoBoundaryEntry r a z1) hy hmom

/-- The original R-null/E-positive E2 saturated zero-body case is
excluded without any supplied bound on the number of exterior atoms. -/
theorem no_e2_zero_body_R_null_of_E_positive
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hbenchmark : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    hdq ▸ LowerE2Scalar.contact_density_mem hq
  obtain ⟨_, hell, _, _, hratio, _⟩ :=
    S.e2_atom_contact_guards r hW hq hdq hbenchmark hderiv hgap hglobal
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  by_cases hfirst : ∃ z1 : S.I, z1 ≠ r ∧ z1 ≠ a
  · obtain ⟨z1, hz1r, hz1a⟩ := hfirst
    by_cases hsecond : ∃ z2 : S.I, z2 ≠ r ∧ z2 ≠ a ∧ z2 ≠ z1
    · obtain ⟨z2, hz2r, hz2a, hz21⟩ := hsecond
      have hatoms := S.covered_boundary_atoms_eq_four false r a z1 z2 hW hd hgap hpair
        hzero hD (by simpa using hR) hell.1 hratio
        (Ne.symm hz1r) (Ne.symm hz1a) (Ne.symm hz2r) (Ne.symm hz2a) (Ne.symm hz21)
      exact S.no_e2_zero_body_two_exterior r a z1 z2 hW hq hdq hbenchmark hderiv hgap hglobal
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
      exact S.no_e2_zero_body_one_exterior r a z1 hW hq hdq hbenchmark hderiv hgap hglobal
        hpair hzero hR hE hz1r hz1a hatoms
  · have hatoms : ∀ u : S.I, u = r ∨ u = a := by
      intro u
      by_cases hur : u = r
      · exact Or.inl hur
      have hua : u = a := by
        by_contra hn
        exact hfirst ⟨u, hur, hn⟩
      exact Or.inr hua
    exact S.no_e2_zero_body_zero_exterior r a hW hq hdq hbenchmark hderiv hgap hglobal
      hpair hzero hR hE hatoms

/-- The original R-null E2 saturated zero-body boundary is excluded
with both E-null and E-positive cases derived internally. -/
theorem no_e2_zero_body_R_null
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hbenchmark : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0) : False := by
  by_cases hE : μ (S.D \ S.rootNeighborhood a) = 0
  · exact S.no_e2_zero_body_E_null r a hW hq hdq hbenchmark hderiv hgap hglobal
      hpair hzero hE
  · exact S.no_e2_zero_body_R_null_of_E_positive r a hW hq hdq hbenchmark hderiv hgap hglobal
      hpair hzero hR (pos_iff_ne_zero.mpr hE)

end Erdos1017.CappedModel.SelectedHighLowStructure

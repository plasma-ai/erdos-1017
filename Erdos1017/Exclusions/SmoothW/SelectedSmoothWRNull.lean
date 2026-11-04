module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWZeroExterior
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWOneExterior
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWTwoExterior
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredBoundaryRepeat
public import Erdos1017.Exclusions.SmoothW.SelectedCoveredSmoothWContact

/-!
# `R`-null zero-body case at the smooth `W` contact

The `R`-null, `E`-positive smooth-`W` saturated zero-body case is excluded
without any supplied bound on the number of exterior atoms
(`no_smoothW_zero_body_R_null`).
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

/-- The original R-null/E-positive smooth-W saturated zero-body case is
excluded without any supplied bound on the number of exterior atoms. -/
theorem no_smoothW_zero_body_R_null
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  obtain ⟨hell, _, _, hratio, _⟩ :=
    S.smoothW_covered_contact_guards r a hpair.1 hW hd hgap he hactive hglobal
  have hD : 0 < μ S.D := hE.trans_le (measure_mono sdiff_subset)
  by_cases hfirst : ∃ z1 : S.I, z1 ≠ r ∧ z1 ≠ a
  · obtain ⟨z1, hz1r, hz1a⟩ := hfirst
    by_cases hsecond : ∃ z2 : S.I, z2 ≠ r ∧ z2 ≠ a ∧ z2 ≠ z1
    · obtain ⟨z2, hz2r, hz2a, hz21⟩ := hsecond
      have hatoms := S.covered_boundary_atoms_eq_four false r a z1 z2 hW hd hgap hpair
        hzero hD (by simpa using hR) hell.1 hratio
        (Ne.symm hz1r) (Ne.symm hz1a) (Ne.symm hz2r) (Ne.symm hz2a) (Ne.symm hz21)
      exact S.no_smoothW_zero_body_two_exterior r a z1 z2 hW hd hgap he hactive hglobal
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
      exact S.no_smoothW_zero_body_one_exterior r a z1 hW hd hgap he hactive hglobal
        hpair hzero hR hE hz1r hz1a hatoms
  · have hatoms : ∀ u : S.I, u = r ∨ u = a := by
      intro u
      by_cases hur : u = r
      · exact Or.inl hur
      have hua : u = a := by
        by_contra hn
        exact hfirst ⟨u, hur, hn⟩
      exact Or.inr hua
    exact S.no_smoothW_zero_body_zero_exterior r a hW hd hgap he hactive hglobal
      hpair hzero hR hE hatoms

end Erdos1017.CappedModel.SelectedHighLowStructure

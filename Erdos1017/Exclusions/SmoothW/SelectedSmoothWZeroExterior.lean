module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredZeroExteriorCounts
public import Erdos1017.Exclusions.Common.MixedContactIdentity
public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak

/-!
# Zero-exterior `R`-null boundary at a smooth point of `W`

The zero-exterior `R`-null boundary at smooth-`W` contact is excluded by an
explicit constructed optimum together with that model's own contact multiplier
and rows (`no_smoothW_zero_body_zero_exterior`).
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

/-- The actual zero-exterior R-null smooth-W boundary is excluded by its
constructed explicit optimum, that model's own contact multiplier and rows.
No scalar profile, count contact or new stationary record is assumed. -/
theorem no_smoothW_zero_body_zero_exterior
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hepsilon : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) : False := by
  obtain ⟨j, hj, hlo, _, V, m', hV, hmom, _⟩ :=
    S.exists_covered_zero_explicit_optimum r a hW hd hgap hpair hzero hR hE hatoms
  let label := S.coveredZeroBoundaryLabel r a
  let A := μ.real (label ⁻¹' {0})
  let B := μ.real (label ⁻¹' {1})
  let E := μ.real (label ⁻¹' {2})
  let s := Benchmark.mixedInverse (1 / 2 - d)
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
  obtain ⟨hm, hs, hell, _⟩ :=
    hV.smoothW_contact_parameters hd hgap hepsilon hactive hglobalV
  have hs0 : 0 < s := by dsimp only [s]; linarith [hs.1]
  have hfloor := CoveredZeroExterior.penalty_lt_own_multiplier hV hd hgap label hpos
    (CoveredZeroExterior.explicitDual j) hmom
  obtain ⟨hAE, hBA⟩ := CoveredZeroExterior.stationary_row_differences hV label hlabel hpos
    (CoveredZeroExterior.explicitDual j) hmom
  have hjtwo : j = 2 := MixedContactIdentity.integer_contact_eq_two hj hb hell hfirst hfloor hAE
  subst j
  norm_num [CoveredZeroExterior.explicitDual] at hAE hBA
  have hmass : A + B + E = 1 := CoveredZeroExterior.block_mass label hlabel
  have hprofile := MixedContactIdentity.profile_eq hs0 hmass
    (show -m' = (s + 1) / (3 * s) by rw [hm, neg_neg])
    (by norm_num; exact hAE)
    (show A * (1 + -m') + E * (2 / 3 + -m') = B * (1 + -m') by
      dsimp only [A, B, E]
      nlinarith only [hBA])
  have hvalue := (MixedContactIdentity.density_value_eq hs0
    hprofile.1 hprofile.2.1 hprofile.2.2).2
  have hc : A * B + B * E * (2 / 3) - E ^ 2 / 6 = c := by
    have hi := CoveredZeroExterior.block_physicalObjective (μ := μ) label hlabel
      (CoveredZeroExterior.explicitDual 2)
    have ho : FiniteCappedSamplingCost.physicalObjective μ
        (fun x y => CoveredZeroExterior.blockCharge (CoveredZeroExterior.explicitDual 2)
          (label x) (label y)) = objective V := by
      unfold FiniteCappedSamplingCost.physicalObjective objective
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
    rw [ho, hV.objective_eq] at hi
    norm_num [CoveredZeroExterior.objective, CoveredZeroExterior.explicitDual] at hi
    dsimp only [A, B, E]
    nlinarith only [hi]
  have hbenchmark : benchmark d = Benchmark.mixedValue s := by
    simp only [Erdos1017.benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true,
      max_eq_left hactive.le]
    simp only [Benchmark.mixedCurve, not_le.mpr hepsilon.1, ite_false, hepsilon.2.le, ite_true]
    rfl
  rw [hbenchmark, ← hvalue, hc] at hgap
  exact (lt_irrefl c) hgap

end Erdos1017.CappedModel.SelectedHighLowStructure

module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredZeroExteriorCounts
public import Erdos1017.Exclusions.Common.MixedContactIdentity
public import Erdos1017.Exclusions.Corner.FullSharpCornerPeak

/-!
# Exclusion of the corner case with no exterior atom

The `R`-null, `E`-positive corner with no exterior atom is excluded by its own
explicit optimum and stationary mixed profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem integer_contact_eq_two_of_penalty_lt_one {j : ℕ} {b e ell : ℝ}
    (hj : 1 ≤ j) (hb : 0 < b) (hell : ell ∈ Ioo (1 / 2 : ℝ) 1)
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

private theorem stationary_parameter_mem {a s : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hprofile : a = (-3 * s ^ 2 + 3 * s + 1) / Benchmark.mixedDenominator s)
    (hgap : Benchmark.mixedDensity s < Benchmark.mixedValue s) (hone : 1 ≤ s) :
    s ∈ Icc Benchmark.sigmaD Benchmark.sigmaZero := by
  have hQ := Benchmark.mixedDenominator_pos hs.le
  have hnum : 0 ≤ -3 * s ^ 2 + 3 * s + 1 := by
    have heq := (eq_div_iff hQ.ne').mp hprofile
    nlinarith only [heq, mul_nonneg ha hQ.le]
  have hzero : -3 * Benchmark.sigmaZero ^ 2 + 3 * Benchmark.sigmaZero + 1 = 0 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
    unfold Benchmark.sigmaZero
    nlinarith only [hsq]
  have hupper : s ≤ Benchmark.sigmaZero := by
    by_contra hn
    have hlt : Benchmark.sigmaZero < s := lt_of_not_ge hn
    have hprod := mul_pos (sub_pos.mpr hlt)
      (show 0 < s + Benchmark.sigmaZero - 1 by linarith [Benchmark.sigmaZero_bounds.1])
    nlinarith only [hprod, hnum, hzero]
  have hid : Benchmark.mixedValue s - Benchmark.mixedDensity s =
      s * Benchmark.mixedRootPolynomial s / (6 * Benchmark.mixedDenominator s ^ 2) := by
    unfold Benchmark.mixedValue Benchmark.mixedDensity Benchmark.mixedRootPolynomial
    ring
  have hroot : 0 < Benchmark.mixedRootPolynomial s := by
    have hpos := sub_pos.mpr hgap
    rw [hid] at hpos
    have hden : 0 < 6 * Benchmark.mixedDenominator s ^ 2 := by positivity
    have hmul := (div_pos_iff_of_pos_right hden).mp hpos
    exact (mul_pos_iff_of_pos_left hs).mp hmul
  have hlower : Benchmark.sigmaD < s := by
    by_contra hn
    have hmono := Benchmark.mixedRootPolynomial_strictMonoOn.monotoneOn hone
      Benchmark.sigmaD_spec.1.1 (le_of_not_gt hn)
    rw [Benchmark.sigmaD_spec.2] at hmono
    exact (not_le_of_gt hroot) hmono
  exact ⟨hlower.le, hupper⟩

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The actual R-null, E-positive corner with no exterior atom is excluded
by its own explicit optimum and stationary mixed profile. No smooth branch
multiplier or mixed-family envelope certificate is supplied. -/
theorem no_corner_zero_body_zero_exterior
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
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) : False := by
  obtain ⟨j, hj, hlo, _, V, m', hV, hmom, _⟩ :=
    S.exists_covered_zero_explicit_optimum r a hW hd hgap hpair hzero hR hE hatoms
  let label := S.coveredZeroBoundaryLabel r a
  let A := μ.real (label ⁻¹' {0})
  let B := μ.real (label ⁻¹' {1})
  let E := μ.real (label ⁻¹' {2})
  let s := E / B
  have hlabel := S.measurable_coveredZeroBoundaryLabel r a
  have hpos := S.coveredZeroBoundaryLabel_fibers_positive r a hpair.1 hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  obtain ⟨_, hB, hD⟩ := S.coveredZeroBoundaryLabel_fibers r a hpair.1 hatoms
  have hb : 0 < B := ENNReal.toReal_pos (hpos 1).ne' (measure_ne_top _ _)
  have hepos : 0 < E := ENNReal.toReal_pos (hpos 2).ne' (measure_ne_top _ _)
  have hs : 0 < s := div_pos hepos hb
  have hfirst : ((j : ℝ) - 1) * B ≤ E := by simpa only [B, E, label, hB, hD] using hlo
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  obtain ⟨hinterval, hcBound, hhBound, _⟩ :=
    hV.corner_contact_parameters hd hgap he heq hglobalV
  have hell : -m' ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hinterval.1, hinterval.2]
  have hfloor := CoveredZeroExterior.penalty_lt_own_multiplier hV hd hgap label hpos
    (CoveredZeroExterior.explicitDual j) hmom
  obtain ⟨hAE, hBA⟩ := CoveredZeroExterior.stationary_row_differences hV label hlabel hpos
    (CoveredZeroExterior.explicitDual j) hmom
  have hjtwo := integer_contact_eq_two_of_penalty_lt_one hj hb hell hfirst hfloor hAE
  subst j
  norm_num [CoveredZeroExterior.explicitDual] at hAE hBA hfirst
  have hone : 1 ≤ s := (le_div_iff₀ hb).mpr (by simpa only [one_mul] using hfirst)
  have hslope : -m' = (s + 1) / (3 * s) := by
    have hsB : s * B = E := by dsimp only [s]; field_simp
    apply (eq_div_iff (by positivity : 3 * s ≠ 0)).mpr
    change B * (1 / 3) = E * (-m' - 1 / 3) at hAE
    rw [← hsB] at hAE
    apply (mul_left_inj' hb.ne').mp
    nlinarith only [hAE]
  have hmass : A + B + E = 1 := CoveredZeroExterior.block_mass label hlabel
  have hprofile := MixedContactIdentity.profile_eq hs hmass hslope
    (by norm_num; exact hAE)
    (show A * (1 + -m') + E * (2 / 3 + -m') = B * (1 + -m') by
      dsimp only [A, B, E]
      nlinarith only [hBA])
  obtain ⟨hmissing, hvalue⟩ := MixedContactIdentity.density_value_eq hs
    hprofile.1 hprofile.2.1 hprofile.2.2
  have hdensity : A * B + B * E + E ^ 2 / 2 = d := by
    have hi := CoveredZeroExterior.block_physicalDensity (μ := μ) label hlabel
    have hm : FiniteCappedSamplingCost.physicalDensity μ
        (fun x y => CoveredZeroExterior.blockAdjacency (label x) (label y)) = density V := by
      unfold FiniteCappedSamplingCost.physicalDensity density
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).1.symm))
    rw [hm, hV.density_eq] at hi
    exact hi.symm
  have hepsilon : Benchmark.mixedDensity s = 1 / 2 - d := by
    have hmasssq := congrArg (fun x : ℝ => x ^ 2) hmass
    nlinarith only [hmissing, hdensity, hmasssq]
  have hcost : A * B + B * E * (2 / 3) - E ^ 2 / 6 = c := by
    have hi := CoveredZeroExterior.block_physicalObjective (μ := μ) label hlabel
      (CoveredZeroExterior.explicitDual 2)
    have hm : FiniteCappedSamplingCost.physicalObjective μ
        (fun x y => CoveredZeroExterior.blockCharge (CoveredZeroExterior.explicitDual 2)
          (label x) (label y)) = objective V := by
      unfold FiniteCappedSamplingCost.physicalObjective objective
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
    rw [hm, hV.objective_eq] at hi
    norm_num [CoveredZeroExterior.objective, CoveredZeroExterior.explicitDual] at hi
    dsimp only [A, B, E]
    nlinarith only [hi]
  have hcurve : Benchmark.mixedValue s = c := hvalue.symm.trans hcost
  have hdomain := stationary_parameter_mem hs (show 0 ≤ A from measureReal_nonneg)
    hprofile.1 (by rw [hepsilon, hcurve]; linarith only [hcBound, hhBound]) hone
  have hloc := (Benchmark.crossing_contact_location he heq).2
  have hstar : Benchmark.epsilonStar < 1 / 2 - d := by
    linarith [hloc.1, Benchmark.epsilonStar_lt_tenth, Benchmark.tenth_lt_epsilonC]
  have hinverse := Benchmark.mixedInverse_unique ⟨hstar.le, hloc.2.le⟩ hdomain hepsilon
  have hbenchmark : benchmark d = c := by
    simp only [Erdos1017.benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true,
      heq, max_self, Benchmark.mixedCurve, not_le.mpr hstar, hloc.2.le, ite_true,
      ← hinverse, hcurve]
  exact (ne_of_lt hgap) hbenchmark

end Erdos1017.CappedModel.SelectedHighLowStructure

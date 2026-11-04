module

public import Erdos1017.Benchmark.BenchmarkCrossingBounds
public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Activity of the two-head branch on the `E₂` range

Throughout the `E₂` range `0 < q ≤ 1/5`, endpoint included, the two-head family
strictly beats the mixed family, so the benchmark equals the two-head stationary
value at the same explicit parameter (`benchmark_e2_q`), and the parameter and
missing density lie strictly inside their intervals.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Benchmark

open LowerE2Scalar

/-- For `q ≥ 0`, `missingMass q / 2 = twoHeadDensity ((q + 2)/3)`. -/
private theorem e2_density_eq {q : ℝ} (hq : 0 ≤ q) :
    missingMass q / 2 = twoHeadDensity ((q + 2) / 3) := by
  rw [missingMass_eq_twoHeadDensity hq]
  ring

/-- For `0 < q < 1/4`, the two-head parameter satisfies `2/3 < (q + 2)/3 < z_C`. -/
private theorem e2_parameter_mem {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) (1 / 4)) :
    (q + 2) / 3 ∈ Set.Ioo (2 / 3 : ℝ) zC := by
  constructor <;> linarith [hq.1, hq.2, zC_spec.1.1]

/-- For `0 < q < 1/4`, the missing-edge density satisfies `ε_C < missingMass q / 2 < 1/4`. -/
private theorem e2_density_mem {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) (1 / 4)) :
    missingMass q / 2 ∈ Set.Ioo epsilonC (1 / 4) := by
  have hz := e2_parameter_mem hq
  rw [e2_density_eq hq.1.le]
  constructor
  · exact twoHeadDensity_strictAntiOn ⟨hz.1.le, hz.2.le⟩
      ⟨by linarith [zC_spec.1.1], le_rfl⟩ hz.2
  · have h := twoHeadDensity_strictAntiOn
      (show (2 / 3 : ℝ) ∈ Set.Icc (2 / 3) zC from ⟨le_rfl, by linarith [zC_spec.1.1]⟩)
      ⟨hz.1.le, hz.2.le⟩ hz.1
    simpa only [twoHeadDensity_two_thirds] using h

/-- The actual inverse identity holds on an open q interval containing the
legal endpoint one fifth. No benchmark branch comparison is a premise. -/
theorem twoHeadInverse_e2_q_of_lt_quarter {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) (1 / 4)) :
    twoHeadInverse (missingMass q / 2) = (q + 2) / 3 := by
  have he := e2_density_mem hq
  have hz := e2_parameter_mem hq
  exact (twoHeadInverse_unique ⟨he.1.le, he.2.le⟩ ⟨hz.1.le, hz.2.le⟩
    (e2_density_eq hq.1.le).symm).symm

/-- Every legal positive E2 parameter lies strictly inside the inverse interval. -/
theorem e2_q_parameter_mem {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5)) :
    (q + 2) / 3 ∈ Set.Ioo (2 / 3 : ℝ) zC :=
  e2_parameter_mem ⟨hq.1, by linarith [hq.2]⟩

/-- Every legal positive E2 missing density lies strictly between the two junctions. -/
theorem e2_q_density_mem {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5)) :
    missingMass q / 2 ∈ Set.Ioo epsilonC (1 / 4) :=
  e2_density_mem ⟨hq.1, by linarith [hq.2]⟩

/-- For `0 < q ≤ 1/5`, `twoHeadInverse (missingMass q / 2) = (q + 2)/3`. -/
theorem twoHeadInverse_e2_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5)) :
    twoHeadInverse (missingMass q / 2) = (q + 2) / 3 :=
  twoHeadInverse_e2_q_of_lt_quarter ⟨hq.1, by linarith [hq.2]⟩

/-- For `0 < q ≤ 1/5`, `E₂(missingMass q / 2) = twoHeadValue ((q + 2)/3)`. -/
private theorem e2_curve_eq {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5)) :
    twoHeadCurve (missingMass q / 2) = twoHeadValue ((q + 2) / 3) := by
  have he := e2_q_density_mem hq
  have he0 : missingMass q / 2 ≠ 0 := by linarith [he.1, tenth_lt_epsilonC]
  simp only [twoHeadCurve, he0, ite_false, not_le.mpr he.1, twoHeadInverse_e2_q hq]

/-- For `0 < q ≤ 1/5`, `missingMass q / 2` exceeds the right end
`23243417/(2·10⁸)` of the crossing box. -/
private theorem crossing_upper_lt_e2_density {q : ℝ}
    (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5)) :
    23243417 / (2 * 10 ^ 8) < missingMass q / 2 := by
  have hz : (q + 2) / 3 ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) := by
    constructor <;> linarith [hq.1, hq.2]
  have hbound := twoHeadDensity_strictAntiOn_full.antitoneOn hz
    (show (11 / 15 : ℝ) ∈ Set.Icc (2 / 3) (4 / 5) by norm_num)
    (show (q + 2) / 3 ≤ (11 / 15 : ℝ) by linarith [hq.2])
  have hgap : (23243417 / (2 * 10 ^ 8) : ℝ) < twoHeadDensity (11 / 15) := by
    norm_num [twoHeadDensity, twoHeadDenominator]
  rw [e2_density_eq hq.1.le]
  exact hgap.trans_le hbound

/-- The actual two-head benchmark family strictly wins throughout the legal
positive E2 range, including the one-fifth endpoint. -/
theorem mixedCurve_lt_twoHeadCurve_e2_q {q : ℝ}
    (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5)) :
    mixedCurve (missingMass q / 2) < twoHeadCurve (missingMass q / 2) := by
  have he := e2_q_density_mem hq
  have hcross := crossing_upper_lt_e2_density hq
  by_cases heD : missingMass q / 2 ≤ epsilonD
  · have hu := crossing_box_stationary (e := 23243417 / (2 * 10 ^ 8)) (by norm_num)
    have hdiff := family_difference_strictMonoOn
      ⟨hu.2.1.1, hu.1.2⟩ ⟨he.1.le, heD⟩ hcross
    dsimp only at hdiff
    linarith [crossing_upper_sign]
  · have heStar : epsilonStar < missingMass q / 2 := by
      linarith [he.1, epsilonStar_lt_tenth, tenth_lt_epsilonC]
    have hm : mixedCurve (missingMass q / 2) = missingMass q / 2 := by
      simp only [mixedCurve, not_le.mpr heStar, ite_false, heD]
    rw [hm, e2_curve_eq hq, e2_density_eq hq.1.le]
    have hz := e2_q_parameter_mem hq
    have hden := twoHeadDenominator_pos hz.1.le
    have hleft : 0 < 3 * ((q + 2) / 3) - 2 := by linarith [hq.1]
    have hright : 0 < 1 - (q + 2) / 3 := by linarith [hq.2]
    have hthird : 0 < 3 * ((q + 2) / 3) - 1 := by linarith [hq.1]
    have hexcess : 0 < (3 * ((q + 2) / 3) - 2) ^ 2 *
        (1 - (q + 2) / 3) * (3 * ((q + 2) / 3) - 1) /
        (24 * twoHeadDenominator ((q + 2) / 3) ^ 2) := by positivity
    exact lt_add_of_pos_right _ hexcess

/-- At the legal E2 density the actual benchmark equals the stationary
value of the same explicit two-head parameter. -/
theorem benchmark_e2_q {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) (1 / 5)) :
    Erdos1017.benchmark ((1 - missingMass q) / 2) = twoHeadValue ((q + 2) / 3) := by
  have he := e2_q_density_mem hq
  have hdlo : (1 / 4 : ℝ) < (1 - missingMass q) / 2 := by linarith [he.2]
  have hdhi : (1 - missingMass q) / 2 < (1 / 2 : ℝ) := by
    linarith [he.1, tenth_lt_epsilonC]
  have harg : 1 / 2 - (1 - missingMass q) / 2 = missingMass q / 2 := by ring
  simp only [Erdos1017.benchmark, not_le.mpr hdlo, ite_false, hdhi, ite_true, harg,
    max_eq_right (mixedCurve_lt_twoHeadCurve_e2_q hq).le]
  exact e2_curve_eq hq

end Erdos1017.Benchmark

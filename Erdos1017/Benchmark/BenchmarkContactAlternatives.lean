module

public import Erdos1017.Benchmark.BenchmarkDenseHeadCountGuards
public import Erdos1017.Benchmark.BenchmarkE2Activity

/-!
# Active-branch alternatives of the benchmark

Between the split junction and the low-density endpoint, the benchmark is
strictly on the `W` branch, strictly on the `E₂` branch, or at a tie of the two
(`family_contact_alternatives`); strict activity gives a two-sided derivative
and supplies the parameter, value and derivative of the active `E₂` branch.
-/

@[expose] public section

noncomputable section

open Set Filter

namespace Erdos1017.Benchmark

/-- Between the split junction and the low-density endpoint, the actual
benchmark has exactly the strict W, strict E2, or equality alternatives.
The two inverse-family endpoints are included in the strict alternatives. -/
theorem family_contact_alternatives {e : ℝ} (he : e ∈ Ioo epsilonStar (1 / 4)) :
    (e ∈ Ioo epsilonStar epsilonD ∧ twoHeadCurve e < mixedCurve e) ∨
    (e ∈ Ioo epsilonC (1 / 4) ∧ mixedCurve e < twoHeadCurve e) ∨
    (e ∈ Ioo epsilonC epsilonD ∧ twoHeadCurve e = mixedCurve e) := by
  have he0 : 0 < e := epsilonStar_pos.trans he.1
  by_cases hC : e ≤ epsilonC
  · left
    have hD : e < epsilonD := by
      linarith [epsilonC_lt_nine_eightieths, eighth_lt_epsilonD]
    refine ⟨⟨he.1, hD⟩, ?_⟩
    rw [show twoHeadCurve e = splitValue (Real.sqrt (2 * e)) by
      simp only [twoHeadCurve, ne_of_gt he0, ite_false, hC, ite_true]]
    apply split_lt_mixedCurve ⟨he.1, hD.le⟩
    have hs := Real.sq_sqrt (show 0 ≤ 2 * e by positivity)
    have hn := Real.sqrt_nonneg (2 * e)
    constructor <;>
      nlinarith [he.1, two_twenty_fifths_lt_epsilonStar, epsilonC_lt_nine_eightieths]
  · have hC : epsilonC < e := lt_of_not_ge hC
    by_cases hD : e < epsilonD
    · rcases lt_trichotomy (twoHeadCurve e) (mixedCurve e) with hlt | heq | hgt
      · exact Or.inl ⟨⟨he.1, hD⟩, hlt⟩
      · exact Or.inr (Or.inr ⟨⟨hC, hD⟩, heq⟩)
      · exact Or.inr (Or.inl ⟨⟨hC, he.2⟩, hgt⟩)
    · right
      left
      refine ⟨⟨hC, he.2⟩, ?_⟩
      have hm : mixedCurve e = e := by
        rcases eq_or_lt_of_le (le_of_not_gt hD) with heq | hgt
        · rw [← heq, mixedCurve_epsilonD]
        · simp only [mixedCurve, not_le.mpr he.1, ite_false, not_le.mpr hgt]
      obtain ⟨hz, hdensity⟩ := twoHeadInverse_spec ⟨hC.le, he.2.le⟩
      have hzlo : 2 / 3 < twoHeadInverse e := by
        by_contra h
        have hzq : twoHeadInverse e = 2 / 3 := le_antisymm (le_of_not_gt h) hz.1
        rw [hzq, twoHeadDensity_two_thirds] at hdensity
        linarith [he.2]
      have hzhi : twoHeadInverse e < 1 := by linarith [hz.2, zC_lt_four_fifths]
      have hp : 0 < (3 * twoHeadInverse e - 2) ^ 2 * (1 - twoHeadInverse e) *
          (3 * twoHeadInverse e - 1) / (24 * twoHeadDenominator (twoHeadInverse e) ^ 2) := by
        apply div_pos
        · exact mul_pos (mul_pos (sq_pos_of_pos (by linarith)) (by linarith))
            (by linarith)
        · exact mul_pos (by norm_num) (sq_pos_of_pos (twoHeadDenominator_pos hz.1))
      rw [hm]
      simp only [twoHeadCurve, ne_of_gt he0, ite_false, not_le.mpr hC]
      unfold twoHeadValue
      linarith

/-- Strict activity supplies a genuine two-sided derivative, unlike an
E2/W tie, where only the separate one-sided slopes are available. -/
theorem strict_twoHead_benchmark_hasDerivAt {d : ℝ}
    (hd : d ∈ Ioo (1 / 4) (1 / 2)) (he : epsilonC < 1 / 2 - d)
    (hactive : mixedCurve (1 / 2 - d) < twoHeadCurve (1 / 2 - d)) :
    HasDerivAt benchmark
      (-((4 - 3 * twoHeadInverse (1 / 2 - d)) / (3 * twoHeadInverse (1 / 2 - d)))) d := by
  have he0 : 0 < 1 / 2 - d := by linarith [hd.2]
  have hehi : 1 / 2 - d < 1 / 4 := by linarith [hd.1]
  have hm := (mixedCurve_continuousOn (1 / 2 - d) ⟨he0.le, hehi.le⟩).continuousAt
    (Icc_mem_nhds he0 hehi)
  have ht := (twoHeadCurve_continuousOn (1 / 2 - d) ⟨he0.le, hehi.le⟩).continuousAt
    (Icc_mem_nhds he0 hehi)
  have hmc : ContinuousAt (fun x : ℝ => mixedCurve (1 / 2 - x)) d :=
    hm.comp (by fun_prop)
  have htc : ContinuousAt (fun x : ℝ => twoHeadCurve (1 / 2 - x)) d :=
    ht.comp (by fun_prop)
  have hder : HasDerivAt (fun x : ℝ => twoHeadCurve (1 / 2 - x))
      (-((4 - 3 * twoHeadInverse (1 / 2 - d)) / (3 * twoHeadInverse (1 / 2 - d)))) d := by
    convert (twoHeadCurve_hasDerivAt ⟨he, hehi⟩).comp d
      ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)) using 1
    · rfl
    · ring
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hd.1 hd.2, hmc.eventually_lt htc hactive] with x hx hact
  simp only [benchmark, not_le.mpr hx.1, ite_false, hx.2, ite_true, max_eq_right hact.le]

/-- The actual strictly active E2 branch provides its parameter, value,
and derivative from its literal activity inequality. -/
theorem strict_twoHead_contact_parameters {d : ℝ}
    (hd : d ∈ Ioo (1 / 4) (1 / 2)) (he : epsilonC < 1 / 2 - d)
    (hactive : mixedCurve (1 / 2 - d) < twoHeadCurve (1 / 2 - d)) :
    ∃ q ∈ Ioo (0 : ℝ) (213 / 1000),
      d = (1 - LowerE2Scalar.missingMass q) / 2 ∧
      benchmark d = twoHeadValue ((q + 2) / 3) ∧
      HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d := by
  let z := twoHeadInverse (1 / 2 - d)
  have hi := twoHeadInverse_spec ⟨he.le, show 1 / 2 - d ≤ 1 / 4 by linarith [hd.1]⟩
  have hzlo : 2 / 3 < z := by
    by_contra h
    have hzq : z = 2 / 3 := le_antisymm (le_of_not_gt h) hi.1.1
    have hden := hi.2
    change twoHeadDensity z = 1 / 2 - d at hden
    rw [hzq, twoHeadDensity_two_thirds] at hden
    linarith [hd.1]
  have hq : 0 < 3 * z - 2 := by linarith
  refine ⟨3 * z - 2, ⟨hq, active_twoHead_parameter_lt_cutoff
    ⟨he.le, by linarith [hd.1]⟩ hactive.le⟩, ?_, ?_, ?_⟩
  · have hmass := LowerE2Scalar.missingMass_eq_twoHeadDensity hq.le
    rw [show (3 * z - 2 + 2) / 3 = z by ring] at hmass
    have hden : twoHeadDensity z = 1 / 2 - d := hi.2
    linarith
  · rw [show (3 * z - 2 + 2) / 3 = z by ring]
    have he0 : 1 / 2 - d ≠ 0 := by linarith [hd.2]
    simp only [benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true]
    rw [max_eq_right hactive.le]
    simp only [twoHeadCurve, he0, ite_false, not_le.mpr he]
    rfl
  · convert strict_twoHead_benchmark_hasDerivAt hd he hactive using 1
    unfold LowerE2Scalar.multiplier
    change -((2 - (3 * z - 2)) / (2 + (3 * z - 2))) = -((4 - 3 * z) / (3 * z))
    congr 1
    ring

end Erdos1017.Benchmark

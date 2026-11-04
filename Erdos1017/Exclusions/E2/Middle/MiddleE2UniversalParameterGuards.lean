module

public import Erdos1017.Benchmark.BenchmarkE2Activity
public import Erdos1017.Exclusions.E2.Lower.LowerE2PeakScalar

/-!
# Parameter guards for the universal middle `E₂` case

The forward-gap floor `universalPeakGapFloor` uses the same `E₂` denominator as
the density and multiplier, is computed from the benchmark at the `E₂` contact,
and increases on `[0, 1/5]`; the saturated-ratio ceiling increases there too,
and the multiplier gap pays at least `q` times its penalty.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.LowerE2Scalar

/-- The benchmark's strict original forward-gap floor, using the same
E2 denominator as its density, multiplier and shifted-row floor. -/
def universalPeakGapFloor (q : ℝ) : ℝ :=
  9 * q ^ 2 * (1 - q ^ 2) / (4 * denominator q ^ 2)

private theorem universalPeakGapFloor_hasDerivAt {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt universalPeakGapFloor
      (9 * q * (1 - 3 * q ^ 2 - 7 * q ^ 3) / (2 * denominator q ^ 3)) q := by
  have hi := hasDerivAt_id q
  have hn := (((hi.pow 2).const_mul 9).mul ((hasDerivAt_const q 1).sub (hi.pow 2)))
  have hR := ((hasDerivAt_const q 1).add (hi.const_mul 7)).add (hi.pow 2)
  have hd := (hR.pow 2).const_mul 4
  have hne := (denominator_pos hq).ne'
  convert hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)) using 1
  · ext x
    dsimp [universalPeakGapFloor, denominator]
  · dsimp [denominator]
    field_simp
    ring

/-- The original forward-gap floor increases throughout the closed parameter
interval `[0, 1/5]`. -/
theorem universalPeakGapFloor_strictMonoOn :
    StrictMonoOn universalPeakGapFloor (Icc (0 : ℝ) (1 / 5)) := by
  have hc : ContinuousOn universalPeakGapFloor (Icc (0 : ℝ) (1 / 5)) := by
    intro q hq
    exact (universalPeakGapFloor_hasDerivAt hq.1).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
  intro q hq
  have hq' : q ∈ Ioo (0 : ℝ) (1 / 5) := by simpa only [interior_Icc] using hq
  have h2 := pow_le_pow_left₀ hq'.1.le hq'.2.le 2
  have h3 := pow_le_pow_left₀ hq'.1.le hq'.2.le 3
  have hpoly : 0 < 1 - 3 * q ^ 2 - 7 * q ^ 3 := by nlinarith only [h2, h3]
  rw [(universalPeakGapFloor_hasDerivAt hq'.1.le).deriv]
  exact div_pos (mul_pos (mul_pos (by norm_num) hq'.1) hpoly)
    (mul_pos (by norm_num) (pow_pos (denominator_pos hq'.1.le) 3))

/-- The saturated-ratio ceiling increases on the same closed parameter
interval. The product comparison keeps the common positive denominator. -/
theorem universal_ratio_monotoneOn_middle :
    MonotoneOn (fun q : ℝ => 9 * q / (2 * denominator q)) (Icc (0 : ℝ) (1 / 5)) := by
  intro q hq r hr hqr
  apply (div_le_div_iff₀ (mul_pos (by norm_num) (denominator_pos hq.1))
    (mul_pos (by norm_num) (denominator_pos hr.1))).mpr
  have hqrprod := mul_le_mul hq.2 hr.2 hr.1 (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hpositive := mul_nonneg (sub_nonneg.mpr hqr)
    (show 0 ≤ 1 - q * r by nlinarith only [hqrprod])
  unfold denominator
  nlinarith only [hpositive]

/-- The strict forward gap is computed from the same benchmark value and
missing density that determine the actual E2 contact. -/
theorem universalPeakGapFloor_eq_benchmark {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    universalPeakGapFloor q =
      2 * Erdos1017.benchmark ((1 - missingMass q) / 2) - missingMass q := by
  rw [Benchmark.benchmark_e2_q hq]
  have he := gapFloor_eq_twoHeadValue hq.1.le
  have hR := (denominator_pos hq.1.le).ne'
  have hq2 : 2 + q ≠ 0 := by linarith only [hq.1]
  have htwo : 2 * Benchmark.twoHeadValue ((q + 2) / 3) =
      gapFloor q + multiplier q * missingMass q := by linarith only [he]
  rw [htwo]
  unfold universalPeakGapFloor gapFloor multiplier missingMass
  field_simp [hR, hq2]
  unfold denominator
  ring

/-- The own multiplier's positive slope gap pays at least q times its
penalty, on the same exact E2 parameter. -/
theorem multiplier_gap_ge_parameter {q : ℝ} (hq : 0 ≤ q) :
    multiplier q * q ≤ 1 - multiplier q := by
  have hden : 0 < 2 + q := by linarith only [hq]
  have hid : 1 - multiplier q - multiplier q * q = q ^ 2 / (2 + q) := by
    unfold multiplier
    field_simp
    ring
  have hpos := div_nonneg (sq_nonneg q) hden.le
  linarith only [hid, hpos]

end Erdos1017.LowerE2Scalar

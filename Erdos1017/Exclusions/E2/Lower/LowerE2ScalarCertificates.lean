module

public import Erdos1017.Benchmark
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# Scalar certificates for the lower `E₂` contact

The lower `E₂` contact denominator, order-two mass floor and multiplier are
defined in the parameter `q = 3z - 2`, with exact clearings of the joined-head
and missing-head margins, their contradictions with the order-two floor and mass
budget, the ratio bound `2/7`, and the radical scalings.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Erdos1017.LowerE2Scalar

/-- The lower-E2 contact denominator in the parameter `q = 3z - 2`. -/
def denominator (q : ℝ) : ℝ := 1 + 7 * q + q ^ 2

/-- The numerator of the order-two mass floor. -/
def pairNumerator (q : ℝ) : ℝ := 4 - 16 * q - 39 * q ^ 2 + 56 * q ^ 3 - 5 * q ^ 4

/-- The lower-E2 multiplier, before any original-model hypotheses are used. -/
def multiplier (q : ℝ) : ℝ := (2 - q) / (2 + q)

/-- The strict lower bound for the shifted-row parameter at an E2 contact. -/
def gapFloor (q : ℝ) : ℝ := q * (1 + 2 * q) / (2 * denominator q)

/-- Twice the stationary E2 missing density. -/
def missingMass (q : ℝ) : ℝ :=
  (q + 2) ^ 2 * (1 + 4 * q + 13 * q ^ 2) / (8 * denominator q ^ 2)

/-- The order-two mass lower bound used by the lower-E2 scalar exclusions. -/
def pairFloor (q : ℝ) : ℝ := pairNumerator q / (16 * denominator q ^ 2)

/-- The cleared missing-head margin on the first lower-E2 interval. -/
def lowMissingPolynomial (q : ℝ) : ℝ :=
  12 - 120 * q - 333 * q ^ 2 + 168 * q ^ 3 - 51 * q ^ 4

/-- The cleared joined-head margin on the first lower-E2 interval. -/
def lowJoinedPolynomial (q : ℝ) : ℝ :=
  24 - 236 * q - 702 * q ^ 2 + 279 * q ^ 3 - 40 * q ^ 4

/-- The cleared missing-head margin on the second lower-E2 interval. -/
def middleMissingPolynomial (q : ℝ) : ℝ :=
  3634 - 29416 * q - 139983 * q ^ 2 / 2 + 76076 * q ^ 3 - 18925 * q ^ 4 / 2

/-- The positive common denominator for the second interval's radical test. -/
def radicalDenominator (q : ℝ) : ℝ :=
  62100 * denominator q ^ 2 * (q + 2) ^ 2

/-- The first squared radical, scaled by the common denominator. -/
def radicalX (q : ℝ) : ℝ := 89600 * q * (1 + 2 * q) * denominator q

/-- The second squared radical, scaled by the common denominator. -/
def radicalY (q : ℝ) : ℝ := 17388 * (14 + 10 * q) * pairNumerator q

/-- The square of the comparison target, scaled by the common denominator. -/
def radicalZ (q : ℝ) : ℝ :=
  15525 * (2 * denominator q - q * (1 + 2 * q)) ^ 2 * (q + 2) ^ 2

/-- The double-radical certificate does not assume the sign of `Z - X - Y`. -/
def middleJoinedPolynomial (q : ℝ) : ℝ :=
  4 * radicalX q * radicalY q - (radicalZ q - radicalX q - radicalY q) ^ 2

private theorem bernstein_sum_pos (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : ∀ i, (1 / 100 : ℝ) ≤ c i) (x : I) :
    0 < ∑ i, c i * bernstein n i x := by
  have hsum : (∑ i : Fin (n + 1), (1 / 100 : ℝ) * bernstein n i x) ≤
      ∑ i : Fin (n + 1), c i * bernstein n i x :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i) bernstein_nonneg)
  rw [← Finset.mul_sum, bernstein.probability, mul_one] at hsum
  exact (by norm_num : (0 : ℝ) < 1 / 100).trans_le hsum

/-- All 5 exact Bernstein coefficients are positive on the whole closed interval. -/
theorem low_missing_pos {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (2 / 25)) :
    0 < lowMissingPolynomial q := by
  let x : I := ⟨25 * q / 2, by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 4
    (fun i => ![12, 48 / 5, 4278 / 625, 58686 / 15625, 137784 / 390625] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [lowMissingPolynomial, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

/-- All 5 exact Bernstein coefficients are positive on the whole closed interval. -/
theorem low_joined_pos {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (2 / 25)) :
    0 < lowJoinedPolynomial q := by
  let x : I := ⟨25 * q / 2, by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 4
    (fun i => ![24, 482 / 25, 8632 / 625, 119208 / 15625, 60032 / 78125] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [lowJoinedPolynomial, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

/-- All 5 exact Bernstein coefficients are positive on the whole closed interval. -/
theorem middle_missing_pos {q : ℝ} (hq : q ∈ Set.Icc (2 / 25 : ℝ) (1 / 10)) :
    0 < middleMissingPolynomial q := by
  let x : I := ⟨50 * q - 4, by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 4
    (fun i => ![13614652 / 15625, 42216933 / 62500, 23806551 / 50000,
      2734641 / 10000, 270459 / 4000] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [middleMissingPolynomial, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

/-- All 11 exact Bernstein coefficients are positive on the whole closed interval. -/
theorem middle_joined_pos {q : ℝ} (hq : q ∈ Set.Icc (2 / 25 : ℝ) (1 / 10)) :
    0 < middleJoinedPolynomial q := by
  let x : I := ⟨50 * q - 4, by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 10
    (fun i => ![4921296645011481030656 / 152587890625,
      5264101113754050567168 / 152587890625, 9812464178966977424384 / 274658203125,
      219088425878967510536 / 6103515625, 179277794570396000138 / 5126953125,
      9639586223920880447 / 292968750, 81105299962991533377 / 2734375000,
      15750967749366120201 / 625000000, 9741098545184620719 / 500000000,
      249225461053435251 / 20000000, 655386605200719 / 160000] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [middleJoinedPolynomial, radicalX, radicalY, radicalZ, pairNumerator, denominator,
    Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

theorem denominator_pos {q : ℝ} (hq : 0 ≤ q) : 0 < denominator q := by
  unfold denominator
  positivity

/-- The q formula is the actual benchmark family's missing density. -/
theorem missingMass_eq_twoHeadDensity {q : ℝ} (hq : 0 ≤ q) :
    missingMass q = 2 * Benchmark.twoHeadDensity ((q + 2) / 3) := by
  have hR := ne_of_gt (denominator_pos hq)
  have hz : Benchmark.twoHeadDenominator ((q + 2) / 3) = denominator q / 9 := by
    unfold Benchmark.twoHeadDenominator denominator
    ring
  unfold missingMass Benchmark.twoHeadDensity
  simp only [hz]
  field_simp
  ring

/-- The shifted-row floor is computed from the same benchmark value and density. -/
theorem gapFloor_eq_twoHeadValue {q : ℝ} (hq : 0 ≤ q) :
    gapFloor q = 2 * Benchmark.twoHeadValue ((q + 2) / 3) - multiplier q * missingMass q := by
  have hR := ne_of_gt (denominator_pos hq)
  have hz : Benchmark.twoHeadDenominator ((q + 2) / 3) = denominator q / 9 := by
    unfold Benchmark.twoHeadDenominator denominator
    ring
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold gapFloor multiplier missingMass Benchmark.twoHeadValue Benchmark.twoHeadDensity
  simp only [hz]
  field_simp
  simp only [denominator]
  ring

/-- The order-two mass floor comes from the actual stationary family value. -/
theorem pairFloor_eq_twoHeadValue {q : ℝ} (hq : 0 ≤ q) :
    2 * pairFloor q = 3 * Benchmark.twoHeadValue ((q + 2) / 3) - (1 - missingMass q) / 2 := by
  have hR := ne_of_gt (denominator_pos hq)
  have hz : Benchmark.twoHeadDenominator ((q + 2) / 3) = denominator q / 9 := by
    unfold Benchmark.twoHeadDenominator denominator
    ring
  unfold pairFloor pairNumerator missingMass Benchmark.twoHeadValue Benchmark.twoHeadDensity
  simp only [hz]
  field_simp
  simp only [denominator]
  ring

/-- Positive order-two reserve throughout the lower-E2 parameter interval. -/
theorem pairFloor_pos {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (1 / 10)) : 0 < pairFloor q := by
  have h2 : q ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
    gcongr
    · exact hq.1
    · exact hq.2
  have h4 : q ^ 4 ≤ (1 / 10 : ℝ) ^ 4 := by
    gcongr
    · exact hq.1
    · exact hq.2
  have h3 : 0 ≤ q ^ 3 := pow_nonneg hq.1 3
  apply div_pos _ (mul_pos (by norm_num) (pow_pos (denominator_pos hq.1) 2))
  unfold pairNumerator
  nlinarith [hq.2]

/-- Exact clearing of the first interval's missing-head scalar margin. -/
theorem lowMissing_identity {q : ℝ} (hq : 0 ≤ q) :
    (5 * pairFloor q - missingMass q) * (16 * denominator q ^ 2) = lowMissingPolynomial q := by
  have hR := ne_of_gt (denominator_pos hq)
  unfold pairFloor pairNumerator missingMass lowMissingPolynomial
  field_simp
  ring

/-- Exact clearing of the first interval's joined-head scalar margin. -/
theorem lowJoined_identity {q : ℝ} (hq : 0 ≤ q) :
    (8 * (1 + multiplier q) * pairFloor q - (1 - gapFloor q) ^ 2) *
      (4 * (q + 2) * denominator q ^ 2) = lowJoinedPolynomial q := by
  have hR := ne_of_gt (denominator_pos hq)
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold pairFloor pairNumerator multiplier gapFloor lowJoinedPolynomial
  field_simp
  simp only [denominator]
  ring

/-- Exact clearing of the second interval's missing-head scalar margin. -/
theorem middleMissing_identity {q : ℝ} (hq : 0 ≤ q) :
    ((21 / 23) * gapFloor q + (119 / 20) * pairFloor q - missingMass q) *
      (3680 * denominator q ^ 2) = middleMissingPolynomial q := by
  have hR := ne_of_gt (denominator_pos hq)
  unfold gapFloor pairFloor pairNumerator missingMass middleMissingPolynomial
  field_simp
  simp only [denominator]
  ring

/-- The first interval's missing-head budget contradicts the order-two floor. -/
theorem missingMass_lt_five_pairFloor {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (2 / 25)) :
    missingMass q < 5 * pairFloor q := by
  have hpos := low_missing_pos hq
  rw [← lowMissing_identity hq.1] at hpos
  have hden : 0 < 16 * denominator q ^ 2 := by
    have hR := denominator_pos hq.1
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hpos)

/-- The first interval's joined-head inequality contradicts the order-two floor. -/
theorem one_sub_gapFloor_sq_lt {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (2 / 25)) :
    (1 - gapFloor q) ^ 2 < 8 * (1 + multiplier q) * pairFloor q := by
  have hpos := low_joined_pos hq
  rw [← lowJoined_identity hq.1] at hpos
  have hden : 0 < 4 * (q + 2) * denominator q ^ 2 := by
    have hR := denominator_pos hq.1
    have hq2 : 0 < q + 2 := by linarith [hq.1]
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hpos)

/-- The second interval's missing-head inequality contradicts the mass budget. -/
theorem missingMass_lt_middle_bound {q : ℝ} (hq : q ∈ Set.Icc (2 / 25 : ℝ) (1 / 10)) :
    missingMass q < (21 / 23) * gapFloor q + (119 / 20) * pairFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hpos := middle_missing_pos hq
  rw [← middleMissing_identity hq0] at hpos
  have hden : 0 < 3680 * denominator q ^ 2 := by
    have hR := denominator_pos hq0
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hpos)

/-- The lower-E2 ratio lies below the universal positive-hole threshold. -/
theorem ratio_lt_two_sevenths {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (1 / 9)) :
    9 * q / (2 * denominator q) < 2 / 7 := by
  apply (div_lt_iff₀ (mul_pos (by norm_num) (denominator_pos hq.1))).mpr
  unfold denominator
  nlinarith [hq.2, sq_nonneg q]

/-- The radical radicands and target are scaled by one common positive denominator. -/
theorem radical_scalings {q : ℝ} (hq : 0 ≤ q) :
    radicalX q / radicalDenominator q =
      112 * (1 + multiplier q) ^ 2 * gapFloor q / 621 ∧
    radicalY q / radicalDenominator q =
      4 * (7 * (1 + multiplier q) / 10 + (1 - multiplier q)) *
        (7 * (1 + multiplier q) / 5) * pairFloor q ∧
    radicalZ q / radicalDenominator q = (1 - gapFloor q) ^ 2 := by
  have hR := ne_of_gt (denominator_pos hq)
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold radicalX radicalY radicalZ radicalDenominator multiplier gapFloor pairFloor
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  · field_simp
    ring

private theorem lt_sqrt_add_sqrt {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hgap : 0 < 4 * x * y - (t ^ 2 - x - y) ^ 2) :
    t < Real.sqrt x + Real.sqrt y := by
  have hsx := Real.sqrt_nonneg x
  have hsy := Real.sqrt_nonneg y
  have hx2 := Real.sq_sqrt hx
  have hy2 := Real.sq_sqrt hy
  have hxy : (Real.sqrt x * Real.sqrt y) ^ 2 = x * y := by
    rw [mul_pow, hx2, hy2]
  have hsxy := mul_nonneg hsx hsy
  have hmiddle : t ^ 2 - x - y < 2 * (Real.sqrt x * Real.sqrt y) := by
    by_contra h
    have hle := le_of_not_gt h
    nlinarith [sq_nonneg (t ^ 2 - x - y - 2 * (Real.sqrt x * Real.sqrt y))]
  by_contra h
  have hle := le_of_not_gt h
  nlinarith [sq_nonneg (t - Real.sqrt x - Real.sqrt y)]

/-- The second interval's joined-head scalar inequality has the reverse strict sign.
Original-model inequalities yielding the opposite sign remain separate hypotheses. -/
theorem one_sub_gapFloor_lt_radicals {q : ℝ}
    (hq : q ∈ Set.Icc (2 / 25 : ℝ) (1 / 10)) :
    1 - gapFloor q < Real.sqrt (112 * (1 + multiplier q) ^ 2 * gapFloor q / 621) +
      Real.sqrt (4 * (7 * (1 + multiplier q) / 10 + (1 - multiplier q)) *
        (7 * (1 + multiplier q) / 5) * pairFloor q) := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hD : 0 < radicalDenominator q := by
    unfold radicalDenominator
    have hq2 : 0 < q + 2 := by linarith
    positivity
  have hX : 0 ≤ radicalX q := by unfold radicalX; positivity
  have hY : 0 ≤ radicalY q := by
    have hp : 0 < pairNumerator q := by
      have hp := pairFloor_pos (show q ∈ Set.Icc (0 : ℝ) (1 / 10) from ⟨hq0, hq.2⟩)
      exact (div_pos_iff_of_pos_right (by positivity : 0 < 16 * denominator q ^ 2)).mp hp
    unfold radicalY
    positivity
  have hs := radical_scalings hq0
  rw [← hs.1, ← hs.2.1]
  apply lt_sqrt_add_sqrt (div_nonneg hX hD.le) (div_nonneg hY hD.le)
  have hid :
      4 * (radicalX q / radicalDenominator q) * (radicalY q / radicalDenominator q) -
          ((1 - gapFloor q) ^ 2 - radicalX q / radicalDenominator q -
            radicalY q / radicalDenominator q) ^ 2 =
        middleJoinedPolynomial q / radicalDenominator q ^ 2 := by
    rw [← hs.2.2]
    unfold middleJoinedPolynomial
    field_simp
  rw [hid]
  exact div_pos (middle_joined_pos hq) (pow_pos hD 2)

end Erdos1017.LowerE2Scalar

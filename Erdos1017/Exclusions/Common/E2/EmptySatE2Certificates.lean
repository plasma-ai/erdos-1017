module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Bernstein certificates for the empty-source saturated `E₂` case

Three polynomial numerators (the support numerator and the two exceptional-atom
numerators) are shown positive on a closed rectangle through their 21 tensor
Bernstein coefficients, and the support and exceptional-atom scores are positive
at the head endpoints.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators unitInterval

namespace Erdos1017.EmptySatE2

/-- The original E2 deficit parameter. -/
def delta (q : ℝ) : ℝ := 1 - LowerE2Scalar.multiplier q

/-- The signed difference of the two original head masses at zero excess. -/
def baseDifference (A D : ℝ) : ℝ := 2 * A - 1 + D

/-- The positive support-square argument at zero excess. -/
def baseCredit (δ A D : ℝ) : ℝ := (2 - δ) * baseDifference A D - D / 12

/-- The original restricted support price at zero excess. -/
def baseScore (δ h A D : ℝ) : ℝ :=
  δ * (1 - D - 2 * h) - 2 * (1 - δ) * baseDifference A D ^ 2 - D ^ 2 / 12 +
    (12 / 25) * baseCredit δ A D ^ 2

/-- The support price after deleting the actual saturated partner. -/
def supportScore (δ h A D L : ℝ) : ℝ :=
  baseScore δ h A D - (4 * (2 - δ) * baseDifference A D + 8 * D) * L / 25 -
    8 * L ^ 2 / 25

/-- The exceptional-atom price after its actual deficit is maximized. -/
def exceptionalBaseScore (δ h A D : ℝ) : ℝ :=
  baseScore δ h A D + (24 / 25) * baseCredit δ A D * δ * (D - A) +
    (12 / 25) * (δ * (D - A)) ^ 2 - 2 * A * δ * (D - A)

/-- The exact polynomial numerator of the first tensor certificate. -/
def supportNumerator (q A D : ℝ) : ℝ :=
  600 * q * (q + 2) * LowerE2Scalar.denominator q ^ 2 * (1 - D) -
    150 * q * (q + 2) * ((q + 2) ^ 2 * (1 + 4 * q + 13 * q ^ 2)) -
    600 * (2 - q) * (q + 2) * LowerE2Scalar.denominator q ^ 2 *
      baseDifference A D ^ 2 -
    25 * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2 * D ^ 2 +
    (48 * baseDifference A D - D * (q + 2)) ^ 2 *
      LowerE2Scalar.denominator q ^ 2 -
    192 * baseDifference A D * (D - A) * (q + 2) * LowerE2Scalar.denominator q ^ 2 -
    96 * D * (D - A) * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2 -
    96 * (D - A) ^ 2 * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2

/-- The exact polynomial numerator of the two exceptional-atom certificates. -/
def exceptionalNumerator (q A D : ℝ) : ℝ :=
  600 * q * (q + 2) * LowerE2Scalar.denominator q ^ 2 * (1 - D) -
    150 * q * (q + 2) * ((q + 2) ^ 2 * (1 + 4 * q + 13 * q ^ 2)) -
    600 * (2 - q) * (q + 2) * LowerE2Scalar.denominator q ^ 2 *
      baseDifference A D ^ 2 -
    25 * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2 * D ^ 2 -
    1200 * q * (q + 2) * LowerE2Scalar.denominator q ^ 2 * A * (D - A) +
    (48 * baseDifference A D + 24 * q * (D - A) - D * (q + 2)) ^ 2 *
      LowerE2Scalar.denominator q ^ 2

private theorem tensor_bernstein_pos (n m : ℕ)
    (c : Fin (n + 1) → Fin (m + 1) → ℝ) (hc : ∀ i j, 1 ≤ c i j) (x y : I) :
    0 < ∑ i, ∑ j, c i j * (bernstein n i x * bernstein m j y) := by
  have hsum : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      bernstein n i x * bernstein m j y) ≤
      ∑ i, ∑ j, c i j * (bernstein n i x * bernstein m j y) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact (one_mul _).symm.trans_le
      (mul_le_mul_of_nonneg_right (hc i j) (mul_nonneg bernstein_nonneg bernstein_nonneg))
  have hunit : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      bernstein n i x * bernstein m j y) = 1 := by
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    exact bernstein.probability _ _
  rw [hunit] at hsum
  exact (by norm_num : (0 : ℝ) < 1).trans_le hsum

/-- All 21 exact tensor Bernstein coefficients are positive on the closed rectangle. -/
theorem support_numerator_pos {q D : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hD : D ∈ Icc (7 / 20 : ℝ) (19 / 50)) :
    0 < supportNumerator q (7 / 20) D := by
  let x : I := ⟨(1000 / 33 : ℝ) * (q - 9 / 50), by
    constructor <;> nlinarith [hq.1, hq.2]⟩
  let y : I := ⟨(100 / 3 : ℝ) * (D - 7 / 20), by
    constructor <;> nlinarith [hD.1, hD.2]⟩
  have hpos := tensor_bernstein_pos 6 2
    (fun i j => (![
      ![69745405241798400000000, 40813285850794560000000, 6764584668587904000000],
      ![79185541280941440000000, 48781250472961296000000, 13063195428300806400000],
      ![89313071887354704000000, 57372839088402573600000, 19916191892316546240000],
      ![100151466949773566400000, 66609395262702242760000, 27342718445504533584000],
      ![111724055031724005240000, 76512076954971624666000, 35361689847749276594400],
      ![124053991655730490284000, 87101824168991542028100, 43991758269045753752040],
      ![137164226327180280156900,
        98399325336862483223085, 53251279050233601793614]] i j : ℝ) / 625000000000000000000)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num) x y
  convert hpos using 1
  norm_num [supportNumerator, exceptionalNumerator, baseDifference,
    LowerE2Scalar.denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x, y]
  ring

/-- All 21 exact tensor Bernstein coefficients are positive on the closed rectangle. -/
theorem exceptional_lower_numerator_pos {q D : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hD : D ∈ Icc (7 / 20 : ℝ) (19 / 50)) :
    0 < exceptionalNumerator q (7 / 20) D := by
  let x : I := ⟨(1000 / 33 : ℝ) * (q - 9 / 50), by
    constructor <;> nlinarith [hq.1, hq.2]⟩
  let y : I := ⟨(100 / 3 : ℝ) * (D - 7 / 20), by
    constructor <;> nlinarith [hD.1, hD.2]⟩
  have hpos := tensor_bernstein_pos 6 2
    (fun i j => (![
      ![69745405241798400000000, 42288538934763840000000, 14874976735310784000000],
      ![79185541280941440000000, 50102791874827344000000, 21104113542245654400000],
      ![89313071887354704000000, 58522979422423370400000, 27861322853606627040000],
      ![100151466949773566400000, 67569471611927489640000, 35164056042012330264000],
      ![111724055031724005240000, 77262427047490397874000, 43029487410071263772400],
      ![124053991655730490284000, 87621760144808082330900, 51474480458192569223340],
      ![137164226327180280156900,
        98667107100518371597065, 60515552868795163233219]] i j : ℝ) / 625000000000000000000)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num) x y
  convert hpos using 1
  norm_num [supportNumerator, exceptionalNumerator, baseDifference,
    LowerE2Scalar.denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x, y]
  ring

/-- All 21 exact tensor Bernstein coefficients are positive on the closed rectangle. -/
theorem exceptional_upper_numerator_pos {q D : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hD : D ∈ Icc (7 / 20 : ℝ) (19 / 50)) :
    0 < exceptionalNumerator q D D := by
  let x : I := ⟨(1000 / 33 : ℝ) * (q - 9 / 50), by
    constructor <;> nlinarith [hq.1, hq.2]⟩
  let y : I := ⟨(100 / 3 : ℝ) * (D - 7 / 20), by
    constructor <;> nlinarith [hD.1, hD.2]⟩
  have hpos := tensor_bernstein_pos 6 2
    (fun i j => (![
      ![69745405241798400000000, 41739528361581120000000, 9503810682105216000000],
      ![79185541280941440000000, 49775998333246992000000, 16012452520222905600000],
      ![89313071887354704000000, 58440427380996007200000, 23089476107078784960000],
      ![100151466949773566400000, 67754381785444328520000, 30754798307488267536000],
      ![111724055031724005240000, 77739250364995877082000, 39028137386079554517600],
      ![124053991655730490284000, 88416212273319424013700, 47928980614072566329160],
      ![137164226327180280156900,
        99806203531193529972045, 57476550609042559656006]] i j : ℝ) / 625000000000000000000)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num) x y
  convert hpos using 1
  norm_num [supportNumerator, exceptionalNumerator, baseDifference,
    LowerE2Scalar.denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x, y]
  ring

/-- Clearing the positive E2 denominators gives the first exact numerator. -/
theorem supportNumerator_eq {q : ℝ} (hq : 0 ≤ q) (A D : ℝ) :
    supportNumerator q A D = 300 * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2 *
      supportScore (delta q) (LowerE2Scalar.missingMass q) A D (D - A) := by
  have hR := (LowerE2Scalar.denominator_pos hq).ne'
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold supportNumerator supportScore baseScore baseCredit baseDifference delta
    LowerE2Scalar.multiplier LowerE2Scalar.missingMass
  field_simp [hR, hq2]
  ring

/-- Clearing the same denominators gives the exceptional-atom numerator. -/
theorem exceptionalNumerator_eq {q : ℝ} (hq : 0 ≤ q) (A D : ℝ) :
    exceptionalNumerator q A D = 300 * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2 *
      exceptionalBaseScore (delta q) (LowerE2Scalar.missingMass q) A D := by
  have hR := (LowerE2Scalar.denominator_pos hq).ne'
  have hq2 : q + 2 ≠ 0 := by linarith
  unfold exceptionalNumerator exceptionalBaseScore baseScore baseCredit baseDifference delta
    LowerE2Scalar.multiplier LowerE2Scalar.missingMass
  field_simp [hR, hq2]
  ring

/-- The first original support score is strictly positive at the lower head endpoint. -/
theorem supportScore_lower_pos {q D : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hD : D ∈ Icc (7 / 20 : ℝ) (19 / 50)) :
    0 < supportScore (delta q) (LowerE2Scalar.missingMass q) (7 / 20) D (D - 7 / 20) := by
  have h := support_numerator_pos hq hD
  rw [supportNumerator_eq (by linarith [hq.1])] at h
  have hR := LowerE2Scalar.denominator_pos (show 0 ≤ q by linarith [hq.1])
  have hq2 : 0 < q + 2 := by linarith [hq.1]
  exact (mul_pos_iff_of_pos_left (by positivity :
    0 < 300 * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2)).mp h

/-- Both head endpoints of the concave exceptional-atom score are positive. -/
theorem exceptionalBaseScore_endpoints_pos {q D : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hD : D ∈ Icc (7 / 20 : ℝ) (19 / 50)) :
    0 < exceptionalBaseScore (delta q) (LowerE2Scalar.missingMass q) (7 / 20) D ∧
      0 < exceptionalBaseScore (delta q) (LowerE2Scalar.missingMass q) D D := by
  have h₁ := exceptional_lower_numerator_pos hq hD
  have h₂ := exceptional_upper_numerator_pos hq hD
  rw [exceptionalNumerator_eq (by linarith [hq.1])] at h₁ h₂
  have hR := LowerE2Scalar.denominator_pos (show 0 ≤ q by linarith [hq.1])
  have hq2 : 0 < q + 2 := by linarith [hq.1]
  have hscale : 0 < 300 * (q + 2) ^ 2 * LowerE2Scalar.denominator q ^ 2 := by positivity
  exact ⟨(mul_pos_iff_of_pos_left hscale).mp h₁, (mul_pos_iff_of_pos_left hscale).mp h₂⟩

end Erdos1017.EmptySatE2

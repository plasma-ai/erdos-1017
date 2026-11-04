module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Erdos1017.Exclusions.Common.Flows.FullForwardSelectorEnvelope
public import Erdos1017.Benchmark.SplitCurve

/-!
# Scalar bounds for the middle `E₂` off-pair case

The head-row cap `headCap` and score-ratio cap `ratioCap` at the benchmark
contact are defined and bounded, together with the pair-product margin, the gap
above the selector at `13/50`, the parent-count criterion through the cutoff,
and the three-distinct-square obstruction through `19/160`. A private source is
smaller than twice its peak.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Erdos1017.MiddleE2OffPair

open LowerE2Scalar

/-- The original saturated-head row cap at the benchmark contact. -/
def headCap (q : ℝ) : ℝ := (q + 2) * (2 + 13 * q) / (8 * denominator q)

/-- The strict score-ratio upper bound at the benchmark contact. -/
def ratioCap (q : ℝ) : ℝ := 9 * q / (2 * denominator q)

private theorem bernstein_sum_pos (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : ∀ i, (1 / 1000000000 : ℝ) ≤ c i) (x : I) :
    0 < ∑ i, c i * bernstein n i x := by
  have hsum : (∑ i : Fin (n + 1), (1 / 1000000000 : ℝ) * bernstein n i x) ≤
      ∑ i : Fin (n + 1), c i * bernstein n i x :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i) bernstein_nonneg)
  rw [← Finset.mul_sum, bernstein.probability, mul_one] at hsum
  exact (by norm_num : (0 : ℝ) < 1 / 1000000000).trans_le hsum

private theorem small_pair_polynomial {q : ℝ} (hq : q ∈ Set.Icc (1 / 10 : ℝ) (4 / 25)) :
    0 < 1000 * pairNumerator q - 144 * denominator q ^ 2 := by
  let x : I := ⟨(50 / 3) * q + (-5 / 3), by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 4
    (fun i => ![2055537 / 1250,
      3934818 / 3125,
      13368429 / 15625,
      34105212 / 78125,
      1867536 / 390625] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [pairNumerator, denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

private theorem small_head_polynomial {q : ℝ} (hq : q ∈ Set.Icc (1 / 10 : ℝ) (4 / 25)) :
    0 < 2056 * denominator q - 500 * (q + 2) * (2 + 13 * q) := by
  let x : I := ⟨(50 / 3) * q + (-5 / 3), by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 2
    (fun i => ![1269 / 25,
      4482 / 125,
      3096 / 625] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [pairNumerator, denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

private theorem head_polynomial {q : ℝ} (hq : q ∈ Set.Icc (1 / 10 : ℝ) (1 / 5)) :
    0 < 104 * denominator q - 25 * (q + 2) * (2 + 13 * q) := by
  let x : I := ⟨(10) * q + (-1), by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 2
    (fun i => ![459 / 100,
      189 / 50,
      19 / 25] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [pairNumerator, denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

private theorem selector_polynomial {q : ℝ} (hq : q ∈ Set.Icc (4 / 25 : ℝ) (1 / 5)) :
    0 < 7500 * q * (1 + 2 * q) * (q + 2) - 2028 * denominator q * (q + 2) +
      1525 * (2 - q) * denominator q := by
  let x : I := ⟨(25) * q + (-4), by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 3
    (fun i => ![675558 / 15625,
      510257 / 3125,
      548359 / 1875,
      53937 / 125] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [pairNumerator, denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

private theorem pair_polynomial {q : ℝ} (hq : q ∈ Set.Icc (1 / 10 : ℝ) (19 / 160)) :
    0 < pairNumerator q := by
  let x : I := ⟨(160 / 3) * q + (-16 / 3), by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 4
    (fun i => ![4131 / 2000,
      2511 / 1280,
      950589 / 512000,
      14338377 / 8192000,
      215327727 / 131072000] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [pairNumerator, denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

private theorem square_polynomial {q : ℝ} (hq : q ∈ Set.Icc (1 / 10 : ℝ) (19 / 160)) :
    0 < 4 * (q + 2 * q ^ 2) * denominator q * (q + 2) + (2 - q) * pairNumerator q -
      162 * (2 + 3 * q) * q ^ 2 := by
  let x : I := ⟨(160 / 3) * q + (-16 / 3), by constructor <;> nlinarith [hq.1, hq.2]⟩
  have hpos := bernstein_sum_pos 5
    (fun i => ![192213 / 100000,
      2503467 / 1600000,
      30577743 / 25600000,
      332326557 / 409600000,
      2721421233 / 6553600000,
      635941287 / 104857600000] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [pairNumerator, denominator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

/-- The exact small-parameter saturated-pair product margin. -/
theorem pair_floor_gt_nine_thousandths {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 10 : ℝ) (4 / 25)) :
    9 / 1000 < pairFloor q := by
  have hR := denominator_pos (show 0 ≤ q by linarith [hq.1])
  have hp := small_pair_polynomial hq
  unfold pairFloor
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith

/-- The exact head-row cap on the small-parameter interval. -/
theorem head_cap_lt_small {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 10 : ℝ) (4 / 25)) :
    headCap q < 257 / 500 := by
  have hR := denominator_pos (show 0 ≤ q by linarith [hq.1])
  have hp := small_head_polynomial hq
  unfold headCap
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

/-- The exact head-row cap throughout the actual middle-E2 interval. -/
theorem head_cap_lt_thirteen_twenty_fifths {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 10 : ℝ) (1 / 5)) :
    headCap q < 13 / 25 := by
  have hR := denominator_pos (show 0 ≤ q by linarith [hq.1])
  have hp := head_polynomial hq
  unfold headCap
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

/-- The contact gap lies strictly above the selector value at `13/50`. -/
theorem gap_floor_gt_selector_thirteen_fiftieths {q : ℝ}
    (hq : q ∈ Set.Icc (4 / 25 : ℝ) (1 / 5)) :
    169 / 1250 - 61 / 600 * multiplier q < gapFloor q := by
  have hR := denominator_pos (show 0 ≤ q by linarith [hq.1])
  have hq2 : 0 < 2 + q := by linarith [hq.1]
  have hq2' : 0 < q + 2 := by linarith
  have hid : 15000 * denominator q * (q + 2) *
      (gapFloor q - (169 / 1250 - 61 / 600 * multiplier q)) =
      7500 * q * (1 + 2 * q) * (q + 2) - 2028 * denominator q * (q + 2) +
        1525 * (2 - q) * denominator q := by
    unfold gapFloor multiplier
    field_simp
    ring
  have hp := selector_polynomial hq
  rw [← hid] at hp
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity)).mp hp)

/-- The actual parent-count criterion is strictly positive through the cutoff. -/
theorem pair_floor_pos_cutoff {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 10 : ℝ) (19 / 160)) : 0 < pairFloor q := by
  have hR := denominator_pos (show 0 ≤ q by linarith [hq.1])
  exact div_pos (pair_polynomial hq) (by positivity)

/-- The exact three-distinct-square obstruction through `19/160`. -/
theorem off_pair_square_margin_pos {q : ℝ}
    (hq : q ∈ Set.Icc (1 / 10 : ℝ) (19 / 160)) :
    (2 - multiplier q) * ratioCap q ^ 2 <
      gapFloor q + 2 * multiplier q * pairFloor q := by
  have hR := denominator_pos (show 0 ≤ q by linarith [hq.1])
  have hq2 : 0 < 2 + q := by linarith [hq.1]
  have hq2' : 0 < q + 2 := by linarith
  have hid : 8 * denominator q ^ 2 * (q + 2) *
      (gapFloor q + 2 * multiplier q * pairFloor q -
        (2 - multiplier q) * ratioCap q ^ 2) =
      4 * (q + 2 * q ^ 2) * denominator q * (q + 2) +
        (2 - q) * pairNumerator q - 162 * (2 + 3 * q) * q ^ 2 := by
    unfold gapFloor multiplier pairFloor ratioCap
    field_simp
    ring
  have hp := square_polynomial hq
  rw [← hid] at hp
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity)).mp hp)

/-- Only the cell above the already proved quarter floor is needed. -/
theorem selectorEnvelope_le_thirteen_fiftieths {ell A : ℝ}
    (hell : ell ∈ Set.Icc (0 : ℝ) 1)
    (hA : A ∈ Set.Icc (1 / 4 : ℝ) (13 / 50)) :
    ForwardPeak.selectorEnvelope ell A ≤ 169 / 1250 - 61 / 600 * ell := by
  have hcell : A ∈ Set.Icc (1 / ((2 : ℝ) + 2)) (1 / ((2 : ℝ) + 1)) := by
    constructor <;> norm_num <;> linarith [hA.1, hA.2]
  rw [ForwardPeak.selectorEnvelope, Benchmark.splitValue_on_cell 2 hcell]
  norm_num [Benchmark.splitPolynomial]
  have hcoef : 0 ≤ 2 * (A + 13 / 50) + ell * (4 / 3 - 25 / 6 * (A + 13 / 50)) := by
    have hneg : 4 / 3 - 25 / 6 * (A + 13 / 50) ≤ 0 := by linarith [hA.1]
    have hmul := mul_le_mul_of_nonpos_right hell.2 hneg
    nlinarith [hA.2]
  have hprod := mul_nonneg (show 0 ≤ 13 / 50 - A by linarith [hA.2]) hcoef
  nlinarith

/-- A private source is smaller than twice its peak using only the paid
contact, selector, product and head-row bounds. -/
theorem private_source_mass_lt_twice_peak {q A u v a gamma : ℝ}
    (hq : q ∈ Set.Icc (1 / 10 : ℝ) (1 / 5))
    (hquarter : 1 / 4 < A) (hhalf : A < 1 / 2)
    (hu : 0 < u) (hv : v < A) (hproduct : pairFloor q < u * v)
    (hhead : u + a < headCap q) (hgamma : gapFloor q < gamma)
    (hselector : gamma ≤ ForwardPeak.selectorEnvelope (multiplier q) A) : a < 2 * A := by
  by_cases hsmall : q ≤ 4 / 25
  · have hqsmall : q ∈ Set.Icc (1 / 10 : ℝ) (4 / 25) := ⟨hq.1, hsmall⟩
    have hp := pair_floor_gt_nine_thousandths hqsmall
    have hh := head_cap_lt_small hqsmall
    have huv := mul_lt_mul_of_pos_left (show v < 1 / 2 by linarith) hu
    nlinarith
  · have hlarge : q ∈ Set.Icc (4 / 25 : ℝ) (1 / 5) := ⟨(lt_of_not_ge hsmall).le, hq.2⟩
    have hfloor := gap_floor_gt_selector_thirteen_fiftieths hlarge
    have hA : 13 / 50 < A := by
      by_contra hn
      have hq2 : 0 < 2 + q := by linarith [hq.1]
      have hell : multiplier q ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith [hq.2]) hq2.le
        · exact (div_le_iff₀ hq2).mpr (by linarith [hq.1])
      have hbound := selectorEnvelope_le_thirteen_fiftieths hell
        ⟨hquarter.le, le_of_not_gt hn⟩
      linarith
    have hh := head_cap_lt_thirteen_twenty_fifths hq
    linarith

end Erdos1017.MiddleE2OffPair

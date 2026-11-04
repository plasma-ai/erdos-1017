module

public import Erdos1017.Multipartite.TwoHead.TwoHeadFamilyBoundary

/-!
# Scalar interfaces for the positive-dust tail cells

The factorial-moment gap is `t + (S-t)^2`, equivalently `S - (S-t)*(1-(S-t))`.
The individual tail-count case exclusions are not part of this module.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TwoHeadTailAlgebra

open TwoHeadCountLaw

theorem floorMoment_gap_identity (t : ℕ) (S : ℝ) :
    S ^ 2 - floorMoment t S = (t : ℝ) + (S - (t : ℝ)) ^ 2 := by
  unfold floorMoment
  ring

theorem floorMoment_gap_remainder (t : ℕ) (S : ℝ) :
    S ^ 2 - floorMoment t S = S - (S - (t : ℝ)) * (1 - (S - (t : ℝ))) := by
  unfold floorMoment
  ring

/-- The corrected gap is positive and at most the dust mean on each closed
adjacent-count cell, including integer means. -/
theorem floorMoment_gap_bounds (t : ℕ) {S : ℝ} (hS : 0 < S)
    (htlo : (t : ℝ) ≤ S) (hthi : S ≤ (t : ℝ) + 1) :
    0 < S ^ 2 - floorMoment t S ∧ S ^ 2 - floorMoment t S ≤ S := by
  constructor
  · rw [floorMoment_gap_identity]
    by_cases ht : t = 0
    · subst t
      simpa using sq_pos_of_pos hS
    · have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)
      positivity
  · rw [floorMoment_gap_remainder]
    have hp := mul_nonneg (sub_nonneg.mpr htlo)
      (show 0 ≤ 1 - (S - (t : ℝ)) by linarith)
    linarith

theorem conditionalMoment_gt_sq (t : ℕ) {x S : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hS : 0 < S) (htlo : (t : ℝ) ≤ S) (hthi : S ≤ (t : ℝ) + 1) :
    S ^ 2 < conditionalMoment x S t := by
  have hgap := (floorMoment_gap_bounds t hS htlo hthi).1
  unfold conditionalMoment
  apply (lt_div_iff₀ (by linarith : 0 < 1 - x)).mpr
  nlinarith [mul_pos hx hgap]

theorem conditional_ratio_identity (t : ℕ) {x S : ℝ} (hx1 : x < 1) (hS : S ≠ 0) :
    conditionalMoment x S t / S =
      S + (x / (1 - x)) * ((S ^ 2 - floorMoment t S) / S) := by
  have hx' : 1 - x ≠ 0 := by linarith
  unfold conditionalMoment
  field_simp
  ring

/-- The ceiling upper estimate, from the upper bound on the factorial-moment
gap. -/
theorem conditional_ratio_le (t : ℕ) {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hS : 0 < S) (htlo : (t : ℝ) ≤ S) (hthi : S ≤ (t : ℝ) + 1) :
    conditionalMoment x S t / S ≤ S + x / (1 - x) := by
  have hgap := (floorMoment_gap_bounds t hS htlo hthi).2
  have hratio : (S ^ 2 - floorMoment t S) / S ≤ 1 := (div_le_one hS).mpr hgap
  have hxratio : 0 ≤ x / (1 - x) := div_nonneg hx (by linarith)
  rw [conditional_ratio_identity t hx1 hS.ne']
  nlinarith [mul_le_mul_of_nonneg_left hratio hxratio]

/-- A genuinely positive secondary head selects an index above the floor. -/
theorem floor_lt_selectedIndex {x S : ℝ} (hx : 0 < x) (hx1 : x < 1) (hS : 0 < S) :
    ⌊S⌋₊ < selectedIndex x S := by
  have hR := conditionalMoment_gt_sq ⌊S⌋₊ hx hx1 hS
    (Nat.floor_le hS.le) (Nat.lt_floor_add_one S).le
  have hratio : S < conditionalMoment x S ⌊S⌋₊ / S :=
    (lt_div_iff₀ hS).mpr (by simpa only [pow_two] using hR)
  unfold selectedIndex
  exact Nat.lt_ceil.mpr ((Nat.floor_le hS.le).trans_lt hratio)

theorem cellValue_conditional (j t : ℕ) {x S : ℝ} (hj : 0 < j) (hx1 : x < 1) :
    cellValue j t x S = x + (1 - x) *
      ((2 * (j : ℝ) * S - conditionalMoment x S t) / ((j : ℝ) * ((j : ℝ) + 1))) := by
  have hj0 : (j : ℝ) ≠ 0 := (Nat.cast_pos.mpr hj).ne'
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hx' : 1 - x ≠ 0 := by linarith
  unfold cellValue conditionalMoment floorMoment
  field_simp
  ring

/-- The selected lower ceiling bracket bounds the nonempty conditional
count mass, giving the anchor-normalized cost estimate. -/
theorem cellValue_le_count_bound (j t : ℕ) {x S : ℝ} (hj : 0 < j) (hx1 : x < 1)
    (hRlo : ((j : ℝ) - 1) * S ≤ conditionalMoment x S t) :
    cellValue j t x S ≤ x + (1 - x) * S / (j : ℝ) := by
  have hj0 : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hJ : 0 < (j : ℝ) * ((j : ℝ) + 1) := by positivity
  have hquot : (2 * (j : ℝ) * S - conditionalMoment x S t) /
      ((j : ℝ) * ((j : ℝ) + 1)) ≤ S / (j : ℝ) := by
    apply (div_le_iff₀ hJ).mpr
    have hid : (S / (j : ℝ)) * ((j : ℝ) * ((j : ℝ) + 1)) = ((j : ℝ) + 1) * S := by
      field_simp
    rw [hid]
    linarith
  rw [cellValue_conditional j t hj hx1]
  have h := mul_le_mul_of_nonneg_left hquot (show 0 ≤ 1 - x by linarith)
  simpa only [mul_div_assoc] using add_le_add (le_refl x) h

/-- Exact source comparison identity with a supplied algebraic square root. -/
theorem comparison_identity_of_sq (j t : ℕ) {x S ρ : ℝ} (hj : 0 < j)
    (hM : 1 + x + S ≠ 0) (hρ : ρ ^ 2 = 1 + x ^ 2) (hρ1 : ρ + 1 ≠ 0) :
    ((j : ℝ) * ((j : ℝ) + 1)) *
        ((1 + x + S) ^ 2 * Benchmark.splitPolynomial j (ρ / (1 + x + S)) -
          cellValue j t x S) =
      2 * ((j : ℝ) + 1) * x ^ 2 * (S + x - ρ) / (ρ + 1) -
        x * ((j : ℝ) - (t : ℝ) - 1) * ((j : ℝ) + (t : ℝ) - 2 * S) := by
  have hj0 : (j : ℝ) ≠ 0 := (Nat.cast_pos.mpr hj).ne'
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hfactor : (ρ + 1) *
      (((j : ℝ) * ((j : ℝ) + 1)) *
          ((1 + x + S) ^ 2 * Benchmark.splitPolynomial j (ρ / (1 + x + S)) -
            cellValue j t x S) -
        (2 * ((j : ℝ) + 1) * x ^ 2 * (S + x - ρ) / (ρ + 1) -
          x * ((j : ℝ) - (t : ℝ) - 1) * ((j : ℝ) + (t : ℝ) - 2 * S))) =
      (ρ ^ 2 - 1 - x ^ 2) *
        (-2 * ρ * (j : ℝ) - ρ + 2 * S * (j : ℝ) + 2 * S + 2 * (j : ℝ) * x + 2 * x + 1) := by
    unfold Benchmark.splitPolynomial cellValue
    field_simp
    ring
  have hzero : ρ ^ 2 - 1 - x ^ 2 = 0 := by linarith
  rw [hzero, zero_mul] at hfactor
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hρ1)

/-- The comparison identity for the actual nonnegative square root. -/
theorem comparison_identity (j t : ℕ) {x S : ℝ} (hj : 0 < j) (hM : 1 + x + S ≠ 0) :
    ((j : ℝ) * ((j : ℝ) + 1)) *
        ((1 + x + S) ^ 2 *
          Benchmark.splitPolynomial j (Real.sqrt (1 + x ^ 2) / (1 + x + S)) -
          cellValue j t x S) =
      2 * ((j : ℝ) + 1) * x ^ 2 * (S + x - Real.sqrt (1 + x ^ 2)) /
          (Real.sqrt (1 + x ^ 2) + 1) -
        x * ((j : ℝ) - (t : ℝ) - 1) * ((j : ℝ) + (t : ℝ) - 2 * S) := by
  exact comparison_identity_of_sq j t hj hM (Real.sq_sqrt (by positivity))
    (ne_of_gt (by positivity))

end Erdos1017.TwoHeadTailAlgebra

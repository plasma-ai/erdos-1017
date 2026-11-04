module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorSumTwo
public import Erdos1017.Exclusions.Common.SelectorPairUnion

/-!
# Middle and large count-cell estimates for the sharp selector

Exact rescaling of the dual's linear and quadratic terms gives the sharp middle
count-cell estimate from two sum-two Boolean-dual inequalities, and above total
load three the nonpositive pair coefficients make rescaling an upper bound;
selector attainment turns both into value bounds.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace Erdos1017.Selector.Sharp

variable {n : ℕ}

/-- Exact rescaling of the original dual's linear and quadratic terms. -/
theorem objective_scale (p : Fin n → ℝ) (D : Dual n) (r : ℝ) :
    objective (fun i => r * p i) D = r * (∑ i, D.alpha i * p i) +
      r ^ 2 * ((∑ i, ∑ j, D.beta i j * (p i * p j)) / 2) := by
  unfold objective
  have hlin : (∑ i, D.alpha i * (r * p i)) = r * ∑ i, D.alpha i * p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hquad : (∑ i, ∑ j, D.beta i j * (r * p i * (r * p j))) =
      r ^ 2 * ∑ i, ∑ j, D.beta i j * (p i * p j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlin, hquad]
  ring

/-- The sharp middle count-cell estimate follows from two genuine
sum-two Boolean-dual inequalities at the same rescaled load vector. -/
theorem objective_le_middle_countCell (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : (∑ i, p i) ∈ Icc (2 : ℝ) 3)
    (D : Dual n) (hD : DualFeasible D)
    (hα : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) (hβ : ∀ i j, D.beta i j ≤ 0) :
    objective p D ≤ (6 * (∑ i, p i) - (∑ i, p i) ^ 2) / 12 + (∑ i, (p i) ^ 2) / 3 := by
  let S : ℝ := ∑ i, p i
  let Q : ℝ := ∑ i, (p i) ^ 2
  let L : ℝ := ∑ i, D.alpha i * p i
  let B : ℝ := (∑ i, ∑ j, D.beta i j * (p i * p j)) / 2
  let r : ℝ := 2 / S
  have hS0 : 0 < S := by dsimp [S]; linarith [hS.1]
  have hr : r ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by norm_num) hS0.le, (div_le_one hS0).mpr hS.1⟩
  have hp' (i : Fin n) : r * p i ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hr.1 (hp i).1, (mul_le_mul_of_nonneg_left (hp i).2 hr.1).trans (by simpa using hr.2)⟩
  have hsum : ∑ i, r * p i = 2 := by
    rw [← Finset.mul_sum]
    change (2 / S) * S = 2
    exact div_mul_cancel₀ 2 hS0.ne'
  have hsq : (∑ i, (r * p i) ^ 2) = r ^ 2 * Q := by
    simp only [mul_pow, ← Finset.mul_sum]
    rfl
  have hlin : (∑ i, D.alpha i * (r * p i)) = r * L := by
    dsimp [L]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hthree := objective_le_sumTwo (fun i => r * p i) hp' hsum D hD
  have hfour := three_objective_sub_linear_sub_square_le_one
    (fun i => r * p i) hp' hsum D hD hα hβ
  rw [objective_scale, hsq] at hthree
  rw [objective_scale, hlin, hsq] at hfour
  change r * L + r ^ 2 * B ≤ (2 + r ^ 2 * Q) / 3 at hthree
  change 3 * (r * L + r ^ 2 * B) - r * L - r ^ 2 * Q ≤ 1 at hfour
  have hw3 : 0 ≤ S * (3 - S) / 2 := by
    have h : S ≤ 3 := hS.2
    positivity
  have hw4 : 0 ≤ S * (S - 2) / 4 := by
    have h : 2 ≤ S := hS.1
    positivity
  have hnonneg := add_nonneg
    (mul_nonneg hw3 (sub_nonneg.mpr hthree)) (mul_nonneg hw4 (sub_nonneg.mpr hfour))
  have hid : S * (3 - S) / 2 * ((2 + r ^ 2 * Q) / 3 - (r * L + r ^ 2 * B)) +
      S * (S - 2) / 4 * (1 - (3 * (r * L + r ^ 2 * B) - r * L - r ^ 2 * Q)) =
      (6 * S - S ^ 2) / 12 + Q / 3 - (L + B) := by
    dsimp [r]
    field_simp
    ring
  rw [hid] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Exact selector attainment supplies the signed dual needed above. -/
theorem value_le_middle_countCell (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : (∑ i, p i) ∈ Icc (2 : ℝ) 3) :
    value p ≤ (6 * (∑ i, p i) - (∑ i, p i) ^ 2) / 12 + (∑ i, (p i) ^ 2) / 3 := by
  obtain ⟨_, _, _, D, hD, hvalue, hα, hβ⟩ := value_attained p hp
  rw [← hvalue]
  exact objective_le_middle_countCell p hp hS D hD.1 hα hβ

/-- Above total load three, the actual nonpositive pair coefficients
make rescaling a valid upper bound on the original dual objective. -/
theorem objective_le_large_countCell (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : 3 ≤ ∑ i, p i)
    (D : Dual n) (hD : DualFeasible D)
    (hα : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) (hβ : ∀ i j, D.beta i j ≤ 0) :
    objective p D ≤ (∑ i, p i) / 4 + (∑ i, (p i) ^ 2) / (∑ i, p i) := by
  let S : ℝ := ∑ i, p i
  let Q : ℝ := ∑ i, (p i) ^ 2
  let L : ℝ := ∑ i, D.alpha i * p i
  let B : ℝ := (∑ i, ∑ j, D.beta i j * (p i * p j)) / 2
  let r : ℝ := 3 / S
  have hS0 : 0 < S := by dsimp [S]; linarith
  have hr : r ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by norm_num) hS0.le, (div_le_one hS0).mpr hS⟩
  have hp' (i : Fin n) : r * p i ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hr.1 (hp i).1, (mul_le_mul_of_nonneg_left (hp i).2 hr.1).trans (by simpa using hr.2)⟩
  have hsum : ∑ i, r * p i = 3 := by
    rw [← Finset.mul_sum]
    exact div_mul_cancel₀ 3 hS0.ne'
  have hB : B ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    exact Finset.sum_nonpos (fun i _ => Finset.sum_nonpos
      (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hβ i j) (mul_nonneg (hp i).1 (hp j).1)))
  have hmiddle := objective_le_middle_countCell (fun i => r * p i) hp'
    (by rw [hsum]; norm_num) D hD hα hβ
  rw [hsum, objective_scale] at hmiddle
  have hsq : (∑ i, (r * p i) ^ 2) = r ^ 2 * Q := by
    simp only [mul_pow, ← Finset.mul_sum]
    rfl
  rw [hsq] at hmiddle
  change r * L + r ^ 2 * B ≤ (6 * 3 - 3 ^ 2) / 12 + r ^ 2 * Q / 3 at hmiddle
  have hscaled := mul_le_mul_of_nonneg_left hmiddle (show 0 ≤ S / 3 by positivity)
  have hnormalize : S / 3 * (r * L + r ^ 2 * B) = L + r * B := by
    dsimp [r]
    field_simp
  have hright : S / 3 * ((6 * 3 - 3 ^ 2) / 12 + r ^ 2 * Q / 3) = S / 4 + Q / S := by
    dsimp [r]
    field_simp
    ring
  rw [hnormalize, hright] at hscaled
  have hpair := mul_nonneg (sub_nonneg.mpr hr.2) (neg_nonneg.mpr hB)
  change L + B ≤ S / 4 + Q / S
  nlinarith

/-- The large-total sharp estimate holds for the exact finite selector value. -/
theorem value_le_large_countCell (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : 3 ≤ ∑ i, p i) :
    value p ≤ (∑ i, p i) / 4 + (∑ i, (p i) ^ 2) / (∑ i, p i) := by
  obtain ⟨_, _, _, D, hD, hvalue, hα, hβ⟩ := value_attained p hp
  rw [← hvalue]
  exact objective_le_large_countCell p hp hS D hD.1 hα hβ

end Erdos1017.Selector.Sharp

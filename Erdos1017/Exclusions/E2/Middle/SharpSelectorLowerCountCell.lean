module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorCountCells
public import Erdos1017.Multipartite.Selector.SelectorSigns
public import Mathlib.Analysis.Real.Sqrt

/-!
# Lower count cell for the sharp selector

Pair tests of a feasible dual bound its two-draw moment by its diagonal, and
balanced and heavy-root cases give the two-fifths lower count cell for every
sign-feasible dual on `10/7 ≤ S ≤ 2`; selector attainment turns this into
`U(p) ≤ g₂(S) + (2/5) Q` (`value_le_lower_countCell`).
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace Erdos1017.Selector.Sharp

variable {n : ℕ}

/-- The two-label Boolean test of a feasible dual. -/
theorem pair_test (D : Dual n) (hD : DualFeasible D) (i j : Fin n) (hij : i ≠ j) :
    D.alpha i + D.alpha j + D.beta i j ≤ 1 := by
  let X : Selection n := fun l => decide (l = i ∨ l = j)
  have hb (l : Fin n) : bit (X l) = (if l = i then 1 else 0) + (if l = j then 1 else 0) := by
    by_cases hi : l = i
    · subst l
      simp [X, bit, hij]
    by_cases hj : l = j
    · subst l
      simp [X, bit, Ne.symm hij]
    simp [X, bit, hi, hj]
  have ht := hD X
  unfold quadratic objective at ht
  simp only [hb, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, D.beta_diag] at ht
  rw [D.beta_symm j i] at ht
  linarith

/-- The pair tests, summed against a nonnegative load vector, bound its
two-draw moment by its diagonal. -/
theorem pair_moment_le (D : Dual n) (hD : DualFeasible D)
    (hα : ∀ i, D.alpha i ≤ 1) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    2 * (∑ i, p i) * (∑ i, D.alpha i * p i) + (∑ i, ∑ j, D.beta i j * (p i * p j)) ≤
      (∑ i, p i) ^ 2 + ∑ i, (p i) ^ 2 := by
  have hrow (i : Fin n) : (∑ j, p i * p j * (D.alpha i + D.alpha j + D.beta i j - 1)) ≤
      (p i) ^ 2 * (2 * D.alpha i - 1) := by
    calc
      (∑ j, p i * p j * (D.alpha i + D.alpha j + D.beta i j - 1)) ≤
          ∑ j, (if j = i then (p i) ^ 2 * (2 * D.alpha i - 1) else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hji : j = i
        · subst j
          simp only [↓reduceIte, D.beta_diag]
          exact le_of_eq (by ring)
        · simp only [hji, ↓reduceIte]
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hp i) (hp j))
            (by linarith [pair_test D hD i j (Ne.symm hji)])
      _ = (p i) ^ 2 * (2 * D.alpha i - 1) := by simp
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  have hexp : (∑ i, ∑ j, p i * p j * (D.alpha i + D.alpha j + D.beta i j - 1)) =
      (∑ i, ∑ j, D.alpha i * p i * p j) + (∑ i, ∑ j, p i * (D.alpha j * p j)) +
        (∑ i, ∑ j, D.beta i j * (p i * p j)) - ∑ i, ∑ j, p i * p j := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h1 : (∑ i, ∑ j, D.alpha i * p i * p j) = (∑ i, D.alpha i * p i) * ∑ j, p j :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have h2 : (∑ i, ∑ j, p i * (D.alpha j * p j)) = (∑ i, p i) * ∑ j, D.alpha j * p j :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have h3 : (∑ i, ∑ j, p i * p j) = (∑ i, p i) * ∑ j, p j :=
    (Finset.sum_mul_sum _ _ _ _).symm
  have hdiag : (∑ i, (p i) ^ 2 * (2 * D.alpha i - 1)) ≤ ∑ i, (p i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (p i), hα i]
  rw [hexp, h1, h2, h3] at hsum
  nlinarith

/-- Lower count cell when every load is at most half the total: the sharp
sum-two bound at `2p/S` and the pair moment combine with nonnegative weights
`(2 - S)/(2S)` and `(S - 1)/(2S)`. -/
theorem objective_le_lower_countCell_balanced (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : (∑ i, p i) ∈ Icc (10 / 7 : ℝ) 2)
    (hhalf : ∀ i, p i ≤ (∑ i, p i) / 2)
    (D : Dual n) (hD : DualFeasible D) (hα : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) :
    objective p D ≤ (4 * (∑ i, p i) - (∑ i, p i) ^ 2) / 6 + 2 / 5 * ∑ i, (p i) ^ 2 := by
  let S : ℝ := ∑ i, p i
  let Q : ℝ := ∑ i, (p i) ^ 2
  let L : ℝ := ∑ i, D.alpha i * p i
  let B : ℝ := (∑ i, ∑ j, D.beta i j * (p i * p j)) / 2
  let r : ℝ := 2 / S
  have hS0 : 0 < S := by dsimp [S]; linarith [hS.1]
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (p i))
  have hp' (i : Fin n) : r * p i ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (by positivity) (hp i).1, ?_⟩
    have h := hhalf i
    change p i ≤ S / 2 at h
    calc r * p i ≤ r * (S / 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 1 := by dsimp [r]; field_simp
  have hsum : ∑ i, r * p i = 2 := by
    rw [← Finset.mul_sum]
    change (2 / S) * S = 2
    exact div_mul_cancel₀ 2 hS0.ne'
  have hsq : (∑ i, (r * p i) ^ 2) = r ^ 2 * Q := by
    simp only [mul_pow, ← Finset.mul_sum]
    rfl
  have htwo := objective_le_sumTwo (fun i => r * p i) hp' hsum D hD
  rw [objective_scale, hsq] at htwo
  change r * L + r ^ 2 * B ≤ (2 + r ^ 2 * Q) / 3 at htwo
  have htwo' : 2 * S * L + 4 * B ≤ (2 * S ^ 2 + 4 * Q) / 3 := by
    have hmul := mul_le_mul_of_nonneg_left htwo (sq_nonneg S)
    have hl : S ^ 2 * (r * L + r ^ 2 * B) = 2 * S * L + 4 * B := by
      dsimp [r]; field_simp; ring
    have hr : S ^ 2 * ((2 + r ^ 2 * Q) / 3) = (2 * S ^ 2 + 4 * Q) / 3 := by
      dsimp [r]; field_simp; ring
    rw [hl, hr] at hmul
    exact hmul
  have hpair : 2 * S * L + 2 * B ≤ S ^ 2 + Q := by
    have h := pair_moment_le D hD (fun i => (hα i).2) p (fun i => (hp i).1)
    dsimp only [S, L, B, Q]
    linarith
  have hw1 : 0 ≤ 2 - S := by dsimp [S]; linarith [hS.2]
  have hw2 : 0 ≤ S - 1 := by dsimp [S]; linarith [hS.1]
  have hw3 : 0 ≤ 7 * S - 10 := by dsimp [S]; linarith [hS.1]
  have hcomb : 2 * S * (L + B) ≤ 2 * S * ((4 * S - S ^ 2) / 6 + 2 / 5 * Q) := by
    nlinarith [mul_le_mul_of_nonneg_left hpair hw1, mul_le_mul_of_nonneg_left htwo' hw2,
      mul_nonneg hw3 hQ]
  have hfinal := le_of_mul_le_mul_left hcomb (by positivity)
  change L + B ≤ (4 * S - S ^ 2) / 6 + 2 / 5 * Q
  exact hfinal

/-- Lower count cell with a heavy root `x > S/2`: the root contributes at
most `x` by its pair tests, and the scaled tail obeys the independent
Bernoulli bound at scale `v = max (1 - x) √Q_tail`. -/
theorem objective_le_lower_countCell_heavy (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : (∑ i, p i) ∈ Icc (10 / 7 : ℝ) 2)
    (k : Fin n) (hk : (∑ i, p i) / 2 < p k)
    (D : Dual n) (hD : DualFeasible D) (hα : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1)
    (hβ : ∀ i j, D.beta i j ≤ 0) :
    objective p D ≤ (4 * (∑ i, p i) - (∑ i, p i) ^ 2) / 6 + 2 / 5 * ∑ i, (p i) ^ 2 := by
  let x := p k
  let t := Function.update p k 0
  have ht (j : Fin n) : t j = if j = k then 0 else p j := by
    by_cases hj : j = k
    · subst j; simp [t]
    · simp [t, hj]
  have ht0 (j : Fin n) : 0 ≤ t j := by rw [ht]; split_ifs <;> simp [(hp j).1]
  have hpt : p = Function.update t k x := by
    simp only [t, x, Function.update_idem, Function.update_eq_self]
  have hsplit (f : ℝ → ℝ) (hf : f 0 = 0) : (∑ j, f (p j)) = f x + ∑ j, f (t j) := by
    have hpoint (j : Fin n) : f (p j) = f (t j) + if j = k then f x else 0 := by
      rw [ht]
      by_cases hj : j = k
      · subst j; simp [x, hf]
      · simp [hj]
    simp only [hpoint, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  let R := ∑ j, t j
  let Qt := ∑ j, (t j) ^ 2
  let Lt := ∑ j, D.alpha j * t j
  let Bt := (∑ i, ∑ j, D.beta i j * (t i * t j)) / 2
  have hSR : (∑ i, p i) = x + R := hsplit id rfl
  have hQ : (∑ i, (p i) ^ 2) = x ^ 2 + Qt := hsplit (fun a => a ^ 2) (by norm_num)
  have hx1 : x ≤ 1 := (hp k).2
  have hR1 : R ≤ 1 := by
    have h := hS.2
    rw [hSR] at h hk
    linarith
  have hQt : 0 ≤ Qt := Finset.sum_nonneg (fun j _ => sq_nonneg (t j))
  have hBt : Bt ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    exact Finset.sum_nonpos (fun i _ => Finset.sum_nonpos
      (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hβ i j) (mul_nonneg (ht0 i) (ht0 j))))
  -- Root part.
  have hupdate := objective_update t D k x
  rw [← hpt] at hupdate
  have htk : t k = 0 := by simp [t]
  rw [htk, sub_zero] at hupdate
  have hrow : (∑ j, D.beta k j * t j) ≤ ∑ j, t j * (1 - D.alpha k - D.alpha j) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = k
    · subst j; rw [htk]; simp
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith [pair_test D hD k j (Ne.symm hj)]) (ht0 j)
  have hrow' : (∑ j, t j * (1 - D.alpha k - D.alpha j)) = R * (1 - D.alpha k) - Lt := by
    have e (j : Fin n) : t j * (1 - D.alpha k - D.alpha j) =
        t j * (1 - D.alpha k) - D.alpha j * t j := by ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hroot : D.alpha k + R * (1 - D.alpha k) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hα k).2) (sub_nonneg.mpr hR1)]
  have hx0 : 0 ≤ x := (hp k).1
  have hobjt : objective t D = Lt + Bt := rfl
  -- Tail part, at scale `v`.
  have hq0 : 0 ≤ 1 - x := by linarith
  obtain ⟨v, hv⟩ : ∃ v, v = max (1 - x) (Real.sqrt Qt) := ⟨_, rfl⟩
  have hqv : 1 - x ≤ v := hv ▸ le_max_left _ _
  have htv (j : Fin n) : t j ≤ v := by
    have hj : (t j) ^ 2 ≤ Qt :=
      Finset.single_le_sum (fun i _ => sq_nonneg (t i)) (Finset.mem_univ j)
    exact (le_abs_self _).trans ((Real.abs_le_sqrt hj).trans (hv ▸ le_max_right _ _))
  have hv2 : v ^ 2 ≤ (1 - x) ^ 2 + Qt := by
    rcases max_choice (1 - x) (Real.sqrt Qt) with h | h
    · rw [hv, h]; linarith
    · rw [hv, h, Real.sq_sqrt hQt]; nlinarith [sq_nonneg (1 - x)]
  have htail : (1 - x) * Lt + Bt ≤ (1 - x) * v := by
    rcases (hq0.trans hqv).eq_or_lt with hv0 | hv0
    · have hq : 1 - x = 0 := le_antisymm (hqv.trans hv0.symm.le) hq0
      rw [hq]
      linarith
    · have hy (j : Fin n) : 0 ≤ (1 / v) * t j ∧ (1 / v) * t j ≤ 1 := by
        refine ⟨mul_nonneg (by positivity) (ht0 j), ?_⟩
        calc (1 / v) * t j ≤ (1 / v) * v := mul_le_mul_of_nonneg_left (htv j) (by positivity)
          _ = 1 := by field_simp
      have h1 := objective_le_one (fun j => (1 / v) * t j) D hy hD
      rw [objective_scale] at h1
      change (1 / v) * Lt + (1 / v) ^ 2 * Bt ≤ 1 at h1
      have hscaled := mul_le_mul_of_nonneg_left h1 (mul_nonneg hq0 hv0.le)
      have he : (1 - x) * v * ((1 / v) * Lt + (1 / v) ^ 2 * Bt) =
          (1 - x) * Lt + (1 - x) / v * Bt := by
        field_simp
      rw [he, mul_one] at hscaled
      have hqv' : (1 - x) / v ≤ 1 := (div_le_one hv0).mpr hqv
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hqv') hBt]
  have hmain : objective p D ≤ x + (1 - x) * v := by
    rw [hupdate, hobjt]
    have hxrow := mul_le_mul_of_nonneg_left (hrow.trans_eq hrow') hx0
    have hxroot := mul_le_mul_of_nonneg_left hroot hx0
    nlinarith
  have hamgm : (1 - x) * v ≤ 5 / 8 * (1 - x) ^ 2 + 2 / 5 * v ^ 2 := by
    nlinarith [sq_nonneg (v - 5 / 4 * (1 - x))]
  have hx57 : 5 / 7 ≤ x := by
    have h := hS.1
    linarith
  have hg2 : 30 / 49 ≤ (4 * (x + R) - (x + R) ^ 2) / 6 := by
    have h1 : 10 / 7 ≤ x + R := hSR ▸ hS.1
    have h2 : x + R ≤ 2 := hSR ▸ hS.2
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show (0 : ℝ) ≤ 18 / 7 - (x + R) by linarith)]
  have hH : x + 41 / 40 * (1 - x) ^ 2 ≤ 30 / 49 + 2 / 5 * x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx57) (sub_nonneg.mpr hx1)]
  rw [hSR, hQ]
  nlinarith

/-- The two-fifths lower count cell for every sign-feasible dual, on the
whole closed range `10/7 ≤ S ≤ 2`, which contains `[3/2, 2]`. -/
theorem objective_le_lower_countCell (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : (∑ i, p i) ∈ Icc (10 / 7 : ℝ) 2)
    (D : Dual n) (hD : DualFeasible D) (hα : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1)
    (hβ : ∀ i j, D.beta i j ≤ 0) :
    objective p D ≤ (4 * (∑ i, p i) - (∑ i, p i) ^ 2) / 6 + 2 / 5 * ∑ i, (p i) ^ 2 := by
  by_cases hhalf : ∀ i, p i ≤ (∑ i, p i) / 2
  · exact objective_le_lower_countCell_balanced p hp hS hhalf D hD hα
  · push Not at hhalf
    obtain ⟨k, hk⟩ := hhalf
    exact objective_le_lower_countCell_heavy p hp hS k hk D hD hα hβ

/-- Exact selector attainment turns the dual estimate into the lower
count-cell value bound `U(p) ≤ g₂(S) + (2/5) Q`. -/
theorem value_le_lower_countCell (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hS : (∑ i, p i) ∈ Icc (10 / 7 : ℝ) 2) :
    value p ≤ (4 * (∑ i, p i) - (∑ i, p i) ^ 2) / 6 + 2 / 5 * ∑ i, (p i) ^ 2 := by
  obtain ⟨_, _, _, D, hD, hvalue, hα, hβ⟩ := value_attained p hp
  rw [← hvalue]
  exact objective_le_lower_countCell p hp hS D hD.1 hα hβ

end Erdos1017.Selector.Sharp

module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

/-!
# Two-point rounding and coercivity

Independent two-point rounding about a lower integer endpoint is defined, with
the expected clique charge at prescribed bin counts; tested positive-weight
rounded outcomes force the coercive quadratic estimate, which holds on every
probability vector with constant `δ = p₀/(2T)` and controls the charge at large
counts.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

open Selector

variable {m : ℕ}

/-- Independent two-point rounding about a supplied lower integer endpoint. -/
def rounded (a : Fin m → ℝ) (X : Selection m) (i : Fin m) : ℝ := a i + bit (X i)

theorem rounded_first (a p : Fin m → ℝ) (i : Fin m) :
    (∑ X, bernoulliWeight p X * rounded a X i) = a i + p i := by
  simp only [rounded, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    bernoulli_total, one_mul, bernoulli_first_moment]

theorem rounded_second (a p : Fin m → ℝ) (i j : Fin m) :
    (∑ X, bernoulliWeight p X * (rounded a X i * rounded a X j)) =
      (a i + p i) * (a j + p j) + if i = j then p i * (1 - p i) else 0 := by
  by_cases hij : i = j
  · subst j
    have hpoint (X : Selection m) :
        rounded a X i * rounded a X i = a i ^ 2 + (2 * a i + 1) * bit (X i) := by
      unfold rounded
      cases X i <;> simp [bit] <;> ring
    simp_rw [hpoint, mul_add, Finset.sum_add_distrib, ← mul_assoc,
      ← Finset.sum_mul]
    simp only [bernoulli_total, one_mul, ite_true]
    have hmoment := bernoulli_first_moment p i
    have hswap : (∑ X, bernoulliWeight p X * (2 * a i + 1) * bit (X i)) =
        (2 * a i + 1) * p i := by
      rw [← hmoment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      ring
    rw [hswap]
    ring
  · have hpoint (X : Selection m) :
        bernoulliWeight p X * (rounded a X i * rounded a X j) =
          bernoulliWeight p X * (a i * a j) +
          a i * (bernoulliWeight p X * bit (X j)) +
          a j * (bernoulliWeight p X * bit (X i)) +
          bernoulliWeight p X * (bit (X i) * bit (X j)) := by
      unfold rounded
      ring
    simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [bernoulli_total, bernoulli_first_moment, bernoulli_first_moment,
      bernoulli_pair_moment p i j hij, ite_eq_right hij]
    ring

/-- The sole diagonal correction in independent rounding is the Bernoulli variance. -/
theorem rounded_quadratic (a p : Fin m → ℝ) (P : Fin m → Fin m → ℝ) :
    (∑ X, bernoulliWeight p X * (∑ i, ∑ j, P i j * rounded a X i * rounded a X j)) =
      (∑ i, ∑ j, P i j * (a i + p i) * (a j + p j)) +
      ∑ i, P i i * (p i * (1 - p i)) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (i : Fin m) :
      (∑ X, ∑ j, bernoulliWeight p X * (P i j * rounded a X i * rounded a X j)) =
        (∑ j, P i j * (a i + p i) * (a j + p j)) + P i i * (p i * (1 - p i)) := by
    rw [Finset.sum_comm]
    have heq (j : Fin m) :
        (∑ X, bernoulliWeight p X * (P i j * rounded a X i * rounded a X j)) =
          P i j * ((a i + p i) * (a j + p j) + if i = j then p i * (1 - p i) else 0) := by
      rw [← rounded_second a p i j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      ring
    simp_rw [heq, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp [mul_add, add_mul, mul_assoc]
  simp_rw [hinner, Finset.sum_add_distrib]

/-- The fractional part used as the Bernoulli rounding probability. -/
def roundingProbability (x : Fin m → ℝ) (i : Fin m) : ℝ := x i - (⌊x i⌋₊ : ℝ)

/-- Actual integer counts, with zero-probability outcomes retained in the finite sample space. -/
def roundedCount (x : Fin m → ℝ) (X : Selection m) (i : Fin m) : ℕ :=
  ⌊x i⌋₊ + if X i then 1 else 0

theorem roundingProbability_mem (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) (i : Fin m) :
    0 ≤ roundingProbability x i ∧ roundingProbability x i < 1 := by
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le (hx i))
  · exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using Nat.lt_floor_add_one (x i))

theorem roundedCount_cast (x : Fin m → ℝ) (X : Selection m) (i : Fin m) :
    (roundedCount x X i : ℝ) = rounded (fun j => (⌊x j⌋₊ : ℝ)) X i := by
  unfold roundedCount rounded bit
  cases X i <;> simp

/-- Positive-weight outcomes never round past an integer upper bound. -/
theorem roundedCount_le (x : Fin m → ℝ) (T : ℕ) (hx0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, x i ≤ T) (X : Selection m)
    (hX : bernoulliWeight (roundingProbability x) X ≠ 0) (i : Fin m) :
    roundedCount x X i ≤ T := by
  have hf : ⌊x i⌋₊ ≤ T := Nat.floor_le_of_le (hx i)
  by_cases h : X i = true
  · have hlt : ⌊x i⌋₊ < T := by
      by_contra hlt
      have heq : ⌊x i⌋₊ = T := Nat.le_antisymm hf (Nat.le_of_not_gt hlt)
      have hxi : x i = T := le_antisymm (hx i) (by simpa [heq] using Nat.floor_le (hx0 i))
      apply hX
      unfold bernoulliWeight
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h, roundingProbability, hxi])
    simpa [roundedCount, h] using Nat.succ_le_of_lt hlt
  · simpa [roundedCount, h] using hf

theorem roundedCount_sum_le (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i)
    (X : Selection m) :
    (∑ i, (roundedCount x X i : ℝ)) ≤ (∑ i, x i) + m := by
  calc
    (∑ i, (roundedCount x X i : ℝ)) ≤ ∑ i, (x i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [roundedCount_cast, rounded]
      have hb : bit (X i) ≤ 1 := by cases X i <;> simp [bit]
      exact add_le_add (Nat.floor_le (hx i)) hb
    _ = (∑ i, x i) + m := by simp [Finset.sum_add_distrib]

/-- The expected clique charge at prescribed bin counts. -/
def countCharge (P : Fin m → Fin m → ℝ) (v : Fin m → ℝ) : ℝ :=
  ((∑ i, P i i * v i) - ∑ i, ∑ j, P i j * v i * v j) / 2

theorem rounded_charge (a p : Fin m → ℝ) (P : Fin m → Fin m → ℝ) :
    (∑ X, bernoulliWeight p X * countCharge P (rounded a X)) =
      countCharge P (fun i => a i + p i) -
        (∑ i, P i i * (p i * (1 - p i))) / 2 := by
  have hlin : (∑ X, bernoulliWeight p X * ∑ i, P i i * rounded a X i) =
      ∑ i, P i i * (a i + p i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← rounded_first a p i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _
    ring
  unfold countCharge
  simp only [mul_div, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hlin, rounded_quadratic]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Tested positive-weight rounded outcomes force the coercive quadratic estimate. -/
theorem quadratic_lower_bound_of_rounding (a p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (P : Fin m → Fin m → ℝ)
    (htest : ∀ X, bernoulliWeight p X ≠ 0 → countCharge P (rounded a X) ≤ 1) :
    (∑ i, P i i * (a i + p i)) - (∑ i, P i i * (p i * (1 - p i))) - 2 ≤
      ∑ i, ∑ j, P i j * (a i + p i) * (a j + p j) := by
  have hmean : (∑ X, bernoulliWeight p X * countCharge P (rounded a X)) ≤ 1 := by
    rw [← bernoulli_total p]
    apply Finset.sum_le_sum
    intro X _
    by_cases hX : bernoulliWeight p X = 0
    · simp [hX]
    · exact mul_le_of_le_one_right (bernoulliWeight_nonneg p hp X) (htest X hX)
  rw [rounded_charge] at hmean
  unfold countCharge at hmean
  linarith

/-- The numerical coercivity estimate in the finite-arity certificate. -/
theorem coercive_of_bounded_rounding (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i)
    (P : Fin m → Fin m → ℝ) (p₀ T : ℝ) (hp₀ : 0 ≤ p₀)
    (hdiag : ∀ i, p₀ ≤ P i i ∧ P i i ≤ 3) (hsum : ∑ i, x i = T)
    (htest : ∀ X, bernoulliWeight (roundingProbability x) X ≠ 0 →
      countCharge P (fun i => (roundedCount x X i : ℝ)) ≤ 1)
    (hsize : 3 * (m : ℝ) / 2 + 4 ≤ T * p₀) :
    T * p₀ / 2 ≤ ∑ i, ∑ j, P i j * x i * x j := by
  let a : Fin m → ℝ := fun i => (⌊x i⌋₊ : ℝ)
  let p := roundingProbability x
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i =>
    ⟨(roundingProbability_mem x hx i).1, (roundingProbability_mem x hx i).2.le⟩
  have hmean : ∀ i, a i + p i = x i := by
    intro i
    dsimp [a, p, roundingProbability]
    ring
  have hbound := quadratic_lower_bound_of_rounding a p hp P (by
    intro X hX
    simpa only [roundedCount_cast] using htest X hX)
  simp only [hmean] at hbound
  have hlinear : T * p₀ ≤ ∑ i, P i i * x i := by
    calc
      T * p₀ = ∑ i, p₀ * x i := by rw [← Finset.mul_sum, hsum, mul_comm]
      _ ≤ ∑ i, P i i * x i := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hdiag i).1 (hx i))
  have hvariance : (∑ i, P i i * (p i * (1 - p i))) ≤ 3 * (m : ℝ) / 4 := by
    calc
      (∑ i, P i i * (p i * (1 - p i))) ≤ ∑ _ : Fin m, (3 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hv : p i * (1 - p i) ≤ (1 / 4 : ℝ) := by
          nlinarith [sq_nonneg (p i - 1 / 2)]
        have hd : 0 ≤ P i i := hp₀.trans (hdiag i).1
        have hmul := mul_le_mul_of_nonneg_left hv hd
        nlinarith [(hdiag i).2]
      _ = 3 * (m : ℝ) / 4 := by simp; ring
  linarith

/-- The coercive bound on every probability vector, with the constant δ=p₀/(2T). -/
theorem probability_coercive (θ : Fin m → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    (hθsum : ∑ i, θ i = 1) (P : Fin m → Fin m → ℝ) (p₀ T : ℝ)
    (hp₀ : 0 ≤ p₀) (hT : 0 < T) (hdiag : ∀ i, p₀ ≤ P i i ∧ P i i ≤ 3)
    (htest : ∀ X, bernoulliWeight (roundingProbability (fun i => T * θ i)) X ≠ 0 →
      countCharge P (fun i => (roundedCount (fun i => T * θ i) X i : ℝ)) ≤ 1)
    (hsize : 3 * (m : ℝ) / 2 + 4 ≤ T * p₀) :
    p₀ / (2 * T) ≤ ∑ i, ∑ j, P i j * θ i * θ j := by
  have h := coercive_of_bounded_rounding (fun i => T * θ i)
    (fun i => mul_nonneg hT.le (hθ i)) P p₀ T hp₀ hdiag
    (by rw [← Finset.mul_sum, hθsum, mul_one]) htest hsize
  have heq : (∑ i, ∑ j, P i j * (T * θ i) * (T * θ j)) =
      T ^ 2 * (∑ i, ∑ j, P i j * θ i * θ j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at h
  apply (div_le_iff₀ (mul_pos (by norm_num) hT)).mpr
  nlinarith

/-- Bounded integer count tests suffice; zero-probability rounding outcomes require no test. -/
theorem probability_coercive_of_count_tests (θ : Fin m → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    (hθsum : ∑ i, θ i = 1) (P : Fin m → Fin m → ℝ) (p₀ : ℝ) (T : ℕ)
    (hp₀ : 0 ≤ p₀) (hT : 0 < T) (hdiag : ∀ i, p₀ ≤ P i i ∧ P i i ≤ 3)
    (htest : ∀ n : Fin m → ℕ, (∀ i, n i ≤ T) → (∑ i, n i) ≤ T + m →
      countCharge P (fun i => (n i : ℝ)) ≤ 1)
    (hsize : 3 * (m : ℝ) / 2 + 4 ≤ T * p₀) :
    p₀ / (2 * T) ≤ ∑ i, ∑ j, P i j * θ i * θ j := by
  have hx : ∀ i, 0 ≤ (T : ℝ) * θ i := fun i => mul_nonneg (Nat.cast_nonneg T) (hθ i)
  apply probability_coercive θ hθ hθsum P p₀ T hp₀ (by exact_mod_cast hT) hdiag _ hsize
  intro X hX
  apply htest
  · apply roundedCount_le _ T hx _ X hX
    intro i
    have hi : θ i ≤ 1 := by
      rw [← hθsum]
      exact Finset.single_le_sum (fun j _ => hθ j) (Finset.mem_univ i)
    simpa using mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg T)
  · have htotal := roundedCount_sum_le (fun i => (T : ℝ) * θ i) hx X
    rw [← Finset.mul_sum, hθsum, mul_one] at htotal
    exact_mod_cast htotal

/-- A coercive matrix controls the charge at actual large counts, without
assuming that those large counts were among the tested configurations. -/
theorem countCharge_le_of_coercive (P : Fin m → Fin m → ℝ) (δ : ℝ)
    (hdiag : ∀ i, P i i ≤ 3)
    (hcoercive : ∀ θ : Fin m → ℝ, (∀ i, 0 ≤ θ i) → (∑ i, θ i) = 1 →
      δ ≤ ∑ i, ∑ j, P i j * θ i * θ j)
    (v : Fin m → ℝ) (hv : ∀ i, 0 ≤ v i) (n : ℝ) (hsum : ∑ i, v i = n)
    (hn : 0 < n) : countCharge P v ≤ 3 * n / 2 - δ * n ^ 2 / 2 := by
  let θ : Fin m → ℝ := fun i => v i / n
  have hθsum : ∑ i, θ i = 1 := by
    dsimp [θ]
    rw [← Finset.sum_div, hsum, div_self hn.ne']
  have hq := hcoercive θ (fun i => div_nonneg (hv i) hn.le) hθsum
  have heq : n ^ 2 * (∑ i, ∑ j, P i j * θ i * θ j) =
      ∑ i, ∑ j, P i j * v i * v j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [θ]
    field_simp
  have hl : (∑ i, P i i * v i) ≤ 3 * n := by
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hdiag i) (hv i))
  have hq' := mul_le_mul_of_nonneg_left hq (sq_nonneg n)
  rw [heq] at hq'
  unfold countCharge
  nlinarith

/-- The discarded-bin error is dominated beyond the quadratic cutoff. -/
theorem omitted_charge_negative (L δ n y : ℝ) (hL : 0 ≤ L) (hn : 2 < n)
    (hcutoff : 4 * (L + 4) ≤ δ * n)
    (hy : y ≤ 1 + (L + 3 / 2) * n - δ * n ^ 2 / 2) : y < 0 := by
  have hn0 : 0 ≤ n := by linarith
  have hquad := mul_le_mul_of_nonneg_right hcutoff hn0
  have hLn : 0 ≤ L * n := mul_nonneg hL hn0
  nlinarith

end Erdos1017.FiniteArity

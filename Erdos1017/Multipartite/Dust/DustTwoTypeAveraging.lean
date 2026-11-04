module

public import Erdos1017.Multipartite.Dust.DustCountExtension

/-!
# Two-type averaging of count tests

Exact two-type independent averaging retains the distinct self penalties of a
completed head and the pre-existing dust, averaging feasible count tests
preserves feasibility including zero-probability words, and independent
assignment to a completed head or the original dust yields all averaged count
tests without assuming mixed feasibility.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

open Selector.Collision

/-- Exact two-type independent averaging, retaining the distinct self
penalties of a completed head and the pre-existing dust. -/
theorem two_type_expectation {k : ℕ} (q : Fin 2 → ℝ) (hq : ∑ i, q i = 1)
    (A u v c t p : ℝ) :
    (∑ w : Fin k → Fin 2, wordWeight q w *
      (A + (wordCount w 0 : ℝ) * u + (wordCount w 1 : ℝ) * v -
        c * (wordCount w 0 : ℝ) * (wordCount w 1 : ℝ) -
        t * (wordCount w 0 : ℝ) * ((wordCount w 0 : ℝ) - 1) / 2 -
        p * (wordCount w 1 : ℝ) * ((wordCount w 1 : ℝ) - 1) / 2)) =
      A + (k : ℝ) * (u * q 0 + v * q 1) -
        (k : ℝ) * ((k : ℝ) - 1) * (t * q 0 ^ 2 + 2 * c * q 0 * q 1 + p * q 1 ^ 2) / 2 := by
  have ht (w : Fin k → Fin 2) : wordWeight q w *
      (A + (wordCount w 0 : ℝ) * u + (wordCount w 1 : ℝ) * v -
        c * (wordCount w 0 : ℝ) * (wordCount w 1 : ℝ) -
        t * (wordCount w 0 : ℝ) * ((wordCount w 0 : ℝ) - 1) / 2 -
        p * (wordCount w 1 : ℝ) * ((wordCount w 1 : ℝ) - 1) / 2) =
      wordWeight q w * A + u * (wordWeight q w * (wordCount w 0 : ℝ)) +
        v * (wordWeight q w * (wordCount w 1 : ℝ)) -
        c * (wordWeight q w * ((wordCount w 0 : ℝ) * (wordCount w 1 : ℝ))) -
        (t / 2) * (wordWeight q w * ((wordCount w 0 : ℝ) * ((wordCount w 0 : ℝ) - 1))) -
        (p / 2) * (wordWeight q w * ((wordCount w 1 : ℝ) * ((wordCount w 1 : ℝ) - 1))) := by ring
  simp_rw [ht]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_mul, wordWeight_total q hq, word_first_moment q hq 0,
    word_first_moment q hq 1, word_pair_moment q hq 0 1 (by decide),
    word_factorial_moment q hq 0, word_factorial_moment q hq 1]
  ring

/-- Averaging actual feasible count tests preserves feasibility. This lemma
keeps the full two-type random experiment, including zero-probability words. -/
theorem two_type_average_le_one {k : ℕ} (q : Fin 2 → ℝ)
    (hq₀ : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) (A u v c t p : ℝ)
    (htest : ∀ n d : ℕ, A + (n : ℝ) * u + (d : ℝ) * v - c * n * d -
      t * n * ((n : ℝ) - 1) / 2 - p * d * ((d : ℝ) - 1) / 2 ≤ 1) :
    A + (k : ℝ) * (u * q 0 + v * q 1) -
      (k : ℝ) * ((k : ℝ) - 1) * (t * q 0 ^ 2 + 2 * c * q 0 * q 1 + p * q 1 ^ 2) / 2 ≤ 1 := by
  rw [← two_type_expectation q hq]
  conv_rhs => rw [← wordWeight_total (k := k) q hq]
  apply Finset.sum_le_sum
  intro w _
  have hw : 0 ≤ wordWeight q w := Finset.prod_nonneg (fun i _ => hq₀ (w i))
  simpa using mul_le_mul_of_nonneg_left (htest (wordCount w 0) (wordCount w 1)) hw

/-- The two-type tests used for merging one head are consequences of the
proved mixed-count extension, with the retained head subset fixed. -/
theorem single_head_count_test {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (X : Selector.Selection m) (i : Fin m) (hXi : X i = false) (n d : ℕ) :
    objective (fun j => Selector.bit (X j)) 0 C +
      (n : ℝ) * (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (X j)) +
      (d : ℝ) * (linear C - ∑ j, incident C j * Selector.bit (X j)) -
      incident C i * n * d - head C i * n * ((n : ℝ) - 1) / 2 -
      penalty C * d * ((d : ℝ) - 1) / 2 ≤ 1 := by
  let b : Fin m → ℕ := fun j => if X j then 1 else 0
  have hb : b i = 0 := by simp [b, hXi]
  have hbit (j : Fin m) : (b j : ℝ) = Selector.bit (X j) := by
    cases h : X j <;> simp [b, h, Selector.bit]
  have htest := repeatedCharge_le_one C hC (Function.update b i n) d
  rw [repeatedCharge_update, hb] at htest
  have hbase : repeatedCharge C b d = charge C X d := repeatedCharge_boolean C X d
  rw [hbase] at htest
  simp_rw [hbit] at htest
  have hcharge : charge C X d = objective (fun j => Selector.bit (X j)) 0 C +
      (d : ℝ) * (linear C - ∑ j, incident C j * Selector.bit (X j)) -
      penalty C * d * ((d : ℝ) - 1) / 2 := by
    simp [charge, objective]
  rw [hcharge] at htest
  convert htest using 1
  norm_num
  ring

/-- Actual independent assignment to a completed head or the old dust yields
all averaged count tests, without assuming mixed feasibility. -/
theorem single_head_average_test {m k : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (X : Selector.Selection m) (i : Fin m) (hXi : X i = false)
    (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1) :
    objective (fun j => Selector.bit (X j)) 0 C +
      (k : ℝ) * ((head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (X j)) * q 0 +
        (linear C - ∑ j, incident C j * Selector.bit (X j)) * q 1) -
      (k : ℝ) * ((k : ℝ) - 1) *
        (head C i * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2) / 2 ≤ 1 := by
  apply two_type_average_le_one q hq₀ hq
  exact single_head_count_test C hC X i hXi

end Erdos1017.MultipartiteDust

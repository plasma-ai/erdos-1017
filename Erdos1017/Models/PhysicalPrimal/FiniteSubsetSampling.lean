module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Averaging over subsets of a fixed size

Exact without-replacement incidence counting and the uniform average over
subsets of a given cardinality are set up, and averaging the hub-plus-subset
tests gives the bin inequality, so a positive average hub charge forces a
uniform positive penalty in every large adjacency bin.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

variable {α : Type*} [DecidableEq α]

/-- Exact without-replacement incidence counting, for arbitrary signed charges
on the smaller subsets. -/
theorem sum_subset_sample (U : Finset α) (r k : ℕ) (hrk : r ≤ k)
    (f : Finset α → ℝ) :
    (∑ S ∈ U.powersetCard k, ∑ t ∈ S.powersetCard r, f t) =
      ((U.card - r).choose (k - r) : ℝ) * ∑ t ∈ U.powersetCard r, f t := by
  have hinner (S : Finset α) (hS : S ∈ U.powersetCard k) :
      (∑ t ∈ S.powersetCard r, f t) =
        ∑ t ∈ U.powersetCard r, if t ⊆ S then f t else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨htS, hcard⟩
      exact ⟨⟨htS.trans (Finset.mem_powersetCard.mp hS).1, hcard⟩, htS⟩
    · rintro ⟨⟨_, hcard⟩, htS⟩
      exact ⟨htS, hcard⟩
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard := Finset.card_filter_powersetCard_subset t U k
    (Finset.mem_powersetCard.mp ht).1
    (by simpa [(Finset.mem_powersetCard.mp ht).2] using hrk)
  rw [hcard, (Finset.mem_powersetCard.mp ht).2]

/-- Uniform average over unordered subsets of a specified cardinality. -/
def subsetAverage (U : Finset α) (r : ℕ) (f : Finset α → ℝ) : ℝ :=
  (∑ t ∈ U.powersetCard r, f t) / (U.card.choose r : ℝ)

theorem subset_sample_average (U : Finset α) (r k : ℕ) (hrk : r ≤ k)
    (hkU : k ≤ U.card) (f : Finset α → ℝ) :
    (∑ S ∈ U.powersetCard k, ∑ t ∈ S.powersetCard r, f t) / (U.card.choose k : ℝ) =
      (k.choose r : ℝ) * subsetAverage U r f := by
  have hk : (U.card.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkU).ne'
  have hr : (U.card.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hrk.trans hkU)).ne'
  have hcoeff : ((U.card - r).choose (k - r) : ℝ) / (U.card.choose k : ℝ) =
      (k.choose r : ℝ) / (U.card.choose r : ℝ) := by
    apply (div_eq_div_iff hk hr).mpr
    exact_mod_cast (by simpa [mul_comm] using (Nat.choose_mul (n := U.card) hrk).symm)
  rw [sum_subset_sample U r k hrk f]
  unfold subsetAverage
  calc
    _ = (((U.card - r).choose (k - r) : ℝ) / (U.card.choose k : ℝ)) *
        ∑ t ∈ U.powersetCard r, f t := by ring
    _ = _ := by rw [hcoeff]; ring

/-- The averaging identity also covers samples smaller than the tested subset order. -/
theorem subset_sample_average_all (U : Finset α) (r k : ℕ) (hkU : k ≤ U.card)
    (f : Finset α → ℝ) :
    (∑ S ∈ U.powersetCard k, ∑ t ∈ S.powersetCard r, f t) / (U.card.choose k : ℝ) =
      (k.choose r : ℝ) * subsetAverage U r f := by
  by_cases hrk : r ≤ k
  · exact subset_sample_average U r k hrk hkU f
  · have hkr : k < r := Nat.lt_of_not_ge hrk
    have hzero : (∑ S ∈ U.powersetCard k, ∑ t ∈ S.powersetCard r, f t) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      have hempty : S.powersetCard r = ∅ := Finset.powersetCard_eq_empty.mpr
        (by simpa [(Finset.mem_powersetCard.mp hS).2] using hkr)
      rw [hempty, Finset.sum_empty]
    rw [hzero, zero_div, Nat.choose_eq_zero_of_lt hkr, Nat.cast_zero, zero_mul]

/-- Averaging the actual hub-plus-subset tests gives the first/pair bin inequality. -/
theorem averaged_hub_test (U : Finset α) (k : ℕ) (hk : 2 ≤ k) (hkU : k ≤ U.card)
    (first pair : Finset α → ℝ)
    (htest : ∀ S ∈ U.powersetCard k,
      (∑ t ∈ S.powersetCard 1, first t) + (∑ t ∈ S.powersetCard 2, pair t) ≤ 1) :
    (k : ℝ) * subsetAverage U 1 first + (k.choose 2 : ℝ) * subsetAverage U 2 pair ≤ 1 := by
  have hsum := Finset.sum_le_sum htest
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard,
    nsmul_eq_mul, mul_one] at hsum
  have hc : (0 : ℝ) < U.card.choose k := by exact_mod_cast Nat.choose_pos hkU
  have havg : ((∑ S ∈ U.powersetCard k, ∑ t ∈ S.powersetCard 1, first t) +
      (∑ S ∈ U.powersetCard k, ∑ t ∈ S.powersetCard 2, pair t)) /
      (U.card.choose k : ℝ) ≤ 1 := (div_le_iff₀ hc).mpr (by simpa using hsum)
  rw [add_div, subset_sample_average U 1 k (by omega) hkU first,
    subset_sample_average U 2 k hk hkU pair, Nat.choose_one_right] at havg
  simpa using havg

/-- Positive average hub charge forces a uniform positive penalty in every
large adjacency bin. Only the actual hub-plus-subset tests are used. -/
theorem hub_bin_penalty (h k : ℕ) (hh : 0 < h) (hk : 2 ≤ k)
    (s : Fin h → ℝ) (sees : Fin h → Bool) (p γ : ℝ) (hγ : 0 < γ)
    (hmean : γ ≤ (h : ℝ)⁻¹ * ∑ i, s i)
    (hmissing : ∀ i, sees i = false → s i = 0)
    (htest : ∀ i, sees i = true → (k : ℝ) * s i - (k.choose 2 : ℝ) * p ≤ 1) :
    2 * (γ - 1 / k) / (k - 1) ≤ p := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  let r : ℝ := 1 / k + (k - 1) * p / 2
  have hr : (k : ℝ) * r = 1 + (k.choose 2 : ℝ) * p := by
    dsimp [r]
    rw [Nat.cast_choose_two]
    field_simp
  have hsees (i : Fin h) (hi : sees i = true) : s i ≤ r := by
    have htesti := htest i hi
    nlinarith
  have hr0 : 0 ≤ r := by
    by_contra hn
    have hrneg : r < 0 := lt_of_not_ge hn
    have hs0 : ∀ i, s i ≤ 0 := by
      intro i
      cases hi : sees i
      · rw [hmissing i hi]
      · exact (hsees i hi).trans hrneg.le
    have hsum : (∑ i, s i) ≤ 0 := Finset.sum_nonpos (fun i _ => hs0 i)
    have havg := mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hh').le hsum
    linarith
  have hsum : (∑ i, s i) ≤ h * r := by
    calc
      (∑ i, s i) ≤ ∑ _ : Fin h, r := by
        apply Finset.sum_le_sum
        intro i _
        cases hi : sees i
        · rw [hmissing i hi]
          exact hr0
        · exact hsees i hi
      _ = h * r := by simp
  have havg := mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hh').le
  have hcancel : (h : ℝ)⁻¹ * ((h : ℝ) * r) = r := by
    rw [← mul_assoc, inv_mul_cancel₀ hh'.ne', one_mul]
  rw [hcancel] at havg
  have hgr : γ ≤ r := hmean.trans havg
  apply (div_le_iff₀ (show (0 : ℝ) < k - 1 by linarith)).mpr
  dsimp [r] at hgr
  linarith

end Erdos1017.FiniteArity

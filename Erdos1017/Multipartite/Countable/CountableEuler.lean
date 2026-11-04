module

public import Erdos1017.Multipartite.Dust.CountableDustVariation

/-!
# Euler identity for the countable objective

The weighted head rows are absolutely summable and sum to twice the head-head
interactions, giving Euler's degree-two identity for the countable homogeneous
objective with arbitrary real dust mass and no stationarity premise.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteCountableDual

/-- The weighted head rows are absolutely summable, and their sum counts
each head-head interaction twice. -/
theorem weighted_headRow_sum {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (s : ℝ) :
    Summable (fun i => p i * headRow p s D i) ∧
      (∑' i, p i * headRow p s D i) =
        (∑' i, head D i * p i) -
          2 * (∑' z : ℕ × ℕ, if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) -
          s * (∑' i, incident D i * p i) := by
  let a : ℕ × ℕ → ℝ := fun z =>
    if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0
  let k : ℕ × ℕ → ℝ := fun z =>
    MultipartiteCountableMeasure.kernel D (.inl (some z.1)) (.inl (some z.2)) * p z.1 * p z.2
  have ha : Summable a := pair_summable p hp hsum hD.1
  have hk : Summable k := by
    apply (hsum.mul_of_nonneg hsum hp hp).of_norm_bounded
    intro z
    dsimp [k]
    rw [abs_mul, abs_mul, abs_of_nonneg (hp _), abs_of_nonneg (hp _)]
    have hb := MultipartiteCountableMeasure.norm_kernel_le_one hD
      (.inl (some z.1)) (.inl (some z.2))
    rw [Real.norm_eq_abs] at hb
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (hp z.1)) (hp z.2)).trans_eq (by ring)
  have hka (z : ℕ × ℕ) : k z = -(a z + a z.swap) := by
    rcases lt_trichotomy z.1 z.2 with h | h | h
    · simp [k, a, MultipartiteCountableMeasure.kernel, h, not_lt_of_gt h]
    · simp [k, a, MultipartiteCountableMeasure.kernel, h]
    · simp [k, a, MultipartiteCountableMeasure.kernel, h, not_lt_of_gt h]
      ring
  have hksum : (∑' z, k z) = -2 * ∑' z, a z := by
    have hswap : (∑' z : ℕ × ℕ, a z.swap) = ∑' z, a z :=
      (Equiv.prodComm ℕ ℕ).tsum_eq a
    rw [tsum_congr hka, tsum_neg, ha.tsum_add ha.prod_symm, hswap]
    ring
  have hh := head_summable p hp hsum hD.1
  have hi := incident_summable p hp hsum hD.1
  have hrow (i : ℕ) : p i * headRow p s D i =
      head D i * p i + (∑' j, k (i, j)) - s * (incident D i * p i) := by
    have hinner : p i * (∑' j, MultipartiteCountableMeasure.kernel D
        (.inl (some i)) (.inl (some j)) * p j) = ∑' j, k (i, j) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      dsimp [k]
      ring
    unfold headRow
    rw [mul_sub, mul_add, hinner]
    ring
  have hs := (hh.add hk.prod).sub (hi.mul_left s)
  refine ⟨hs.congr (fun i => (hrow i).symm), ?_⟩
  rw [tsum_congr hrow, (hh.add hk.prod).tsum_sub (hi.mul_left s),
    hh.tsum_add hk.prod, ← hk.tsum_prod, hksum, tsum_mul_left]
  dsimp only [a]
  ring

/-- Euler's degree-two identity for the actual countable homogeneous
objective, with arbitrary real dust mass and no stationarity premise. -/
theorem row_euler {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (s : ℝ) :
    anchorRow p s D + (∑' i, p i * headRow p s D i) + s * dustRow p s D =
      2 * objective p s D := by
  rw [(weighted_headRow_sum hD p hp hsum s).2]
  unfold anchorRow dustRow objective
  rw [tsum_mul_right]
  ring

end Erdos1017.MultipartiteCountableDual

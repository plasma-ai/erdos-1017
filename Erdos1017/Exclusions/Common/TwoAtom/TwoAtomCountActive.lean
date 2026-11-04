module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomOptimalFace
public import Erdos1017.Multipartite.Selector.VertexClassification

/-!
# Active count rows at a positive vertex

Positive penalties force every count outside a finite square strictly below one,
uniformly in a coefficient neighborhood, so the all-count set has a locally
sufficient finite description; a positive five-coordinate vertex therefore needs
at least five active count rows, and every direction annihilating them vanishes.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- One penalized integer-count polynomial has a genuine uniform upper
bound, including its finitely many small counts. -/
theorem penalized_count_le (M a : ℝ) (ha : 0 < a)
    (s p : ℝ) (hs : s ≤ M) (hp : a ≤ p) (n : ℕ) :
    (n : ℝ) * s - p * n * ((n : ℝ) - 1) / 2 ≤ (M + a) ^ 2 / a := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnn : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    simpa using TightCounts.gap_nonneg 0 n
  have h₁ := mul_le_mul_of_nonneg_left hs hn
  have h₂ := mul_nonneg (sub_nonneg.mpr hp) hnn
  have hD : a * ((M + a) ^ 2 / a) = (M + a) ^ 2 :=
    mul_div_cancel₀ _ (ne_of_gt ha)
  have hbase : (n : ℝ) * M - a * n * ((n : ℝ) - 1) / 2 ≤ (M + a) ^ 2 / a := by
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith [sq_nonneg (a * (n : ℝ) - (M + a)),
      mul_nonneg (sq_nonneg a) hn, sq_nonneg (M + a)]
  nlinarith

/-- Positive penalties force every count outside a genuine finite square
strictly below one, uniformly in the stated coefficient neighborhood. -/
theorem count_uniform_tail (M a : ℝ) (hM : 0 < M) (ha : 0 < a) :
    ∃ N : ℕ, ∀ x : Coefficients, x 0 ≤ M → x 1 ≤ M → a ≤ x 2 → a ≤ x 3 →
      0 ≤ x 4 → ∀ k l, N ≤ k ∨ N ≤ l → countTest k l x < 1 := by
  let D := (M + a) ^ 2 / a
  let C := |D| + M + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := VertexClassification.uniform_tail C a hC ha
  refine ⟨N, ?_⟩
  intro x hh hv hp hq hr k l hlarge
  have hDC : D ≤ C := by dsimp [C]; linarith [le_abs_self D]
  have hMC : M ≤ C := by dsimp [C]; linarith [abs_nonneg D]
  have hmix := mul_nonneg (mul_nonneg hr (Nat.cast_nonneg k)) (Nat.cast_nonneg l)
  have hk := penalized_count_le M a ha (x 0) (x 2) hh hp k
  have hl := penalized_count_le M a ha (x 1) (x 3) hv hq l
  rw [countTest_apply]
  rcases hlarge with hlarge | hlarge
  · have ht := hN D (x 0) (x 2) hDC (hh.trans hMC) hp k hlarge
    unfold TightCounts.value at ht
    dsimp only [D] at ht
    nlinarith
  · have ht := hN D (x 1) (x 3) hDC (hv.trans hMC) hq l hlarge
    unfold TightCounts.value at ht
    dsimp only [D] at ht
    nlinarith

/-- The local finite square is derived from all-count quadratic decay.
No cutoff is an input to the original feasible set. -/
theorem local_finiteness (x : Coefficients) (hx : ∀ i, 0 < x i) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, (∀ i, 0 < y i) ∧
      ∀ k l, N ≤ k ∨ N ≤ l → countTest k l y < 1 := by
  let M := |x 0| + |x 1| + 1
  let a := min (x 2) (x 3) / 2
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := by dsimp [a]; exact half_pos (lt_min (hx 2) (hx 3))
  obtain ⟨N, hN⟩ := count_uniform_tail M a hM ha
  have hh : ∀ᶠ y in 𝓝 x, y 0 < M :=
    (continuous_apply 0).continuousAt.eventually_lt_const
      (by dsimp [M]; linarith [le_abs_self (x 0), abs_nonneg (x 1)])
  have hv : ∀ᶠ y in 𝓝 x, y 1 < M :=
    (continuous_apply 1).continuousAt.eventually_lt_const
      (by dsimp [M]; linarith [le_abs_self (x 1), abs_nonneg (x 0)])
  have hp : ∀ᶠ y in 𝓝 x, a < y 2 :=
    (continuous_apply 2).continuousAt.eventually_const_lt
      (by dsimp [a]; have := min_le_left (x 2) (x 3); linarith [hx 2])
  have hq : ∀ᶠ y in 𝓝 x, a < y 3 :=
    (continuous_apply 3).continuousAt.eventually_const_lt
      (by dsimp [a]; have := min_le_right (x 2) (x 3); linarith [hx 3])
  have hpos : ∀ᶠ y in 𝓝 x, ∀ i, 0 < y i :=
    Filter.eventually_all.mpr (fun i =>
      (continuous_apply i).continuousAt.eventually_const_lt (hx i))
  refine ⟨N, ?_⟩
  filter_upwards [hh, hv, hp, hq, hpos] with y hh hv hp hq hpos
  exact ⟨hpos, hN y hh.le hv.le hp.le hq.le (hpos 4).le⟩

/-- The original all-count set has an actual locally sufficient finite
square at every positive coefficient vector. -/
theorem finite_local_description (x : Coefficients) (hx : ∀ i, 0 < x i) :
    ∃ N : ℕ, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      (∀ i : Fin N × Fin N, countTest i.1.val i.2.val y ≤ 1) → y ∈ feasible := by
  obtain ⟨N, hN⟩ := local_finiteness x hx
  refine ⟨N, {y | (∀ i, 0 < y i) ∧
    ∀ k l, N ≤ k ∨ N ≤ l → countTest k l y < 1}, hN, ?_⟩
  intro y hy htests
  apply mem_feasible_of_nonnegative y (fun i => (hy.1 i).le)
  intro k l
  by_cases hk : k < N
  · by_cases hl : l < N
    · exact htests (⟨k, hk⟩, ⟨l, hl⟩)
    · exact (hy.2 k l (Or.inr (Nat.le_of_not_gt hl))).le
  · exact (hy.2 k l (Or.inl (Nat.le_of_not_gt hk))).le

/-- A positive genuine five-coordinate vertex requires at least five
active count rows in a finite square derived from the original all-count set. -/
theorem five_active_tests (x : Coefficients) (hvertex : x ∈ feasible.extremePoints ℝ)
    (hx : ∀ i, 0 < x i) :
    ∃ N : ℕ, 5 ≤ Nat.card {i : Fin N × Fin N // countTest i.1.val i.2.val x = 1} := by
  obtain ⟨N, U, hU, hlocal⟩ := finite_local_description x hx
  let L : Fin N × Fin N → Coefficients →L[ℝ] ℝ :=
    fun i => (countTest i.1.val i.2.val).toContinuousLinearMap
  have hcard := PolyhedralVertex.finrank_le_active_card feasible x L hvertex
    (fun i => hvertex.1.2.2.1 i.1.val i.2.val) ⟨U, hU, hlocal⟩
  refine ⟨N, ?_⟩
  simpa [L, Module.finrank_pi_fintype] using hcard

/-- Every direction annihilating all genuine active count rows at a
positive vertex vanishes. This retains independence, not just row count. -/
theorem active_direction_eq_zero (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i)
    (v : Coefficients) (hv : ∀ k l, countTest k l x = 1 → countTest k l v = 0) : v = 0 := by
  obtain ⟨N, U, hU, hlocal⟩ := finite_local_description x hx
  let L : Fin N × Fin N → Coefficients →L[ℝ] ℝ :=
    fun i => (countTest i.1.val i.2.val).toContinuousLinearMap
  exact PolyhedralVertex.active_direction_eq_zero feasible x L hvertex
    (fun i => hvertex.1.2.2.1 i.1.val i.2.val) ⟨U, hU, hlocal⟩ v
    (fun i hi => hv i.1.val i.2.val hi)

end Erdos1017.TwoAtomCountGate

module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleRun

/-!
# Near-perfect matching with an order threshold

This module proves the near-perfect matching statement with an auxiliary order
threshold, constructing all matching rounds, exceptional vertices and waste
(`near_perfect_matching_with_order`). The threshold is removed in
`HypergraphNearPerfectMatching`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

private theorem schedule_cost_identity (r : ℕ) (θ C : ℝ) (i : ℕ) :
    4 * (θ / idealDegree r θ i) ^ 2 * (r : ℝ) ^ 2 * C ^ 2 =
      4 * θ ^ 2 * (r : ℝ) ^ 2 * C ^ 2 * Real.exp (2 * ((r - 1 : ℕ) : ℝ) * θ * i) := by
  have hpow : (θ / idealDegree r θ i) ^ 2 =
      θ ^ 2 * Real.exp (2 * ((r - 1 : ℕ) : ℝ) * θ * i) := by
    unfold idealDegree
    rw [show -((r - 1 : ℕ) : ℝ) * θ * i = -(((r - 1 : ℕ) : ℝ) * θ * i) by ring,
      Real.exp_neg, div_inv_eq_mul, mul_pow, ← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  rw [hpow]
  ring

/-- Near-perfect matching with an auxiliary order threshold. All matching rounds,
exceptional vertices and waste have been constructed; the subsequent threshold-removal
lemma is needed to recover the published theorem's exact degree-only hypothesis. -/
theorem near_perfect_matching_with_order (r : ℕ) (C δ : ℝ)
    (hr : 2 ≤ r) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ γ D₀ N₀ : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < D₀ ∧ 0 < N₀ ∧
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (W : Finset (Fin n)) (D : ℝ),
        D₀ ≤ D → N₀ ≤ n →
        (∀ e ∈ H, e.card = r) →
        (∀ v, (degree H v : ℝ) ≤ C * D) →
        (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ γ * D) →
        (∀ v, v ∉ W → (1 - γ) * D ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + γ) * D) →
        (W.card : ℝ) ≤ γ * n →
        ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id ∧
          (1 - δ) * n / r ≤ (M.card : ℝ) := by
  obtain ⟨h, T, hh, hT, _, hsmall, hcost⟩ := exists_ideal_schedule r C δ hδ
  let θ : ℝ := h / T
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hθ : 0 < θ := div_pos hh hTR
  have hθT : θ * T = h := by dsimp [θ]; field_simp
  have hβ : Real.exp (-θ * T) < δ / 2 := by
    rw [neg_mul, hθT]
    linarith
  obtain ⟨ε, D₀, N₀, hε, hε1, hD₀, hN₀, hparams⟩ := exists_schedule_thresholds r T θ C (δ / 2) hθ hβ
  have hγ : 0 < ε ^ (2 * T + 6) := pow_pos hε _
  have hγ1 : ε ^ (2 * T + 6) < 1 := pow_lt_one₀ hε.le hε1 (by omega)
  refine ⟨ε ^ (2 * T + 6), D₀, N₀, hγ, hγ1, hD₀, hN₀, ?_⟩
  intro n H W D hDmin hNmin huniform hmax hcodegree hregular hW
  have hD : 0 < D := hD₀.trans_le hDmin
  have hnR : (0 : ℝ) < n := hN₀.trans_le hNmin
  have hn : 0 < n := by exact_mod_cast hnR
  have hpar := hparams D hDmin n hNmin
  have hmax' : ∀ v, (degree H v : ℝ) ≤ C * D := hmax
  obtain ⟨xs, _, hactive, hwaste⟩ := exists_scheduled_rounds H W r T θ C ε D (by omega) hθ
    (by linarith) hε hε1.le hD (by simpa using hn) huniform hmax' hcodegree hregular
    (by simpa using hW) (fun i => (hpar.2.1 i).2.1)
    (fun i => (hpar.2.1 i).2.2.1) (fun i => by simpa using (hpar.2.1 i).2.2.2)
  have hsum : (∑ i ∈ Finset.range T, 4 * (θ / idealDegree r θ i) ^ 2 * (r : ℝ) ^ 2 * C ^ 2) < δ / 4 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [schedule_cost_identity]
    exact hcost
  have haccount := matchingRounds_accounting H Finset.univ xs r (by omega)
    (fun _ _ => Finset.subset_univ _) huniform
  simp only [Finset.card_univ, Fintype.card_fin] at haccount
  have haccountR : (r : ℝ) * (matchingRounds H xs).card + (activeRounds H Finset.univ xs).card +
      (wasteRounds H Finset.univ xs : ℝ) = n := by exact_mod_cast haccount
  have hactive' : ((activeRounds H Finset.univ xs).card : ℝ) < (δ / 2) * n := by
    have hmul := mul_lt_mul_of_pos_right hpar.2.2 hnR
    have hbound : ((activeRounds H Finset.univ xs).card : ℝ) ≤ activeEnvelope r T θ (r * C) ε D T * n := by
      simpa using hactive
    exact hbound.trans_lt hmul
  have hwaste' : (wasteRounds H Finset.univ xs : ℝ) < (δ / 4) * n := by
    have hbound : (wasteRounds H Finset.univ xs : ℝ) ≤
        (∑ i ∈ Finset.range T, 4 * (θ / idealDegree r θ i) ^ 2 * (r : ℝ) ^ 2 * C ^ 2) * n := by
      simpa using hwaste
    exact hbound.trans_lt (mul_lt_mul_of_pos_right hsum hnR)
  refine ⟨matchingRounds H xs, matchingRounds_subset H xs, matchingRounds_pairwise_disjoint H xs, ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < r by omega))).mpr
  nlinarith

end Erdos1017.HypergraphNibble

module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNearPerfectWithOrder

/-!
# Pippenger's near-perfect matching theorem

This module proves Pippenger's near-perfect matching theorem in a form where
near-regularity may fail on a small fraction of vertices, with an explicit
exceptional vertex set and thresholds depending only on the rank, the
maximum-degree multiplier and the desired error
(`near_perfect_matching_with_exceptions`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

/-- A finite simple hypergraph has at most one incident edge per vertex subset. -/
theorem degree_le_pow_card {n : ℕ} (H : Finset (Finset (Fin n))) (v : Fin n) :
    degree H v ≤ 2 ^ n := by
  have h := Finset.card_le_card (Finset.subset_univ (H.filter (fun e => v ∈ e)))
  simpa only [degree, Finset.card_univ, Fintype.card_finset, Fintype.card_fin] using h

/-- The near-perfect matching theorem with an explicit exceptional vertex set.
The thresholds depend only on rank, the maximum-degree multiplier, and the desired error. -/
theorem near_perfect_matching_with_exceptions (r : ℕ) (C δ : ℝ)
    (hr : 2 ≤ r) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ γ D₀ : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < D₀ ∧
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (W : Finset (Fin n)) (D : ℝ),
        D₀ ≤ D → (∀ e ∈ H, e.card = r) →
        (∀ v, (degree H v : ℝ) ≤ C * D) →
        (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ γ * D) →
        (∀ v, v ∉ W → (1 - γ) * D ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + γ) * D) →
        (W.card : ℝ) ≤ γ * n →
        ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id ∧
          (1 - δ) * n / r ≤ (M.card : ℝ) := by
  obtain ⟨γ, D₁, N₀, hγ, hγ1, hD₁, _, hmatching⟩ := near_perfect_matching_with_order r C δ hr hC hδ
  obtain ⟨N, hN⟩ := exists_nat_gt N₀
  let D₀ : ℝ := max D₁ (((2 : ℝ) ^ N + 1) / (1 - γ))
  have hD₀ : 0 < D₀ := hD₁.trans_le (le_max_left _ _)
  refine ⟨γ, D₀, hγ, hγ1, hD₀, ?_⟩
  intro n H W D hD huniform hmax hcodegree hregular hW
  by_cases hn : n = 0
  · subst n
    exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hWlt : (W.card : ℝ) < n := lt_of_le_of_lt hW (by nlinarith)
  obtain ⟨v, hv⟩ : ∃ v : Fin n, v ∉ W := by
    by_contra h
    push Not at h
    have hWeq : W = Finset.univ := by ext v; simp [h v]
    simp only [hWeq, Finset.card_univ, Fintype.card_fin] at hWlt
    exact (lt_irrefl _ hWlt)
  have horder : N₀ ≤ (n : ℝ) := by
    by_contra h
    have hnN : n ≤ N := by
      have : (n : ℝ) < N := (lt_of_not_ge h).trans hN
      exact_mod_cast this.le
    have hdeg : (degree H v : ℝ) ≤ (2 : ℝ) ^ N := by
      have hnat := (degree_le_pow_card H v).trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hnN)
      exact_mod_cast hnat
    have hscale : ((2 : ℝ) ^ N + 1) / (1 - γ) ≤ D := (le_max_right _ _).trans hD
    have hscale' := mul_le_mul_of_nonneg_left hscale (sub_pos.mpr hγ1).le
    have hcancel : (1 - γ) * (((2 : ℝ) ^ N + 1) / (1 - γ)) = (2 : ℝ) ^ N + 1 := by
      field_simp [(sub_pos.mpr hγ1).ne']
    rw [hcancel] at hscale'
    have hlow := (hregular v hv).1
    linarith
  exact hmatching n H W D ((le_max_left _ _).trans hD) horder huniform hmax hcodegree hregular hW

/-- Pippenger's near-perfect matching statement in the form used by
Balogh–He–Krueger–Nguyen–Wigal, Theorem 4.5: near-regularity may fail on a small
fraction of vertices, while the maximum degree and distinct-pair codegree bounds hold everywhere. -/
theorem near_perfect_matching (r : ℕ) (C δ : ℝ)
    (hr : 2 ≤ r) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∃ γ D₀ : ℝ, 0 < γ ∧ 0 < D₀ ∧
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))) (D : ℝ), D₀ ≤ D →
        (∀ e ∈ H, e.card = r) →
        (∀ v, (degree H v : ℝ) < C * D) →
        (∀ u v, u ≠ v → (codegree H u v : ℝ) < γ * D) →
        ((Finset.univ.filter (fun v => ¬((1 - γ) * D ≤ (degree H v : ℝ) ∧
          (degree H v : ℝ) ≤ (1 + γ) * D))).card : ℝ) ≤ γ * n →
        ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id ∧
          (1 - δ) * n / r ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ, D₀, hγ, _, hD₀, hmatching⟩ := near_perfect_matching_with_exceptions r C δ hr hC hδ
  refine ⟨γ, D₀, hγ, hD₀, ?_⟩
  intro n H D hD huniform hmax hcodegree hbad
  let W := Finset.univ.filter (fun v => ¬((1 - γ) * D ≤ (degree H v : ℝ) ∧
    (degree H v : ℝ) ≤ (1 + γ) * D))
  apply hmatching n H W D hD huniform (fun v => (hmax v).le)
    (fun u v huv => (hcodegree u v huv).le) _ hbad
  intro v hv
  simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv

end Erdos1017.HypergraphNibble

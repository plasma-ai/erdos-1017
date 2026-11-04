module

public import Erdos1017.IntegerTransfer.CleanedValueRounding
public import Erdos1017.IntegerTransfer.IntegerSubgraphRepair
public import Erdos1017.IntegerTransfer.EquitableEqualization

/-!
# The same-graph integer transfer

Uniformly over all graphs of sufficiently large order, the integer clique
partition number is at most the fractional value plus an arbitrarily small
quadratic error (`exists_same_graph_integer_upper_transfer`). It is the main
result of the integer transfer.
-/

@[expose] public section

noncomputable section

namespace Erdos1017

open RegularityCleaning MultipartiteAllocation

/-- Uniformly over all graphs of sufficiently large order, the integer clique
partition number is at most the fractional value plus an arbitrarily small
quadratic error, on the same original graph. -/
theorem exists_same_graph_integer_upper_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
      (cliquePartitionNumber G : ℝ) ≤ FractionalGraph.value G + ε * (n : ℝ) ^ 2 := by
  classical
  let σ := min ε 1
  have hσ : 0 < σ := lt_min hε (by norm_num)
  have hσε : σ ≤ ε := min_le_left _ _
  have hσ1 : σ ≤ 1 := min_le_right _ _
  let d := σ / 128
  let δ := d / 2
  have hd : 0 < d := div_pos hσ (by norm_num)
  have hδ : 0 < δ := div_pos hd (by norm_num)
  obtain ⟨ε₀, hε₀, hround⟩ := exists_cleaned_value_rounding_tolerance δ (σ / 4) hδ
    (div_pos hσ (by norm_num)) (by linarith)
  let η := min ((ε₀ / 2) ^ 2) (min (d / 2) (1 / 4))
  have hη : 0 < η := lt_min (sq_pos_of_pos (div_pos hε₀ (by norm_num)))
    (lt_min (div_pos hd (by norm_num)) (by norm_num))
  have hηroot : η ≤ (ε₀ / 2) ^ 2 := min_le_left _ _
  have hηd : η ≤ d / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηquarter : η ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hsqrt : Real.sqrt η < ε₀ := by
    have h := (Real.sqrt_le_iff).mpr ⟨by linarith, hηroot⟩
    linarith
  let ξ := σ / 16
  have hξ : 0 < ξ := div_pos hσ (by norm_num)
  obtain ⟨l, hl⟩ := exists_nat_gt (4 / ξ)
  have hlpos : 0 < l := by
    exact_mod_cast (lt_trans (div_pos (by norm_num) hξ) hl)
  let p := SzemerediRegularity.bound η l
  obtain ⟨C, hC'⟩ := exists_nat_gt (1 / δ)
  have hC : 0 < C := by exact_mod_cast ((one_div_pos.mpr hδ).trans hC')
  have hscale : 1 ≤ (C : ℝ) * δ := by
    have h := (div_lt_iff₀ hδ).mp hC'
    linarith
  obtain ⟨N₀, hN₀, hroundsize⟩ := hround p C hC hscale
  obtain ⟨m, hm⟩ := exists_nat_gt (64 * (p : ℝ) / σ)
  let n₀ := max 1 (l + p * N₀ + m)
  refine ⟨n₀, by dsimp only [n₀]; omega, ?_⟩
  intro n hn G
  have hnpos : 0 < n := by dsimp only [n₀] at hn; omega
  let : NeZero n := ⟨by omega⟩
  have hnp : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hln : l ≤ n := by dsimp only [n₀] at hn; omega
  have hpn : p * N₀ ≤ n := by dsimp only [n₀] at hn; omega
  have hmn : m ≤ n := by dsimp only [n₀] at hn; omega
  obtain ⟨P, hPeq, hlP, hPbound, hPuniform, _, _⟩ :=
    exists_fixed_density_cleaning G η d ξ l hη hd hξ hl.le (by simpa only [Fintype.card_fin] using hln)
  let q := P.parts.card
  let N := Fintype.card (Fin n) / q
  obtain ⟨e, he⟩ := exists_equal_parts_embedding P hPeq
  have hq : 0 < q := (equal_parts_remainder P).1
  have hqp : q ≤ p := hPbound
  have hN : N₀ ≤ N := by
    dsimp only [N]
    rw [Fintype.card_fin]
    apply (Nat.le_div_iff_mul_le hq).mpr
    simpa only [Nat.mul_comm N₀ q] using (Nat.mul_le_mul_right N₀ hqp).trans hpn
  let H := (G.regularityReduced P η d).comap e
  have hHparts (i : Fin q) (a z : Fin N) : ¬H.Adj (i, a) (i, z) :=
    equalized_independent G P e he η d i a z
  have hHclean (i j : Fin q) (_hij : i < j) :
      (∀ a z : Fin N, ¬H.Adj (i, a) (j, z)) ∨
        (H.IsUniform (Real.sqrt η) (MultipartiteCounting.part i) (MultipartiteCounting.part j) ∧
          δ ≤ H.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j)) := by
    rcases equalized_pair G P hPeq e he hηquarter i j with hempty | ⟨hreg, hden⟩
    · refine Or.inl ?_
      intro a z
      exact hempty (i, a) ((TransversalThinning.mem_part_iff i _).mpr rfl)
        (j, z) ((TransversalThinning.mem_part_iff j _).mpr rfl)
    · have hdensity : δ ≤ d - η := by dsimp only [δ]; linarith only [hηd]
      exact Or.inr ⟨hreg, hdensity.trans hden⟩
  have hHround := hroundsize N hN q hq hqp H hHparts (Real.sqrt η) (Real.sqrt_nonneg _) hsqrt hHclean n e
  have hle : H.map e ≤ G := equalized_map_le G P e η d
  have hlower : 4 / ξ ≤ (P.parts.card : ℝ) := hl.le.trans (by exact_mod_cast hlP)
  have hloss := equalized_edge_loss G P hPeq e hη hd hξ hPuniform hlower
  simp only [Fintype.card_fin] at hloss
  have hqn : (q : ℝ) * n < σ * (n : ℝ) ^ 2 / 64 := by
    have hlarge : 64 * (p : ℝ) / σ < n := hm.trans_le (by exact_mod_cast hmn)
    have hmul := (div_lt_iff₀ hσ).mp hlarge
    have hqcast : (q : ℝ) ≤ p := by exact_mod_cast hqp
    have hqmul := mul_le_mul_of_nonneg_right hqcast hnp.le
    have hmul' := mul_lt_mul_of_pos_right hmul hnp
    nlinarith only [hqmul, hmul']
  have hloss' : (G.edgeFinset.card : ℝ) - (H.map e).edgeFinset.card < σ * (n : ℝ) ^ 2 / 16 := by
    have hηbound : 2 * η + 2 * d + ξ / 4 ≤ 3 * σ / 64 := by
      dsimp only [d, ξ] at hηd ⊢
      linarith only [hηd, hσ.le]
    have hcoef := mul_le_mul_of_nonneg_right hηbound (sq_nonneg (n : ℝ))
    dsimp only [q, H] at hqn ⊢
    nlinarith only [hloss, hqn, hcoef]
  have hproduct : q * N ≤ n := by simpa only [N, Fintype.card_fin] using Nat.mul_div_le (Fintype.card (Fin n)) q
  have hproduct' : (q * N : ℕ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hproduct) 2
  have hroundbound : (σ / 4) * (q * N : ℕ) ^ 2 ≤ σ / 4 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hproduct' (by positivity)
  have hfinal := cliquePartitionNumber_le_value_of_subgraph_rounding G (H.map e) hle _ hHround
  have hεbound := mul_le_mul_of_nonneg_right hσε (sq_nonneg (n : ℝ))
  nlinarith only [hfinal, hloss', hroundbound, hεbound, mul_pos hσ (sq_pos_of_pos hnp)]

end Erdos1017

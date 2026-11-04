module

public import Erdos1017.FractionalLimit.FractionalLimitFoundation
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The fractional density limit

This module defines the density limit `densityLimit` from penalized finite-graph
bounds, proves its continuity and that it bounds every finite graph and
normalized extremum, and shows that every admissible edge-count sequence with a
limiting density has the same limit (`tendsto_extremal_of_density`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped Topology
open Filter

/-- Finite graphs give penalized density bounds; zero is always an admissible lower bound. -/
def densityCandidates (d : ℝ) : Set ℝ :=
  {c | c = 0 ∨ ∃ N : ℕ, ∃ G : SimpleGraph (Fin (N + 1)),
    c = value G / ((N + 1 : ℕ) : ℝ) ^ 2 -
      3 * |(G.edgeSet.ncard : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 - d|}

def densityLimit (d : ℝ) : ℝ := sSup (densityCandidates d)

theorem normalized_value_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    value G / (n : ℝ) ^ 2 ≤ 1 := by
  have hcard := (edge_count_le_choose G).trans (Nat.choose_le_pow n 2)
  have hreal : (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard
  have hden : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) _
  rw [div_le_one hden]
  exact (value_le_edge_count G).trans hreal

theorem densityCandidates_bddAbove (d : ℝ) : BddAbove (densityCandidates d) := by
  refine ⟨1, ?_⟩
  rintro c (rfl | ⟨N, G, rfl⟩)
  · norm_num
  · have h := normalized_value_le_one G (Nat.succ_pos N)
    linarith [abs_nonneg ((G.edgeSet.ncard : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 - d)]

theorem densityCandidates_nonempty (d : ℝ) : (densityCandidates d).Nonempty := ⟨0, Or.inl rfl⟩

theorem densityLimit_nonneg (d : ℝ) : 0 ≤ densityLimit d :=
  le_csSup (densityCandidates_bddAbove d) (Or.inl rfl)

theorem finite_graph_le_densityLimit {N : ℕ} (G : SimpleGraph (Fin N)) (hN : 0 < N) (d : ℝ) :
    value G / (N : ℝ) ^ 2 - 3 * |(G.edgeSet.ncard : ℝ) / (N : ℝ) ^ 2 - d| ≤ densityLimit d := by
  cases N with
  | zero => omega
  | succ N => exact le_csSup (densityCandidates_bddAbove d) (Or.inr ⟨N, G, rfl⟩)

theorem normalized_extremal_le_densityLimit (n k : ℕ) (hn : 0 < n) (hk : k ≤ n.choose 2)
    (d : ℝ) : extremal n k / (n : ℝ) ^ 2 ≤ densityLimit d + 3 * |(k : ℝ) / (n : ℝ) ^ 2 - d| := by
  obtain ⟨G, hG, hvG⟩ := extremal_attained n k hk
  have h := finite_graph_le_densityLimit G hn d
  rw [hG, hvG] at h
  linarith

theorem densityLimit_le_add (d e : ℝ) : densityLimit d ≤ densityLimit e + 3 * |d - e| := by
  apply csSup_le (densityCandidates_nonempty d)
  rintro c (rfl | ⟨N, G, rfl⟩)
  · linarith [densityLimit_nonneg e, abs_nonneg (d - e)]
  · have h := finite_graph_le_densityLimit G (Nat.succ_pos N) e
    have htri := abs_sub_le ((G.edgeSet.ncard : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2) d e
    linarith

theorem densityLimit_abs_sub_le (d e : ℝ) : |densityLimit d - densityLimit e| ≤ 3 * |d - e| := by
  have h₁ := densityLimit_le_add d e
  have h₂ := densityLimit_le_add e d
  rw [abs_sub_comm e d] at h₂
  rw [abs_le]
  constructor <;> linarith

theorem densityLimit_lipschitz : LipschitzWith 3 densityLimit := by
  apply LipschitzWith.of_dist_le_mul
  intro d e
  simpa only [Real.dist_eq, NNReal.coe_ofNat] using densityLimit_abs_sub_le d e

theorem densityLimit_continuous : Continuous densityLimit := densityLimit_lipschitz.continuous

/-- Every admissible prescribed-edge-count sequence with a limiting density has the same limit. -/
theorem tendsto_extremal_of_density_along (v k : ℕ → ℕ) (hv : Tendsto v atTop atTop)
    (hk : ∀ n, k n ≤ (v n).choose 2) (d : ℝ)
    (hd : Tendsto (fun n : ℕ => (k n : ℝ) / (v n : ℝ) ^ 2) atTop (𝓝 d)) :
    Tendsto (fun n : ℕ => extremal (v n) (k n) / (v n : ℝ) ^ 2) atTop (𝓝 (densityLimit d)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨c, hc, hac⟩ := exists_lt_of_lt_csSup (densityCandidates_nonempty d) ha
    rcases hc with rfl | ⟨N, G, rfl⟩
    · exact Eventually.of_forall (fun n => hac.trans_le
        (div_nonneg (extremal_nonneg (v n) (k n)) (sq_nonneg _)))
    · exact finite_graph_eventual_lower_along G (Nat.succ_pos N) v k hv hk d a hd hac
  · intro b hb
    have hlim : Tendsto (fun n : ℕ => densityLimit d +
        3 * |(k n : ℝ) / (v n : ℝ) ^ 2 - d|) atTop (𝓝 (densityLimit d)) := by
      have hsub := hd.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d))
      have hc : Tendsto (fun _ : ℕ => densityLimit d) atTop (𝓝 (densityLimit d)) := tendsto_const_nhds
      simpa using hc.add (hsub.abs.const_mul 3)
    filter_upwards [hlim.eventually (gt_mem_nhds hb), hv.eventually (eventually_gt_atTop 0)] with n hn hnpos
    exact (normalized_extremal_le_densityLimit (v n) (k n) hnpos (hk n) d).trans_lt hn

/-- Every admissible prescribed-edge-count sequence with a limiting density has the same limit. -/
theorem tendsto_extremal_of_density (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n.choose 2) (d : ℝ)
    (hd : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 d)) :
    Tendsto (fun n : ℕ => extremal n (k n) / (n : ℝ) ^ 2) atTop (𝓝 (densityLimit d)) :=
  tendsto_extremal_of_density_along id k tendsto_id hk d hd

end Erdos1017.FractionalGraph

module

public import Erdos1017.FractionalLimit.FractionalDensityLimit
public import Mathlib.Topology.Sequences

/-!
# Uniform convergence of the fractional extremum

The fractional extremum converges to the density limit uniformly over every
admissible integer edge count, including both density endpoints
(`extremal_uniform_convergence`), and the maximum error `uniformError` over all
feasible edge counts tends to zero.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped Topology
open Filter

theorem normalized_edge_count_mem_Icc (n k : ℕ) (hk : k ≤ n.choose 2) :
    (k : ℝ) / (n : ℝ) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (sq_nonneg _), ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast (Nat.pos_of_ne_zero hn)) _
    rw [div_le_one hnpos]
    exact_mod_cast hk.trans (Nat.choose_le_pow n 2)

/-- Uniform convergence over every admissible integer edge count, including both density endpoints. -/
theorem extremal_uniform_convergence (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n.choose 2 →
      |extremal n k / (n : ℝ) ^ 2 - densityLimit ((k : ℝ) / (n : ℝ) ^ 2)| < ε := by
  by_contra h
  push Not at h
  choose v hv k hk hbad using h
  have hvlim : Tendsto v atTop atTop := tendsto_atTop_mono hv tendsto_id
  obtain ⟨d, _, φ, hφ, hd⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq
    (fun i => normalized_edge_count_mem_Icc (v i) (k i) (hk i))
  have hcost := tendsto_extremal_of_density_along (v ∘ φ) (k ∘ φ)
    (hvlim.comp hφ.tendsto_atTop) (fun i => hk (φ i)) d hd
  have hvalue := densityLimit_continuous.continuousAt.tendsto.comp hd
  have hzero : Tendsto (fun i : ℕ =>
      |extremal (v (φ i)) (k (φ i)) / (v (φ i) : ℝ) ^ 2 -
        densityLimit ((k (φ i) : ℝ) / (v (φ i) : ℝ) ^ 2)|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using (hcost.sub hvalue).abs
  obtain ⟨i, hi⟩ := (hzero.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad (φ i))) hi

/-- The maximum error over the finite set of all feasible edge counts. -/
def uniformError (n : ℕ) : ℝ :=
  (Finset.range (n.choose 2 + 1)).sup' ⟨0, by simp⟩
    (fun k => |extremal n k / (n : ℝ) ^ 2 - densityLimit ((k : ℝ) / (n : ℝ) ^ 2)|)

theorem uniformError_nonneg (n : ℕ) : 0 ≤ uniformError n := by
  unfold uniformError
  have h := Finset.le_sup'
    (fun k => |extremal n k / (n : ℝ) ^ 2 - densityLimit ((k : ℝ) / (n : ℝ) ^ 2)|)
    (show 0 ∈ Finset.range (n.choose 2 + 1) by simp)
  exact (abs_nonneg _).trans h

/-- The literal finite maximum in the uniform convergence assertion tends to zero. -/
theorem tendsto_uniformError : Tendsto uniformError atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (uniformError_nonneg n))
  · intro b hb
    obtain ⟨N, hN⟩ := extremal_uniform_convergence (b / 2) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hmax : uniformError n ≤ b / 2 := by
      apply Finset.sup'_le
      intro k hk
      exact (hN n hn k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).le
    linarith

end Erdos1017.FractionalGraph

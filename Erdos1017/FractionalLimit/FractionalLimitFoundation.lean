module

public import Erdos1017.FractionalLimit.FractionalExtremal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Fin.Embedding

/-!
# Padded blowups and finite-graph lower bounds on the limit

This module defines the `paddedBlowup` of a finite graph, which fits as many
uniform clones as possible and leaves the remaining vertices isolated, and
proves that its value and density converge, so that every finite graph supplies
an asymptotic lower bound at every prescribed density
(`finite_graph_eventual_lower`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators Topology
open Filter

variable {N : ℕ}

/-- Fit as many uniform clones as possible and leave all remaining vertices isolated. -/
def paddedBlowup (G : SimpleGraph (Fin N)) (n : ℕ) : SimpleGraph (Fin n) :=
  (blowup G (n / N)).map (Fin.castLEEmb (Nat.mul_div_le n N))

theorem paddedBlowup_edge_count (G : SimpleGraph (Fin N)) (n : ℕ) :
    (paddedBlowup G n).edgeSet.ncard = (n / N) ^ 2 * G.edgeSet.ncard := by
  rw [paddedBlowup, edge_count_map, edge_count_blowup]

theorem paddedBlowup_value (G : SimpleGraph (Fin N)) (n : ℕ) (hN : 0 < N) (hn : N ≤ n) :
    value (paddedBlowup G n) = (n / N : ℕ) ^ 2 * value G := by
  rw [paddedBlowup, value_map, value_blowup G (Nat.div_pos hn hN)]

theorem tendsto_clone_ratio (hN : 0 < N) :
    Tendsto (fun n : ℕ => ((n / N : ℕ) : ℝ) / n) atTop (𝓝 ((N : ℝ)⁻¹)) := by
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    (tendsto_mod_div_atTop_nhds_zero_nat hN)).div_const (N : ℝ)
  have heq : (fun n : ℕ => ((n / N : ℕ) : ℝ) / n) =ᶠ[atTop]
      (fun n : ℕ => (1 - ((n % N : ℕ) : ℝ) / n) / N) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hdiv : ((n % N : ℕ) : ℝ) + N * (n / N : ℕ) = n := by
      exact_mod_cast Nat.mod_add_div n N
    field_simp
    nlinarith [hdiv]
  apply Tendsto.congr' heq.symm
  simpa using h

theorem tendsto_paddedBlowup_value (G : SimpleGraph (Fin N)) (hN : 0 < N) :
    Tendsto (fun n : ℕ => value (paddedBlowup G n) / (n : ℝ) ^ 2) atTop
      (𝓝 (value G / (N : ℝ) ^ 2)) := by
  have h := (tendsto_clone_ratio hN).pow 2 |>.mul_const (value G)
  apply Tendsto.congr' (show _ =ᶠ[atTop] _ from ?_) (by simpa [div_eq_mul_inv, mul_comm] using h)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [paddedBlowup_value G n hN hn]
  ring

theorem tendsto_paddedBlowup_density (G : SimpleGraph (Fin N)) (hN : 0 < N) :
    Tendsto (fun n : ℕ => ((paddedBlowup G n).edgeSet.ncard : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 ((G.edgeSet.ncard : ℝ) / (N : ℝ) ^ 2)) := by
  have h := (tendsto_clone_ratio hN).pow 2 |>.mul_const (G.edgeSet.ncard : ℝ)
  convert h using 1
  · funext n
    rw [paddedBlowup_edge_count, Nat.cast_mul, Nat.cast_pow]
    ring
  · simp [div_eq_mul_inv, mul_comm]

/-- Every actual finite graph supplies an asymptotic lower bound at every prescribed density. -/
theorem finite_graph_eventual_lower_along (G : SimpleGraph (Fin N)) (hN : 0 < N)
    (v k : ℕ → ℕ) (hv : Tendsto v atTop atTop)
    (hk : ∀ n, k n ≤ (v n).choose 2) (d a : ℝ)
    (hd : Tendsto (fun n : ℕ => (k n : ℝ) / (v n : ℝ) ^ 2) atTop (𝓝 d))
    (ha : a < value G / (N : ℝ) ^ 2 - 3 * |(G.edgeSet.ncard : ℝ) / (N : ℝ) ^ 2 - d|) :
    ∀ᶠ n : ℕ in atTop, a < extremal (v n) (k n) / (v n : ℝ) ^ 2 := by
  have hlim := ((tendsto_paddedBlowup_value G hN).comp hv).sub
    ((((tendsto_paddedBlowup_density G hN).comp hv).sub hd).abs.const_mul 3)
  filter_upwards [hlim.eventually (lt_mem_nhds ha), hv.eventually (eventually_gt_atTop 0)] with n hn hnpos
  have h := value_le_extremal_edit (paddedBlowup G (v n)) (k n) (hk n)
  have hden : 0 < (v n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hnpos) _
  have hdiv := (div_le_div_iff_of_pos_right hden).mpr h
  rw [add_div, mul_div_assoc, ← abs_of_pos hden, ← abs_div, sub_div] at hdiv
  simp only [abs_of_pos hden] at hdiv
  simp only [Function.comp_apply] at hn
  linarith

/-- Every actual finite graph supplies an asymptotic lower bound at every prescribed density. -/
theorem finite_graph_eventual_lower (G : SimpleGraph (Fin N)) (hN : 0 < N)
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n.choose 2) (d a : ℝ)
    (hd : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 d))
    (ha : a < value G / (N : ℝ) ^ 2 - 3 * |(G.edgeSet.ncard : ℝ) / (N : ℝ) ^ 2 - d|) :
    ∀ᶠ n : ℕ in atTop, a < extremal n (k n) / (n : ℝ) ^ 2 :=
  finite_graph_eventual_lower_along G hN id k tendsto_id hk d a hd ha

end Erdos1017.FractionalGraph

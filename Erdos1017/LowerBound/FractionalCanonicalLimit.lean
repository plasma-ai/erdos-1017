module

public import Erdos1017.FractionalLimit.FractionalUniformLimit
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Convergence of the canonical capped edge counts

The prescribed edge count capped by the complete-graph count (`canonicalCount`)
gives a capped-floor sequence whose density and extremal values converge, and
the limiting extremal function keeps both one-sided finite edit bounds.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped Topology
open Filter

/-- The prescribed count is capped by the exact complete-graph edge count. -/
def canonicalCount (n : ℕ) (d : ℝ) : ℕ := min ⌊d * (n : ℝ) ^ 2⌋₊ (n.choose 2)

theorem canonicalCount_le (n : ℕ) (d : ℝ) : canonicalCount n d ≤ n.choose 2 := min_le_right _ _

theorem tendsto_inverse_square :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  simpa only [div_pow, one_pow, zero_pow (by decide : 2 ≠ 0)] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

theorem tendsto_floor_density (d : ℝ) (hd : 0 ≤ d) :
    Tendsto (fun n : ℕ => (⌊d * (n : ℝ) ^ 2⌋₊ : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 d) := by
  have hconst : Tendsto (fun _ : ℕ => d) atTop (𝓝 d) := tendsto_const_nhds
  have hlower : Tendsto (fun n : ℕ => d - 1 / (n : ℝ) ^ 2) atTop (𝓝 d) := by
    simpa only [sub_zero] using hconst.sub tendsto_inverse_square
  apply hlower.squeeze' hconst
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hden : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) _
    rw [le_div_iff₀ hden]
    have hfloor := Nat.lt_floor_add_one (d * (n : ℝ) ^ 2)
    have hcancel : (d - 1 / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 = d * (n : ℝ) ^ 2 - 1 := by
      field_simp
    rw [hcancel]
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hden : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) _
    rw [div_le_iff₀ hden]
    exact Nat.floor_le (mul_nonneg hd (sq_nonneg _))

theorem tendsto_complete_density :
    Tendsto (fun n : ℕ => (n.choose 2 : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (hc.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 2
  apply Tendsto.congr' (show _ =ᶠ[atTop] _ from ?_) (by simpa using h)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Nat.cast_choose_two]
  field_simp

theorem tendsto_canonical_density (d : ℝ) (hd : d ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Tendsto (fun n : ℕ => (canonicalCount n d : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 d) := by
  have h := (tendsto_floor_density d hd.1).min tendsto_complete_density
  rw [min_eq_left hd.2] at h
  convert h using 1
  funext n
  simp only [canonicalCount, Nat.cast_min, min_div_div_right (sq_nonneg (n : ℝ))]

/-- The exact capped-floor sequence in the prescribed-density definition converges. -/
theorem tendsto_canonical_extremal (d : ℝ) (hd : d ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Tendsto (fun n : ℕ => extremal n (canonicalCount n d) / (n : ℝ) ^ 2)
      atTop (𝓝 (densityLimit d)) :=
  tendsto_extremal_of_density (fun n => canonicalCount n d) (fun n => canonicalCount_le n d)
    d (tendsto_canonical_density d hd)

theorem canonicalCount_mono (n : ℕ) {d e : ℝ} (hde : d ≤ e) :
    canonicalCount n d ≤ canonicalCount n e :=
  min_le_min (Nat.floor_mono (mul_le_mul_of_nonneg_right hde (sq_nonneg _))) le_rfl

/-- The limiting extremal function retains both one-sided finite edit bounds. -/
theorem densityLimit_edit_bounds (d e : ℝ) (hd : d ∈ Set.Icc (0 : ℝ) (1 / 2))
    (he : e ∈ Set.Icc (0 : ℝ) (1 / 2)) (hde : d ≤ e) :
    densityLimit e ≤ densityLimit d + (e - d) ∧
      densityLimit d ≤ densityLimit e + 3 * (e - d) := by
  have hdlim := tendsto_canonical_extremal d hd
  have helim := tendsto_canonical_extremal e he
  have hdiff := (tendsto_canonical_density e he).sub (tendsto_canonical_density d hd)
  constructor
  · apply le_of_tendsto_of_tendsto helim (hdlim.add hdiff)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (extremal_edit_bounds n (canonicalCount n d) (canonicalCount n e)
      (canonicalCount_mono n hde) (canonicalCount_le n e)).1
    have hden : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) _
    have hdiv := (div_le_div_iff_of_pos_right hden).mpr h
    simpa only [sub_div, add_div, add_sub_assoc] using hdiv
  · apply le_of_tendsto_of_tendsto hdlim (helim.add (hdiff.const_mul 3))
    filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (extremal_edit_bounds n (canonicalCount n d) (canonicalCount n e)
      (canonicalCount_mono n hde) (canonicalCount_le n e)).2
    have hden : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) _
    have hdiv := (div_le_div_iff_of_pos_right hden).mpr h
    simpa only [add_div, mul_div_assoc, sub_div] using hdiv

end Erdos1017.FractionalGraph

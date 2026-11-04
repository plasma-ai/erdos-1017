module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleIteration
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Convergence of survival factors to exponential form

Exact exponential bounds on the edge exposure retain the full survival factor
with no per-round loss, and the exact survival factors converge to the
exponential factors used in a fixed finite nibble schedule, allowing the
normalized incident exponent to vary (`survival_factor_limit`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped Topology
open Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Exact exponential bounds retain the full survival factor, with no per-round Taylor loss. -/
theorem edge_exposure_rpow_bounds (H : Finset (Finset V)) (v : V) (e : Finset V)
    (p L D c : ℝ) (r : ℕ) (hp : 0 ≤ p) (hp1 : p < 1) (hc : 0 ≤ c)
    (hev : v ∈ e) (her : e.card = r)
    (hdegree : ∀ u ∈ e.erase v, L ≤ (degree H u : ℝ) ∧ (degree H u : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) :
    (1 - p) ^ (((r - 1 : ℕ) : ℝ) * D) ≤ (1 - p) ^ (blockers H v e).card ∧
      (1 - p) ^ (blockers H v e).card ≤
        (1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c) := by
  have hk : (e.erase v).card = r - 1 := by rw [Finset.card_erase_of_mem hev, her]
  have hb := blockers_card_bounds H v e L D c hc hdegree hcodegree
  rw [hk] at hb
  rw [← Real.rpow_natCast]
  exact ⟨Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) hb.2,
    Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) hb.1⟩

/-- The exact survival factors converge to the exponential factors used in a fixed finite
nibble schedule, allowing the normalized incident exponent to vary with the degree scale. -/
theorem survival_factor_limit (θ z : ℝ) (f : ℝ → ℝ) (hf : Tendsto f atTop (𝓝 z)) :
    Tendsto (fun D : ℝ => (1 - θ / D) ^ (D * f D)) atTop (𝓝 (Real.exp (-θ * z))) := by
  have hlog := Real.tendsto_mul_log_one_add_div_atTop (-θ)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hlog.mul hf)
  apply hexp.congr'
  filter_upwards [eventually_gt_atTop (max θ 0)] with D hD
  have hDpos : 0 < D := lt_of_le_of_lt (le_max_right _ _) hD
  have hθ : θ < D := lt_of_le_of_lt (le_max_left _ _) hD
  have hbase : 0 < 1 - θ / D := by
    have hdiv := (div_lt_one hDpos).mpr hθ
    linarith
  change Real.exp (D * Real.log (1 + -θ / D) * f D) = (1 - θ / D) ^ (D * f D)
  rw [Real.rpow_def_of_pos hbase]
  apply congrArg Real.exp
  simp only [neg_div, sub_eq_add_neg]
  ring

end Erdos1017.HypergraphNibble

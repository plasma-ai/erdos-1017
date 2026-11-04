module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleSurvivalLimit

/-!
# An ideal finite nibble schedule

A finite ideal schedule makes both the remaining-vertex fraction and the total
second-order waste budget arbitrarily small, with the number of rounds chosen
first (`exists_ideal_schedule`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped Topology BigOperators
open Filter

/-- A finite ideal schedule can make both the remaining-vertex fraction and the total
second-order waste budget arbitrarily small. The number of rounds is chosen before the
large-degree and small-codegree thresholds in the matching theorem. -/
theorem exists_ideal_schedule (r : ℕ) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ (h : ℝ) (T : ℕ), 0 < h ∧ 0 < T ∧ h / T < 1 / 2 ∧ Real.exp (-h) < δ / 4 ∧
      (∑ i : Fin T, 4 * (h / T) ^ 2 * (r : ℝ) ^ 2 * C ^ 2 *
        Real.exp (2 * ((r - 1 : ℕ) : ℝ) * (h / T) * (i : ℕ))) < δ / 4 := by
  have hexp : Tendsto (fun h : ℝ => Real.exp (-h)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hevent := (eventually_gt_atTop (0 : ℝ)).and
    (hexp.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 4 by positivity)))
  obtain ⟨h, hh, hsmall⟩ := hevent.exists
  let K : ℝ := 4 * h ^ 2 * (r : ℝ) ^ 2 * C ^ 2 * Real.exp (2 * ((r - 1 : ℕ) : ℝ) * h)
  have hlimit : Tendsto (fun T : ℕ => K / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ T : ℕ in atTop, 2 * h < (T : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2 * h))
  obtain ⟨T, hTlarge, hTcost⟩ := (hlarge.and
    (hlimit.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 4 by positivity)))).exists
  have hTpos : (0 : ℝ) < T := by linarith
  have hT : 0 < T := by exact_mod_cast hTpos
  have hθ : 0 ≤ h / (T : ℝ) := div_nonneg hh.le hTpos.le
  have hhalf : h / (T : ℝ) < 1 / 2 := by
    apply (div_lt_iff₀ hTpos).mpr
    linarith
  refine ⟨h, T, hh, hT, hhalf, hsmall, ?_⟩
  calc
    _ ≤ ∑ _i : Fin T, 4 * (h / T) ^ 2 * (r : ℝ) ^ 2 * C ^ 2 *
        Real.exp (2 * ((r - 1 : ℕ) : ℝ) * h) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (i : ℝ) ≤ T := by exact_mod_cast i.isLt.le
      have hprod : h / (T : ℝ) * (i : ℝ) ≤ h := by
        have hmul := mul_le_mul_of_nonneg_left hi hθ
        simpa [hTpos.ne'] using hmul
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hk : 0 ≤ 2 * ((r - 1 : ℕ) : ℝ) := by positivity
      nlinarith
    _ = K / T := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [K]
      field_simp
    _ < _ := hTcost

end Erdos1017.HypergraphNibble

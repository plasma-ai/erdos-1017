module

public import Erdos1017.Models.Capped.CappedAttainment
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz continuity of the capped value in density

Attained capped optima and density restoration give the three-Lipschitz
comparison of the capped value at admissible densities, hence its continuity
(`capValue_continuousOn`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Actual attained capped optima and the constructed density restoration
give the three-Lipschitz comparison at every admissible density. -/
theorem capValue_le_add_three_mul_abs_sub (r : ℕ) (d e : ℝ)
    (hd : d ∈ Icc 0 (1 / 2)) (he : e ∈ Icc 0 (1 / 2)) :
    capValue Ω μ r d ≤ capValue Ω μ r e + 3 * |d - e| := by
  obtain ⟨W, _, hdW, hoW, hmax⟩ := exists_fixedMeasureMaximizer (μ := μ) r e he
  obtain ⟨V, hV, hdV, hoV, _⟩ := exists_fixedMeasureMaximizer (μ := μ) r d hd
  obtain ⟨U, hU, hdU, hcost⟩ := exists_density_restoration V hV e he
  have hcompare := hmax.2 U hU (hdU.trans hdW.symm)
  rw [hoV, hdV] at hcost
  rw [hoW] at hcompare
  linarith

theorem capValue_abs_sub_le (r : ℕ) (d e : ℝ)
    (hd : d ∈ Icc 0 (1 / 2)) (he : e ∈ Icc 0 (1 / 2)) :
    |capValue Ω μ r d - capValue Ω μ r e| ≤ 3 * |d - e| := by
  have hde := capValue_le_add_three_mul_abs_sub (μ := μ) r d e hd he
  have hed := capValue_le_add_three_mul_abs_sub (μ := μ) r e d he hd
  rw [abs_sub_comm e d] at hed
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem capValue_lipschitzOnWith (r : ℕ) :
    LipschitzOnWith 3 (capValue Ω μ r) (Icc 0 (1 / 2)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro d hd e he
  simpa only [Real.dist_eq, NNReal.coe_ofNat] using capValue_abs_sub_le (μ := μ) r d e hd he

theorem capValue_continuousOn (r : ℕ) :
    ContinuousOn (capValue Ω μ r) (Icc 0 (1 / 2)) :=
  (capValue_lipschitzOnWith (μ := μ) r).continuousOn

end Erdos1017.CappedModel

module

public import Erdos1017.Multipartite.Dust.DustCellRestriction
public import Erdos1017.Multipartite.Physical.PhysicalCellLift

/-!
# Physical clique laws from a selector

An attained selector gives independently sampled physical clique laws with an
explicit repair on chosen completed cells, and with equal dust cells the
constructed laws have exact pair measures and cost within `s²/N` of the bounded
dust value.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.DustPhysicalLift

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An attained selector gives actual independently sampled physical clique laws,
with an explicit repair on any chosen completed cells. -/
theorem exists_anchored_lift {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (μ : Option (Fin m) → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset (Option (Fin m))) :
    ∃ w : Multipartite.Selection (Option (Fin m)) → ℝ,
      Multipartite.PrimalFeasible (Multipartite.anchorMasses p) w ∧
      PhysicalCellLift.cost μ (Multipartite.anchorMasses p) w S =
        Selector.value p + (∑ i ∈ S, Multipartite.anchorMasses p i ^ 2) / 2 := by
  obtain ⟨v, hv, heq, _⟩ := Selector.value_attained p hp
  refine ⟨Multipartite.anchorWeight v, Multipartite.anchor_feasible p v hv, ?_⟩
  rw [PhysicalCellLift.cost_eq μ _ _ (Multipartite.anchor_feasible p v hv).1,
    Multipartite.anchor_cost, heq]

/-- The square mass of equal dust cells is exactly s²/N. -/
theorem uniform_repair_square {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (p : Fin m → ℝ) (s : ℝ) (hpzero : ∀ i ∈ S, p i = 0) :
    (∑ i ∈ S.image some,
      Multipartite.anchorMasses (fun j => p j + s * Selector.uniformCellWeights S j) i ^ 2) =
      s ^ 2 / (S.card : ℝ) := by
  rw [Finset.sum_image (fun i _ j _ h => Option.some.inj h)]
  have h := (DustCellRestriction.uniform_cell_moments S hS p s hpzero).2.2
  simpa [DustCellRestriction.cell, Finset.sum_ite, Multipartite.anchorMasses] using h

/-- The constructed physical laws have exact pair measures and cost within
s²/N of the bounded dust value. No physical-infimum identification is assumed. -/
theorem exists_uniform_cell_lift {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (p : Fin m → ℝ) (s : ℝ) (hpzero : ∀ i ∈ S, p i = 0)
    (hp : ∀ i, 0 ≤ p i + s * Selector.uniformCellWeights S i ∧
      p i + s * Selector.uniformCellWeights S i ≤ 1)
    (μ : Option (Fin m) → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ w : Multipartite.Selection (Option (Fin m)) → ℝ,
      Multipartite.PrimalFeasible
        (Multipartite.anchorMasses (fun i => p i + s * Selector.uniformCellWeights S i)) w ∧
      (∀ i j, PhysicalCellLift.completedPairLoad μ
        (Multipartite.anchorMasses (fun i => p i + s * Selector.uniformCellWeights S i))
        w (S.image some) i j =
        if i ≠ j ∨ i ∈ S.image some then
          ENNReal.ofReal
            (Multipartite.anchorMasses (fun i => p i + s * Selector.uniformCellWeights S i) i *
              Multipartite.anchorMasses (fun i => p i + s * Selector.uniformCellWeights S i) j) •
              (μ i).prod (μ j) else 0) ∧
      PhysicalCellLift.cost μ
        (Multipartite.anchorMasses (fun i => p i + s * Selector.uniformCellWeights S i))
        w (S.image some) ≤ MultipartiteDust.value p s + s ^ 2 / (S.card : ℝ) := by
  obtain ⟨w, hw, hcost⟩ := exists_anchored_lift
    (fun i => p i + s * Selector.uniformCellWeights S i) hp μ (S.image some)
  refine ⟨w, hw, PhysicalCellLift.completedPairLoad_eq μ _ w hw (S.image some), ?_⟩
  rw [hcost, uniform_repair_square S hS p s hpzero]
  have h := DustCellBridge.selector_value_le_dust_add_error S hS p s hpzero hp
  have herr : s ^ 2 / (2 * (S.card : ℝ)) = (s ^ 2 / (S.card : ℝ)) / 2 := by ring
  rw [herr] at h
  linarith

end Erdos1017.DustPhysicalLift

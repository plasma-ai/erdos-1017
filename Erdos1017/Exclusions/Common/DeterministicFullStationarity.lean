module

public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Full stationarity of deterministic-charge optima

A deterministic-charge full optimum above the benchmark has its own full
stationary record on the same model, with a newly constructed multiplier, and
strict support puts every present charge strictly above the lower color
boundary.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual deterministic-charge full optimum above the benchmark has
its own full stationary record on the same model. The multiplier is newly
constructed; neither a model nor its selected row structure is replaced. -/
theorem exists_same_model_fullStationaryClass (W : Model Ω μ)
    (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < objective W) :
    ∃ m : ℝ, FullStationaryClass (density W) (objective W) W m := by
  have hregular := full_regular_of_strict_benchmark_gap W hW hopt hd hgap
  obtain ⟨m, ν, hm, _, _, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
    exists_full_regular_kernel W hW hopt hregular (by linarith [hd.1]) hd.2
  have hdet := shiftedColor_deterministic_of_complementary W m hcomp hphysical
  rw [hν] at hrow
  exact ⟨m, hW, rfl, rfl, hopt, hm, hdet, hmem, hcomp, hrow, hfinite, hindex⟩

/-- Strict support in the newly constructed own record puts every actual
present charge strictly above the lower color boundary. A positive whole
block with charge exactly minus three is therefore impossible. -/
theorem ae_present_charge_gt_neg_three_of_full_optimum (W : Model Ω μ)
    (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < objective W) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p = 1 →
      -3 < W.moment CappedColor.charge p := by
  obtain ⟨m, hm⟩ := exists_same_model_fullStationaryClass W hW hopt hphysical hd hgap
  have hstrict := (hm.strict_gap_structure hd hgap).strict_support
  filter_upwards [hstrict] with p hp hG
  have hM : 0 < shiftedMoment W m p := by
    by_contra hn
    rw [ite_eq_right hn, hG] at hp
    norm_num at hp
  rw [shiftedMoment_eq, hG] at hM
  linarith [hm.multiplier_mem.1]

end Erdos1017.CappedModel

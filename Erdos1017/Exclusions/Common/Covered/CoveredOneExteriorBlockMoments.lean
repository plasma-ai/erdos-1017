module

public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorBlocks

/-!
# Density and objective of the one-exterior block

The one-exterior-part graph has three independent squares with the `A`-`C` and
`A`-`E` rectangles missing in both orientations, and its objective separates
into the fixed `AB` charge plus the child's own linear objective, by exact
product integration.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace Erdos1017.CoveredOneExterior

private theorem integral_finite_labels {Ω ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ι] [Fintype ι] [DiscreteMeasurableSpace ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (qLabel : Ω → ι) (hq : Measurable qLabel) (f : ι → ℝ) :
    (∫ x, f (qLabel x) ∂μ) = ∑ i, μ.real (qLabel ⁻¹' {i}) * f i := by
  have he : (fun x => f (qLabel x)) =
      fun x => ∑ i, (qLabel ⁻¹' {i}).indicator (fun _ => f i) x := by
    funext x
    simp [Set.indicator_apply]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hq (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hq (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

private theorem integral_finite_label_pairs {Ω ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ι] [Fintype ι] [DiscreteMeasurableSpace ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (qLabel : Ω → ι) (hq : Measurable qLabel) (f : ι → ι → ℝ) :
    (∫ p : Ω × Ω, f (qLabel p.1) (qLabel p.2) ∂μ.prod μ) =
      ∑ i, ∑ j, μ.real (qLabel ⁻¹' {i}) * μ.real (qLabel ⁻¹' {j}) * f i j := by
  have hi := integral_finite_labels (μ := μ.prod μ)
    (fun p : Ω × Ω => (qLabel p.1, qLabel p.2))
    ((hq.comp measurable_fst).prodMk (hq.comp measurable_snd))
    (fun p => f p.1 p.2)
  rw [Fintype.sum_prod_type] at hi
  refine hi.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)))
  have he : (fun p : Ω × Ω => (qLabel p.1, qLabel p.2)) ⁻¹' {(i, j)} =
      (qLabel ⁻¹' {i}) ×ˢ (qLabel ⁻¹' {j}) := by
    ext p
    simp
  rw [he, measureReal_prod_prod]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original one-exterior-part graph has three independent squares,
with A-to-C and A-to-E missing in both orientations. -/
theorem block_physicalDensity (label : Ω → Fin 4) (hlabel : Measurable label) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let x := μ.real (label ⁻¹' {2})
    let e := μ.real (label ⁻¹' {3})
    FiniteCappedSamplingCost.physicalDensity μ
      (fun v w => blockAdjacency (label v) (label w)) =
        (1 - a ^ 2 - b ^ 2 - x ^ 2 - 2 * a * (x + e)) / 2 := by
  let a := μ.real (label ⁻¹' {0})
  let b := μ.real (label ⁻¹' {1})
  let x := μ.real (label ⁻¹' {2})
  let e := μ.real (label ⁻¹' {3})
  have hmass : a + b + x + e = 1 := by
    have hi := integral_finite_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, a, b, x, e, add_assoc] using hi.symm
  have hmass2 := congrArg (fun z : ℝ => z ^ 2) hmass
  have hi := integral_finite_label_pairs (μ := μ) label hlabel
    (fun i j => if blockAdjacency i j = true then (1 : ℝ) else 0)
  change (∫ p : Ω × Ω,
    if blockAdjacency (label p.1) (label p.2) = true then (1 : ℝ) else 0
      ∂μ.prod μ) / 2 = (1 - a ^ 2 - b ^ 2 - x ^ 2 - 2 * a * (x + e)) / 2
  rw [hi]
  simp [blockAdjacency, Fin.sum_univ_succ]
  dsimp only [a, b, x, e] at hmass2 ⊢
  nlinarith only [hmass2]

/-- Exact original product integration separates the fixed AB charge
from the child's own linear objective. No conditional normalization is used. -/
theorem block_physicalObjective (label : Ω → Fin 4) (hlabel : Measurable label)
    (y : Coefficients) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let x := μ.real (label ⁻¹' {2})
    let e := μ.real (label ⁻¹' {3})
    FiniteCappedSamplingCost.physicalObjective μ
      (fun v w => blockCharge y (label v) (label w)) = a * b + objective b x e y := by
  have hi := integral_finite_label_pairs (μ := μ) label hlabel (blockCharge y)
  change (∫ p : Ω × Ω, blockCharge y (label p.1) (label p.2) ∂μ.prod μ) / 2 = _
  rw [hi, objective_apply]
  simp [blockCharge, Fin.sum_univ_succ]
  ring

end Erdos1017.CoveredOneExterior

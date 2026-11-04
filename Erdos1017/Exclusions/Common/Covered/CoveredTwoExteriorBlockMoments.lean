module

public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorBlocks
public import Erdos1017.Multipartite.TwoHead.TwoHeadVertexComparison
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# Density and objective of the two-exterior block

The `R`-empty five-region graph has exact density and an objective equal to the
fixed `AB` charge plus the child objective in the `B,C1,C2,E` masses; completing
either secondary square raises the density by half its mass squared and costs
`D` times that amount.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace Erdos1017.CoveredTwoExterior

open VertexClassification

private theorem integral_labels {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    [Fintype ι] [DiscreteMeasurableSpace ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    (label : Ω → ι) (hlabel : Measurable label) (f : ι → ℝ) :
    (∫ z, f (label z) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have he : (fun z => f (label z)) =
      fun z => ∑ i, (label ⁻¹' {i}).indicator (fun _ => f i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

private theorem integral_label_pairs {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (label : Ω → Fin 5) (hlabel : Measurable label)
    (f : Fin 5 → Fin 5 → ℝ) :
    (∫ p : Ω × Ω, f (label p.1) (label p.2) ∂μ.prod μ) =
      ∑ i, ∑ j, μ.real (label ⁻¹' {i}) * μ.real (label ⁻¹' {j}) * f i j := by
  have h := integral_labels (μ := μ.prod μ)
    (fun p : Ω × Ω => (label p.1, label p.2))
    ((hlabel.comp measurable_fst).prodMk (hlabel.comp measurable_snd))
    (fun ij => f ij.1 ij.2)
  rw [Fintype.sum_prod_type] at h
  refine h.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)))
  have heq : (fun p : Ω × Ω => (label p.1, label p.2)) ⁻¹' {(i, j)} =
      (label ⁻¹' {i}) ×ˢ (label ⁻¹' {j}) := by
    ext p
    simp
  rw [heq, measureReal_prod_prod]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exact original density of the R-empty five-region graph. Both
secondary atomic squares and all A-to-exterior missing rectangles remain. -/
theorem block_physicalDensity (label : Ω → Fin 5) (hlabel : Measurable label) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let u1 := μ.real (label ⁻¹' {2})
    let u2 := μ.real (label ⁻¹' {3})
    let e := μ.real (label ⁻¹' {4})
    FiniteCappedSamplingCost.physicalDensity μ
      (fun x y => blockAdjacency (label x) (label y)) =
        (1 - a ^ 2 - b ^ 2 - u1 ^ 2 - u2 ^ 2 - 2 * a * (u1 + u2 + e)) / 2 := by
  have hmass : μ.real (label ⁻¹' {0}) + μ.real (label ⁻¹' {1}) +
      μ.real (label ⁻¹' {2}) + μ.real (label ⁻¹' {3}) + μ.real (label ⁻¹' {4}) = 1 := by
    have h := integral_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, add_assoc] using h.symm
  have hmass2 := congrArg (fun z : ℝ => z ^ 2) hmass
  change (∫ p : Ω × Ω,
    if blockAdjacency (label p.1) (label p.2) = true then (1 : ℝ) else 0 ∂μ.prod μ) / 2 = _
  rw [integral_label_pairs label hlabel (fun i j => if blockAdjacency i j = true then 1 else 0)]
  simp [blockAdjacency, Fin.sum_univ_succ]
  nlinarith only [hmass2]

omit [IsProbabilityMeasure μ] in
/-- The full original objective is fixed AB plus the existing child
objective with the literal B,C1,C2,E masses. No own-value transfer occurs. -/
theorem block_physicalObjective [IsFiniteMeasure μ]
    (label : Ω → Fin 5) (hlabel : Measurable label) (x : Coefficients) :
    FiniteCappedSamplingCost.physicalObjective μ
      (fun v w => blockCharge x (label v) (label w)) =
        μ.real (label ⁻¹' {0}) * μ.real (label ⁻¹' {1}) +
          TwoHeadVertexComparison.objective (μ.real (label ⁻¹' {1}))
            (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) (μ.real (label ⁻¹' {4})) x := by
  change (∫ p : Ω × Ω, blockCharge x (label p.1) (label p.2) ∂μ.prod μ) / 2 = _
  rw [integral_label_pairs label hlabel, TwoHeadVertexComparison.objective_apply]
  simp [blockCharge, Fin.sum_univ_succ]
  ring

/-- Completing either original secondary square increases actual density
by half of its original mass squared. A remains independent. -/
theorem repeated_physicalDensity (label : Ω → Fin 5) (hlabel : Measurable label)
    (i : Fin 5) (hi : i = 2 ∨ i = 3) :
    FiniteCappedSamplingCost.physicalDensity μ
      (fun a b => repeatedAdjacency i (label a) (label b)) =
        FiniteCappedSamplingCost.physicalDensity μ
          (fun a b => blockAdjacency (label a) (label b)) + μ.real (label ⁻¹' {i}) ^ 2 / 2 := by
  change (∫ p : Ω × Ω,
    if repeatedAdjacency i (label p.1) (label p.2) = true then (1 : ℝ) else 0 ∂μ.prod μ) / 2 =
      (∫ p : Ω × Ω,
        if blockAdjacency (label p.1) (label p.2) = true then (1 : ℝ) else 0 ∂μ.prod μ) / 2 + _
  rw [integral_label_pairs label hlabel
    (fun a b => if repeatedAdjacency i a b = true then 1 else 0),
    integral_label_pairs label hlabel (fun a b => if blockAdjacency a b = true then 1 else 0)]
  rcases hi with rfl | rfl <;> simp [repeatedAdjacency, blockAdjacency, Fin.sum_univ_succ] <;> ring

omit [IsProbabilityMeasure μ] in
/-- The same completed square pays exactly minus D times half of its
original mass squared, under the unchanged original finite measure. -/
theorem repeated_physicalObjective [IsFiniteMeasure μ]
    (label : Ω → Fin 5) (hlabel : Measurable label) (x : Coefficients)
    (i : Fin 5) (hi : i = 2 ∨ i = 3) (D : ℝ) :
    FiniteCappedSamplingCost.physicalObjective μ
      (fun a b => repeatedCharge x i D (label a) (label b)) =
        FiniteCappedSamplingCost.physicalObjective μ
          (fun a b => blockCharge x (label a) (label b)) - D * μ.real (label ⁻¹' {i}) ^ 2 / 2 := by
  change (∫ p : Ω × Ω, repeatedCharge x i D (label p.1) (label p.2) ∂μ.prod μ) / 2 =
      (∫ p : Ω × Ω, blockCharge x (label p.1) (label p.2) ∂μ.prod μ) / 2 - _
  rw [integral_label_pairs label hlabel, integral_label_pairs label hlabel]
  rcases hi with rfl | rfl <;> simp [repeatedCharge, blockCharge, Fin.sum_univ_succ] <;> ring

end Erdos1017.CoveredTwoExterior

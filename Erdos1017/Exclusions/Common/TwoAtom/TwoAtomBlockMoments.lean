module

public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountSpace
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockGeometry

/-!
# Density and objective of the four-region block graph

The four-block graph has exactly the two atomic missing squares and the two
ordered `A`-to-`E` missing rectangles, and its product-law objective equals the
count-space objective, including the fixed saturated `AB` contribution and the
signed diffuse penalties.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace Erdos1017.TwoAtomCountGate

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

/-- The actual four-block graph has exactly the two atomic missing
squares and the two ordered A-to-E missing rectangles. -/
theorem block_physicalDensity (qLabel : Ω → Fin 4) (hq : Measurable qLabel) :
    let a := μ.real (qLabel ⁻¹' {0})
    let b := μ.real (qLabel ⁻¹' {1})
    let e := μ.real (qLabel ⁻¹' {3})
    FiniteCappedSamplingCost.physicalDensity μ
      (fun x y => blockAdjacency (qLabel x) (qLabel y)) =
        (1 - a ^ 2 - b ^ 2 - 2 * a * e) / 2 := by
  let a := μ.real (qLabel ⁻¹' {0})
  let b := μ.real (qLabel ⁻¹' {1})
  let u := μ.real (qLabel ⁻¹' {2})
  let e := μ.real (qLabel ⁻¹' {3})
  have hmass : a + b + u + e = 1 := by
    have hi := integral_finite_labels (μ := μ) qLabel hq (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, a, b, u, e, add_assoc] using hi.symm
  have hmass2 := congrArg (fun z : ℝ => z ^ 2) hmass
  have hi := integral_finite_label_pairs (μ := μ) qLabel hq
    (fun i j => if blockAdjacency i j = true then (1 : ℝ) else 0)
  change (∫ p : Ω × Ω,
    if blockAdjacency (qLabel p.1) (qLabel p.2) = true then (1 : ℝ) else 0
      ∂μ.prod μ) / 2 = (1 - a ^ 2 - b ^ 2 - 2 * a * e) / 2
  rw [hi]
  simp [blockAdjacency, Fin.sum_univ_succ]
  dsimp only [a, b, u, e] at hmass2 ⊢
  nlinarith only [hmass2]

/-- The original product-law objective equals the count-space objective,
including its fixed saturated AB contribution and signed diffuse penalties. -/
theorem block_physicalObjective (qLabel : Ω → Fin 4) (hq : Measurable qLabel)
    (x : Coefficients) :
    let a := μ.real (qLabel ⁻¹' {0})
    let b := μ.real (qLabel ⁻¹' {1})
    let u := μ.real (qLabel ⁻¹' {2})
    let e := μ.real (qLabel ⁻¹' {3})
    FiniteCappedSamplingCost.physicalObjective μ
      (fun v w => blockCharge x (qLabel v) (qLabel w)) = objective a b u e x := by
  have hi := integral_finite_label_pairs (μ := μ) qLabel hq (blockCharge x)
  change (∫ p : Ω × Ω, blockCharge x (qLabel p.1) (qLabel p.2) ∂μ.prod μ) / 2 = _
  rw [hi, objective_apply]
  simp [blockCharge, Fin.sum_univ_succ]
  ring

end Erdos1017.TwoAtomCountGate

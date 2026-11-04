module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorBlocks
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# Block tables for the zero-exterior parent

This module defines the three-region parent on `A, B, E`, where only the `AB`,
`BE` and `EE` blocks are present, with its coefficients, feasibility, charge and
objective, and derives its clique tests, mass, density and objective by
embedding into the Boolean-`C` parent with `C` absent.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CoveredZeroExterior

abbrev Coefficients := Fin 2 → ℝ

def feasible : Set Coefficients :=
  {y | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ ∀ n : ℕ, (n : ℝ) * y 0 - y 1 * n * (n - 1) / 2 ≤ 1}

/-- The literal order is A, B, E; only AB, BE and EE are present. -/
def blockAdjacency : Fin 3 → Fin 3 → Bool :=
  ![![false, true, false], ![true, false, true], ![false, true, true]]

def blockCharge (y : Coefficients) : Fin 3 → Fin 3 → ℝ :=
  ![![0, 1, 0], ![1, 0, y 0], ![0, y 0, -y 1]]

def objective (b e : ℝ) (y : Coefficients) : ℝ := b * e * y 0 - e ^ 2 * y 1 / 2

theorem block_properties (y : Coefficients) :
    (∀ i j, blockAdjacency i j = blockAdjacency j i) ∧
      (∀ i j, blockCharge y i j = blockCharge y j i) ∧
      ∀ i j, blockAdjacency i j = false → blockCharge y i j = 0 := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · intro i j; fin_cases i <;> fin_cases j <;> simp [blockAdjacency, blockCharge]

/-- The absent C label embeds the three-cell tests in the already proved
Boolean-C parent; it does not add a positive physical fiber. -/
theorem block_tupleCharge_le_one (y : Coefficients) (hy : y ∈ feasible)
    {n : ℕ} (v : Fin n → Fin 3) (hc : FiniteArity.TupleClique blockAdjacency v) :
    FiniteArity.tupleCharge (blockCharge y) v ≤ 1 := by
  let z : CoveredOneExterior.Coefficients := ![0, y 0, 0, y 1]
  let embed : Fin 3 → Fin 4 := ![0, 1, 3]
  have hz : z ∈ CoveredOneExterior.feasible := by
    constructor
    · intro i; fin_cases i <;> simp [z, hy.1, hy.2.1]
    · intro s k
      have h := hy.2.2 k
      cases s <;> simpa [CoveredOneExterior.test_eq_value, CoveredOneExterior.constant,
        CoveredOneExterior.slope, TightCounts.value, z, mul_comm, mul_left_comm] using h
  have hG (i j : Fin 3) :
      CoveredOneExterior.blockAdjacency (embed i) (embed j) = blockAdjacency i j := by
    fin_cases i <;> fin_cases j <;> rfl
  have hY (i j : Fin 3) :
      CoveredOneExterior.blockCharge z (embed i) (embed j) = blockCharge y i j := by
    fin_cases i <;> fin_cases j <;> rfl
  have ht := CoveredOneExterior.block_tupleCharge_le_one z hz (embed ∘ v)
    (fun i j hij => by simpa only [Function.comp_apply, hG] using hc i j hij)
  simpa only [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
    Function.comp_apply, hY] using ht

theorem block_full_scalar_tests (y : Coefficients) (hy : y ∈ feasible)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 3) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => blockCharge y (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv => block_tupleCharge_le_one y hy (label ∘ v) hv)

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

theorem block_mass (label : Ω → Fin 3) (hlabel : Measurable label) :
    μ.real (label ⁻¹' {0}) + μ.real (label ⁻¹' {1}) + μ.real (label ⁻¹' {2}) = 1 := by
  have h := integral_finite_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
  simpa [Fin.sum_univ_succ, add_assoc] using h.symm

theorem block_physicalDensity (label : Ω → Fin 3) (hlabel : Measurable label) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let e := μ.real (label ⁻¹' {2})
    FiniteCappedSamplingCost.physicalDensity μ
      (fun v w => blockAdjacency (label v) (label w)) = a * b + b * e + e ^ 2 / 2 := by
  have h := integral_finite_label_pairs (μ := μ) label hlabel
    (fun i j => if blockAdjacency i j = true then (1 : ℝ) else 0)
  change (∫ p : Ω × Ω,
    if blockAdjacency (label p.1) (label p.2) = true then (1 : ℝ) else 0
      ∂μ.prod μ) / 2 = _
  rw [h]
  simp [blockAdjacency, Fin.sum_univ_succ]
  ring

theorem block_physicalObjective (label : Ω → Fin 3) (hlabel : Measurable label)
    (y : Coefficients) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let e := μ.real (label ⁻¹' {2})
    FiniteCappedSamplingCost.physicalObjective μ
      (fun v w => blockCharge y (label v) (label w)) = a * b + objective b e y := by
  have h := integral_finite_label_pairs (μ := μ) label hlabel (blockCharge y)
  change (∫ p : Ω × Ω, blockCharge y (label p.1) (label p.2) ∂μ.prod μ) / 2 = _
  rw [h]
  simp [blockCharge, objective, Fin.sum_univ_succ]
  ring

end Erdos1017.CoveredZeroExterior

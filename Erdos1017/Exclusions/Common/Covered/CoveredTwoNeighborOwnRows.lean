module

public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorNeighborBlockMoments
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Own rows of the two-neighbor model

The finite shifted rows follow from the model's own stationary event on each
positive fiber, the positive-`R` charge equation uses the corrected star
coefficient `b-a`, and that row gives `a<b` before any compact face is selected.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredTwoExteriorNeighbor

open CappedModel VertexClassification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integral_labels (label : Ω → Fin 5) (hlabel : Measurable label)
    (f : Fin 5 → ℝ) :
    (∫ w, f (label w) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have heq : (fun w => f (label w)) =
      fun w => ∑ i, (label ⁻¹' {i}).indicator (fun _ => f i) w := by
    funext w
    simp [Set.indicator_apply]
  rw [heq, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

/-- The literal finite shifted rows follow from the own stationary event
on each genuine positive original fiber. -/
theorem finite_rows_of_fullStationaryClass {W : Model Ω μ} {m d c : ℝ}
    (hW : FullStationaryClass d c W m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    ∀ i, (∑ j, μ.real (label ⁻¹' {j}) *
      (blockCharge x i j - m * (if blockAdjacency i j = true then 1 else 0))) =
        2 * (c - m * d) := by
  intro i
  obtain ⟨z, hz, hstat⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae hW.stationary)
  have hlabelz : label z = i := hz
  have heq : (∫ w, shiftedKernel W m z w ∂μ) =
      ∫ w, blockCharge x i (label w) - m *
        (if blockAdjacency i (label w) = true then 1 else 0) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => by
      rw [shiftedKernel, shiftedMoment_eq, (hmom (z, w)).1, (hmom (z, w)).2, hlabelz])
  rw [heq, integral_labels label hlabel (fun j => blockCharge x i j - m *
    (if blockAdjacency i j = true then 1 else 0))] at hstat
  exact hstat

/-- The positive-R charge equation uses the corrected star coefficient
b-a on the same original probability law and own multiplier. -/
theorem own_R_row {W : Model Ω μ} {m d c : ℝ}
    (hW : FullStationaryClass d c W m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    2 * (c - m * d) + m =
      (μ.real (label ⁻¹' {1}) - μ.real (label ⁻¹' {0})) * x 2 -
        μ.real (label ⁻¹' {2}) * x 4 - μ.real (label ⁻¹' {3}) * x 5 -
        μ.real (label ⁻¹' {4}) * x 6 := by
  have hR := finite_rows_of_fullStationaryClass hW label hlabel hpositive x hmom 4
  have hmass : μ.real (label ⁻¹' {0}) + μ.real (label ⁻¹' {1}) +
      μ.real (label ⁻¹' {2}) + μ.real (label ⁻¹' {3}) + μ.real (label ⁻¹' {4}) = 1 := by
    have h := integral_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, add_assoc] using h.symm
  have hm := congrArg (fun v : ℝ => m * v) hmass
  norm_num [blockAdjacency, blockCharge, Fin.sum_univ_succ] at hR
  nlinarith only [hR, hm]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The own positive R row derives actual a<b before the corrected
compact face is selected. No mass-order or stationary-row hypothesis is used. -/
theorem a_lt_b_of_fullStationaryClass {W : Model Ω μ} {m d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    μ.real (label ⁻¹' {0}) < μ.real (label ⁻¹' {1}) := by
  have hrow := own_R_row hW label hlabel hpositive x hmom
  have hgamma := (hW.strict_gap_structure hd hgap).gamma_pos
  have hz1 := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {2}) from measureReal_nonneg) (hx.1 4)
  have hz2 := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {3}) from measureReal_nonneg) (hx.1 5)
  have hp := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {4}) from measureReal_nonneg) (hx.1 6)
  by_contra h
  have hbad := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt h)) (hx.1 2)
  linarith only [hrow, hgamma, hz1, hz2, hp, hbad]

end Erdos1017.CoveredTwoExteriorNeighbor

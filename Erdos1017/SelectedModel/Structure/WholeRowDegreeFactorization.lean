module

public import Erdos1017.SelectedModel.Structure.WholeRowDegreeSeparation

/-!
# Degree factorization through whole rows

The original adjacency degree factors almost everywhere through the supplied
whole shifted-kernel row, including diffuse vertices, so equal row values give
equal degrees at almost every pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual original adjacency degree factors through the same supplied
whole shifted-kernel row almost everywhere, including diffuse vertices. -/
theorem ae_degree_eq_wholeRowDegree (W : Model Ω μ) (m : ℝ) (R : Ω → Lp ℝ 2 μ)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    ∀ᵐ x ∂μ, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = wholeRowDegree (R x) := by
  filter_upwards [hrow, Measure.ae_ae_of_ae_prod hsupport,
    KernelOperator.onL2_coe (adjacencyKernel W) (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ))] with x hr hs hop
  change KernelOperator.onL2 (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ)) x = _
  rw [hop, KernelOperator.applyKernel, wholeRowDegree]
  apply integral_congr_ae
  filter_upwards [hr, hs, Lp.coeFn_const 2 μ (1 : ℝ)] with y hry hsy hone
  rw [hone]
  simp only [Function.const_apply, mul_one]
  change W.moment CappedColor.adjacency (x, y) = _
  rw [hsy]
  change (if 0 < shiftedKernel W m x y then (1 : ℝ) else 0) = _
  rw [hry]

/-- One common degree-factorization event gives the original degree
identity at almost every pair of equal supplied row values. -/
theorem ae_row_eq_imp_degree_eq (W : Model Ω μ) (m : ℝ) (R : Ω → Lp ℝ 2 μ)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    ∀ᵐ p ∂μ.prod μ, R p.1 = R p.2 →
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 =
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
  have hdegree := ae_degree_eq_wholeRowDegree W m R hrow hsupport
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hdegree,
    Measure.quasiMeasurePreserving_snd.ae hdegree] with p hx hy heq
  rw [hx, hy, heq]

end Erdos1017.CappedModel

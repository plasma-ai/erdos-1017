module

public import Erdos1017.SelectedModel.Structure.NormalizedSetL2
public import Erdos1017.SelectedModel.Structure.WholeRowAtoms
public import Erdos1017.SelectedModel.Selection.SelectedStrictGapModel

/-!
# Degree separation of nonadjacent independent fibers

This module defines `wholeRowDegree`, the adjacency degree represented by a
whole shifted-kernel row, and shows that in the selected model with `c > B(d)`,
distinct positive independent whole row fibers that are mutually nonadjacent
have different original adjacency degrees.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original adjacency degree represented by a whole shifted-kernel row. -/
def wholeRowDegree (r : Lp ℝ 2 μ) : ℝ :=
  ∫ y, (if 0 < r y then 1 else 0 : ℝ) ∂μ

/-- Whole-row homogeneity identifies the original adjacency operator's
actual degree function on the same physical row fiber. -/
theorem wholeRowFiber_degree (W : Model Ω μ) (m : ℝ)
    (R : Ω → Lp ℝ 2 μ) (r : Lp ℝ 2 μ)
    (hr : KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) 4 m R r) :
    ∀ᵐ x ∂μ.restrict {x | R x = r},
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = wholeRowDegree r := by
  filter_upwards [hr.rows, ae_restrict_of_ae
    (KernelOperator.onL2_coe (adjacencyKernel W) (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ)))] with x hx hop
  change KernelOperator.onL2 (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ)) x = _
  rw [hop, KernelOperator.applyKernel, wholeRowDegree]
  apply integral_congr_ae
  filter_upwards [hx.2.1, Lp.coeFn_const 2 μ (1 : ℝ)] with y hy hone
  simp only [hy, hone, Function.const_apply, mul_one]

/-- Nonnegativity and strict support turn an actual missing rectangle in G
into a zero rectangle in the original shifted kernel. -/
theorem shiftedKernel_zero_of_adjacency_zero (W : Model Ω μ) (m : ℝ)
    (hmem : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Icc (0 : ℝ) 4)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (s t : Set Ω)
    (hzero : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), adjacencyKernel W p.1 p.2 = 0) :
    ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), shiftedKernel W m p.1 p.2 = 0 := by
  have hle : (μ.restrict s).prod (μ.restrict t) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [hzero, ae_mono hle hmem, ae_mono hle hsupport] with p hp hm hs
  change shiftedMoment W m p = 0
  change W.moment CappedColor.adjacency p = 0 at hp
  have hn : ¬0 < shiftedMoment W m p := by
    intro hpos
    rw [ite_eq_left hpos] at hs
    linarith
  exact le_antisymm (le_of_not_gt hn) hm.1

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- In the same selected model with c > B(d), distinct positive independent
whole row fibers that are mutually nonadjacent have different original
adjacency degrees. Tangent-null rigidity is derived from the actual class
and its minimum-multiplier selection, not assumed. -/
theorem FullStationaryClass.wholeRowDegree_ne_of_independent_nonadjacent
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmin : ∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n)
    (R : Ω → Lp ℝ 2 μ) (r u : Lp ℝ 2 μ) (hru : r ≠ u)
    (hrmeas : MeasurableSet {x | R x = r}) (humeas : MeasurableSet {x | R x = u})
    (hrpos : 0 < μ {x | R x = r}) (hupos : 0 < μ {x | R x = u})
    (hr : KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) 4 m R r)
    (hu : KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) 4 m R u)
    (hrr : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
      adjacencyKernel W p.1 p.2 = 0)
    (huu : ∀ᵐ p ∂(μ.restrict {x | R x = u}).prod (μ.restrict {x | R x = u}),
      adjacencyKernel W p.1 p.2 = 0)
    (hruzero : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
      adjacencyKernel W p.1 p.2 = 0) :
    wholeRowDegree r ≠ wholeRowDegree u := by
  have hsupport := (hW.strict_gap_structure hd hgap).strict_support
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  apply KernelOperator.degree_ne_of_homogeneous_zero_blocks
    (shiftedKernel W m) (by positivity) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) hsym (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)))
    (fun f hf hmean hdegree henergy =>
      (hW.selected_tangent_null_vector_rigidity_of_strict_gap hd hgap hmin
        f hf hmean hdegree henergy).2)
    _ _ hrmeas humeas hrpos hupos r u hru
    (hr.rows.mono (fun _ h => h.1)) (hu.rows.mono (fun _ h => h.1))
    (shiftedKernel_zero_of_adjacency_zero W m hW.moment_mem hsupport _ _ hrr)
    (shiftedKernel_zero_of_adjacency_zero W m hW.moment_mem hsupport _ _ huu)
    (shiftedKernel_zero_of_adjacency_zero W m hW.moment_mem hsupport _ _ hruzero)
    _ _ (wholeRowFiber_degree W m R r hr) (wholeRowFiber_degree W m R u hu)

end Erdos1017.CappedModel

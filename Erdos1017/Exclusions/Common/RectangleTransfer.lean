module

public import Erdos1017.Exclusions.Common.CancelingEdgeExtension
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Symmetric rectangle kernels

The kernel `rectangle` of a row-constant rectangle is defined, reduces to one
charge on the symmetric rectangle for disjoint cells, is integrable whenever the
exterior row is, and both orientations contribute once to the unhalved pair
integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.NeighborhoodExchange

/-- The symmetric kernel of a row-constant rectangle. -/
def rectangle {Ω : Type*} (J E : Set Ω) (s : Ω → ℝ) (x y : Ω) : ℝ :=
  J.indicator (fun _ => 1) x * E.indicator s y +
    E.indicator s x * J.indicator (fun _ => 1) y

/-- Disjoint cells make the indicator-product kernel one literal charge
on the symmetric rectangle, with no factor of two. -/
theorem rectangle_eq_ite {Ω : Type*} (J E : Set Ω) (hJE : Disjoint J E)
    (s : Ω → ℝ) (x y : Ω) : rectangle J E s x y =
      if FiniteArity.extensionPair J E x y then E.indicator s x + E.indicator s y else 0 := by
  have hx : ¬(x ∈ J ∧ x ∈ E) := fun h => Set.disjoint_left.mp hJE h.1 h.2
  have hy : ¬(y ∈ J ∧ y ∈ E) := fun h => Set.disjoint_left.mp hJE h.1 h.2
  by_cases hxJ : x ∈ J <;> by_cases hxE : x ∈ E <;>
    by_cases hyJ : y ∈ J <;> by_cases hyE : y ∈ E <;>
    simp_all [rectangle, FiniteArity.extensionPair]

theorem rectangle_one_eq_ite {Ω : Type*} (J E : Set Ω) (hJE : Disjoint J E)
    (x y : Ω) : rectangle J E (fun _ => 1) x y =
      if FiniteArity.extensionPair J E x y then 1 else 0 := by
  rw [rectangle_eq_ite J E hJE]
  split_ifs with h
  · rcases h with h | h
    · have hx : x ∉ E := fun hx => Set.disjoint_left.mp hJE h.1 hx
      simp [hx, h.2]
    · have hy : y ∉ E := fun hy => Set.disjoint_left.mp hJE h.1 hy
      simp [hy, h.2]
  · rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Boundedness is unnecessary for the actual rectangle integral: an
integrable exterior row suffices. -/
theorem integrable_rectangle (J E : Set Ω) (hJ : MeasurableSet J) (hE : MeasurableSet E)
    (s : Ω → ℝ) (hs : Integrable s μ) :
    Integrable (Function.uncurry (rectangle J E s)) (μ.prod μ) := by
  have hJint : Integrable (J.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hJ
  have hEint := hs.indicator hE
  exact (hJint.mul_prod hEint).add (hEint.mul_prod hJint)

/-- The row formula keeps its exterior point and its old conditioning law
explicit. -/
theorem integral_rectangle_row (J E : Set Ω) (hJ : MeasurableSet J) (hE : MeasurableSet E)
    (s : Ω → ℝ) (hs : Integrable s μ) (x : Ω) :
    (∫ y, rectangle J E s x y ∂μ) =
      J.indicator (fun _ => 1) x * (∫ y in E, s y ∂μ) + E.indicator s x * μ.real J := by
  unfold rectangle
  rw [integral_add ((hs.indicator hE).const_mul _) (((integrable_const (1 : ℝ)).indicator hJ).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator hE, integral_indicator hJ]
  simp only [setIntegral_const, smul_eq_mul, mul_one]

/-- Both orientations contribute once to the unhalved pair integral. -/
theorem integral_rectangle (J E : Set Ω) (hJ : MeasurableSet J) (hE : MeasurableSet E)
    (s : Ω → ℝ) (hs : Integrable s μ) :
    (∫ p, rectangle J E s p.1 p.2 ∂μ.prod μ) = 2 * μ.real J * (∫ y in E, s y ∂μ) := by
  have hJint : Integrable (J.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hJ
  have hEint := hs.indicator hE
  unfold rectangle
  rw [integral_add (hJint.mul_prod hEint) (hEint.mul_prod hJint), integral_prod_mul,
    integral_prod_mul, integral_indicator hE, integral_indicator hJ]
  simp only [setIntegral_const, smul_eq_mul, mul_one]
  ring

end Erdos1017.NeighborhoodExchange

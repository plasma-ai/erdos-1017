module

public import Erdos1017.Models.Capped.CappedMultilinearMoments

/-!
# Clique violation with deterministic charges

Conditionally independent pair colors with deterministic present charges have an
exact clique-violation expectation in terms of adjacency moments and the fixed
charges, and a positive first factor cannot hide a nonzero second factor on an
almost-everywhere zero product.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Conditional independent pair colors with deterministic present charges
have an exact clique-violation expectation in terms of their adjacency
moments and the fixed charges. -/
theorem integral_colorViolation_of_deterministic_charge
    (ρ : ι → Measure CappedColor) [∀ i, IsProbabilityMeasure (ρ i)]
    (z : ι → ℝ)
    (hdet : ∀ i, ∀ᵐ c ∂ρ i,
      CappedColor.charge c = z i * CappedColor.adjacency c) :
    (∫ c, colorViolation c ∂Measure.pi ρ) =
      max ((∑ i, z i) - 1) 0 *
        ∏ i, ∫ c, CappedColor.adjacency c ∂ρ i := by
  have hae : ∀ᵐ c ∂Measure.pi ρ,
      ∀ i, CappedColor.charge (c i) = z i * CappedColor.adjacency (c i) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval ρ i).quasiMeasurePreserving.ae (hdet i)
  calc
    (∫ c, colorViolation c ∂Measure.pi ρ) =
        ∫ c, max ((∑ i, z i) - 1) 0 *
          ∏ i, CappedColor.adjacency (c i) ∂Measure.pi ρ := by
      exact integral_congr_ae (hae.mono fun c hc =>
        (deterministic_color_expressions c z hc).2)
    _ = _ := by rw [integral_const_mul, integral_fintype_prod_eq_prod]

/-- A genuinely positive first factor cannot hide a nonzero second factor
on a product-almost-everywhere zero product. -/
theorem ae_zero_right_of_positive_factor {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (ξ : Measure X) (η : Measure Y) [SFinite ξ] [SFinite η]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hpos : 0 < ∫ x, f x ∂ξ)
    (hzero : ∀ᵐ p ∂ξ.prod η, f p.1 * g p.2 = 0) :
    ∀ᵐ y ∂η, g y = 0 := by
  have hmeas : MeasurableSet {p : X × Y | f p.1 * g p.2 = 0} :=
    measurableSet_eq_fun ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
      measurable_const
  have hsection := (Measure.ae_ae_comm hmeas).mp (Measure.ae_ae_of_ae_prod hzero)
  filter_upwards [hsection] with y hy
  by_contra hgy
  have hfzero : ∀ᵐ x ∂ξ, f x = 0 :=
    hy.mono (fun x hx => (mul_eq_zero.mp hx).resolve_right hgy)
  have hint : (∫ x, f x ∂ξ) = 0 := integral_eq_zero_of_ae hfzero
  linarith

end Erdos1017.CappedModel

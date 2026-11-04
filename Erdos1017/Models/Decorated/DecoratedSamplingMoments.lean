module

public import Erdos1017.Models.Capped.CappedSampleStatistics
public import Erdos1017.Models.Decorated.DecoratedSamplingIndependence
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Expectations of sampled density and charge

Unordered pairs of distinct sampled vertices are counted once, so the expected
sum of one-pair color tests counts each pair once and the sampled edge density
and signed charge expectations carry the exact finite-size bias.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Unordered pairs of distinct sampled vertices are counted once. -/
theorem card_cliquePair (n : ℕ) : Fintype.card (CliquePair n) = n.choose 2 := by
  classical
  rw [Fintype.card_subtype]
  simpa using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

/-- The expected sum of one-pair color tests counts each unordered pair once. -/
theorem integral_sampledColorLaw_sum (W : Model Ω μ) (n : ℕ)
    (f : C(CappedColor, ℝ)) :
    (∫ c, ∑ e : CliquePair n, f (c e)
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      (n.choose 2 : ℝ) * ∫ p, W.moment f p ∂μ.prod μ := by
  have hint (e : CliquePair n) : Integrable
      (fun c : CliquePair n → CappedColor => f (c e))
      (sampledColorLaw W n : Measure (CliquePair n → CappedColor)) := by
    apply Integrable.of_bound
      (f.continuous.comp (continuous_apply e)).aestronglyMeasurable ‖f‖
    exact Filter.Eventually.of_forall (fun c => f.norm_coe_le_norm (c e))
  rw [integral_finsetSum Finset.univ (fun e _ => hint e)]
  simp_rw [integral_sampledColorLaw_pair W n]
  simp only [Finset.sum_const, Finset.card_univ, card_cliquePair, nsmul_eq_mul]

/-- The sampled edge-density expectation has the exact finite-size bias. -/
theorem integral_sampleDensity (W : Model Ω μ) (n : ℕ) (hn : 0 < n) :
    (∫ c, sampleDensity c
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      (1 - 1 / (n : ℝ)) * density W := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ n
  have hsum : (∫ c, ∑ e : CliquePair n, CappedColor.adjacency (c e)
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      (n.choose 2 : ℝ) * ∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ :=
    integral_sampledColorLaw_sum W n ⟨CappedColor.adjacency, CappedColor.continuous_adjacency⟩
  unfold sampleDensity density
  simp only [div_eq_mul_inv, integral_mul_const]
  rw [hsum, hcard]
  field_simp

/-- The sampled signed-charge expectation has the same finite-size bias. -/
theorem integral_sampleCharge (W : Model Ω μ) (n : ℕ) (hn : 0 < n) :
    (∫ c, sampleCharge c
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      (1 - 1 / (n : ℝ)) * objective W := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ n
  have hsum : (∫ c, ∑ e : CliquePair n, CappedColor.charge (c e)
      ∂(sampledColorLaw W n : Measure (CliquePair n → CappedColor))) =
      (n.choose 2 : ℝ) * ∫ p, W.moment CappedColor.charge p ∂μ.prod μ :=
    integral_sampledColorLaw_sum W n ⟨CappedColor.charge, CappedColor.continuous_charge⟩
  unfold sampleCharge objective
  simp only [div_eq_mul_inv, integral_mul_const]
  rw [hsum, hcard]
  field_simp

end Erdos1017.CappedModel

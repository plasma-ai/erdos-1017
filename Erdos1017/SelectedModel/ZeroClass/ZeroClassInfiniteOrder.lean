module

public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteDensityRealization
public import Erdos1017.Models.Capped.CappedDensityRestoration
public import Erdos1017.Models.Capped.CappedRegularSelection

/-!
# Internal density below or equal to one

A normalized internal edge density strictly below one has an exact finite
multipartite realization with positive parts, while unit unhalved density forces
the conditional edge moment to be one almost everywhere and every sampled pair
to be the present color.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.MultipartiteDensityRealization

/-- Any normalized internal edge density strictly below one has an exact
finite multipartite realization. Positive density makes all chosen parts
positive, so every selected finite part pattern has positive label mass. -/
theorem exists_finite_part_masses_of_lt_one (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : Fin k → ℝ,
      (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧
        (∑ i, (a i) ^ 2) = 1 - q ∧ (0 < q → ∀ i, 0 < a i) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hq1)
  have hk : 0 < n + 1 := Nat.succ_pos n
  have hsmall : 1 / ((n + 1 : ℕ) : ℝ) < 1 - q := by
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  have hqk : q ≤ 1 - 1 / ((n + 1 : ℕ) : ℝ) := by linarith
  exact ⟨n + 1, hk, exists_part_masses (n + 1) hk q hq0 hqk⟩

end Erdos1017.MultipartiteDensityRealization

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Unit unhalved adjacency density forces the actual conditional edge
moment to be one almost everywhere. -/
theorem adjacency_ae_one_of_unhalved_density_one (W : Model Ω μ)
    (hq : 2 * density W = 1) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p = 1 := by
  have ha : Integrable (fun p => W.moment CappedColor.adjacency p) (μ.prod μ) :=
    integrable_bounded_moment W CappedColor.adjacency
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2)
  have hsub : Integrable (fun p => 1 - W.moment CappedColor.adjacency p) (μ.prod μ) :=
    (integrable_const 1).sub ha
  have hnonneg (p : Ω × Ω) : 0 ≤ 1 - W.moment CappedColor.adjacency p := by
    linarith [(adjacency_moment_mem W p).2]
  have hz : (∫ p, 1 - W.moment CappedColor.adjacency p ∂μ.prod μ) = 0 := by
    rw [integral_sub (integrable_const 1) ha, integral_const, probReal_univ]
    simp only [smul_eq_mul, one_mul]
    unfold density at hq
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hsub).mp hz
  filter_upwards [hae] with p hp
  simp only [Pi.zero_apply] at hp
  linarith

/-- If the old color charge is the common multiplier times adjacency,
unit internal density makes every sampled pair the actual present color. -/
theorem ae_present_of_unhalved_density_one (W : Model Ω μ)
    (hq : 2 * density W = 1) (m : ℝ) (hm : m ∈ Icc (-3) 1)
    (hcharge : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p,
      CappedColor.charge c = m * CappedColor.adjacency c) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p,
      c = CappedColor.present m hm := by
  filter_upwards [adjacency_ae_one_of_unhalved_density_one W hq, hcharge] with p hp hc
  filter_upwards [ae_adjacency_one_of_moment_one W p hp, hc] with c ha hy
  apply Subtype.ext
  apply Prod.ext
  · exact ha
  · change c.val.2 = m
    change c.val.2 = m * c.val.1 at hy
    change c.val.1 = 1 at ha
    simpa only [ha, mul_one] using hy

end Erdos1017.CappedModel

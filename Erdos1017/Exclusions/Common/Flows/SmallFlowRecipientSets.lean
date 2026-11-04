module

public import Erdos1017.SelectedModel.ZeroClass.AtomlessClassLabels
public import Erdos1017.SelectedModel.Flows.MissingFlowDensity

/-!
# Small positive recipient sets for a flow

A positive atomless set has positive measurable subsets of arbitrarily small
mass, the mass and the integral of an integrable density can be made small
together on such a subset, and an integrable product flow has small recipient
sets even with unbounded receipt.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- An actual positive atomless set has positive measurable subsets with
arbitrarily small original mass. The subsets are constructed by labels on
its actual conditioned law. -/
theorem exists_positive_subset_measureReal_lt (C₀ : Set Ω)
    (hC₀ : MeasurableSet C₀) (hpos : 0 < μ C₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ C ⊆ C₀, MeasurableSet C ∧ 0 < μ.real C ∧ μ.real C < ε := by
  let a := μ.real C₀
  have ha : 0 < a := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  let t := min (1 / 2 : ℝ) (ε / (2 * a))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let w : Fin 2 → ℝ := ![t, 1 - t]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · exact ht.le
    · exact sub_nonneg.mpr ht1
  have hsum : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_two]
  obtain ⟨L, hL, hmass⟩ := exists_atomless_class_labels_of_masses
    C₀ hC₀ hpos (by decide : 0 < 2) w hw hsum
  refine ⟨C₀ ∩ L ⁻¹' {0}, inter_subset_left,
    hC₀.inter (hL.measurable (measurableSet_singleton 0)), ?_, ?_⟩
  · rw [hmass]
    exact mul_pos ha ht
  · rw [hmass]
    change a * t < ε
    have hle : a * t ≤ ε / 2 := by
      have h := mul_le_mul_of_nonneg_left (min_le_right (1 / 2 : ℝ) (ε / (2 * a))) ha.le
      have he : a * (ε / (2 * a)) = ε / 2 := by field_simp
      exact h.trans_eq he
    linarith

/-- Original mass and the integral of any actual integrable density can
be made simultaneously small on a positive measurable subset. The density
need not be bounded or nonnegative. -/
theorem exists_positive_subset_mass_add_integral_lt (C₀ : Set Ω)
    (hC₀ : MeasurableSet C₀) (hpos : 0 < μ C₀)
    (f : Ω → ℝ) (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C ⊆ C₀, MeasurableSet C ∧ 0 < μ.real C ∧
      μ.real C + (∫ x in C, f x ∂μ) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf.2.ne
    (ENNReal.ofReal_ne_zero_iff.mpr (half_pos hε))
  let δ₁ := min δ 1
  have hδ₁ : 0 < δ₁ := lt_min hδ (by simp)
  have hfinite : δ₁ ≠ ∞ := ne_of_lt ((min_le_right δ 1).trans_lt (by simp))
  have hreal : 0 < δ₁.toReal := ENNReal.toReal_pos hδ₁.ne' hfinite
  obtain ⟨C, hCC, hC, hCpos, hCsmall⟩ := exists_positive_subset_measureReal_lt
    C₀ hC₀ hpos (min (ε / 2) δ₁.toReal) (lt_min (half_pos hε) hreal)
  have hμlt : μ C < δ₁ := (ENNReal.toReal_lt_toReal (measure_ne_top μ C) hfinite).mp
    (hCsmall.trans_le (min_le_right _ _))
  have hint : (∫⁻ x in C, ‖f x‖ₑ ∂μ) < ENNReal.ofReal (ε / 2) :=
    hsmall C (hμlt.trans_le (min_le_left _ _))
  have hnorm : ‖∫ x in C, f x ∂μ‖ < ε / 2 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mp
    rw [ofReal_norm]
    exact (enorm_integral_le_lintegral_enorm f).trans_lt hint
  refine ⟨C, hCC, hC, hCpos, ?_⟩
  have hmass : μ.real C < ε / 2 := hCsmall.trans_le (min_le_left _ _)
  rw [Real.norm_eq_abs] at hnorm
  have hle := le_abs_self (∫ x in C, f x ∂μ)
  linarith

/-- Small actual recipient sets for an arbitrary integrable product flow.
The receipt may be unbounded; its integrability follows from actual Fubini. -/
theorem exists_positive_small_flow_recipient (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C₀ : Set Ω)
    (hC₀ : MeasurableSet C₀) (hpos : 0 < μ C₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ C ⊆ C₀, MeasurableSet C ∧ 0 < μ.real C ∧
      μ.real C + (∫ x in C, MissingFlow.receipt μ q x ∂μ) < ε :=
  exists_positive_subset_mass_add_integral_lt C₀ hC₀ hpos (MissingFlow.receipt μ q)
    (MissingFlow.integrable_marginals hq).1 ε hε

end Erdos1017.CappedModel

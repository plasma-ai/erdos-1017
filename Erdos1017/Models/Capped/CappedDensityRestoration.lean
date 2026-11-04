module

public import Erdos1017.Models.Capped.CappedInsertionMoments
public import Erdos1017.Models.Capped.CappedWeightEdits
public import Erdos1017.Models.Capped.CappedTransport

/-!
# Density restoration and the three-Lipschitz comparison

Deletion and cost-four insertion restore any target density with objective loss
at most three times the density change, so capped maximality gives a
three-Lipschitz comparison at every competing density
(`objective_le_max_add_three_density`, `weight_lipschitz_max`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem adjacency_moment_mem (W : Model Ω μ) (p : Ω × Ω) :
    W.moment CappedColor.adjacency p ∈ Icc 0 1 :=
  W.moment_mem_Icc CappedColor.continuous_adjacency.measurable.stronglyMeasurable
    CappedColor.adjacency_mem p

theorem charge_le_adjacency (c : CappedColor) : CappedColor.charge c ≤ CappedColor.adjacency c := by
  change c.val.2 ≤ c.val.1
  rcases c.property with h | h
  · have h0 : c.val.1 = 0 := h.1
    have hy0 : c.val.2 = 0 := h.2
    rw [h0, hy0]
  · have h1 : c.val.1 = 1 := h.1
    rw [h1]
    exact h.2.2

theorem charge_moment_le_adjacency (W : Model Ω μ) (p : Ω × Ω) :
    W.moment CappedColor.charge p ≤ W.moment CappedColor.adjacency p := by
  have ha : Integrable CappedColor.adjacency (W.kernel p) :=
    Integrable.of_bound CappedColor.continuous_adjacency.measurable.stronglyMeasurable.aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2))
  have hy : Integrable CappedColor.charge (W.kernel p) :=
    Integrable.of_bound CappedColor.continuous_charge.measurable.stronglyMeasurable.aestronglyMeasurable
      3 (Filter.Eventually.of_forall (fun c => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
          (CappedColor.charge_mem c).2.trans (by norm_num)⟩))
  exact integral_mono hy ha charge_le_adjacency

variable [IsProbabilityMeasure μ]

theorem density_mem (W : Model Ω μ) : density W ∈ Icc 0 (1 / 2) := by
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  have hlo := integral_nonneg (μ := μ.prod μ) (fun p => (adjacency_moment_mem W p).1)
  have hhi := integral_mono ha (integrable_const 1) (fun p => (adjacency_moment_mem W p).2)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hhi
  constructor <;> unfold density <;> linarith

theorem objective_le_density (W : Model Ω μ) : objective W ≤ density W := by
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  have hy := integrable_bounded_moment W CappedColor.charge
    CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩)
  exact div_le_div_of_nonneg_right (integral_mono hy ha (charge_moment_le_adjacency W)) (by norm_num)

/-- Actual deletion and cost-four insertion restore any target density with
objective loss at most three times the density change. -/
theorem exists_density_restoration (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    ∃ V : Model Ω μ, Feasible r V ∧ density V = d ∧
      objective W - 3 * |density W - d| ≤ objective V := by
  by_cases hle : d ≤ density W
  · by_cases hz : density W = 0
    · have hd0 : d = 0 := le_antisymm (by simpa [hz] using hle) hd.1
      refine ⟨W, hW, hz.trans hd0.symm, ?_⟩
      simp [hz, hd0]
    · have hpos : 0 < density W := lt_of_le_of_ne (density_mem W).1 (Ne.symm hz)
      let t : unitInterval := ⟨(density W - d) / density W,
        div_nonneg (sub_nonneg.mpr hle) hpos.le,
        (div_le_one hpos).mpr (by linarith [hd.1])⟩
      have ht : (t : ℝ) * density W = density W - d := div_mul_cancel₀ _ hpos.ne'
      refine ⟨thin W t, feasible_thin W hW t, ?_, ?_⟩
      · rw [density_thin]
        nlinarith
      · rw [objective_thin, abs_of_nonneg (sub_nonneg.mpr hle)]
        have hc := mul_le_mul_of_nonneg_left (objective_le_density W) t.property.1
        nlinarith [sub_nonneg.mpr hle]
  · have hlt : density W < d := lt_of_not_ge hle
    have hroom : 0 < 1 / 2 - density W := by linarith [hd.2]
    let t : unitInterval := ⟨(d - density W) / (1 / 2 - density W),
      div_nonneg (sub_nonneg.mpr hlt.le) hroom.le,
      (div_le_one hroom).mpr (by linarith [hd.2])⟩
    have ht : (t : ℝ) * (1 / 2 - density W) = d - density W := div_mul_cancel₀ _ hroom.ne'
    refine ⟨sprinkle W t, feasible_sprinkle W hW t, ?_, ?_⟩
    · rw [density_sprinkle]
      linarith
    · rw [objective_sprinkle, abs_of_nonpos (sub_nonpos.mpr hlt.le)]
      linarith

/-- Actual capped maximality gives the three-Lipschitz comparison at every
competing density, by restoring that competitor to the maximizing density. -/
theorem objective_le_max_add_three_density (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hν : ν ≪ μ) (V : Model Ω ν) (hV : Feasible r V) :
    objective V ≤ objective W + 3 * |density V - density W| := by
  obtain ⟨U, hU, hd, hc⟩ := exists_density_restoration V hV (density W) (density_mem W)
  have hm := hW.2 ν hν U hU hd
  linarith

/-- The singular branch's actual local three-Lipschitz comparison follows
from capped maximality and the constructed feasible density restoration. -/
theorem weight_lipschitz_max (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    Variation.weightedPairIntegral (fun x y => W.moment CappedColor.charge (x, y))
        (Variation.vertexWeight f) -
      Variation.weightedPairIntegral (fun x y => W.moment CappedColor.charge (x, y))
        (Lp.const 2 μ (1 : ℝ)) ≤
      3 * |Variation.weightedPairIntegral (fun x y => W.moment CappedColor.adjacency (x, y))
          (Variation.vertexWeight f) -
        Variation.weightedPairIntegral (fun x y => W.moment CappedColor.adjacency (x, y))
          (Lp.const 2 μ (1 : ℝ))| := by
  have := weightedMeasure_probability ((Lp.memLp (Variation.vertexWeight f)).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative f hf) (Variation.vertexWeight_integral f)
  have he := objective_le_max_add_three_density W hW
    (weightedMeasure (μ := μ) (Variation.vertexWeight f)) (withDensity_absolutelyContinuous _ _)
    (reweight W f hf) (feasible_reweight W hW.1 f hf)
  have hd : density W = Variation.weightedPairIntegral
      (fun x y => W.moment CappedColor.adjacency (x, y)) (Lp.const 2 μ (1 : ℝ)) / 2 := by
    rw [weightedPairIntegral_one]
    rfl
  have hc : objective W = Variation.weightedPairIntegral
      (fun x y => W.moment CappedColor.charge (x, y)) (Lp.const 2 μ (1 : ℝ)) / 2 := by
    rw [weightedPairIntegral_one]
    rfl
  rw [objective_reweight W f hf, density_reweight W f hf, hd, hc, ← sub_div, abs_div] at he
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at he
  linarith

/-- On the canonical atomless standard-Borel presentation, the same actual
comparison needs only fixed-measure capped maximality. -/
theorem weight_lipschitz_max_of_fixed [StandardBorelSpace Ω] [NullSingletonClass μ]
    (W : Model Ω μ) {r : ℕ} (hW : IsFixedMeasureMaximizer r W)
    (f : Variation.WeightDirections μ) (hf : ‖f‖ < 1) :
    Variation.weightedPairIntegral (fun x y => W.moment CappedColor.charge (x, y))
        (Variation.vertexWeight f) -
      Variation.weightedPairIntegral (fun x y => W.moment CappedColor.charge (x, y))
        (Lp.const 2 μ (1 : ℝ)) ≤
      3 * |Variation.weightedPairIntegral (fun x y => W.moment CappedColor.adjacency (x, y))
          (Variation.vertexWeight f) -
        Variation.weightedPairIntegral (fun x y => W.moment CappedColor.adjacency (x, y))
          (Lp.const 2 μ (1 : ℝ))| :=
  weight_lipschitz_max W (isMaximizer_of_isFixedMeasureMaximizer W hW) f hf

end Erdos1017.CappedModel

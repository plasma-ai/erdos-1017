module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpMultipartiteCountCells
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassMasses

/-!
# Sharp count-cell bounds for the multipartite objective

Both sharp count-cell formulas refer to the same anchor, current law, density
and nonnegative atomic tail-square quantity, countable class coding preserves
them, and a positive largest part of mass at most one third has both sharp
small-part bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.MultipartiteModelValue

open MultipartiteComponentRealization CappedModel

local instance sharpCellLabelMeasurable : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Both sharp count-cell formulas refer to the same actual anchor,
current law, density and nonnegative atomic tail-square quantity. -/
theorem objective_sharp_countCells (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Label) (hq : Measurable q) (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0) :
    let A := anchor (μ := μ) q
    let T := (1 - A) / A
    let σ := 1 - 2 * density W - A ^ 2
    0 ≤ σ ∧
      (T ∈ Icc (2 : ℝ) 3 → objective W ≤ A ^ 2 * (6 * T - T ^ 2) / 12 + σ / 3) ∧
      (3 ≤ T → objective W ≤ A ^ 2 * T / 4 + σ / T) := by
  let a := anchor (μ := μ) q
  let T := dust (μ := μ) q + ∑' i, heads (μ := μ) q i
  let Q := ∑' i, (heads (μ := μ) q i) ^ 2
  have hnorm : 1 + T = 1 / a := by
    simpa only [T, add_assoc] using normalized_mass q hq ha
  have hmult : a * (1 + T) = 1 := by rw [hnorm, mul_one_div, div_self ha.ne']
  have hsquare : a ^ 2 * (1 + T) ^ 2 = 1 := by rw [← mul_pow, hmult]; norm_num
  have hdensity : density W = a ^ 2 * (T + (T ^ 2 - Q) / 2) :=
    density_eq_own_profile W q hq ha hmax hsupport
  have htail : a ^ 2 * Q = 1 - 2 * density W - a ^ 2 := by nlinarith
  have hT : T = (1 - a) / a := (eq_div_iff ha.ne').mpr (by nlinarith [hmult])
  change 0 ≤ 1 - 2 * density W - a ^ 2 ∧
    ((1 - a) / a ∈ Icc (2 : ℝ) 3 → objective W ≤
      a ^ 2 * (6 * ((1 - a) / a) - ((1 - a) / a) ^ 2) / 12 +
        (1 - 2 * density W - a ^ 2) / 3) ∧
    (3 ≤ (1 - a) / a → objective W ≤ a ^ 2 * ((1 - a) / a) / 4 +
      (1 - 2 * density W - a ^ 2) / ((1 - a) / a))
  rw [← hT, ← htail]
  have hQ : 0 ≤ Q := tsum_nonneg (fun _ => sq_nonneg _)
  have hvalue := objective_le_own_value W hW q hq ha hmax hsupport
  refine ⟨mul_nonneg (sq_nonneg _) hQ, ?_, ?_⟩
  · intro hmiddle
    have hb := MultipartiteCountableDual.value_le_middle_countCell (heads (μ := μ) q)
      (heads_cube q ha hmax) (heads_summable q hq) (dust (μ := μ) q) (dust_nonneg q ha.le)
      (by simpa only [T, add_comm] using hmiddle)
    have hscaled := mul_le_mul_of_nonneg_left hb (sq_nonneg a)
    change a ^ 2 * MultipartiteCountableDual.value (heads (μ := μ) q) (dust (μ := μ) q) ≤
      a ^ 2 * ((6 * ((∑' i, heads (μ := μ) q i) + dust (μ := μ) q) -
        ((∑' i, heads (μ := μ) q i) + dust (μ := μ) q) ^ 2) / 12 + Q / 3) at hscaled
    have he : (∑' i, heads (μ := μ) q i) + dust (μ := μ) q = T := by dsimp [T]; ring
    rw [he] at hscaled
    nlinarith
  · intro hlarge
    have hb := MultipartiteCountableDual.value_le_large_countCell (heads (μ := μ) q)
      (heads_cube q ha hmax) (heads_summable q hq) (dust (μ := μ) q) (dust_nonneg q ha.le)
      (by simpa only [T, add_comm] using hlarge)
    have hscaled := mul_le_mul_of_nonneg_left hb (sq_nonneg a)
    have he : (∑' i, heads (μ := μ) q i) + dust (μ := μ) q = T := by dsimp [T]; ring
    rw [he] at hscaled
    calc
      objective W ≤ a ^ 2 * (T / 4 + Q / T) := hvalue.trans hscaled
      _ = _ := by ring

end Erdos1017.MultipartiteModelValue

namespace Erdos1017.MultipartiteClassMasses

open CappedModel MultipartiteComponentRealization

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

local instance sharpCellOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance sharpCellLabelMeasurable : MeasurableSpace Label := ⊤
local instance sharpCellDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Actual countable class coding preserves both sharp formulas and the
literal tail-square value at the specified original class. -/
theorem objective_sharp_countCells (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i : ι) (hpos : 0 < classMass μ q i) (hmax : ∀ j, classMass μ q j ≤ classMass μ q i) :
    let A := classMass μ q i
    let T := (1 - A) / A
    let σ := 1 - 2 * density W - A ^ 2
    0 ≤ σ ∧
      (T ∈ Icc (2 : ℝ) 3 → objective W ≤ A ^ 2 * (6 * T - T ^ 2) / 12 + σ / 3) ∧
      (3 ≤ T → objective W ≤ A ^ 2 * T / 4 + σ / T) := by
  obtain ⟨q', hq', hanchor, _, ha, hmax', hrel, _⟩ :=
    MultipartiteClassCoding.exists_anchored_coding q hq i hpos hmax
  have hs : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q' p.1 ≠ q' p.2 ∨ q' p.1 = .inr () then 1 else 0 := by
    filter_upwards [hsupport] with p hp
    by_cases he : q p.1 ≠ q p.2 ∨ q p.1 = none
    · have he' := (hrel p.1 p.2).mpr he
      simpa only [he, he', ite_true] using hp
    · have he' : ¬(q' p.1 ≠ q' p.2 ∨ q' p.1 = .inr ()) :=
        fun h => he ((hrel p.1 p.2).mp h)
      simpa only [he, he', ite_false] using hp
  have hb := MultipartiteModelValue.objective_sharp_countCells W hW q' hq' ha hmax' hs
  simpa only [anchor, mass, hanchor, classMass] using hb

/-- Every actual positive largest part of mass at most one third has
both sharp small-part bounds, without a physical-cost hypothesis. -/
theorem objective_le_sharp_smallPart (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i : ι) (hpos : 0 < classMass μ q i) (ha : classMass μ q i ≤ 1 / 3)
    (hmax : ∀ j, classMass μ q j ≤ classMass μ q i) :
    objective W ≤ min (1 / 9) ((1 - 2 * density W) / 3 + 1 / 27) := by
  let a := classMass μ q i
  let T := (1 - a) / a
  let σ := 1 - 2 * density W - a ^ 2
  have hbounds := objective_sharp_countCells W hW q hq hsupport i hpos hmax
  change 0 ≤ σ ∧ (T ∈ Icc (2 : ℝ) 3 → objective W ≤ a ^ 2 * (6 * T - T ^ 2) / 12 + σ / 3) ∧
    (3 ≤ T → objective W ≤ a ^ 2 * T / 4 + σ / T) at hbounds
  have hT : 2 ≤ T := (le_div_iff₀ hpos).mpr (by dsimp [a]; linarith)
  have hnormalize : a ^ 2 * (1 + T) ^ 2 = 1 := by
    have ha0 : a ≠ 0 := hpos.ne'
    dsimp [T]
    field_simp
    ring
  have hcost := objective_le_class_bound_sq W hW q hq hsupport a hmax
  refine le_min ?_ ?_
  · have hsq : a ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by gcongr
    nlinarith
  · by_cases hmid : T ≤ 3
    · have hb := hbounds.2.1 ⟨hT, hmid⟩
      have hscalar : (6 * T - T ^ 2) / 12 ≤ 1 / 3 + (1 + T) ^ 2 / 27 := by
        have hp := mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ 13 * T - 20 by linarith)
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hscalar (sq_nonneg a)
      dsimp only [σ] at hb
      nlinarith
    · have hlarge : 3 ≤ T := (lt_of_not_ge hmid).le
      have hb := hbounds.2.2 hlarge
      have hdiv : σ / T ≤ σ / 3 := div_le_div_of_nonneg_left hbounds.1 (by norm_num) hlarge
      have hscalar : T / 4 ≤ 1 / 3 + (1 + T) ^ 2 / 27 := by
        nlinarith [sq_nonneg (8 * T - 19)]
      have hscaled := mul_le_mul_of_nonneg_left hscalar (sq_nonneg a)
      dsimp only [σ] at hb hdiv
      nlinarith

end Erdos1017.MultipartiteClassMasses

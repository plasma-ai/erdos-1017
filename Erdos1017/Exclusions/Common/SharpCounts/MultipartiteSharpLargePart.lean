module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpMultipartiteSmallTotal
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassMasses

/-!
# Sharp large-part bound for the multipartite objective

A largest anchor of mass at least one third has total tail load at most two, so
the sharp selector theorem bounds the objective, and anchored coding transfers
this bound to the specified largest class with the same current law and density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.MultipartiteModelValue

open MultipartiteComponentRealization CappedModel

local instance sharpLabelMeasurable : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- An actual largest anchor of mass at least one third has total tail
load at most two, so the sharp selector theorem bounds its actual objective. -/
theorem objective_le_third_missing_add_anchor_sq (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Label) (hq : Measurable q) (ha : 1 / 3 ≤ anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0) :
    objective W ≤ (1 - 2 * density W + (anchor (μ := μ) q) ^ 2) / 3 := by
  let a := anchor (μ := μ) q
  have ha0 : 0 < a := by dsimp [a]; linarith
  let T := dust (μ := μ) q + ∑' i, heads (μ := μ) q i
  let Q := ∑' i, (heads (μ := μ) q i) ^ 2
  have hnorm : 1 + T = 1 / a := by
    simpa only [T, add_assoc] using normalized_mass q hq ha0
  have htotal : (∑' i, heads (μ := μ) q i) + dust (μ := μ) q ≤ 2 := by
    have hinv : 1 / a ≤ 3 := (div_le_iff₀ ha0).mpr (by dsimp [a]; linarith)
    dsimp only [T] at hnorm
    linarith
  have hmult : a * (1 + T) = 1 := by rw [hnorm, mul_one_div, div_self ha0.ne']
  have hsquare : a ^ 2 * (1 + T) ^ 2 = 1 := by rw [← mul_pow, hmult]; norm_num
  have hdensity : density W = a ^ 2 * (T + (T ^ 2 - Q) / 2) :=
    density_eq_own_profile W q hq ha0 hmax hsupport
  have htail : a ^ 2 * Q = 1 - 2 * density W - a ^ 2 := by nlinarith
  have hselector := MultipartiteCountableDual.value_le_sumTwo (heads (μ := μ) q)
    (heads_cube q ha0 hmax) (heads_summable q hq) (dust (μ := μ) q)
    (dust_nonneg q ha0.le) htotal
  have hscaled := mul_le_mul_of_nonneg_left hselector (sq_nonneg a)
  have hvalue := objective_le_own_value W hW q hq ha0 hmax hsupport
  change a ^ 2 * MultipartiteCountableDual.value (heads (μ := μ) q) (dust (μ := μ) q) ≤
    a ^ 2 * ((2 + Q) / 3) at hscaled
  change objective W ≤ (1 - 2 * density W + a ^ 2) / 3
  nlinarith

end Erdos1017.MultipartiteModelValue

namespace Erdos1017.MultipartiteClassMasses

open CappedModel MultipartiteComponentRealization

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

local instance sharpOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance sharpLabelMeasurable : MeasurableSpace Label := ⊤
local instance sharpDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Actual anchored coding transfers the sharp bound at the specified
largest class, with the same current probability law and actual density. -/
theorem objective_le_sharp_largePart (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i : ι) (ha : 1 / 3 ≤ classMass μ q i) (hmax : ∀ j, classMass μ q j ≤ classMass μ q i) :
    objective W ≤ min ((classMass μ q i) ^ 2)
      ((1 - 2 * density W + (classMass μ q i) ^ 2) / 3) := by
  have hpos : 0 < classMass μ q i := by linarith
  obtain ⟨q', hq', hanchor, _, ha', hmax', hrel, _⟩ :=
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
  have hlarge : 1 / 3 ≤ anchor (μ := μ) q' := by
    simpa only [anchor, mass, hanchor, classMass] using ha
  have hb := MultipartiteModelValue.objective_le_third_missing_add_anchor_sq
    W hW q' hq' hlarge hmax' hs
  refine le_min (objective_le_class_bound_sq W hW q hq hsupport (classMass μ q i) hmax) ?_
  simpa only [anchor, mass, hanchor, classMass] using hb

end Erdos1017.MultipartiteClassMasses

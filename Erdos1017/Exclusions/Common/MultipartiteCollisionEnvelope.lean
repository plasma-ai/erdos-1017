module

public import Erdos1017.Exclusions.Common.CountableCollisionEnvelope
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassMasses

/-!
# Collision envelope for countable partitions

An anchored countable model obeys the selector collision bound with its
tail-square quantity recovered from its density, and any countable partition
with a specified positive largest class has the collision envelope at that class
mass and density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.MultipartiteModelValue

open MultipartiteComponentRealization CappedModel

local instance collisionLabelMeasurable : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- The actual anchored countable model obeys the selector collision
bound, with its own tail-square quantity recovered from its actual density. -/
theorem objective_le_split_add_missing_tail (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Label) (hq : Measurable q) (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0) :
    objective W ≤ Benchmark.splitValue (anchor (μ := μ) q) +
      (1 - 2 * density W - (anchor (μ := μ) q) ^ 2) / 2 := by
  let a := anchor (μ := μ) q
  let T := dust (μ := μ) q + ∑' i, heads (μ := μ) q i
  let Q := ∑' i, (heads (μ := μ) q i) ^ 2
  have hnorm : 1 + T = 1 / a := by
    simpa only [T, add_assoc] using normalized_mass q hq ha
  have hmult : a * (1 + T) = 1 := by rw [hnorm, mul_one_div, div_self ha.ne']
  have hdensity : density W = a ^ 2 * (T + (T ^ 2 - Q) / 2) :=
    density_eq_own_profile W q hq ha hmax hsupport
  have hsquare : a ^ 2 * (1 + T) ^ 2 = 1 := by rw [← mul_pow, hmult]; norm_num
  have htail : a ^ 2 * Q = 1 - 2 * density W - a ^ 2 := by nlinarith
  have hcollision := MultipartiteCountableDual.value_le_split_add_square
    (heads (μ := μ) q) (heads_cube q ha hmax) (heads_summable q hq)
    (dust (μ := μ) q) (dust_nonneg q ha.le)
  have hM : 1 + (∑' i, heads (μ := μ) q i) + dust (μ := μ) q = 1 / a := by
    dsimp only [T] at hnorm
    linarith
  rw [hM] at hcollision
  have hscaled := mul_le_mul_of_nonneg_left hcollision (sq_nonneg a)
  have hvalue := objective_le_own_value W hW q hq ha hmax hsupport
  have hnormalize : a ^ 2 * ((1 / a) ^ 2 * Benchmark.splitValue (1 / (1 / a)) + Q / 2) =
      Benchmark.splitValue a + (a ^ 2 * Q) / 2 := by
    rw [one_div_one_div]
    have ha' : a ≠ 0 := ha.ne'
    field_simp
  change a ^ 2 * MultipartiteCountableDual.value (heads (μ := μ) q) (dust (μ := μ) q) ≤
    a ^ 2 * ((1 / a) ^ 2 * Benchmark.splitValue (1 / (1 / a)) + Q / 2) at hscaled
  rw [hnormalize, htail] at hscaled
  exact hvalue.trans hscaled

end Erdos1017.MultipartiteModelValue

namespace Erdos1017.MultipartiteClassMasses

open CappedModel MultipartiteComponentRealization

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

local instance collisionOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance collisionLabelMeasurable : MeasurableSpace Label := ⊤
local instance collisionDecidableEq : DecidableEq ι := Classical.decEq ι

/-- An arbitrary actual countable partition with a specified positive
largest class has the collision envelope at that same class mass and density. -/
theorem objective_le_split_add_tail (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i : ι) (hpos : 0 < classMass μ q i) (hmax : ∀ j, classMass μ q j ≤ classMass μ q i) :
    objective W ≤ Benchmark.splitValue (classMass μ q i) +
      (1 - 2 * density W - (classMass μ q i) ^ 2) / 2 := by
  obtain ⟨q', hq', hanchor, _, ha, hmax', hrel, _⟩ :=
    MultipartiteClassCoding.exists_anchored_coding q hq i hpos hmax
  have hs : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q' p.1 ≠ q' p.2 ∨ q' p.1 = .inr () then 1 else 0 := by
    filter_upwards [hsupport] with p hp
    by_cases he : q p.1 ≠ q p.2 ∨ q p.1 = none
    · have he' := (hrel p.1 p.2).mpr he
      simpa only [he, he', ↓reduceIte] using hp
    · have he' : ¬(q' p.1 ≠ q' p.2 ∨ q' p.1 = .inr ()) :=
        fun h => he ((hrel p.1 p.2).mp h)
      simpa only [he, he', ↓reduceIte] using hp
  have hb := MultipartiteModelValue.objective_le_split_add_missing_tail W hW q' hq' ha hmax' hs
  simpa only [anchor, mass, hanchor, classMass] using hb

end Erdos1017.MultipartiteClassMasses

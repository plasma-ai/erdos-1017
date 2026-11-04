module

public import Erdos1017.Exclusions.E2.Middle.SharpMultipartiteLowerCountCell
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassMasses

/-!
# Lower count cell for multipartite models

For a physical multipartite model whose largest part has mass `A ∈ [1/3, 2/5]`,
the two-fifths lower count cell gives
`objective ≤ A² g₂((1 - A)/A) + (2/5)(1 - 2·density - A²)`, in finite and
countable form (`objective_le_lower_countCell`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.MultipartiteModelValue

open MultipartiteComponentRealization CappedModel

local instance lowerCellLabelMeasurable : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- The two-fifths lower count-cell price for an actual physical
multipartite model whose anchor is a largest part of mass in `[1/3, 2/5]`.
The tail square is the literal `1 - 2·density - A²` of the same model. -/
theorem objective_le_lower_countCell (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Label) (hq : Measurable q) (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0)
    (hlo : 1 / 3 ≤ anchor (μ := μ) q) (hhi : anchor (μ := μ) q ≤ 2 / 5) :
    objective W ≤ (anchor (μ := μ) q) ^ 2 *
        ((4 * ((1 - anchor (μ := μ) q) / anchor (μ := μ) q) -
          ((1 - anchor (μ := μ) q) / anchor (μ := μ) q) ^ 2) / 6) +
      2 / 5 * (1 - 2 * density W - (anchor (μ := μ) q) ^ 2) := by
  let a := anchor (μ := μ) q
  let T := dust (μ := μ) q + ∑' i, heads (μ := μ) q i
  let Q := ∑' i, (heads (μ := μ) q i) ^ 2
  have hnorm : 1 + T = 1 / a := by
    simpa only [T, add_assoc] using normalized_mass q hq ha
  have hmult : a * (1 + T) = 1 := by rw [hnorm, mul_one_div, div_self ha.ne']
  have hdensity : density W = a ^ 2 * (T + (T ^ 2 - Q) / 2) :=
    density_eq_own_profile W q hq ha hmax hsupport
  have htail : a ^ 2 * Q = 1 - 2 * density W - a ^ 2 := by nlinarith
  have hT : T = (1 - a) / a := (eq_div_iff ha.ne').mpr (by nlinarith [hmult])
  change objective W ≤ a ^ 2 * ((4 * ((1 - a) / a) - ((1 - a) / a) ^ 2) / 6) +
    2 / 5 * (1 - 2 * density W - a ^ 2)
  rw [← hT, ← htail]
  have hTcell : T ∈ Icc (3 / 2 : ℝ) 2 := by
    rw [hT]
    constructor
    · exact (le_div_iff₀ ha).mpr (by dsimp [a]; linarith)
    · exact (div_le_iff₀ ha).mpr (by dsimp [a]; linarith)
  have hvalue := objective_le_own_value W hW q hq ha hmax hsupport
  have hb := MultipartiteCountableDual.value_le_lower_countCell (heads (μ := μ) q)
    (heads_cube q ha hmax) (heads_summable q hq) (dust (μ := μ) q) (dust_nonneg q ha.le)
    (by simpa only [T, add_comm] using hTcell)
  have he : (∑' i, heads (μ := μ) q i) + dust (μ := μ) q = T := by dsimp [T]; ring
  rw [he] at hb
  have hscaled := mul_le_mul_of_nonneg_left hb (sq_nonneg a)
  calc
    objective W ≤ a ^ 2 * MultipartiteCountableDual.value (heads (μ := μ) q)
        (dust (μ := μ) q) := hvalue
    _ ≤ a ^ 2 * ((4 * T - T ^ 2) / 6 + 2 / 5 * Q) := hscaled
    _ = _ := by ring

end Erdos1017.MultipartiteModelValue

namespace Erdos1017.MultipartiteClassMasses

open CappedModel MultipartiteComponentRealization

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

local instance lowerCellOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance lowerCellLabelMeasurable : MeasurableSpace Label := ⊤
local instance lowerCellDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Actual countable class coding: a largest class of mass `A ∈ [1/3, 2/5]`
gives `objective ≤ A² g₂((1 - A)/A) + (2/5)(1 - 2·density - A²)`. -/
theorem objective_le_lower_countCell (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i : ι) (hmax : ∀ j, classMass μ q j ≤ classMass μ q i)
    (hlo : 1 / 3 ≤ classMass μ q i) (hhi : classMass μ q i ≤ 2 / 5) :
    objective W ≤ (classMass μ q i) ^ 2 *
        ((4 * ((1 - classMass μ q i) / classMass μ q i) -
          ((1 - classMass μ q i) / classMass μ q i) ^ 2) / 6) +
      2 / 5 * (1 - 2 * density W - (classMass μ q i) ^ 2) := by
  have hpos : 0 < classMass μ q i := by linarith
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
  have hA : anchor (μ := μ) q' = classMass μ q i := by
    simp only [anchor, mass, classMass]
    rw [hanchor]
  have hb := MultipartiteModelValue.objective_le_lower_countCell W hW q' hq' ha hmax' hs
    (hA ▸ hlo) (hA ▸ hhi)
  rwa [hA] at hb

end Erdos1017.MultipartiteClassMasses

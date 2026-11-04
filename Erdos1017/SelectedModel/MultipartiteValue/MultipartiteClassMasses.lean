module

public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassCoding

/-!
# Masses of the original independent classes

`classMass` is the mass of an original independent class, with `none` for clique
dust; multipartite adjacency gives the missing density as the sum of squared
class masses, and the objective is bounded by the square of the largest class
(`objective_le_largest_class_sq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Function

namespace Erdos1017.MultipartiteClassMasses

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

local instance classMassOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance classMassDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The mass of an original independent class; none remains clique dust. -/
def classMass (μ : Measure Ω) (q : Ω → Option ι) (i : ι) : ℝ :=
  μ.real (q ⁻¹' {some i})

omit [Countable ι] in
theorem classMass_nonneg (μ : Measure Ω) (q : Ω → Option ι) (i : ι) :
    0 ≤ classMass μ q i := ENNReal.toReal_nonneg

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Countable ι] in
theorem classMass_le_one (q : Ω → Option ι) (i : ι) : classMass μ q i ≤ 1 :=
  measureReal_le_one

theorem classMass_summable (q : Ω → Option ι) (hq : Measurable q) :
    Summable (classMass μ q) := MultipartiteClassCoding.class_masses_summable q hq

/-- The entire original independent-class mass is the actual mass of the
countable union of its disjoint physical class fibers. -/
theorem tsum_classMass (q : Ω → Option ι) (hq : Measurable q) :
    ∑' i, classMass μ q i = μ.real (⋃ i, q ⁻¹' {some i}) := by
  rw [measureReal_def, measure_iUnion (fun i j hij =>
    Set.disjoint_left.mpr (fun x hx hy => hij (Option.some_injective _ (hx.symm.trans hy))))
    (fun i => hq (measurableSet_singleton (some i))),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  rfl

theorem tsum_classMass_le_one (q : Ω → Option ι) (hq : Measurable q) :
    ∑' i, classMass μ q i ≤ 1 := by
  rw [tsum_classMass q hq]
  exact measureReal_le_one

theorem classMass_sq_summable (q : Ω → Option ι) (hq : Measurable q) :
    Summable (fun i => (classMass μ q i) ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => by
    nlinarith [mul_nonneg (classMass_nonneg μ q i) (sub_nonneg.mpr (classMass_le_one (μ := μ) q i))])
    (classMass_summable q hq)

/-- Missing pairs lie in a common independent class. Clique dust contributes
no missing pairs, including its diagonal. -/
def independentPairs (q : Ω → Option ι) : Set (Ω × Ω) :=
  ⋃ i, (q ⁻¹' {some i}) ×ˢ (q ⁻¹' {some i})

omit [IsProbabilityMeasure μ] in
theorem independentPairs_measurable (q : Ω → Option ι) (hq : Measurable q) :
    MeasurableSet (independentPairs q) :=
  MeasurableSet.iUnion (fun i => (hq (measurableSet_singleton (some i))).prod
    (hq (measurableSet_singleton (some i))))

omit [Countable ι] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem mem_independentPairs_iff (q : Ω → Option ι) (p : Ω × Ω) :
    p ∈ independentPairs q ↔ ¬ (q p.1 ≠ q p.2 ∨ q p.1 = none) := by
  classical
  simp only [independentPairs, mem_iUnion, mem_prod, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨i, hx, hy⟩
    rw [hx, hy]
    simp
  · intro hp
    have heq : q p.1 = q p.2 := by tauto
    cases hx : q p.1 with
    | none => exact False.elim (hp (Or.inr hx))
    | some i => exact ⟨i, rfl, heq.symm.trans hx⟩

/-- The actual missing-pair measure is exactly the sum of the squares of
the original independent-class masses. -/
theorem independentPairs_mass (q : Ω → Option ι) (hq : Measurable q) :
    (μ.prod μ).real (independentPairs q) = ∑' i, (classMass μ q i) ^ 2 := by
  have hdisjoint : Pairwise (Disjoint on fun i : ι =>
      (q ⁻¹' {some i}) ×ˢ (q ⁻¹' {some i})) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hp hq =>
      hij (Option.some_injective _ (hp.1.symm.trans hq.1)))
  rw [measureReal_def, independentPairs, measure_iUnion hdisjoint (fun i =>
    (hq (measurableSet_singleton (some i))).prod (hq (measurableSet_singleton (some i)))),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  apply tsum_congr
  intro i
  rw [← measureReal_def, measureReal_prod_prod]
  simp only [classMass, pow_two]

open CappedModel

/-- Original multipartite adjacency determines the exact missing density
from its own actual countable independent classes, without any anchor choice. -/
theorem one_sub_two_density_eq_tsum_classMass_sq (W : Model Ω μ)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0) :
    1 - 2 * density W = ∑' i, (classMass μ q i) ^ 2 := by
  classical
  have hmissing := independentPairs_measurable q hq
  have hA : W.moment CappedColor.adjacency =ᵐ[μ.prod μ]
      (fun p => 1 - (independentPairs q).indicator (fun _ => (1 : ℝ)) p) := by
    filter_upwards [hsupport] with p hp
    rw [hp]
    by_cases he : q p.1 ≠ q p.2 ∨ q p.1 = none
    · have hm : p ∉ independentPairs q := fun h => (mem_independentPairs_iff q p).mp h he
      simp only [he, ↓reduceIte, indicator_of_notMem hm, sub_zero]
    · have hm : p ∈ independentPairs q := (mem_independentPairs_iff q p).mpr he
      simp only [he, ↓reduceIte, indicator_of_mem hm, sub_self]
  rw [density, integral_congr_ae hA,
    integral_sub (integrable_const 1) ((integrable_const (1 : ℝ)).indicator hmissing),
    integral_indicator hmissing, setIntegral_const, smul_eq_mul, mul_one,
    independentPairs_mass q hq]
  simp
  ring

omit [IsProbabilityMeasure μ] in
/-- Actual integrals over the disjoint original classes form an absolutely
summable family and sum to the integral over their original union. -/
theorem hasSum_integral_classes (q : Ω → Option ι) (hq : Measurable q)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    HasSum (fun i => ∫ x in q ⁻¹' {some i}, f x ∂μ)
      (∫ x in ⋃ i, q ⁻¹' {some i}, f x ∂μ) :=
  hasSum_integral_iUnion (fun i => hq (measurableSet_singleton (some i)))
    (fun _ _ hij => Set.disjoint_left.mpr (fun _ hx hy =>
      hij (Option.some_injective _ (hx.symm.trans hy)))) hf.restrict

/-- A positive original independent class yields an actual attained
largest class mass, without a finiteness or anchor hypothesis. -/
theorem exists_largest_class (q : Ω → Option ι) (hq : Measurable q)
    (hpos : ∃ i, 0 < classMass μ q i) :
    ∃ i₀, 0 < classMass μ q i₀ ∧ ∀ i, classMass μ q i ≤ classMass μ q i₀ :=
  MultipartiteClassCoding.exists_largest_class q hq hpos

/-- Null independent-class masses give the actual pure-dust objective bound. -/
theorem objective_le_zero_of_null_classMass (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (hnull : ∀ i, classMass μ q i = 0) : objective W ≤ 0 := by
  apply MultipartiteClassCoding.objective_le_zero_of_null_classes W hW q hsupport
  intro i
  exact (measureReal_eq_zero_iff (measure_ne_top μ (q ⁻¹' {some i}))).mp (hnull i)

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- Every actual bound on all original independent-class masses gives the
corresponding square objective bound, including the pure-dust case. -/
theorem objective_le_class_bound_sq (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (M : ℝ) (hM : ∀ i, classMass μ q i ≤ M) : objective W ≤ M ^ 2 := by
  classical
  by_cases hpos : ∃ i, 0 < classMass μ q i
  · obtain ⟨i₀, q', _, _, _, _, _, _, _, _, _, hbound⟩ :=
      MultipartiteClassCoding.exists_own_value_bound W hW q hq hsupport hpos
    exact hbound.trans (pow_le_pow_left₀ (classMass_nonneg μ q i₀) (hM i₀) 2)
  · have hnull : ∀ i, classMass μ q i = 0 := fun i =>
      le_antisymm (le_of_not_gt (fun hi => hpos ⟨i, hi⟩)) (classMass_nonneg μ q i)
    exact (objective_le_zero_of_null_classMass W hW q hsupport hnull).trans (sq_nonneg M)

/-- The actual objective is bounded by the square of an actually largest
original class, even when that largest mass is zero. -/
theorem objective_le_largest_class_sq (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i₀ : ι) (hmax : ∀ i, classMass μ q i ≤ classMass μ q i₀) :
    objective W ≤ (classMass μ q i₀) ^ 2 :=
  objective_le_class_bound_sq W hW q hq hsupport _ hmax

end Erdos1017.MultipartiteClassMasses

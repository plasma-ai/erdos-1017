module

public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteModelValue

/-!
# Coding countable independent classes

Independent class masses are summable, a positive class yields a largest one,
and coding the original fibers onto natural-number labels gives a largest-part
anchored profile with its own-value bound; if every class is null the model is
pure clique dust with nonpositive objective.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.MultipartiteClassCoding

open MultipartiteComponentRealization

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

local instance classCodingOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance classCodingLabelMeasurable : MeasurableSpace Label := ⊤
local instance classCodingDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Keep the actual dust label, choose one actual independent anchor, and
encode every other independent class without merging any classes. -/
def code (e : ι ↪ ℕ) (i₀ : ι) : Option ι → Label := by
  classical
  exact fun
    | none => .inr ()
    | some i => if i = i₀ then .inl none else .inl (some (e i))

omit [Countable ι] [MeasurableSpace Ω] in
theorem code_injective (e : ι ↪ ℕ) (i₀ : ι) : Function.Injective (code e i₀) := by
  classical
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some j => simp only [code] at h; split_ifs at h
  | some i =>
    cases y with
    | none => simp only [code] at h; split_ifs at h
    | some j =>
      simp only [code] at h
      split_ifs at h with hi hj hj
      · exact congrArg some (hi.trans hj.symm)
      · cases h
      · cases h
      · exact congrArg some (e.injective (by simpa using h))

omit [Countable ι] [MeasurableSpace Ω] in
theorem code_eq_dust_iff (e : ι ↪ ℕ) (i₀ : ι) (j : Option ι) :
    code e i₀ j = .inr () ↔ j = none := by
  cases j with
  | none => simp [code]
  | some i => simp only [code]; split_ifs <;> simp

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual independent class masses form a summable family even before
choosing any enumeration or anchor. -/
theorem class_masses_summable (q : Ω → Option ι) (hq : Measurable q) :
    Summable (fun i => μ.real (q ⁻¹' {some i})) := by
  apply ENNReal.summable_toReal
  rw [← measure_iUnion (fun i j hij => Set.disjoint_left.mpr (fun x hx hy =>
    hij (Option.some_injective _ (hx.symm.trans hy))))
    (fun i => hq (measurableSet_singleton (some i)))]
  exact measure_ne_top _ _

/-- If an actual independent class has positive mass, an actual class of
largest positive mass exists. This is derived from summability. -/
theorem exists_largest_class (q : Ω → Option ι) (hq : Measurable q)
    (hpos : ∃ i, 0 < μ.real (q ⁻¹' {some i})) :
    ∃ i₀, 0 < μ.real (q ⁻¹' {some i₀}) ∧
      ∀ i, μ.real (q ⁻¹' {some i}) ≤ μ.real (q ⁻¹' {some i₀}) := by
  classical
  obtain ⟨i, hi⟩ := hpos
  let w := fun j => μ.real (q ⁻¹' {some j})
  have hfinite : {j | w i ≤ w j}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp
      ((class_masses_summable q hq).tendsto_cofinite_zero.eventually_lt_const hi)
  obtain ⟨j, hj, hmax⟩ := hfinite.toFinset.exists_max_image w
    ⟨i, hfinite.mem_toFinset.mpr (by change w i ≤ w i; exact le_rfl)⟩
  have hij : w i ≤ w j := hfinite.mem_toFinset.mp hj
  refine ⟨j, hi.trans_le hij, fun k => ?_⟩
  by_cases hk : w i ≤ w k
  · exact hmax k (hfinite.mem_toFinset.mpr hk)
  · exact (le_of_not_ge hk).trans hij

omit [IsProbabilityMeasure μ] in
/-- Literal original fibers, including the dust region, survive coding.
Unused natural-number labels simply have zero mass. -/
theorem exists_anchored_coding (q : Ω → Option ι) (hq : Measurable q) (i₀ : ι)
    (hpos : 0 < μ.real (q ⁻¹' {some i₀}))
    (hmax : ∀ i, μ.real (q ⁻¹' {some i}) ≤ μ.real (q ⁻¹' {some i₀})) :
    ∃ q' : Ω → Label, Measurable q' ∧
      q' ⁻¹' {.inl none} = q ⁻¹' {some i₀} ∧ q' ⁻¹' {.inr ()} = q ⁻¹' {none} ∧
      0 < anchor (μ := μ) q' ∧
      (∀ n, mass (μ := μ) q' (.inl (some n)) ≤ anchor (μ := μ) q') ∧
      (∀ x y, (q' x ≠ q' y ∨ q' x = .inr ()) ↔ (q x ≠ q y ∨ q x = none)) ∧
      ∃ e : ι ↪ ℕ, ∀ i, i ≠ i₀ → q' ⁻¹' {.inl (some (e i))} = q ⁻¹' {some i} := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let e : ι ↪ ℕ := ⟨e, he⟩
  let q' := code e i₀ ∘ q
  have hinj := code_injective e i₀
  have hanchor : q' ⁻¹' {.inl none} = q ⁻¹' {some i₀} := by
    ext x
    change code e i₀ (q x) = .inl none ↔ q x = some i₀
    rw [show (.inl none : Label) = code e i₀ (some i₀) by simp [code]]
    exact hinj.eq_iff
  have hdust : q' ⁻¹' {.inr ()} = q ⁻¹' {none} := by
    ext x
    exact code_eq_dust_iff e i₀ (q x)
  have hclass (i : ι) (hi : i ≠ i₀) :
      q' ⁻¹' {.inl (some (e i))} = q ⁻¹' {some i} := by
    ext x
    change code e i₀ (q x) = .inl (some (e i)) ↔ q x = some i
    rw [show (.inl (some (e i)) : Label) = code e i₀ (some i) by simp [code, hi]]
    exact hinj.eq_iff
  refine ⟨q', (measurable_of_countable (code e i₀)).comp hq, hanchor, hdust,
    ?_, ?_, ?_, e, hclass⟩
  · simpa only [anchor, mass, hanchor] using hpos
  · intro n
    by_cases hn : ∃ i, code e i₀ (some i) = .inl (some n)
    · obtain ⟨i, hi⟩ := hn
      have hfiber : q' ⁻¹' {.inl (some n)} = q ⁻¹' {some i} := by
        ext x
        change code e i₀ (q x) = .inl (some n) ↔ q x = some i
        rw [← hi]
        exact hinj.eq_iff
      simpa only [mass, anchor, hfiber, hanchor] using hmax i
    · have hfiber : q' ⁻¹' {.inl (some n)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        change code e i₀ (q x) = .inl (some n) at hx
        cases hqx : q x with
        | none => simp [hqx, code] at hx
        | some i => exact hn ⟨i, by simpa only [hqx] using hx⟩
      simp only [mass, hfiber, measureReal_empty]
      exact le_of_lt (by simpa only [anchor, mass, hanchor] using hpos)
  · intro x y
    exact or_congr (not_congr hinj.eq_iff) (code_eq_dust_iff e i₀ (q x))

open CappedModel

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- An arbitrary countable class label with a positive independent class
produces an actual largest-part anchored profile and its own-value bound. -/
theorem exists_own_value_bound (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (hpos : ∃ i, 0 < μ.real (q ⁻¹' {some i})) :
    ∃ (i₀ : ι) (q' : Ω → Label), Measurable q' ∧
      0 < μ.real (q ⁻¹' {some i₀}) ∧
      (∀ i, μ.real (q ⁻¹' {some i}) ≤ μ.real (q ⁻¹' {some i₀})) ∧
      anchor (μ := μ) q' = μ.real (q ⁻¹' {some i₀}) ∧
      q' ⁻¹' {.inr ()} = q ⁻¹' {none} ∧
      (∀ n, mass (μ := μ) q' (.inl (some n)) ≤ anchor (μ := μ) q') ∧
      (∀ x y, (q' x ≠ q' y ∨ q' x = .inr ()) ↔ (q x ≠ q y ∨ q x = none)) ∧
      (∃ e : ι ↪ ℕ, ∀ i, i ≠ i₀ → q' ⁻¹' {.inl (some (e i))} = q ⁻¹' {some i}) ∧
      objective W ≤ (anchor (μ := μ) q') ^ 2 *
        MultipartiteCountableDual.value (heads (μ := μ) q') (dust (μ := μ) q') ∧
      objective W ≤ (μ.real (q ⁻¹' {some i₀})) ^ 2 := by
  classical
  obtain ⟨i₀, hi, hmax⟩ := exists_largest_class q hq hpos
  obtain ⟨q', hq', haFiber, hdust, ha, hmax', hrel, hfibers⟩ :=
    exists_anchored_coding q hq i₀ hi hmax
  have hsupport' : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q' p.1 ≠ q' p.2 ∨ q' p.1 = .inr () then 1 else 0 := by
    filter_upwards [hsupport] with p hp
    by_cases he : q p.1 ≠ q p.2 ∨ q p.1 = none
    · have he' := (hrel p.1 p.2).mpr he
      simpa only [he, he', ↓reduceIte] using hp
    · have he' : ¬ (q' p.1 ≠ q' p.2 ∨ q' p.1 = .inr ()) :=
        fun h => he ((hrel p.1 p.2).mp h)
      simpa only [he, he', ↓reduceIte] using hp
  have haMass : anchor (μ := μ) q' = μ.real (q ⁻¹' {some i₀}) := by
    simp only [anchor, mass, haFiber]
  refine ⟨i₀, q', hq', hi, hmax, haMass, hdust, hmax', hrel, hfibers,
    MultipartiteModelValue.objective_le_own_value W hW q' hq' ha hmax' hsupport', ?_⟩
  rw [← haMass]
  exact MultipartiteModelValue.objective_le_anchor_sq W hW q' hq' ha hmax' hsupport'

omit [StandardBorelSpace Ω] [NullSingletonClass μ] in
/-- If every independent class is null, countability makes the actual
model pure clique dust almost everywhere, and its objective is nonpositive. -/
theorem objective_le_zero_of_null_classes (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (hnull : ∀ i, μ (q ⁻¹' {some i}) = 0) : objective W ≤ 0 := by
  classical
  have hnone : ∀ᵐ x ∂μ, q x = none := by
    have hall : ∀ᵐ x ∂μ, ∀ i, q x ≠ some i := by
      rw [ae_all_iff]
      intro i
      apply ae_iff.mpr
      change μ {x | ¬ q x ≠ some i} = 0
      simp only [not_not]
      have hset : {x | q x = some i} = q ⁻¹' {some i} := by ext x; rfl
      rw [hset]
      exact hnull i
    filter_upwards [hall] with x hx
    cases he : q x with
    | none => rfl
    | some i => exact False.elim (hx i he)
  apply MultipartiteModelValue.objective_le_zero_of_pure_dust W hW
  filter_upwards [hsupport, Measure.quasiMeasurePreserving_fst.ae hnone] with p hp hx
  simp only [hp, hx, or_true, ↓reduceIte]

end Erdos1017.MultipartiteClassCoding

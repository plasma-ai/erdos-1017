module

public import Erdos1017.Multipartite.MultipartiteCountableMeasure
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Representation

/-!
# Realizing part masses on a common component

Raw label masses are realized on a common unit-interval component, anchor
scaling of the canonical countable vertex measure is exactly this class-mass
realization, and classwise conditional sampling realizes the original law and
labels on the tagged carrier (`exists_sampler`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Function

namespace Erdos1017.MultipartiteComponentRealization

abbrev Label := MultipartiteCountableMeasure.Label

local instance componentRealizationLabelMeasurable : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual physical part masses, before anchor normalization. -/
def mass (q : Ω → Label) (i : Label) : ℝ := μ.real (q ⁻¹' {i})

def anchor (q : Ω → Label) : ℝ := mass (μ := μ) q (.inl none)

def heads (q : Ω → Label) (i : ℕ) : ℝ := mass (μ := μ) q (.inl (some i)) / anchor (μ := μ) q

def dust (q : Ω → Label) : ℝ := mass (μ := μ) q (.inr ()) / anchor (μ := μ) q

omit [IsProbabilityMeasure μ] in
theorem mass_nonneg (q : Ω → Label) (i : Label) : 0 ≤ mass (μ := μ) q i :=
  ENNReal.toReal_nonneg

omit [IsProbabilityMeasure μ] in
theorem heads_cube (q : Ω → Label) (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q) :
    ∀ i, 0 ≤ heads (μ := μ) q i ∧ heads (μ := μ) q i ≤ 1 := by
  intro i
  change 0 ≤ mass (μ := μ) q (.inl (some i)) / anchor (μ := μ) q ∧
    mass (μ := μ) q (.inl (some i)) / anchor (μ := μ) q ≤ 1
  exact ⟨div_nonneg (mass_nonneg q _) ha.le, (div_le_one ha).mpr (hmax i)⟩

theorem heads_summable (q : Ω → Label) (hq : Measurable q) : Summable (heads (μ := μ) q) := by
  unfold heads mass
  apply Summable.div_const
  exact summable_measure_toReal
    (fun i : ℕ => hq (measurableSet_singleton (Sum.inl (some i) : Label)))
    (fun i j hij => Set.disjoint_left.mpr (fun x hx hy => by
      have he : (Sum.inl (some i) : Label) = .inl (some j) := hx.symm.trans hy
      exact hij (by simpa using he)))

omit [IsProbabilityMeasure μ] in
theorem dust_nonneg (q : Ω → Label) (ha : 0 ≤ anchor (μ := μ) q) : 0 ≤ dust (μ := μ) q := by
  unfold dust
  exact div_nonneg (mass_nonneg q _) ha

/-- A null class uses an arbitrary probability fallback, with zero weight.
Every positive class uses its actual conditioned original law. -/
def componentLaw (q : Ω → Label) (i : Label) : Measure Ω :=
  if μ (q ⁻¹' {i}) = 0 then μ else ProbabilityTheory.cond μ (q ⁻¹' {i})

instance componentLaw_probability (q : Ω → Label) (i : Label) :
    IsProbabilityMeasure (componentLaw (μ := μ) q i) := by
  classical
  unfold componentLaw
  split_ifs with hi
  · infer_instance
  · exact cond_isProbabilityMeasure hi

omit [IsProbabilityMeasure μ] in
theorem componentLaw_absolutelyContinuous (q : Ω → Label) (i : Label) :
    componentLaw (μ := μ) q i ≪ μ := by
  classical
  unfold componentLaw
  split_ifs
  · exact Measure.absolutelyContinuous_rfl
  · exact cond_absolutelyContinuous

theorem mass_smul_componentLaw (q : Ω → Label) (i : Label) :
    μ (q ⁻¹' {i}) • componentLaw (μ := μ) q i = μ.restrict (q ⁻¹' {i}) := by
  classical
  by_cases hi : μ (q ⁻¹' {i}) = 0
  · simp only [componentLaw, hi, ↓reduceIte, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hi).symm
  · rw [componentLaw, ite_eq_right hi, ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel hi (measure_ne_top _ _), one_smul]

/-- The actual raw label masses on a common unit-interval component. -/
def taggedMeasure (q : Ω → Label) : Measure (Label × unitInterval) :=
  Measure.sum (fun i => μ (q ⁻¹' {i}) •
    MultipartiteCountableMeasure.component (volume : Measure unitInterval) i)

omit [IsProbabilityMeasure μ] in
theorem sum_restrict_fibers (q : Ω → Label) (hq : Measurable q) :
    Measure.sum (fun i : Label => μ.restrict (q ⁻¹' {i})) = μ := by
  have hdisj : Pairwise (Disjoint on fun i : Label => q ⁻¹' {i}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hx hy => hij (hx.symm.trans hy))
  have hcover : (⋃ i : Label, q ⁻¹' {i}) = univ := by ext x; simp
  rw [← Measure.restrict_iUnion hdisj (fun i => hq (measurableSet_singleton i)),
    hcover, Measure.restrict_univ]

private theorem tsum_labels (f : Label → ℝ≥0∞) :
    ∑' i, f i = f (.inl none) + f (.inr ()) + ∑' i, f (.inl (some i)) := by
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  have ho : (∑' i : Option ℕ, f (.inl i)) =
      (∑' i, f (.inl (some i))) + f (.inl none) := by
    rw [← (Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm.tsum_eq]
    rw [ENNReal.summable.tsum_sum ENNReal.summable]
    simp
  rw [ho]
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
  ac_rfl

/-- Anchor scaling of the canonical countable vertex measure is exactly
its actual class-mass realization. No square-mass restriction is needed. -/
theorem taggedMeasure_eq_smul_vertexMeasure (q : Ω → Label)
    (ha : 0 < anchor (μ := μ) q) :
    taggedMeasure (μ := μ) q = ENNReal.ofReal (anchor (μ := μ) q) •
      MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
        (heads (μ := μ) q) (dust (μ := μ) q) := by
  have hm (i : Label) : ENNReal.ofReal (anchor (μ := μ) q) *
      ENNReal.ofReal (mass (μ := μ) q i / anchor (μ := μ) q) = μ (q ⁻¹' {i}) := by
    rw [← ENNReal.ofReal_mul ha.le, mul_div_cancel₀ _ (ne_of_gt ha)]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  ext E hE
  simp only [taggedMeasure, Measure.sum_apply _ hE, Measure.smul_apply, smul_eq_mul]
  rw [tsum_labels]
  simp only [MultipartiteCountableMeasure.vertexMeasure, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ hE,
    MultipartiteCountableMeasure.headMeasure]
  rw [mul_add, mul_add, ← ENNReal.tsum_mul_left]
  have hanchor : μ (q ⁻¹' {Sum.inl none}) = ENNReal.ofReal (anchor (μ := μ) q) := by
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hanchor]
  congr 1
  · simp only [dust]
    rw [← mul_assoc, hm]
  · apply tsum_congr
    intro i
    simp only [heads]
    rw [← mul_assoc, hm]

variable [StandardBorelSpace Ω]

/-- Classwise conditional sampling realizes the actual original law and
its actual labels on the tagged carrier. No physical realization is an input. -/
theorem exists_sampler (q : Ω → Label) (hq : Measurable q) :
    ∃ h : Label × unitInterval → Ω, MeasurePreserving h (taggedMeasure (μ := μ) q) μ ∧
      ∀ᵐ z ∂taggedMeasure (μ := μ) q, q (h z) = z.1 := by
  classical
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hmaps (i : Label) : ∃ f : unitInterval → Ω, Measurable f ∧
      (volume : Measure unitInterval).map f = componentLaw (μ := μ) q i :=
    Measure.exists_measurable_map_eq _
  choose f hf hmap using hmaps
  let h : Label × unitInterval → Ω := fun z => f z.1 z.2
  have hh : Measurable h := measurable_from_prod_countable_right hf
  have hcomponent (i : Label) :
      (MultipartiteCountableMeasure.component (volume : Measure unitInterval) i).map h =
        componentLaw (μ := μ) q i := by
    have ht : Measurable (fun u : unitInterval => (i, u)) :=
      measurable_const.prodMk measurable_id
    rw [MultipartiteCountableMeasure.component, Measure.map_map hh ht]
    exact hmap i
  have hpush : (taggedMeasure (μ := μ) q).map h = μ := by
    rw [taggedMeasure, Measure.map_sum hh.aemeasurable]
    simp_rw [Measure.map_smul _ hh.aemeasurable, hcomponent, mass_smul_componentLaw]
    exact sum_restrict_fibers q hq
  refine ⟨h, ⟨hh, hpush⟩, ?_⟩
  rw [taggedMeasure, Measure.ae_sum_iff]
  intro i
  by_cases hi : μ (q ⁻¹' {i}) = 0
  · simp [hi]
  have hmem : ∀ᵐ x ∂componentLaw (μ := μ) q i, q x = i := by
    rw [componentLaw, ite_eq_right hi]
    have hac : ProbabilityTheory.cond μ (q ⁻¹' {i}) ≪ μ.restrict (q ⁻¹' {i}) :=
      Measure.smul_absolutelyContinuous
    exact hac.ae_le (ae_restrict_mem (hq (measurableSet_singleton i)))
  have hfmem : ∀ᵐ u ∂(volume : Measure unitInterval), q (f i u) = i := by
    have h : MeasurePreserving (f i) (volume : Measure unitInterval) (componentLaw (μ := μ) q i) :=
      ⟨hf i, hmap i⟩
    exact h.quasiMeasurePreserving.ae hmem
  have htag : ∀ᵐ z ∂MultipartiteCountableMeasure.component (volume : Measure unitInterval) i,
      q (h z) = z.1 := by
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hq.comp hh) measurable_fst)).mpr
    exact hfmem
  exact (Measure.smul_absolutelyContinuous (c := μ (q ⁻¹' {i}))).ae_le htag

/-- The conditional sampler on the anchor-normalized canonical carrier
pushes its vertex measure to the correspondingly scaled original law. -/
theorem exists_normalized_sampler (q : Ω → Label) (hq : Measurable q)
    (ha : 0 < anchor (μ := μ) q) :
    ∃ h : Label × unitInterval → Ω, Measurable h ∧
      (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
        (heads (μ := μ) q) (dust (μ := μ) q)).map h =
          (ENNReal.ofReal (anchor (μ := μ) q))⁻¹ • μ ∧
      ∀ᵐ z ∂MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
        (heads (μ := μ) q) (dust (μ := μ) q), q (h z) = z.1 := by
  obtain ⟨h, hh, hlabels⟩ := exists_sampler (μ := μ) q hq
  have hc : ENNReal.ofReal (anchor (μ := μ) q) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  have hpush : ENNReal.ofReal (anchor (μ := μ) q) •
      (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
        (heads (μ := μ) q) (dust (μ := μ) q)).map h = μ := by
    rw [← Measure.map_smul _ hh.measurable.aemeasurable,
      ← taggedMeasure_eq_smul_vertexMeasure q ha]
    exact hh.map_eq
  have hraw := congrArg (fun ν : Measure Ω =>
    (ENNReal.ofReal (anchor (μ := μ) q))⁻¹ • ν) hpush
  rw [smul_smul, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul] at hraw
  refine ⟨h, hh.measurable, hraw, ?_⟩
  rw [taggedMeasure_eq_smul_vertexMeasure q ha] at hlabels
  exact (Measure.absolutelyContinuous_smul hc).ae_le hlabels

/-- The actual masses have the exact total required by anchor normalization. -/
theorem normalized_mass (q : Ω → Label) (hq : Measurable q)
    (ha : 0 < anchor (μ := μ) q) :
    1 + dust (μ := μ) q + ∑' i, heads (μ := μ) q i = 1 / anchor (μ := μ) q := by
  obtain ⟨h, hh, hpush, _⟩ := exists_normalized_sampler q hq ha
  calc
    1 + dust (μ := μ) q + ∑' i, heads (μ := μ) q i =
        (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
          (heads (μ := μ) q) (dust (μ := μ) q)).real univ :=
      (MultipartiteCountableMeasure.vertexMeasure_mass _ _
        (fun i => div_nonneg (mass_nonneg q _) ha.le) (heads_summable q hq) _
        (dust_nonneg q ha.le)).symm
    _ = ((MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
          (heads (μ := μ) q) (dust (μ := μ) q)).map h).real univ := by
      simp [measureReal_def, Measure.map_apply hh]
    _ = 1 / anchor (μ := μ) q := by
      rw [hpush]
      simp [measureReal_def, Measure.smul_apply, ENNReal.toReal_inv, ha.le, one_div]

end Erdos1017.MultipartiteComponentRealization

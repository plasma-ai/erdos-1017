module

public import Erdos1017.SelectedModel.ZeroClass.CountableClassEdits
public import Erdos1017.Models.Capped.CappedRegularSelection
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteModelComparison

/-!
# Kernel and benchmark comparison of countable class edits

The simultaneous edit has deterministic multipartite color within each positive
class and the original conditional law elsewhere, and once its full feasibility
is established, its partition support (with the diagonal-null hypothesis
discharged by atomlessness) gives the benchmark comparison.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open scoped Classical in
/-- The simultaneous edit has its deterministic multipartite color within
each positive class and the literal old conditional law everywhere else. -/
theorem countableClassEdit_kernel (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) :
    (countableClassEdit W t ht m hm).kernel p =
      if 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 then
        Measure.dirac (if (t p.1).2 = (t p.2).2 then CappedColor.absent
          else CappedColor.present m hm)
      else W.kernel p := by
  classical
  change W.editKernel (classReplacementColor t m hm) p = _
  rw [DecoratedKernel.editKernel_apply _ _ (measurable_classReplacementColor t ht m hm)]
  by_cases hclass : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1
  · simp only [classReplacementColor, ite_eq_left hclass]
    by_cases hlabel : (t p.1).2 = (t p.2).2 <;>
      simp [hlabel, Measure.map_const]
  · simp [classReplacementColor, hclass]

open scoped Classical in
/-- Every actual edited color moment has its exact internal deterministic
value and its unchanged old value on the other pairs. -/
theorem countableClassEdit_moment (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (f : CappedColor → ℝ) (p : Ω × Ω) :
    (countableClassEdit W t ht m hm).moment f p =
      if 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 then
        f (if (t p.1).2 = (t p.2).2 then CappedColor.absent else CappedColor.present m hm)
      else W.moment f p := by
  rw [DecoratedKernel.moment, countableClassEdit_kernel]
  by_cases hclass : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1
  · simp only [ite_eq_left hclass, integral_dirac]
  · simp only [ite_eq_right hclass, DecoratedKernel.moment]

/-- The countable family of actual class-square zero assertions holds on
one common set of full pair measure. -/
theorem ae_shiftedMoment_zero_on_same_positive_class (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (m : ℝ)
    (hzero : ∀ k : ℕ, 0 < k → ∀ᵐ p ∂μ.prod μ,
      (t p.1).1 = k ∧ (t p.2).1 = k → shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ,
      0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 → shiftedMoment W m p = 0 := by
  have hall : ∀ᵐ p ∂μ.prod μ, ∀ k : {k : ℕ // 0 < k},
      (t p.1).1 = k.val ∧ (t p.2).1 = k.val → shiftedMoment W m p = 0 :=
    ae_all_iff.mpr (fun k => hzero k.val k.property)
  filter_upwards [hall] with p hp hclass
  exact hp ⟨(t p.1).1, hclass.1⟩ ⟨rfl, hclass.2.symm⟩

/-- Simultaneously replacing any countable collection of actual zero
classes preserves the old shifted moment almost everywhere. -/
theorem shiftedMoment_countableClassEdit_ae_eq (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (ht : Measurable t) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 → shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment (countableClassEdit W t ht m hm) m p = shiftedMoment W m p := by
  filter_upwards [hzero] with p hp
  change (countableClassEdit W t ht m hm).moment (shiftedColor m) p = _
  rw [countableClassEdit_moment]
  by_cases hclass : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1
  · rw [ite_eq_left hclass, hp hclass]
    by_cases hlabel : (t p.1).2 = (t p.2).2 <;>
      simp [hlabel, shiftedColor, CappedColor.absent, CappedColor.present,
        CappedColor.charge, CappedColor.adjacency]
  · simp [hclass, shiftedMoment]

/-- Feature representation, the actual boundary-zero characterization and
nonnegativity survive the simultaneous zero-class replacement. -/
theorem countableClassEdit_preserves_shifted_geometry {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t) (F : Ω → H) (ν m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (hclass : ∀ᵐ p ∂μ.prod μ,
      0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 → shiftedMoment W m p = 0)
    (hrep : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    (∀ᵐ p ∂μ.prod μ, shiftedMoment (countableClassEdit W t ht m hm) m p = ν - ⟪F p.1, F p.2⟫) ∧
    (∀ᵐ p ∂μ.prod μ, shiftedMoment (countableClassEdit W t ht m hm) m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2) ∧
    (∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment (countableClassEdit W t ht m hm) m p) := by
  have heq := shiftedMoment_countableClassEdit_ae_eq W t ht m hm hclass
  constructor
  · filter_upwards [heq, hrep] with p hp hrepP
    exact hp.trans hrepP
  constructor
  · filter_upwards [heq, hzero] with p hp hzeroP
    rwa [hp]
  · filter_upwards [heq, hnonneg] with p hp hnonnegP
    rwa [hp]

/-- Complementarity survives the simultaneous countable-class edit. -/
theorem countableClassEdit_complementary (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ, (1 - (countableClassEdit W t ht m hm).moment CappedColor.adjacency p) *
      shiftedMoment (countableClassEdit W t ht m hm) m p = 0 := by
  classical
  filter_upwards [hcomp] with p hp
  change (1 - (countableClassEdit W t ht m hm).moment CappedColor.adjacency p) *
    (countableClassEdit W t ht m hm).moment (shiftedColor m) p = 0
  rw [countableClassEdit_moment, countableClassEdit_moment]
  by_cases hclass : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1
  · simp only [ite_eq_left hclass]
    by_cases hlabel : (t p.1).2 = (t p.2).2 <;>
      simp [hlabel, shiftedColor, CappedColor.absent, CappedColor.present,
        CappedColor.charge, CappedColor.adjacency]
  · simpa [hclass, shiftedMoment] using hp

/-- The actual edited conditional color law retains shifted-color determinism. -/
theorem countableClassEdit_shifted_deterministic (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (ht : Measurable t) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂(countableClassEdit W t ht m hm).kernel p,
      shiftedColor m c = shiftedMoment (countableClassEdit W t ht m hm) m p := by
  classical
  filter_upwards [hdet] with p hp
  rw [countableClassEdit_kernel]
  change ∀ᵐ c ∂(if 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 then
      Measure.dirac (if (t p.1).2 = (t p.2).2 then CappedColor.absent else CappedColor.present m hm)
      else W.kernel p), shiftedColor m c = (countableClassEdit W t ht m hm).moment (shiftedColor m) p
  rw [countableClassEdit_moment]
  by_cases hclass : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1
  · simp only [ite_eq_left hclass]
    simp
  · simpa only [ite_eq_right hclass, shiftedMoment] using hp

omit [MeasurableSpace Ω] in
/-- A positive class of the truncated labelling is a positive class of the
original labelling. Truncation introduces only the outside label zero. -/
theorem same_positive_class_of_truncated (t : Ω → ℕ × ℕ) (N : ℕ) (p : Ω × Ω)
    (hclass : 0 < (truncatedClassLabels t N p.1).1 ∧
      (truncatedClassLabels t N p.1).1 = (truncatedClassLabels t N p.2).1) :
    0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 := by
  by_cases hfirst : (t p.1).1 ≤ N
  · by_cases hsecond : (t p.2).1 ≤ N
    · simpa [truncatedClassLabels, hfirst, hsecond] using hclass
    · simp [truncatedClassLabels, hfirst, hsecond] at hclass
      omega
  · simp [truncatedClassLabels, hfirst] at hclass

/-- Every finite-prefix edit preserves the old shifted moment under the
same actual zero-class hypothesis as the full simultaneous edit. -/
theorem shiftedMoment_prefixClassEdit_ae_eq (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (ht : Measurable t) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 → shiftedMoment W m p = 0) (N : ℕ) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment (prefixClassEdit W t ht m hm N) m p = shiftedMoment W m p := by
  apply shiftedMoment_countableClassEdit_ae_eq
  filter_upwards [hzero] with p hp hclass
  exact hp (same_positive_class_of_truncated t N p hclass)

/-- Every finite prefix retains the actual feature geometry of the old model. -/
theorem prefixClassEdit_preserves_shifted_geometry {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t) (F : Ω → H) (ν m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1)
    (hclass : ∀ᵐ p ∂μ.prod μ,
      0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 → shiftedMoment W m p = 0)
    (hrep : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) (N : ℕ) :
    (∀ᵐ p ∂μ.prod μ, shiftedMoment (prefixClassEdit W t ht m hm N) m p = ν - ⟪F p.1, F p.2⟫) ∧
    (∀ᵐ p ∂μ.prod μ, shiftedMoment (prefixClassEdit W t ht m hm N) m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2) ∧
    (∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment (prefixClassEdit W t ht m hm N) m p) := by
  apply countableClassEdit_preserves_shifted_geometry W _ _ F ν m hm _ hrep hzero hnonneg
  filter_upwards [hclass] with p hp hpositive
  exact hp (same_positive_class_of_truncated t N p hpositive)

/-- Complementarity survives every actual finite-prefix edit. -/
theorem prefixClassEdit_complementary (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) (N : ℕ) :
    ∀ᵐ p ∂μ.prod μ, (1 - (prefixClassEdit W t ht m hm N).moment CappedColor.adjacency p) *
      shiftedMoment (prefixClassEdit W t ht m hm N) m p = 0 :=
  countableClassEdit_complementary W _ _ m hm hcomp

/-- Shifted-color determinism survives every actual finite-prefix edit. -/
theorem prefixClassEdit_shifted_deterministic (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (ht : Measurable t) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) (N : ℕ) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂(prefixClassEdit W t ht m hm N).kernel p,
      shiftedColor m c = shiftedMoment (prefixClassEdit W t ht m hm N) m p :=
  countableClassEdit_shifted_deterministic W _ _ m hm hdet

open scoped Classical in
/-- Actual parts of the edited model: positive classes use their full pair
of labels, and outside points each receive their own singleton dust label. -/
def classPartLabel (t : Ω → ℕ × ℕ) (x : Ω) : (ℕ × ℕ) ⊕ Ω :=
  if 0 < (t x).1 then Sum.inl (t x) else Sum.inr x

omit [MeasurableSpace Ω] in
/-- Within a positive class, distinct actual part labels mean precisely
distinct second labels. -/
theorem classPartLabel_ne_iff_of_same_positive_class (t : Ω → ℕ × ℕ) (p : Ω × Ω)
    (hclass : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1) :
    classPartLabel t p.1 ≠ classPartLabel t p.2 ↔ (t p.1).2 ≠ (t p.2).2 := by
  classical
  have hsecond : 0 < (t p.2).1 := hclass.2 ▸ hclass.1
  simp only [classPartLabel, ite_eq_left hclass.1, ite_eq_left hsecond, ne_eq, Sum.inl.injEq]
  constructor
  · intro hne heq
    exact hne (Prod.ext hclass.2 heq)
  · intro hne heq
    exact hne (congrArg Prod.snd heq)

omit [MeasurableSpace Ω] in
/-- Distinct points outside a common positive class always have distinct
actual part labels, including the singleton labels of dust points. -/
theorem classPartLabel_ne_of_outside (t : Ω → ℕ × ℕ) (p : Ω × Ω) (hne : p.1 ≠ p.2)
    (hclass : ¬(0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1)) :
    classPartLabel t p.1 ≠ classPartLabel t p.2 := by
  classical
  by_cases hfirst : 0 < (t p.1).1
  · by_cases hsecond : 0 < (t p.2).1
    · simp only [classPartLabel, ite_eq_left hfirst, ite_eq_left hsecond, ne_eq, Sum.inl.injEq]
      intro heq
      exact hclass ⟨hfirst, congrArg Prod.fst heq⟩
    · simp [classPartLabel, hfirst, hsecond]
  · by_cases hsecond : 0 < (t p.2).1
    · simp [classPartLabel, hfirst, hsecond]
    · simpa [classPartLabel, hfirst, hsecond] using hne

/-- If old pairs outside the positive classes are present almost surely,
the full countable edit has actual multipartite conditional support.
Diagonal nullity is explicit because outside points are singleton parts. -/
theorem countableClassEdit_partition_support (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (ht : Measurable t) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (houtside : ∀ᵐ p ∂μ.prod μ,
      ¬(0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1) → W.moment CappedColor.adjacency p = 1)
    (hdiag : ∀ᵐ p ∂μ.prod μ, p.1 ≠ p.2) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂(countableClassEdit W t ht m hm).kernel p,
      CappedColor.adjacency c = 1 ↔ classPartLabel t p.1 ≠ classPartLabel t p.2 := by
  classical
  filter_upwards [houtside, hdiag] with p hp hne
  rw [countableClassEdit_kernel]
  by_cases hclass : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1
  · rw [ite_eq_left hclass]
    have hlabels := classPartLabel_ne_iff_of_same_positive_class t p hclass
    by_cases hlabel : (t p.1).2 = (t p.2).2 <;>
      simp [hlabel, hlabels, CappedColor.absent, CappedColor.present, CappedColor.adjacency]
  · rw [ite_eq_right hclass]
    have hlabels := classPartLabel_ne_of_outside t p hne hclass
    filter_upwards [ae_adjacency_one_of_moment_one W p (hp hclass)] with c hc
    simp [hc, hlabels]

variable [IsProbabilityMeasure μ]

/-- Atomlessness and measurable equality discharge the actual diagonal-null
hypothesis of the multipartite support theorem. -/
theorem countableClassEdit_partition_support_of_atomless [MeasurableEq Ω] [NullSingletonClass μ]
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (houtside : ∀ᵐ p ∂μ.prod μ,
      ¬(0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1) → W.moment CappedColor.adjacency p = 1) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂(countableClassEdit W t ht m hm).kernel p,
      CappedColor.adjacency c = 1 ↔ classPartLabel t p.1 ≠ classPartLabel t p.2 := by
  apply countableClassEdit_partition_support W t ht m hm houtside
  rw [ae_iff]
  change (μ.prod μ) {p : Ω × Ω | ¬p.1 ≠ p.2} = 0
  simp only [not_ne_iff]
  change (μ.prod μ) (Set.diagonal Ω) = 0
  rw [Measure.prod_apply measurableSet_diagonal]
  have hpre (x : Ω) : Prod.mk x ⁻¹' Set.diagonal Ω = {x} := by
    ext y
    simp [Set.diagonal, eq_comm]
  simp_rw [hpre, measure_singleton]
  simp

/-- Once full feasibility of the actual countable edit is established,
its actual partition support gives the original benchmark comparison.
No density or objective preservation premise is needed for this statement. -/
theorem countableClassEdit_objective_le_benchmark (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (ht : Measurable t) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (houtside : ∀ᵐ p ∂μ.prod μ,
      ¬(0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1) → W.moment CappedColor.adjacency p = 1)
    (hdiag : ∀ᵐ p ∂μ.prod μ, p.1 ≠ p.2)
    (hfull : FullFeasible (countableClassEdit W t ht m hm)) :
    objective (countableClassEdit W t ht m hm) ≤ benchmark (density (countableClassEdit W t ht m hm)) :=
  objective_le_benchmark_of_partition_support _ hfull (classPartLabel t)
    (countableClassEdit_partition_support W t ht m hm houtside hdiag)

/-- The atomless version uses the separately proved full feasibility of
the actual countable edit and derives its multipartite support internally. -/
theorem countableClassEdit_objective_le_benchmark_of_atomless [MeasurableEq Ω] [NullSingletonClass μ]
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (houtside : ∀ᵐ p ∂μ.prod μ,
      ¬(0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1) → W.moment CappedColor.adjacency p = 1)
    (hfull : FullFeasible (countableClassEdit W t ht m hm)) :
    objective (countableClassEdit W t ht m hm) ≤ benchmark (density (countableClassEdit W t ht m hm)) :=
  objective_le_benchmark_of_partition_support _ hfull (classPartLabel t)
    (countableClassEdit_partition_support_of_atomless W t ht m hm houtside)

end Erdos1017.CappedModel

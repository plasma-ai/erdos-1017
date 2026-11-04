module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Tensor approximation of continuous color tests

Pure tensor tests and their normalized `[0,1]`-valued versions form algebras
that separate points, so uniform approximation holds and tensor moment
convergence determines convergence of all continuous finite-color tests for
probability laws on a compact color product.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.DecoratedTensor

variable {C ι : Type*} [TopologicalSpace C] [Fintype ι]

/-- A product of one-coordinate continuous color tests. -/
def pureTensor (f : ι → C(C, ℝ)) : C(ι → C, ℝ) :=
  ⟨fun c => ∏ i, f i (c i), by
    apply continuous_finsetProd
    intro i _
    exact (f i).continuous.comp (continuous_apply i)⟩

@[simp] theorem pureTensor_apply (f : ι → C(C, ℝ)) (c : ι → C) :
    pureTensor f c = ∏ i, f i (c i) := rfl

end Erdos1017.DecoratedTensor

namespace Erdos1017.DecoratedTensor

variable {C ι : Type*} [TopologicalSpace C] [Fintype ι]

/-- Finite linear combinations of pure tensor tests. -/
def tensorSpan : Submodule ℝ C(ι → C, ℝ) :=
  Submodule.span ℝ (Set.range (pureTensor (C := C) (ι := ι)))

private theorem pureTensor_one :
    pureTensor (C := C) (ι := ι) (fun _ => 1) = 1 := by
  ext c
  simp [pureTensor]

private theorem pureTensor_mul (f g : ι → C(C, ℝ)) :
    pureTensor f * pureTensor g = pureTensor (fun i => f i * g i) := by
  ext c
  simp only [ContinuousMap.mul_apply, pureTensor_apply, ContinuousMap.mul_apply,
    Finset.prod_mul_distrib]

/-- Tensor polynomials form an algebra of continuous functions. -/
def tensorAlgebra : Subalgebra ℝ C(ι → C, ℝ) where
  carrier := tensorSpan (C := C) (ι := ι)
  zero_mem' := (tensorSpan (C := C) (ι := ι)).zero_mem
  add_mem' := (tensorSpan (C := C) (ι := ι)).add_mem
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one, ← pureTensor_one (C := C) (ι := ι)]
    exact (tensorSpan (C := C) (ι := ι)).smul_mem r
      (Submodule.subset_span ⟨fun _ => 1, rfl⟩)
  mul_mem' := by
    intro a b ha hb
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro x ⟨f, rfl⟩
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
      · rintro y ⟨g, rfl⟩
        rw [pureTensor_mul]
        exact Submodule.subset_span ⟨fun i => f i * g i, rfl⟩
      · simp
      · intro y z _ _ hy hz
        rw [mul_add]
        exact (tensorSpan (C := C) (ι := ι)).add_mem hy hz
      · intro r y _ hy
        rw [mul_smul_comm]
        exact (tensorSpan (C := C) (ι := ι)).smul_mem r hy
    · simp
    · intro x y _ _ hx hy
      rw [add_mul]
      exact (tensorSpan (C := C) (ι := ι)).add_mem hx hy
    · intro r x _ hx
      rw [smul_mul_assoc]
      exact (tensorSpan (C := C) (ι := ι)).smul_mem r hx

variable [T35Space C]

theorem tensorAlgebra_separatesPoints :
    (tensorAlgebra (C := C) (ι := ι)).SeparatesPoints := by
  classical
  intro c d hcd
  have hdiff : ∃ i, c i ≠ d i := by
    by_contra h
    push Not at h
    exact hcd (funext h)
  obtain ⟨i, hi⟩ := hdiff
  obtain ⟨g, hgcont, hg⟩ := separatesPoints_continuous_of_t35Space hi
  let f : ι → C(C, ℝ) := fun j => if j = i then ⟨g, hgcont⟩ else 1
  have hmem : pureTensor f ∈ tensorAlgebra (C := C) (ι := ι) :=
    Submodule.subset_span ⟨f, rfl⟩
  have hcoord (z : ι → C) : pureTensor f z = g (z i) := by
    rw [pureTensor_apply, Finset.prod_eq_single i]
    · simp [f]
    · intro j _ hji
      simp [f, hji]
    · simp
  exact ⟨pureTensor f, ⟨pureTensor f, hmem, rfl⟩, by simpa [hcoord] using hg⟩

variable [CompactSpace C]

/-- Every continuous test on a finite color product can be approximated
uniformly by a finite linear combination of pure tensor tests. -/
theorem exists_tensorSpan_approx (F : C(ι → C, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ G ∈ tensorSpan (C := C) (ι := ι), ‖G - F‖ < ε := by
  obtain ⟨G, hG⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (tensorAlgebra (C := C) (ι := ι)) tensorAlgebra_separatesPoints F ε hε
  exact ⟨G, G.property, hG⟩

variable [MeasurableSpace C] [BorelSpace C] [OpensMeasurableSpace C] [SecondCountableTopology C]

omit [T35Space C] [BorelSpace C] in
private theorem integrable_continuousTest (ν : ProbabilityMeasure (ι → C))
    (F : C(ι → C, ℝ)) : Integrable (fun c => F c) (ν : Measure (ι → C)) :=
  Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)

/-- Integration against a probability law is linear on continuous tests. -/
def expectationLinear (ν : ProbabilityMeasure (ι → C)) : C(ι → C, ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∫ c, F c ∂(ν : Measure (ι → C))
  map_add' F G := by
    change (∫ c, (F + G) c ∂(ν : Measure (ι → C))) = _
    simp only [ContinuousMap.add_apply]
    exact integral_add (integrable_continuousTest ν F) (integrable_continuousTest ν G)
  map_smul' r F := by
    change (∫ c, (r • F) c ∂(ν : Measure (ι → C))) = _
    simp only [ContinuousMap.smul_apply]
    exact integral_const_mul r _

omit [T35Space C] [BorelSpace C] in
private theorem norm_expectationLinear_le (ν : ProbabilityMeasure (ι → C))
    (F : C(ι → C, ℝ)) : ‖expectationLinear ν F‖ ≤ ‖F‖ := by
  change ‖∫ c, F c ∂(ν : Measure (ι → C))‖ ≤ ‖F‖
  have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure (ι → C)))
    (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
  simpa using h

omit [BorelSpace C] in
/-- Tensor moment convergence determines convergence of all continuous
finite-color tests for probability laws on a compact color product. -/
theorem tendsto_integral_of_tendsto_tensor
    (ν : ℕ → ProbabilityMeasure (ι → C)) (νlim : ProbabilityMeasure (ι → C))
    (h : ∀ f : ι → C(C, ℝ), Filter.Tendsto
      (fun k => expectationLinear (ν k) (pureTensor f)) Filter.atTop
      (nhds (expectationLinear νlim (pureTensor f))))
    (F : C(ι → C, ℝ)) :
    Filter.Tendsto (fun k => expectationLinear (ν k) F) Filter.atTop
      (nhds (expectationLinear νlim F)) := by
  classical
  have hspan (G : C(ι → C, ℝ)) (hG : G ∈ tensorSpan (C := C) (ι := ι)) :
      Filter.Tendsto (fun k => expectationLinear (ν k) G) Filter.atTop
        (nhds (expectationLinear νlim G)) := by
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨f, rfl⟩ := hG
      exact h f
    | zero =>
      simp
    | add G H _ _ hG hH =>
      simpa only [map_add] using hG.add hH
    | smul r G _ hG =>
      simpa only [map_smul, smul_eq_mul] using hG.const_smul r
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨G, hG, hclose⟩ := exists_tensorSpan_approx F (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hspan G hG) (ε / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro k hk
  have hmid : |expectationLinear (ν k) G - expectationLinear νlim G| < ε / 3 := by
    simpa only [Real.dist_eq] using hN k hk
  have hleft : |expectationLinear (ν k) F - expectationLinear (ν k) G| < ε / 3 := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact lt_of_le_of_lt (norm_expectationLinear_le (ν k) (F - G))
      (by simpa only [norm_sub_rev] using hclose)
  have hright : |expectationLinear νlim G - expectationLinear νlim F| < ε / 3 := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact lt_of_le_of_lt (norm_expectationLinear_le νlim (G - F)) hclose
  have htri₁ := abs_sub_le (expectationLinear (ν k) F)
    (expectationLinear (ν k) G) (expectationLinear νlim F)
  have htri₂ := abs_sub_le (expectationLinear (ν k) G)
    (expectationLinear νlim G) (expectationLinear νlim F)
  rw [Real.dist_eq]
  linarith

end Erdos1017.DecoratedTensor

namespace Erdos1017.DecoratedTensor

variable {C ι : Type*} [TopologicalSpace C] [Fintype ι]

/-- Pure tensor tests with every coordinate taking values in `[0,1]`. -/
def normalizedTensors : Set C(ι → C, ℝ) :=
  {G | ∃ f : ι → C(C, ℝ), (∀ i c, f i c ∈ Set.Icc 0 1) ∧ G = pureTensor f}

/-- Finite linear combinations of normalized pure tensor tests. -/
def normalizedTensorSpan : Submodule ℝ C(ι → C, ℝ) :=
  Submodule.span ℝ (normalizedTensors (C := C) (ι := ι))

private theorem normalizedTensors_one : (1 : C(ι → C, ℝ)) ∈ normalizedTensors (C := C) (ι := ι) := by
  refine ⟨fun _ => 1, ?_, (pureTensor_one (C := C) (ι := ι)).symm⟩
  intro i c
  simp

private theorem normalizedTensors_mul {F G : C(ι → C, ℝ)}
    (hF : F ∈ normalizedTensors (C := C) (ι := ι))
    (hG : G ∈ normalizedTensors (C := C) (ι := ι)) :
    F * G ∈ normalizedTensors (C := C) (ι := ι) := by
  obtain ⟨f, hf, rfl⟩ := hF
  obtain ⟨g, hg, rfl⟩ := hG
  refine ⟨fun i => f i * g i, ?_, pureTensor_mul f g⟩
  intro i c
  refine ⟨mul_nonneg (hf i c).1 (hg i c).1, ?_⟩
  calc f i c * g i c ≤ 1 * g i c :=
      mul_le_mul_of_nonneg_right (hf i c).2 (hg i c).1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (hg i c).2 (by norm_num)
    _ = 1 := by ring

/-- Normalized tensor polynomials form an algebra. -/
def normalizedTensorAlgebra : Subalgebra ℝ C(ι → C, ℝ) where
  carrier := normalizedTensorSpan (C := C) (ι := ι)
  zero_mem' := (normalizedTensorSpan (C := C) (ι := ι)).zero_mem
  add_mem' := (normalizedTensorSpan (C := C) (ι := ι)).add_mem
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (normalizedTensorSpan (C := C) (ι := ι)).smul_mem r
      (Submodule.subset_span normalizedTensors_one)
  mul_mem' := by
    intro a b ha hb
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · intro x hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
      · intro y hy
        exact Submodule.subset_span (normalizedTensors_mul hx hy)
      · simp
      · intro y z _ _ hy hz
        rw [mul_add]
        exact (normalizedTensorSpan (C := C) (ι := ι)).add_mem hy hz
      · intro r y _ hy
        rw [mul_smul_comm]
        exact (normalizedTensorSpan (C := C) (ι := ι)).smul_mem r hy
    · simp
    · intro x y _ _ hx hy
      rw [add_mul]
      exact (normalizedTensorSpan (C := C) (ι := ι)).add_mem hx hy
    · intro r x _ hx
      rw [smul_mul_assoc]
      exact (normalizedTensorSpan (C := C) (ι := ι)).smul_mem r hx

variable [T35Space C]

theorem normalizedTensorAlgebra_separatesPoints :
    (normalizedTensorAlgebra (C := C) (ι := ι)).SeparatesPoints := by
  classical
  intro c d hcd
  have hdiff : ∃ i, c i ≠ d i := by
    by_contra h
    push Not at h
    exact hcd (funext h)
  obtain ⟨i, hi⟩ := hdiff
  obtain ⟨g, hgcont, hg⟩ := separatesPoints_continuous_of_t35Space_Icc hi
  let g' : C(C, ℝ) := ⟨fun z => (g z : ℝ), continuous_subtype_val.comp hgcont⟩
  let f : ι → C(C, ℝ) := fun j => if j = i then g' else 1
  have hf : ∀ j z, f j z ∈ Set.Icc 0 1 := by
    intro j z
    by_cases hji : j = i
    · simp only [f, hji, ↓reduceIte, g']
      exact (g z).property
    · simp [f, hji]
  have hmem : pureTensor f ∈ normalizedTensorAlgebra (C := C) (ι := ι) :=
    Submodule.subset_span ⟨f, hf, rfl⟩
  have hcoord (z : ι → C) : pureTensor f z = (g (z i) : ℝ) := by
    rw [pureTensor_apply, Finset.prod_eq_single i]
    · simp [f, g']
    · intro j _ hji
      simp [f, hji]
    · simp
  have hg' : (g (c i) : ℝ) ≠ (g (d i) : ℝ) := by
    intro h
    exact hg (Subtype.ext h)
  exact ⟨pureTensor f, ⟨pureTensor f, hmem, rfl⟩, by simpa [hcoord] using hg'⟩

variable [CompactSpace C]

/-- Uniform approximation using only `[0,1]`-valued coordinate tests. -/
theorem exists_normalizedTensorSpan_approx (F : C(ι → C, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ G ∈ normalizedTensorSpan (C := C) (ι := ι), ‖G - F‖ < ε := by
  obtain ⟨G, hG⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (normalizedTensorAlgebra (C := C) (ι := ι))
      normalizedTensorAlgebra_separatesPoints F ε hε
  exact ⟨G, G.property, hG⟩

end Erdos1017.DecoratedTensor

namespace Erdos1017.DecoratedTensor

variable {C ι : Type*} [TopologicalSpace C] [Fintype ι] [T35Space C] [CompactSpace C]
  [MeasurableSpace C] [OpensMeasurableSpace C] [SecondCountableTopology C]

theorem tendsto_integral_of_tendsto_normalizedTensor
    (ν : ℕ → ProbabilityMeasure (ι → C)) (νlim : ProbabilityMeasure (ι → C))
    (h : ∀ f : ι → C(C, ℝ), (∀ i c, f i c ∈ Set.Icc 0 1) → Filter.Tendsto
      (fun k => expectationLinear (ν k) (pureTensor f)) Filter.atTop
      (nhds (expectationLinear νlim (pureTensor f))))
    (F : C(ι → C, ℝ)) :
    Filter.Tendsto (fun k => expectationLinear (ν k) F) Filter.atTop
      (nhds (expectationLinear νlim F)) := by
  classical
  have hspan (G : C(ι → C, ℝ)) (hG : G ∈ normalizedTensorSpan (C := C) (ι := ι)) :
      Filter.Tendsto (fun k => expectationLinear (ν k) G) Filter.atTop
        (nhds (expectationLinear νlim G)) := by
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨f, hf, rfl⟩ := hG
      exact h f hf
    | zero =>
      simp
    | add G H _ _ hG hH =>
      simpa only [map_add] using hG.add hH
    | smul r G _ hG =>
      simpa only [map_smul, smul_eq_mul] using hG.const_smul r
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨G, hG, hclose⟩ := exists_normalizedTensorSpan_approx F (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hspan G hG) (ε / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro k hk
  have hmid : |expectationLinear (ν k) G - expectationLinear νlim G| < ε / 3 := by
    simpa only [Real.dist_eq] using hN k hk
  have hleft : |expectationLinear (ν k) F - expectationLinear (ν k) G| < ε / 3 := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact lt_of_le_of_lt (norm_expectationLinear_le (ν k) (F - G))
      (by simpa only [norm_sub_rev] using hclose)
  have hright : |expectationLinear νlim G - expectationLinear νlim F| < ε / 3 := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact lt_of_le_of_lt (norm_expectationLinear_le νlim (G - F)) hclose
  have htri₁ := abs_sub_le (expectationLinear (ν k) F)
    (expectationLinear (ν k) G) (expectationLinear νlim F)
  have htri₂ := abs_sub_le (expectationLinear (ν k) G)
    (expectationLinear νlim G) (expectationLinear νlim F)
  rw [Real.dist_eq]
  linarith

end Erdos1017.DecoratedTensor

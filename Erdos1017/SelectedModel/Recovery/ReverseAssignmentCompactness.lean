module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Compactness of the relaxed reverse assignment set

The relaxed assignment constraints on countably many `L²` coordinates are
encoded in product weak-dual coordinates, where every almost-everywhere
feasibility constraint is closed, so the feasible set is compact by bounded
Riesz coordinates (`isCompact_dualFeasibleSet`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace Erdos1017.ReverseAssignment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Sources with no diffuse supply and exactly this finite allowed-label set. -/
def finitePattern (allowed : ℕ → Set Ω) (δ : Ω → ℝ) (J : Finset ℕ) : Set Ω :=
  {x | δ x = 0 ∧ ∀ i, i ∈ J ↔ x ∈ allowed i}

/-- The actual relaxed assignment constraints on countably many L² coordinates. -/
structure Feasible (allowed : ℕ → Set Ω) (δ : Ω → ℝ) (q : ℕ → Lp ℝ 2 μ) : Prop where
  box : ∀ i, ∀ᵐ x ∂μ, q i x ∈ Icc (0 : ℝ) 1
  support : ∀ i, ∀ᵐ x ∂μ, x ∉ allowed i → q i x = 0
  partial_sum : ∀ J : Finset ℕ, ∀ᵐ x ∂μ, ∑ i ∈ J, q i x ≤ 1
  full_pattern : ∀ J : Finset ℕ,
    ∀ᵐ x ∂μ.restrict (finitePattern allowed δ J), ∑ i ∈ J, q i x = 1

/-- The original atom mass plus the actual receipt of one assignment coordinate. -/
def mass (a : ℕ → ℝ) (q : ℕ → Lp ℝ 2 μ) (i : ℕ) : ℝ := a i + ∫ x, q i x ∂μ

/-- The actual squared-mass objective of the relaxed countable assignment. -/
def objective (a : ℕ → ℝ) (q : ℕ → Lp ℝ 2 μ) : ℝ := ∑' i, mass a q i ^ 2

/-- Each L² coordinate is genuinely integrable on the finite source measure. -/
theorem coordinate_integrable (q : ℕ → Lp ℝ 2 μ) (i : ℕ) : Integrable (q i) μ :=
  (Lp.memLp (q i)).integrable (by norm_num)

omit [IsFiniteMeasure μ] in
/-- Original nonnegative masses and nonnegative receipts give nonnegative final masses. -/
theorem Feasible.mass_nonneg {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (i : ℕ) : 0 ≤ mass a q i :=
  add_nonneg (ha i) (integral_nonneg_of_ae ((hq.box i).mono fun _ h => h.1))

/-- Every finite collection receives at most the entire finite source measure. -/
theorem Feasible.sum_mass_le {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a) (J : Finset ℕ) :
    ∑ i ∈ J, mass a q i ≤ (∑' i, a i) + μ.real univ := by
  have hA : (∑ i ∈ J, a i) ≤ ∑' i, a i := haSum.sum_le_tsum J (fun i _ => ha i)
  have hQ : (∑ i ∈ J, ∫ x, q i x ∂μ) ≤ μ.real univ := by
    rw [← integral_finsetSum J (fun i _ => coordinate_integrable q i)]
    have hbound := integral_mono_ae
      (integrable_finsetSum J (fun i _ => coordinate_integrable q i))
      (integrable_const (1 : ℝ)) (hq.partial_sum J)
    simpa using hbound
  simpa only [mass, Finset.sum_add_distrib] using add_le_add hA hQ

/-- Actual final masses are summable for every feasible relaxed assignment. -/
theorem Feasible.mass_summable {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a) : Summable (mass a q) :=
  summable_of_sum_le (hq.mass_nonneg ha) (hq.sum_mass_le ha haSum)

/-- The all-label mass bound follows from actual finite partial-supply constraints. -/
theorem Feasible.tsum_mass_le {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a) :
    (∑' i, mass a q i) ≤ (∑' i, a i) + μ.real univ :=
  (hq.mass_summable ha haSum).tsum_le_of_sum_le (hq.sum_mass_le ha haSum)

/-- Squared final masses are summable before the real objective is used. -/
theorem Feasible.square_mass_summable {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a) :
    Summable (fun i => mass a q i ^ 2) := by
  let M : ℝ := (∑' i, a i) + μ.real univ
  have hM : 0 ≤ M := by simpa using hq.sum_mass_le ha haSum ∅
  have hi (i : ℕ) : mass a q i ≤ M := by
    simpa using hq.sum_mass_le ha haSum {i}
  have hsq (i : ℕ) : mass a q i ^ 2 ≤ M * mass a q i := by
    nlinarith [mul_nonneg (hq.mass_nonneg ha i) (sub_nonneg.mpr (hi i))]
  apply summable_of_sum_le (fun i => sq_nonneg (mass a q i))
  intro J
  calc
    ∑ i ∈ J, mass a q i ^ 2 ≤ ∑ i ∈ J, M * mass a q i :=
      Finset.sum_le_sum (fun i _ => hsq i)
    _ = M * ∑ i ∈ J, mass a q i := (Finset.mul_sum J _ M).symm
    _ ≤ M * M := mul_le_mul_of_nonneg_left (hq.sum_mass_le ha haSum J) hM

/-- Literal finite patterns are measurable from the actual allowed sets and diffuse supply. -/
theorem measurableSet_finitePattern {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) (J : Finset ℕ) :
    MeasurableSet (finitePattern allowed δ J) := by
  have hi (i : ℕ) : MeasurableSet {x | i ∈ J ↔ x ∈ allowed i} := by
    by_cases h : i ∈ J
    · simpa only [h, true_iff, ofPred_mem_eq] using hallowed i
    · simpa only [h, false_iff, ← mem_compl_iff, ofPred_mem_eq] using (hallowed i).compl
  simp only [finitePattern, ofPred_and, ofPred_forall]
  exact (measurableSet_eq_fun hδ measurable_const).inter (MeasurableSet.iInter hi)

/-- Weak-dual coordinates are decoded by the actual Hilbert-space Riesz equivalence. -/
abbrev DualFamily (μ : Measure Ω) := ℕ → WeakDual ℝ (Lp ℝ 2 μ)

/-- A single weak-dual coordinate is represented by its actual Riesz L² vector. -/
def decodeCoordinate (d : WeakDual ℝ (Lp ℝ 2 μ)) : Lp ℝ 2 μ :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (WeakDual.toStrongDual d)

/-- The actual countable L² assignment represented by weak-dual coordinates. -/
def decode (d : DualFamily μ) : ℕ → Lp ℝ 2 μ := fun i => decodeCoordinate (d i)

/-- The weak-dual family of an actual L² assignment. -/
def encode (q : ℕ → Lp ℝ 2 μ) : DualFamily μ := fun i =>
  StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) (q i))

omit [IsFiniteMeasure μ] in
theorem decode_encode (q : ℕ → Lp ℝ 2 μ) : decode (encode q) = q := by
  funext i
  exact (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm_apply_apply (q i)

private def indicatorTest (s : Set Ω) (hs : MeasurableSet s) : Lp ℝ 2 μ :=
  indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)

private theorem setIntegral_decodeCoordinate (d : WeakDual ℝ (Lp ℝ 2 μ))
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ x in s, decodeCoordinate d x ∂μ) = d (indicatorTest s hs) := by
  rw [← L2.inner_indicatorConstLp_one hs (measure_ne_top μ s) (decodeCoordinate d),
    real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

private theorem setIntegral_decode (d : DualFamily μ) (i : ℕ)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ x in s, decode d i x ∂μ) = d i (indicatorTest s hs) :=
  setIntegral_decodeCoordinate (d i) s hs

/-- Actual coordinate receipts are continuous weak-dual evaluations. -/
theorem mass_decode (a : ℕ → ℝ) (d : DualFamily μ) (i : ℕ) :
    mass a (decode d) i = a i + d i (Lp.const 2 μ (1 : ℝ)) := by
  unfold mass
  congr 1
  simpa only [setIntegral_univ, indicatorTest, indicatorConstLp_univ] using
    setIntegral_decode d i univ MeasurableSet.univ

private theorem norm_le_const_of_box {f : Lp ℝ 2 μ}
    (hf : ∀ᵐ x ∂μ, f x ∈ Icc (0 : ℝ) 1) : ‖f‖ ≤ ‖Lp.const 2 μ (1 : ℝ)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hf, Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hconst
  rw [hconst, Function.const_apply, Real.norm_of_nonneg hx.1, norm_one]
  exact hx.2

/-- The feasible set in the actual product weak-dual coordinates. -/
def dualFeasibleSet (allowed : ℕ → Set Ω) (δ : Ω → ℝ) : Set (DualFamily μ) :=
  {d | Feasible allowed δ (decode d)}

omit [IsFiniteMeasure μ] in
theorem encode_mem_dualFeasibleSet {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) :
    encode q ∈ dualFeasibleSet allowed δ := by
  simpa only [dualFeasibleSet, mem_ofPred_eq, decode_encode] using hq

private theorem setIntegral_sum_decode (d : DualFamily μ) (J : Finset ℕ)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ x in s, ∑ i ∈ J, decode d i x ∂μ) = ∑ i ∈ J, d i (indicatorTest s hs) := by
  rw [integral_finsetSum J (fun i _ => (coordinate_integrable (decode d) i).integrableOn)]
  exact Finset.sum_congr rfl (fun i _ => setIntegral_decode d i s hs)

private structure IntegralFeasible (allowed : ℕ → Set Ω) (δ : Ω → ℝ)
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) (d : DualFamily μ) : Prop where
  nonneg_test : ∀ (i : ℕ) (s : Set Ω) (hs : MeasurableSet s),
    0 ≤ d i (indicatorTest s hs)
  upper_test : ∀ (i : ℕ) (s : Set Ω) (hs : MeasurableSet s),
    d i (indicatorTest s hs) ≤ μ.real s
  support_test : ∀ i, d i (indicatorTest (allowed i)ᶜ (hallowed i).compl) = 0
  partial_test : ∀ (J : Finset ℕ) (s : Set Ω) (hs : MeasurableSet s),
    ∑ i ∈ J, d i (indicatorTest s hs) ≤ μ.real s
  pattern_test : ∀ J : Finset ℕ,
    ∑ i ∈ J, d i (indicatorTest (finitePattern allowed δ J)
      (measurableSet_finitePattern hallowed hδ J)) = μ.real (finitePattern allowed δ J)

private theorem feasible_of_integralFeasible {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) (d : DualFamily μ)
    (h : IntegralFeasible allowed δ hallowed hδ d) : Feasible allowed δ (decode d) := by
  have hn (i : ℕ) : ∀ᵐ x ∂μ, 0 ≤ decode d i x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg (coordinate_integrable (decode d) i)
    intro s hs _
    rw [setIntegral_decode d i s hs]
    exact h.nonneg_test i s hs
  have hu (i : ℕ) : ∀ᵐ x ∂μ, decode d i x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le (coordinate_integrable (decode d) i) (integrable_const 1)
    intro s hs _
    rw [setIntegral_decode d i s hs]
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using h.upper_test i s hs
  have hp (J : Finset ℕ) : ∀ᵐ x ∂μ, ∑ i ∈ J, decode d i x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le
      (integrable_finsetSum J (fun i _ => coordinate_integrable (decode d) i)) (integrable_const 1)
    intro s hs _
    rw [setIntegral_sum_decode d J s hs]
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using h.partial_test J s hs
  refine ⟨fun i => ?_, ?_, hp, ?_⟩
  · filter_upwards [hn i, hu i] with x hx hy
    exact ⟨hx, hy⟩
  · intro i
    have hzero : (∫ x in (allowed i)ᶜ, decode d i x ∂μ) = 0 :=
      (setIntegral_decode d i _ (hallowed i).compl).trans (h.support_test i)
    have heq := (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae (hn i))
      (coordinate_integrable (decode d) i).integrableOn).mp hzero
    have heq' := (ae_restrict_iff' (hallowed i).compl).mp heq
    simpa only [mem_compl_iff, Pi.zero_apply] using heq'
  · intro J
    let s := finitePattern allowed δ J
    have hs : MeasurableSet s := measurableSet_finitePattern hallowed hδ J
    have hi : Integrable (fun x => 1 - ∑ i ∈ J, decode d i x) μ :=
      (integrable_const 1).sub
        (integrable_finsetSum J (fun i _ => coordinate_integrable (decode d) i))
    have hnonneg : ∀ᵐ x ∂μ, 0 ≤ 1 - ∑ i ∈ J, decode d i x :=
      (hp J).mono (fun _ hx => sub_nonneg.mpr hx)
    have hzero : (∫ x in s, 1 - ∑ i ∈ J, decode d i x ∂μ) = 0 := by
      rw [integral_sub (integrable_const 1)
        (integrable_finsetSum J (fun i _ => (coordinate_integrable (decode d) i).integrableOn)),
        setIntegral_sum_decode d J s hs]
      simp only [setIntegral_const, smul_eq_mul, mul_one]
      exact sub_eq_zero.mpr (h.pattern_test J).symm
    have heq := (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hnonneg)
      hi.integrableOn).mp hzero
    filter_upwards [heq] with x hx
    change 1 - ∑ i ∈ J, decode d i x = 0 at hx
    linarith

private theorem integralFeasible_of_feasible {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) (d : DualFamily μ)
    (h : Feasible allowed δ (decode d)) : IntegralFeasible allowed δ hallowed hδ d := by
  constructor
  · intro i s hs
    rw [← setIntegral_decode d i s hs]
    exact setIntegral_nonneg_of_ae ((h.box i).mono fun _ hx => hx.1)
  · intro i s hs
    rw [← setIntegral_decode d i s hs]
    have hb : (∫ x in s, decode d i x ∂μ) ≤ ∫ _ in s, (1 : ℝ) ∂μ :=
      setIntegral_mono_ae_restrict (coordinate_integrable (decode d) i).integrableOn
        (integrable_const 1) (ae_restrict_of_ae ((h.box i).mono fun _ hx => hx.2))
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using hb
  · intro i
    rw [← setIntegral_decode d i _ (hallowed i).compl]
    have heq : (decode d i : Ω → ℝ) =ᵐ[μ.restrict (allowed i)ᶜ] 0 := by
      change ∀ᵐ x ∂μ.restrict (allowed i)ᶜ, decode d i x = 0
      rw [ae_restrict_iff' (hallowed i).compl]
      simpa only [mem_compl_iff, Pi.zero_apply] using h.support i
    exact (integral_congr_ae heq).trans (by simp)
  · intro J s hs
    rw [← setIntegral_sum_decode d J s hs]
    have hb : (∫ x in s, ∑ i ∈ J, decode d i x ∂μ) ≤ ∫ _ in s, (1 : ℝ) ∂μ :=
      setIntegral_mono_ae_restrict
        (integrable_finsetSum J (fun i _ => coordinate_integrable (decode d) i)).integrableOn
        (integrable_const 1) (ae_restrict_of_ae (h.partial_sum J))
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using hb
  · intro J
    rw [← setIntegral_sum_decode d J _ (measurableSet_finitePattern hallowed hδ J)]
    have heq := integral_congr_ae (h.full_pattern J)
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] using heq

private theorem isClosed_integralFeasible {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) :
    IsClosed {d : DualFamily μ | IntegralFeasible allowed δ hallowed hδ d} := by
  let A : Set (DualFamily μ) := {d | ∀ (i : ℕ) (s : Set Ω) (hs : MeasurableSet s),
    0 ≤ d i (indicatorTest s hs)}
  let B : Set (DualFamily μ) := {d | ∀ (i : ℕ) (s : Set Ω) (hs : MeasurableSet s),
    d i (indicatorTest s hs) ≤ μ.real s}
  let C : Set (DualFamily μ) := {d | ∀ i,
    d i (indicatorTest (allowed i)ᶜ (hallowed i).compl) = 0}
  let D : Set (DualFamily μ) := {d | ∀ (J : Finset ℕ) (s : Set Ω) (hs : MeasurableSet s),
    ∑ i ∈ J, d i (indicatorTest s hs) ≤ μ.real s}
  let E : Set (DualFamily μ) := {d | ∀ J : Finset ℕ,
    ∑ i ∈ J, d i (indicatorTest (finitePattern allowed δ J)
      (measurableSet_finitePattern hallowed hδ J)) = μ.real (finitePattern allowed δ J)}
  have hA : IsClosed A := by
    simp only [A, ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun s => isClosed_iInter (fun hs =>
      isClosed_le continuous_const ((WeakDual.eval_continuous _).comp (continuous_apply i)))))
  have hB : IsClosed B := by
    simp only [B, ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun s => isClosed_iInter (fun hs =>
      isClosed_le ((WeakDual.eval_continuous _).comp (continuous_apply i)) continuous_const)))
  have hC : IsClosed C := by
    simp only [C, ofPred_forall]
    exact isClosed_iInter (fun i =>
      isClosed_eq ((WeakDual.eval_continuous _).comp (continuous_apply i)) continuous_const)
  have hD : IsClosed D := by
    simp only [D, ofPred_forall]
    exact isClosed_iInter (fun J => isClosed_iInter (fun s => isClosed_iInter (fun hs =>
      isClosed_le (continuous_finsetSum J (fun i _ =>
        (WeakDual.eval_continuous _).comp (continuous_apply i))) continuous_const)))
  have hE : IsClosed E := by
    simp only [E, ofPred_forall]
    exact isClosed_iInter (fun J => isClosed_eq (continuous_finsetSum J (fun i _ =>
      (WeakDual.eval_continuous _).comp (continuous_apply i))) continuous_const)
  have heq : {d : DualFamily μ | IntegralFeasible allowed δ hallowed hδ d} =
      A ∩ (B ∩ (C ∩ (D ∩ E))) := by
    ext d
    constructor
    · intro h
      exact ⟨h.nonneg_test, h.upper_test, h.support_test, h.partial_test, h.pattern_test⟩
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  rw [heq]
  exact hA.inter (hB.inter (hC.inter (hD.inter hE)))

/-- Every actual AE feasibility constraint is closed in the product weak-dual coordinates. -/
theorem isClosed_dualFeasibleSet {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) :
    IsClosed (dualFeasibleSet (μ := μ) allowed δ) := by
  have heq : dualFeasibleSet (μ := μ) allowed δ =
      {d | IntegralFeasible allowed δ hallowed hδ d} := by
    ext d
    exact ⟨integralFeasible_of_feasible hallowed hδ d,
      feasible_of_integralFeasible hallowed hδ d⟩
  rw [heq]
  exact isClosed_integralFeasible hallowed hδ

/-- The actual relaxed feasible set is compact, by bounded Riesz coordinates
and the proved closed integral-test description of all its constraints. -/
theorem isCompact_dualFeasibleSet {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) :
    IsCompact (dualFeasibleSet (μ := μ) allowed δ) := by
  let C : ℝ := ‖Lp.const 2 μ (1 : ℝ)‖
  apply (isCompact_pi_infinite (fun _ : ℕ =>
    WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := Lp ℝ 2 μ) 0 C)).of_isClosed_subset
    (isClosed_dualFeasibleSet hallowed hδ)
  intro d hd i
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rw [← (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm.norm_map]
  exact norm_le_const_of_box (hd.box i)

end Erdos1017.ReverseAssignment

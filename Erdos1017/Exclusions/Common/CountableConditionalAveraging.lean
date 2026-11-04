module

public import Erdos1017.Exclusions.Common.ConditionalRootedCounts
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPartitionAverages

/-!
# Conditional averaging over countable labels

This module defines the averaged `charge` of a model over countably many label
fibers and proves it is measurable, symmetric, equal to the conditional
expectation on positive fibers, total-charge preserving, inside the charge box,
zero on nonedges, and feasible at every order (`full_scalar_tests`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.ConditionalAveraging

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
  [Countable ι] [DiscreteMeasurableSpace ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Independent conditioning on two regions is precisely conditioning
the original product law on their rectangle. -/
theorem cond_prod_rectangle (s t : Set Ω) :
    (cond μ s).prod (cond μ t) = cond (μ.prod μ) (s ×ˢ t) := by
  simp only [ProbabilityTheory.cond, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.prod_restrict, Measure.prod_prod]
  rw [ENNReal.mul_inv (Or.inr (measure_ne_top μ t)) (Or.inl (measure_ne_top μ s)),
    mul_comm ((μ t)⁻¹) ((μ s)⁻¹)]

/-- Literal pair averages retain the original countable fiber labels. -/
def charge (q : Ω → ι) (Y : Ω → Ω → ℝ) (x y : Ω) : ℝ :=
  FiniteArity.regionPairCharge μ Y (fun i => q ⁻¹' {i}) (q x) (q y)

omit [IsProbabilityMeasure μ] in
/-- Countable labels make every literal averaged block coefficient
measurable without a continuity or finite-label assumption. -/
theorem measurable_charge (q : Ω → ι) (hq : Measurable q) (Y : Ω → Ω → ℝ) :
    Measurable (Function.uncurry (charge (μ := μ) q Y)) := by
  change Measurable (fun p : Ω × Ω =>
    FiniteArity.regionPairCharge μ Y (fun i => q ⁻¹' {i}) (q p.1) (q p.2))
  have hcoeff : Measurable (fun p : ι × ι =>
      FiniteArity.regionPairCharge μ Y (fun i => q ⁻¹' {i}) p.1 p.2) :=
    measurable_of_countable _
  have hQ : Measurable (fun p : Ω × Ω => (q p.1, q p.2)) :=
    (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  simpa only [Function.comp_def] using hcoeff.comp hQ

omit [MeasurableSpace ι] [Countable ι] [DiscreteMeasurableSpace ι]
  [IsProbabilityMeasure μ] in
/-- Symmetry is preserved pointwise by the actual pair-law averaging. -/
theorem charge_symm (q : Ω → ι) (Y : Ω → Ω → ℝ)
    (hYsym : ∀ x y, Y x y = Y y x) (x y : Ω) :
    charge (μ := μ) q Y x y = charge (μ := μ) q Y y x :=
  FiniteArity.regionPairCharge_symm μ Y hYsym _ _ _

/-- On positive actual fibers, the literal independent pair average is
the real conditional expectation for the pair-label sigma algebra. -/
theorem charge_eq_condExp (q : Ω → ι) (hq : Measurable q)
    (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (Y : Ω → Ω → ℝ)
    (hY : Integrable (Function.uncurry Y) (μ.prod μ)) (p : Ω × Ω) :
    charge (μ := μ) q Y p.1 p.2 =
      ((μ.prod μ)[Function.uncurry Y |
        (inferInstance : MeasurableSpace (ι × ι)).comap (fun z : Ω × Ω => (q z.1, q z.2))]) p := by
  let Q := fun z : Ω × Ω => (q z.1, q z.2)
  have hQ : Measurable Q := (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  have hfiber : Q ⁻¹' {Q p} = (q ⁻¹' {q p.1}) ×ˢ (q ⁻¹' {q p.2}) := by
    ext z
    simp [Q]
  have hp : (μ.prod μ) (Q ⁻¹' {Q p}) ≠ 0 := by
    rw [hfiber, Measure.prod_prod]
    exact mul_ne_zero (hpos _).ne' (hpos _).ne'
  have he := PhysicalPartitionAverages.fiberAverage_eq_condExp (μ.prod μ) Q hQ hY p hp
  rw [hfiber, setAverage_eq'] at he
  change (∫ z, Function.uncurry Y z ∂cond (μ.prod μ)
    ((q ⁻¹' {q p.1}) ×ˢ (q ⁻¹' {q p.2}))) = _ at he
  rw [← cond_prod_rectangle] at he
  exact he

/-- Actual averaging preserves the total original charge exactly. -/
theorem integral_charge (q : Ω → ι) (hq : Measurable q)
    (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (Y : Ω → Ω → ℝ)
    (hY : Integrable (Function.uncurry Y) (μ.prod μ)) :
    (∫ p, charge (μ := μ) q Y p.1 p.2 ∂μ.prod μ) = ∫ p, Y p.1 p.2 ∂μ.prod μ := by
  have hQ : Measurable (fun z : Ω × Ω => (q z.1, q z.2)) :=
    (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  rw [integral_congr_ae (Eventually.of_forall (charge_eq_condExp q hq hpos Y hY))]
  exact integral_condExp hQ.comap_le

/-- Every pointwise clique of the actual label graph satisfies the
averaged charge test, by independently sampling its original positive
fibers. The original all-order feasibility is the only test premise. -/
theorem tupleCharge_le_one (q : Ω → ι) (hq : Measurable q)
    (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (H : ι → ι → Bool)
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hA : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = H (q p.1) (q p.2))
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    {n : ℕ} (v : Fin n → Ω) (hv : FiniteArity.TupleClique (fun x y => H (q x) (q y)) v) :
    FiniteArity.tupleCharge (charge (μ := μ) q Y) v ≤ 1 := by
  exact FiniteArity.conditional_clique_average_le_one (fun i => q ⁻¹' {q (v i)})
    (fun i => hq (measurableSet_singleton _)) (fun i => hpos _) A Y hY B hbound (hfull n)
    (fun i j hij => hA.mono (fun p hp hx hy => by
      change q p.1 = q (v i) at hx
      change q p.2 = q (v j) at hy
      rw [hp, hx, hy]
      exact hv i j hij))

/-- All orders of the same-carrier scalar averaged model are genuinely
feasible; the old exceptional tests are discharged through conditional laws. -/
theorem full_scalar_tests (q : Ω → ι) (hq : Measurable q)
    (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (H : ι → ι → Bool)
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hA : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = H (q p.1) (q p.2))
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) (n : ℕ) :
    FiniteArity.FeasibleOrder μ (fun x y => H (q x) (q y)) (charge (μ := μ) q Y) n :=
  Eventually.of_forall (fun v hv => tupleCharge_le_one q hq hpos H A Y hY B hbound hA hfull v hv)

omit [MeasurableSpace ι] [Countable ι] [DiscreteMeasurableSpace ι] in
/-- The actual conditional average stays in the unchanged charge box. -/
theorem charge_mem_Icc (q : Ω → ι) (hpos : ∀ i, 0 < μ (q ⁻¹' {i}))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (hbound : ∀ x y, Y x y ∈ Icc (-3 : ℝ) 1) (x y : Ω) :
    charge (μ := μ) q Y x y ∈ Icc (-3 : ℝ) 1 := by
  let σ := cond μ (q ⁻¹' {q x})
  let τ := cond μ (q ⁻¹' {q y})
  let : IsProbabilityMeasure σ := cond_isProbabilityMeasure (hpos _).ne'
  let : IsProbabilityMeasure τ := cond_isProbabilityMeasure (hpos _).ne'
  have hi : Integrable (Function.uncurry Y) (σ.prod τ) := Integrable.of_bound
    hY.aestronglyMeasurable 3 (Eventually.of_forall (fun p => by
      have hp := hbound p.1 p.2
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨hp.1, hp.2.trans (by norm_num)⟩))
  change (∫ p, Y p.1 p.2 ∂σ.prod τ) ∈ Icc (-3 : ℝ) 1
  constructor
  · have h := integral_mono_ae (integrable_const (-3 : ℝ)) hi
      (Eventually.of_forall (fun p => (hbound p.1 p.2).1))
    simpa only [Function.uncurry, integral_const, probReal_univ, one_smul] using h
  · have h := integral_mono_ae hi (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun p => (hbound p.1 p.2).2))
    simpa only [Function.uncurry, integral_const, probReal_univ, one_smul] using h

/-- A nonedge block has actual average zero, since both the old
adjacency and old nonedge charge hold under its conditional pair law. -/
theorem charge_zero_of_nonedge (q : Ω → ι) (hq : Measurable q)
    (H : ι → ι → Bool) (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = H (q p.1) (q p.2))
    (hzero : ∀ x y, A x y = false → Y x y = 0) (x y : Ω)
    (hH : H (q x) (q y) = false) : charge (μ := μ) q Y x y = 0 := by
  apply integral_eq_zero_of_ae
  have hac : (cond μ (q ⁻¹' {q x})).prod (cond μ (q ⁻¹' {q y})) ≪ μ.prod μ :=
    cond_absolutelyContinuous.prod cond_absolutelyContinuous
  filter_upwards [hac.ae_le hA,
    Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hq (measurableSet_singleton _))),
    Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hq (measurableSet_singleton _)))]
    with p hp hx hy
  apply hzero
  change q p.1 = q x at hx
  change q p.2 = q y at hy
  rwa [hp, hx, hy]

omit [MeasurableSpace ι] [Countable ι] [DiscreteMeasurableSpace ι] in
/-- Original pair-AE equal charges have identical literal conditional
averages at every pair of labels, by actual absolute continuity. -/
theorem charge_congr_ae (q : Ω → ι) (Y Z : Ω → Ω → ℝ)
    (h : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Z p.1 p.2) (x y : Ω) :
    charge (μ := μ) q Y x y = charge (μ := μ) q Z x y := by
  apply integral_congr_ae
  exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le h

end Erdos1017.ConditionalAveraging

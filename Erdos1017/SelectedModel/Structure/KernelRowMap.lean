module

public import Erdos1017.Models.Kernel.KernelCompactness
public import Erdos1017.SelectedModel.ZeroClass.IndexOneZeroClasses
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Strongly measurable row maps of bounded kernels

An AE bounded joint kernel has a strongly measurable `L²` row map, clipped on a
null set so the norm bound holds at every point, and positive whole-row fibers
are countable with squares exhausting the pair mass of equal kernel rows.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Jointly strongly measurable bounded kernels have strongly measurable L² rows.
The distance to any fixed L² vector is the square root of a measurable integral. -/
theorem exists_stronglyMeasurable_rowMap_of_bound
    (K : Ω → Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : StronglyMeasurable (fun p : Ω × Ω => K p.1 p.2))
    (hbound : ∀ x y, ‖K x y‖ ≤ B) :
    ∃ R : Ω → Lp ℝ 2 μ, StronglyMeasurable R ∧
      (∀ x, (R x : Ω → ℝ) =ᵐ[μ] K x) ∧ (∀ x, ‖R x‖ ≤ B) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hmem (x : Ω) : MemLp (K x) 2 μ :=
    MemLp.of_bound (hK.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      B (Filter.Eventually.of_forall (hbound x))
  let R : Ω → Lp ℝ 2 μ := fun x => (hmem x).toLp (K x)
  have hrow (x : Ω) : (R x : Ω → ℝ) =ᵐ[μ] K x := (hmem x).coeFn_toLp
  have hdist (f : Lp ℝ 2 μ) : Measurable (fun x => dist (R x) f) := by
    have hi : StronglyMeasurable (fun x => ∫ y, (K x y - f y) ^ 2 ∂μ) :=
      ((hK.sub ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)).pow 2).integral_prod_right'
    have heq (x : Ω) : (∫ y, (K x y - f y) ^ 2 ∂μ) = ‖R x - f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hrow x, Lp.coeFn_sub (R x) f] with y hy hsub
      simp only [hsub, Pi.sub_apply, hy, RCLike.inner_apply, conj_trivial]
      ring
    have hs := (Real.continuous_sqrt.comp_stronglyMeasurable hi).measurable
    simpa only [heq, Real.sqrt_sq (norm_nonneg _), dist_eq_norm] using hs
  have hb : TopologicalSpace.IsTopologicalBasis
      {s : Set (Lp ℝ 2 μ) | ∃ f r, s = Metric.ball f r} := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨f, r, rfl⟩
      exact Metric.isOpen_ball
    · intro f s hf hs
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs f hf
      exact ⟨Metric.ball f r, ⟨f, r, rfl⟩, Metric.mem_ball_self hr, hrs⟩
  have hR : Measurable R := by
    change @Measurable _ _ _ (borel (Lp ℝ 2 μ)) R
    rw [hb.borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro s ⟨f, r, rfl⟩
    exact (hdist f) measurableSet_Iio
  refine ⟨R, hR.stronglyMeasurable, hrow, ?_⟩
  intro x
  have hb : ∀ᵐ y ∂μ, ‖R x y‖ ≤ B := by
    filter_upwards [hrow x] with y hy
    rw [hy]
    exact hbound x y
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hB hb

/-- An AE bounded joint kernel has an actual strongly measurable row map. The
representative is clipped on a null set, giving the norm bound at every point. -/
theorem exists_stronglyMeasurable_rowMap
    (K : Ω → Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hbound : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) :
    ∃ R : Ω → Lp ℝ 2 μ, StronglyMeasurable R ∧
      (∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) ∧ (∀ x, ‖R x‖ ≤ B) := by
  let g := hK.mk (fun p : Ω × Ω => K p.1 p.2)
  let K₀ : Ω → Ω → ℝ := fun x y => max (-B) (min B (g (x, y)))
  have hK₀ : StronglyMeasurable (fun p : Ω × Ω => K₀ p.1 p.2) :=
    stronglyMeasurable_const.sup (stronglyMeasurable_const.inf hK.stronglyMeasurable_mk)
  have hb₀ (x y : Ω) : ‖K₀ x y‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (neg_le_self hB) (min_le_left _ _)⟩
  have heq : (fun p : Ω × Ω => K₀ p.1 p.2) =ᵐ[μ.prod μ]
      (fun p : Ω × Ω => K p.1 p.2) := by
    filter_upwards [hK.ae_eq_mk, hbound] with p hp hb
    have h := abs_le.mp (show |K p.1 p.2| ≤ B by simpa using hb)
    dsimp [K₀, g]
    rw [← hp, min_eq_right h.2, max_eq_right h.1]
  obtain ⟨R, hR, hrow, hn⟩ :=
    exists_stronglyMeasurable_rowMap_of_bound (μ := μ) K₀ B hB hK₀ hb₀
  refine ⟨R, hR, ?_, hn⟩
  filter_upwards [Measure.ae_ae_of_ae_prod heq] with x hx
  exact (hrow x).trans hx

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The common AE set of represented rows gives an AE pair equivalence. -/
theorem ae_rowMap_eq_iff (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) :
    ∀ᵐ p ∂μ.prod μ, R p.1 = R p.2 ↔ K p.1 =ᵐ[μ] K p.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrow,
    Measure.quasiMeasurePreserving_snd.ae hrow] with p hx hy
  constructor
  · intro h
    have heq : (R p.1 : Ω → ℝ) =ᵐ[μ] (R p.2 : Ω → ℝ) := by rw [h]
    exact hx.symm.trans (heq.trans hy)
  · intro h
    exact Lp.ext (hx.trans (h.trans hy.symm))

/-- Positive whole-row fibers are countable, and their squares exhaust the
pair mass of equal kernel rows. No pointwise row representation is assumed. -/
theorem exists_countable_positive_row_fibers
    (K : Ω → Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hbound : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) :
    ∃ (R : Ω → Lp ℝ 2 μ) (A : Set (Lp ℝ 2 μ)),
      StronglyMeasurable R ∧
      (∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) ∧ (∀ x, ‖R x‖ ≤ B) ∧
      A.Countable ∧
      (∀ v ∈ A, MeasurableSet {x | R x = v} ∧ 0 < μ {x | R x = v}) ∧
      A.Pairwise (fun v w => Disjoint {x | R x = v} {x | R x = w}) ∧
      (∀ᵐ p ∂μ.prod μ, (K p.1 =ᵐ[μ] K p.2) ↔
        ∃ v ∈ A, R p.1 = v ∧ R p.2 = v) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  obtain ⟨R, hR, hrow, hn⟩ := exists_stronglyMeasurable_rowMap K B hB hK hbound
  refine ⟨R, positiveFiberValues μ R, hR, hrow, hn,
    positiveFiberValues_countable R hR.measurable, ?_, ?_, ?_⟩
  · intro v hv
    exact ⟨hR.measurable (measurableSet_singleton v), hv⟩
  · intro v _ w _ hne
    exact Set.disjoint_left.mpr (fun x hx hy => hne (hx.symm.trans hy))
  · filter_upwards [ae_rowMap_eq_iff K R hrow,
      ae_equal_features_mem_positiveFiberValues R hR.measurable] with p hp ha
    constructor
    · intro h
      have heq := hp.mpr h
      exact ⟨R p.1, ha heq, rfl, heq.symm⟩
    · rintro ⟨v, _, hx, hy⟩
      exact hp.mp (hx.trans hy.symm)

end Erdos1017.KernelOperator

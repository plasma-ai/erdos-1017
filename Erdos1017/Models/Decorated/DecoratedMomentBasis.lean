module

public import Erdos1017.Models.Decorated.DecoratedKernel
public import Graphon.CutDistance
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Dense test sequences for color moments

Compact metric color spaces have a countable dense sequence of normalized tests,
the conditional-moment graphon map is Lipschitz in uniform test distance, and
convergence on one dense test sequence extends to every normalized continuous
color test on the same sequence of kernels in the same frame.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.DecoratedKernel

/-- Continuous color tests already normalized to the graphon range. -/
abbrev Test (C : Type*) [TopologicalSpace C] :=
  {f : C(C, ℝ) // ∀ c, f c ∈ Set.Icc 0 1}

instance {C : Type*} [TopologicalSpace C] : Nonempty (Test C) :=
  ⟨⟨0, fun _ => by simp⟩⟩

/-- Compact metric color spaces have a countable dense sequence of normalized tests. -/
theorem exists_dense_tests (C : Type*) [MetricSpace C] [CompactSpace C] :
    ∃ tests : ℕ → Test C, DenseRange tests :=
  TopologicalSpace.exists_dense_seq (Test C)

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  [MetricSpace C] [CompactSpace C] [BorelSpace C]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Uniformly close color tests have uniformly close actual conditional moments. -/
theorem moment_dist_le (W : DecoratedKernel Ω C μ) (f g : Test C) (p : Ω × Ω) :
    |W.moment f.1 p - W.moment g.1 p| ≤ dist f g := by
  have hf : Integrable f.1 (W.kernel p) :=
    (BoundedContinuousFunction.mkOfCompact f.1).integrable _
  have hg : Integrable g.1 (W.kernel p) :=
    (BoundedContinuousFunction.mkOfCompact g.1).integrable _
  rw [Subtype.dist_eq, moment, moment, ← integral_sub hf hg]
  have h := norm_integral_le_of_norm_le_const
    (μ := W.kernel p) (f := fun c => f.1 c - g.1 c)
    (Filter.Eventually.of_forall (fun c => by
      simpa only [Real.norm_eq_abs, ← Real.dist_eq] using f.1.dist_apply_le_dist (g := g.1) c))
  simpa [Real.norm_eq_abs, Measure.real] using h

/-- The conditional-moment graphon map is Lipschitz for uniform color-test distance. -/
theorem momentGraphon_lipschitz (W : DecoratedKernel Ω C μ) (f g : Test C) :
    Graphon.cutNormDiff
      (W.momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2)
      (W.momentGraphon g.1 g.1.continuous.stronglyMeasurable g.2) ≤ dist f g := by
  have hbound : ∀ᵐ p ∂μ.prod μ,
      |(W.momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2).toAEEqFun p -
        (W.momentGraphon g.1 g.1.continuous.stronglyMeasurable g.2).toAEEqFun p| ≤ dist f g := by
    filter_upwards [AEEqFun.coeFn_mk (W.moment f.1)
      (W.stronglyMeasurable_moment f.1.continuous.stronglyMeasurable).aestronglyMeasurable,
      AEEqFun.coeFn_mk (W.moment g.1)
        (W.stronglyMeasurable_moment g.1.continuous.stronglyMeasurable).aestronglyMeasurable]
      with p hf hg
    simpa only [momentGraphon, hf, hg] using W.moment_dist_le f g p
  unfold Graphon.cutNormDiff
  apply Real.iSup_le _ dist_nonneg
  intro S
  apply Real.iSup_le _ dist_nonneg
  intro _
  apply Real.iSup_le _ dist_nonneg
  intro T
  apply Real.iSup_le _ dist_nonneg
  intro _
  simp only [Graphon.rectIntegralDiff]
  have h := norm_integral_le_of_norm_le_const
    (μ := (μ.prod μ).restrict (S ×ˢ T))
    (f := fun p =>
      (W.momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2).toAEEqFun p -
        (W.momentGraphon g.1 g.1.continuous.stronglyMeasurable g.2).toAEEqFun p)
    (C := dist f g)
    (by simpa only [Real.norm_eq_abs] using ae_restrict_of_ae hbound)
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right dist_nonneg (by
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      (measureReal_le_one (μ := μ.prod μ) (s := S ×ˢ T))))

/-- Convergence on one dense test sequence extends to every normalized continuous
color test on the same sequence of decorated kernels, with the same frame. -/
theorem momentGraphon_converges_of_dense_tests
    (tests : ℕ → Test C) (hdense : DenseRange tests)
    (W : ℕ → DecoratedKernel Ω C μ) (V : DecoratedKernel Ω C μ)
    (hconv : ∀ j ε, 0 < ε → ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff
        ((W n).momentGraphon (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2)
        (V.momentGraphon (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2) < ε) :
    ∀ (f : Test C) ε, 0 < ε → ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff
        ((W n).momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2)
        (V.momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2) < ε := by
  intro f ε hε
  obtain ⟨j, hj⟩ := hdense.exists_dist_lt f (by positivity : 0 < ε / 3)
  obtain ⟨N, hN⟩ := hconv j (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := Graphon.cutNormDiff_triangle
    ((W n).momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2)
    ((W n).momentGraphon (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2)
    (V.momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2)
  have h2 := Graphon.cutNormDiff_triangle
    ((W n).momentGraphon (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2)
    (V.momentGraphon (tests j).1 (tests j).1.continuous.stronglyMeasurable (tests j).2)
    (V.momentGraphon f.1 f.1.continuous.stronglyMeasurable f.2)
  have hleft := (W n).momentGraphon_lipschitz f (tests j)
  have hright := V.momentGraphon_lipschitz (tests j) f
  rw [dist_comm (tests j) f] at hright
  linarith [hN n hn]

end Erdos1017.DecoratedKernel

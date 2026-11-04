module

public import Erdos1017.Models.Decorated.DecoratedCompactness
public import Erdos1017.Models.Capped.CappedTransport
public import Erdos1017.Models.Decorated.DecoratedCountingConvergence

/-!
# Compactness of capped models under sampled tests

Weak convergence of the joint laws preserves continuous color-moment averages,
density and objective, and finite feasibility is closed under convergence of the
continuous sample tests, so capped models have subsequential limits that keep
the imposed clique orders with density and objective converging.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.DecoratedKernel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  [MetricSpace Ω] [MetricSpace C] [CompactSpace Ω] [CompactSpace C]
  [BorelSpace Ω] [BorelSpace C] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Weak convergence of the actual joint laws preserves every continuous
color-moment average, including signed tests. -/
theorem integral_moment_tendsto_of_jointLaw
    (W : ℕ → DecoratedKernel Ω C μ) (V : DecoratedKernel Ω C μ)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw))
    (f : C(C, ℝ)) :
    Tendsto (fun n => ∫ p, (W n).moment f p ∂μ.prod μ) atTop
      (𝓝 (∫ p, V.moment f p ∂μ.prod μ)) := by
  let F : C((Ω × Ω) × C, ℝ) :=
    ⟨fun z => f z.2, f.continuous.comp continuous_snd⟩
  have heq (X : DecoratedKernel Ω C μ) :
      (∫ z, F z ∂(X.jointLaw : Measure _)) = ∫ p, X.moment f p ∂μ.prod μ := by
    rw [X.integral_jointLaw (Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Eventually.of_forall fun z => F.norm_coe_le_norm z))]
    rfl
  have h := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto
    V.jointLaw |>.comp hweak
  change Tendsto (fun n => ∫ z, F z ∂((W n).jointLaw : Measure _)) atTop
    (𝓝 (∫ z, F z ∂(V.jointLaw : Measure _))) at h
  simpa only [heq] using h

end Erdos1017.DecoratedKernel

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Convergence of the continuous violation expectation gives convergence
of the original nonnegative capped test integral. -/
theorem testIntegral_tendsto_of_continuousTestIntegral
    (W : ℕ → Model Ω μ) (V : Model Ω μ) (n : ℕ)
    (hconv : Tendsto (fun k => continuousTestIntegral (W k) n
      ⟨violation, continuous_violation n⟩) atTop
      (𝓝 (continuousTestIntegral V n ⟨violation, continuous_violation n⟩))) :
    Tendsto (fun k => testIntegral (W k) n) atTop (𝓝 (testIntegral V n)) := by
  simp_rw [testIntegral_eq_ofReal_continuousTestIntegral]
  exact ENNReal.continuous_ofReal.tendsto _ |>.comp hconv

/-- Finite feasibility is closed under convergence of the actual continuous
sample tests. The imposed orders remain exactly those bounded by `r`. -/
theorem feasible_of_continuousTestIntegral_tendsto
    (W : ℕ → Model Ω μ) (V : Model Ω μ) (r : ℕ)
    (hW : ∀ k, Feasible r (W k))
    (hconv : ∀ n, 2 ≤ n → n ≤ r →
      Tendsto (fun k => continuousTestIntegral (W k) n
        ⟨violation, continuous_violation n⟩) atTop
        (𝓝 (continuousTestIntegral V n ⟨violation, continuous_violation n⟩))) :
    Feasible r V := by
  apply (feasible_iff_testIntegral V r).mpr
  intro n hn hnr
  have hzero (k : ℕ) :
      continuousTestIntegral (W k) n ⟨violation, continuous_violation n⟩ = 0 := by
    have ht := (feasible_iff_testIntegral (W k) r).mp (hW k) n hn hnr
    rw [testIntegral_eq_ofReal_continuousTestIntegral] at ht
    apply le_antisymm (ENNReal.ofReal_eq_zero.mp ht)
    exact integral_nonneg (fun _ => integral_nonneg violation_nonneg)
  have hv : continuousTestIntegral V n ⟨violation, continuous_violation n⟩ = 0 := by
    apply tendsto_nhds_unique (hconv n hn hnr)
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  rw [testIntegral_eq_ofReal_continuousTestIntegral, hv, ENNReal.ofReal_zero]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The physical edge density converges with the actual joint color law. -/
theorem density_tendsto_of_jointLaw (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw)) :
    Tendsto (fun n => density (W n)) atTop (𝓝 (density V)) := by
  exact (DecoratedKernel.integral_moment_tendsto_of_jointLaw W V hweak
    ⟨CappedColor.adjacency, CappedColor.continuous_adjacency⟩).div_const 2

/-- The signed charge objective converges with the actual joint color law. -/
theorem objective_tendsto_of_jointLaw (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw)) :
    Tendsto (fun n => objective (W n)) atTop (𝓝 (objective V)) := by
  exact (DecoratedKernel.integral_moment_tendsto_of_jointLaw W V hweak
    ⟨CappedColor.charge, CappedColor.continuous_charge⟩).div_const 2

variable [NullSingletonClass μ]

/-- A genuine capped model is the subsequential limit of all finite
continuous sample tests, edge density and signed charge objective. -/
theorem exists_sampledTest_limit (W : ℕ → Model Ω μ) :
    ∃ (V : Model Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ (n : ℕ) (F : C(CliquePair n → CappedColor, ℝ)),
        Tendsto (fun k => continuousTestIntegral (W (φ k)) n F) atTop
          (𝓝 (continuousTestIntegral V n F))) ∧
      Tendsto (fun k => density (W (φ k))) atTop (𝓝 (density V)) ∧
      Tendsto (fun k => objective (W (φ k))) atTop (𝓝 (objective V)) := by
  have : Nonempty CappedColor := ⟨CappedColor.absent⟩
  obtain ⟨V, φ, hφ, e, he, hweak, hcut⟩ := DecoratedKernel.compact_moments W
  let A : ℕ → Model Ω μ := fun k => (W (φ k)).pullback (e k) (he k)
  have hcut' : ∀ (f : C(CappedColor, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) ε,
      0 < ε → ∃ N, ∀ k ≥ N,
        Graphon.cutNormDiff ((A k).momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε := by
    intro f hf ε hε
    simpa only [A, DecoratedKernel.momentGraphon_pullback] using hcut f hf ε hε
  refine ⟨V, φ, hφ, ?_, ?_, ?_⟩
  · intro n F
    have h := continuousTestIntegral_tendsto_of_momentGraphonCut A V hcut' n F
    simpa only [A, continuousTestIntegral_pullback] using h
  · simpa only [A, density_pullback] using density_tendsto_of_jointLaw A V hweak
  · simpa only [A, objective_pullback] using objective_tendsto_of_jointLaw A V hweak

/-- The sampled-test limit preserves exactly the imposed finite clique
orders, together with density and objective convergence. -/
theorem exists_feasible_sampledTest_limit (W : ℕ → Model Ω μ) (r : ℕ)
    (hW : ∀ k, Feasible r (W k)) :
    ∃ (V : Model Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧ Feasible r V ∧
      (∀ (n : ℕ) (F : C(CliquePair n → CappedColor, ℝ)),
        Tendsto (fun k => continuousTestIntegral (W (φ k)) n F) atTop
          (𝓝 (continuousTestIntegral V n F))) ∧
      Tendsto (fun k => density (W (φ k))) atTop (𝓝 (density V)) ∧
      Tendsto (fun k => objective (W (φ k))) atTop (𝓝 (objective V)) := by
  obtain ⟨V, φ, hφ, hconv, hdensity, hobjective⟩ := exists_sampledTest_limit W
  refine ⟨V, φ, hφ, ?_, hconv, hdensity, hobjective⟩
  exact feasible_of_continuousTestIntegral_tendsto (fun k => W (φ k)) V r
    (fun k => hW (φ k)) (fun n _ _ => hconv n ⟨violation, continuous_violation n⟩)

end Erdos1017.CappedModel

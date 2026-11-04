module

public import Erdos1017.Models.Capped.CappedShiftedLimit
public import Erdos1017.Models.Capped.CappedShiftedSelection
public import Erdos1017.Models.Capped.CappedGrowingLimit

/-!
# Common aligned limit of selected cap maximizers

Selected growing-cap maximizers have a common aligned limit on which full
feasibility, shifted-color support, stationarity and positive index are all
derived (`exists_selected_cap_limit`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual selected growing-cap maximizers have a common aligned limit.
Full feasibility, shifted-color support, stationarity and positive index
are derived on the same limit as the actual operator convergence. Density
and objective convergence of the selected sequence are explicit inputs. -/
theorem exists_selected_cap_limit
    (W : ℕ → Model Ω μ) (r : ℕ → ℕ) (m ν : ℕ → ℝ) (d c : ℝ)
    (hr : Tendsto r atTop atTop) (hW : ∀ n, IsMaximizer (r n) (W n))
    (hm : ∀ n, m n ∈ Set.Icc (-3 : ℝ) 1)
    (hdet : ∀ n, ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂(W n).kernel p,
      shiftedColor (m n) z = shiftedMoment (W n) (m n) p)
    (hmem : ∀ n, ∀ᵐ p ∂μ.prod μ, shiftedMoment (W n) (m n) p ∈ Set.Icc 0 4)
    (hrow : ∀ n, ∀ᵐ x ∂μ, (∫ y, shiftedKernel (W n) (m n) x y ∂μ) = ν n)
    (hfinite : ∀ n, FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (W n) (m n))))
    (hindex : ∀ n, Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (W n) (m n))) ≤ 2)
    (hd : Tendsto (fun n => density (W n)) atTop (𝓝 d))
    (hc : Tendsto (fun n => objective (W n)) atTop (𝓝 c)) :
    ∃ (V : Model Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ) (m₀ : ℝ),
        m₀ ∈ Set.Icc (-3 : ℝ) 1 ∧ FullFeasible V ∧ density V = d ∧ objective V = c ∧
        let A := fun n => (W (φ n)).pullback (e n) (he n)
        Tendsto (fun n => (A n).jointLaw) atTop (𝓝 V.jointLaw) ∧
        (∀ (f : C(CappedColor, ℝ)) (hf : ∀ z, f z ∈ Set.Icc 0 1) ε,
          0 < ε → ∃ N, ∀ n ≥ N,
            Graphon.cutNormDiff ((A n).momentGraphon f f.continuous.stronglyMeasurable hf)
              (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε) ∧
        Tendsto (fun n => m (φ n)) atTop (𝓝 m₀) ∧
        Tendsto (fun n => ν (φ n)) atTop (𝓝 (2 * (objective V - m₀ * density V))) ∧
        Tendsto (fun n => shiftedOperator (A n) (m (φ n))) atTop (𝓝 (shiftedOperator V m₀)) ∧
        (∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂V.kernel p, shiftedColor m₀ z ∈ Set.Icc 0 4) ∧
        (∀ᵐ p ∂μ.prod μ, shiftedMoment V m₀ p ∈ Set.Icc 0 4) ∧
        (∀ᵐ x ∂μ, (∫ y, shiftedKernel V m₀ x y ∂μ) = 2 * (objective V - m₀ * density V)) ∧
        FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)) ∧
        Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)) ≤ 2 ∧
        Tendsto (fun n => ∫ p : Ω × Ω,
          (shiftedKernel (A n) (m (φ n)) p.1 p.2 - shiftedKernel V m₀ p.1 p.2)^2 ∂μ.prod μ)
          atTop (𝓝 0) := by
  obtain ⟨V, φ, hφ, e, he, m₀, hm₀, hweak, hcut, hmult, hop⟩ :=
    exists_aligned_shifted_operator_limit W m hm
  let A := fun n => (W (φ n)).pullback (e n) (he n)
  have hfull : FullFeasible V := by
    intro s
    apply feasible_of_eventual_sampledTest_limit A V s
    · have hs := (hr.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop s)
      filter_upwards [hs] with n hn
      exact feasible_pullback (W (φ n)) (feasible_mono (hW (φ n)).1 hn) (e n) (he n)
    · intro n _ _
      exact continuousTestIntegral_tendsto_of_momentGraphonCut A V hcut n
        ⟨violation, continuous_violation n⟩
  have hdA : Tendsto (fun n => density (A n)) atTop (𝓝 (density V)) :=
    density_tendsto_of_jointLaw A V hweak
  have hcA : Tendsto (fun n => objective (A n)) atTop (𝓝 (objective V)) :=
    objective_tendsto_of_jointLaw A V hweak
  have hdV : density V = d := tendsto_nhds_unique hdA (by
    simpa only [A, density_pullback, Function.comp_def] using hd.comp hφ.tendsto_atTop)
  have hcV : objective V = c := tendsto_nhds_unique hcA (by
    simpa only [A, objective_pullback, Function.comp_def] using hc.comp hφ.tendsto_atTop)
  have hmemA (n : ℕ) : ∀ᵐ p ∂μ.prod μ, shiftedMoment (A n) (m (φ n)) p ∈ Set.Icc 0 4 :=
    ((he n).prod (he n)).quasiMeasurePreserving.ae (hmem (φ n))
  have hcolorA (n : ℕ) : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ z ∂(A n).kernel p, shiftedColor (m (φ n)) z ∈ Set.Icc 0 4 := by
    have h := ((he n).prod (he n)).quasiMeasurePreserving.ae (hdet (φ n))
    filter_upwards [h, hmemA n] with p hp hmp
    exact hp.mono (fun z hz => hz.symm ▸ hmp)
  have hcolorV := shiftedColor_mem_of_jointLaw_limit A V (fun n => m (φ n)) m₀ hweak hmult hcolorA
  have hmemV := shiftedMoment_mem_of_color_mem V m₀ hcolorV
  have hfiniteA (n : ℕ) : FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (A n) (m (φ n)))) := by
    let _ := hfinite (φ n)
    exact finiteDimensional_positive_shiftedOperator_pullback (W (φ n)) (m (φ n)) (e n) (he n)
  have hindexA (n : ℕ) : Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (A n) (m (φ n)))) ≤ 2 := by
    rw [finrank_positive_shiftedOperator_pullback]
    exact hindex (φ n)
  obtain ⟨hfiniteV, hindexV⟩ :=
    positive_shifted_index_of_operator_limit A V (fun n => m (φ n)) m₀ hop hfiniteA 2 hindexA
  have hν (n : ℕ) : ν (φ n) = 2 * (objective (A n) - m (φ n) * density (A n)) := by
    simpa only [A, objective_pullback, density_pullback] using
      shifted_stationary_value (W (φ n)) (m (φ n)) (ν (φ n)) (hrow (φ n))
  have hνlim : Tendsto (fun n => ν (φ n)) atTop
      (𝓝 (2 * (objective V - m₀ * density V))) := by
    simpa only [hν] using (hcA.sub (hmult.mul hdA)).const_mul 2
  have hrowV := shifted_row_of_operator_limit A V (fun n => m (φ n)) m₀
    (fun n => ν (φ n)) (2 * (objective V - m₀ * density V)) hop hνlim
    (fun n => shifted_row_pullback (W (φ n)) (m (φ n)) (ν (φ n)) (hrow (φ n)) (e n) (he n))
  refine ⟨V, φ, hφ, e, he, m₀, hm₀, hfull, hdV, hcV, hweak, hcut, hmult, hνlim, hop,
    hcolorV, hmemV, hrowV, hfiniteV, hindexV, ?_⟩
  exact shiftedKernel_sq_tendsto_of_moment_cut A V (fun n => m (φ n)) m₀ hcut hmult
    hmemA hmemV hfiniteA hfiniteV 2 hindexA hindexV

end Erdos1017.CappedModel

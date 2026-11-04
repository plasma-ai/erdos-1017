module

public import Erdos1017.Models.Capped.CappedDeterministicLimit
public import Erdos1017.Models.Capped.CappedLimitValue
public import Erdos1017.Models.Selection.FullKernelSelection

/-!
# Compactness of full stationary optimizers

The joint class of full stationary optimizers at fixed density and objective.
Compactness is expressed by one aligned full-model subsequential limit, with
operator, kernel L2 and squared-energy convergence. No finite-cap maximality or
strict-gap geometry is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The joint class records the original full optimum and its
recorded stationary multiplier, before strict support or positive index two is imposed. -/
structure FullStationaryClass (d c : ℝ) (W : Model Ω μ) (m : ℝ) : Prop where
  full : FullFeasible W
  density_eq : density W = d
  objective_eq : objective W = c
  optimal : c = FractionalGraph.densityLimit d
  multiplier_mem : m ∈ Set.Icc (-3 : ℝ) 1
  deterministic : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p, shiftedColor m z = shiftedMoment W m p
  moment_mem : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4
  complementary : ∀ᵐ p ∂μ.prod μ,
    (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0
  stationary : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = 2 * (c - m * d)
  finite_positive : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))
  index_le_two : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 2

/-- The actual squared shifted-kernel energy used in the second selection. -/
def stationaryEnergy (W : Model Ω μ) (m : ℝ) : ℝ :=
  ∫ p : Ω × Ω, (shiftedMoment W m p) ^ 2 ∂μ.prod μ

/-- Every member has its actual energy in the fixed compact scalar interval. -/
theorem FullStationaryClass.energy_mem {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) : stationaryEnergy W m ∈ Set.Icc (0 : ℝ) 16 := by
  have hi := integrable_shiftedMoment_sq W m hW.moment_mem
  constructor
  · exact integral_nonneg (fun _ => sq_nonneg _)
  · have hle : ∀ᵐ p ∂μ.prod μ, (shiftedMoment W m p) ^ 2 ≤ 16 := by
      filter_upwards [hW.moment_mem] with p hp
      nlinarith [hp.1, hp.2, mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]
    simpa only [stationaryEnergy, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono_ae hi (integrable_const (16 : ℝ)) hle

/-- The original full optimizer class is invariant under each actual alignment. -/
theorem FullStationaryClass.pullback {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) :
    FullStationaryClass d c (W.pullback e he) m := by
  have hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂(W.pullback e he).kernel p,
      shiftedColor m z = shiftedMoment (W.pullback e he) m p :=
    (he.prod he).quasiMeasurePreserving.ae hW.deterministic
  refine ⟨fun r => feasible_pullback W (hW.full r) e he, ?_, ?_, hW.optimal,
    hW.multiplier_mem, hdet, ?_, shifted_complementary_of_deterministic _ _ hdet,
    shifted_row_pullback W m _ hW.stationary e he, ?_, ?_⟩
  · rw [density_pullback]
    exact hW.density_eq
  · rw [objective_pullback]
    exact hW.objective_eq
  · exact (he.prod he).quasiMeasurePreserving.ae hW.moment_mem
  · let _ := hW.finite_positive
    exact finiteDimensional_positive_shiftedOperator_pullback W m e he
  · rw [finrank_positive_shiftedOperator_pullback]
    exact hW.index_le_two

/-- The actual energy is unchanged by the same measure-preserving alignment. -/
theorem stationaryEnergy_pullback (W : Model Ω μ) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) :
    stationaryEnergy (W.pullback e he) m = stationaryEnergy W m := by
  exact (he.prod he).integral_comp (e.prodCongr e).measurableEmbedding
    (fun p : Ω × Ω => (shiftedMoment W m p) ^ 2)

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual full attainment and the proved full-kernel selection populate
the joint class at every interior density. -/
theorem fullStationaryClass_nonempty (d : ℝ) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ (W : Model Ω μ) (m : ℝ), FullStationaryClass d (FractionalGraph.densityLimit d) W m := by
  obtain ⟨W, hW, hdW, hcW⟩ := exists_fullFeasible_at_density (μ := μ) d ⟨hd.1.le, hd.2.le⟩
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by rw [hdW, hcW]
  obtain ⟨V, m, ν, hV, _, hdV, hcV, hm, _, hdet, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
    exists_selected_full_kernel W hW hopt (hdW.symm ▸ hd.1) (hdW.symm ▸ hd.2)
  have hdensity : density V = d := hdV.trans hdW
  have hobjective : objective V = FractionalGraph.densityLimit d := hcV.trans hcW
  refine ⟨V, m, hV, hdensity, hobjective, rfl, hm, hdet, hmem, hcomp, ?_, hfinite, hindex⟩
  rw [hν, hdensity, hobjective] at hrow
  exact hrow

/-- Every sequence in the full optimizer class has one common aligned
full-feasible limit. All clique tests, operators, actual shifted kernels
and energies converge in that same frame. -/
theorem exists_aligned_fullStationary_limit (d c : ℝ)
    (W : ℕ → Model Ω μ) (m : ℕ → ℝ)
    (hclass : ∀ n, FullStationaryClass d c (W n) (m n)) :
    ∃ (V : Model Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ) (m₀ : ℝ),
        FullStationaryClass d c V m₀ ∧
        let A := fun n => (W (φ n)).pullback (e n) (he n)
        Tendsto (fun n => (A n).jointLaw) atTop (𝓝 V.jointLaw) ∧
        (∀ (f : C(CappedColor, ℝ)) (hf : ∀ z, f z ∈ Set.Icc 0 1) ε,
          0 < ε → ∃ N, ∀ n ≥ N,
            Graphon.cutNormDiff ((A n).momentGraphon f f.continuous.stronglyMeasurable hf)
              (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε) ∧
        (∀ (k : ℕ) (F : C(CliquePair k → CappedColor, ℝ)),
          Tendsto (fun n => continuousTestIntegral (A n) k F) atTop
            (𝓝 (continuousTestIntegral V k F))) ∧
        Tendsto (fun n => m (φ n)) atTop (𝓝 m₀) ∧
        Tendsto (fun n => shiftedOperator (A n) (m (φ n))) atTop (𝓝 (shiftedOperator V m₀)) ∧
        Tendsto (fun n => ∫ p : Ω × Ω,
          (shiftedMoment (A n) (m (φ n)) p - shiftedMoment V m₀ p) ^ 2 ∂μ.prod μ)
          atTop (𝓝 0) ∧
        Tendsto (fun n => stationaryEnergy (W (φ n)) (m (φ n))) atTop
          (𝓝 (stationaryEnergy V m₀)) := by
  obtain ⟨V, φ, hφ, e, he, m₀, hm₀, hweak, hcut, hmult, hop⟩ :=
    exists_aligned_shifted_operator_limit W m (fun n => (hclass n).multiplier_mem)
  let A := fun n => (W (φ n)).pullback (e n) (he n)
  have hA (n : ℕ) : FullStationaryClass d c (A n) (m (φ n)) :=
    (hclass (φ n)).pullback (e n) (he n)
  have htests (k : ℕ) (F : C(CliquePair k → CappedColor, ℝ)) :
      Tendsto (fun n => continuousTestIntegral (A n) k F) atTop
        (𝓝 (continuousTestIntegral V k F)) :=
    continuousTestIntegral_tendsto_of_momentGraphonCut A V hcut k F
  have hfullV : FullFeasible V := by
    intro r
    apply feasible_of_continuousTestIntegral_tendsto A V r (fun n => (hA n).full r)
    intro k _ _
    exact htests k ⟨violation, continuous_violation k⟩
  have hdA (n : ℕ) : density (A n) = d := (hA n).density_eq
  have hcA (n : ℕ) : objective (A n) = c := (hA n).objective_eq
  have hdV : density V = d := tendsto_nhds_unique
    (density_tendsto_of_jointLaw A V hweak) (by
      simp only [hdA]
      exact tendsto_const_nhds)
  have hcV : objective V = c := tendsto_nhds_unique
    (objective_tendsto_of_jointLaw A V hweak) (by
      simp only [hcA]
      exact tendsto_const_nhds)
  have hcolorA (n : ℕ) : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂(A n).kernel p,
      shiftedColor (m (φ n)) z ∈ Set.Icc 0 4 := by
    filter_upwards [(hA n).deterministic, (hA n).moment_mem] with p hp hmp
    exact hp.mono (fun z hz => hz.symm ▸ hmp)
  have hcolorV := shiftedColor_mem_of_jointLaw_limit A V (fun n => m (φ n)) m₀ hweak hmult hcolorA
  have hmemV := shiftedMoment_mem_of_color_mem V m₀ hcolorV
  obtain ⟨hfiniteV, hindexV⟩ := positive_shifted_index_of_operator_limit A V
    (fun n => m (φ n)) m₀ hop (fun n => (hA n).finite_positive) 2 (fun n => (hA n).index_le_two)
  have hνlim : Tendsto (fun n => 2 * (c - m (φ n) * d)) atTop (𝓝 (2 * (c - m₀ * d))) :=
    (tendsto_const_nhds.sub (hmult.mul_const d)).const_mul 2
  have hrowV := shifted_row_of_operator_limit A V (fun n => m (φ n)) m₀
    (fun n => 2 * (c - m (φ n) * d)) (2 * (c - m₀ * d)) hop hνlim
    (fun n => (hA n).stationary)
  have hL2 : Tendsto (fun n => ∫ p : Ω × Ω,
      (shiftedMoment (A n) (m (φ n)) p - shiftedMoment V m₀ p) ^ 2 ∂μ.prod μ)
      atTop (𝓝 0) :=
    shiftedKernel_sq_tendsto_of_moment_cut A V (fun n => m (φ n)) m₀ hcut hmult
      (fun n => (hA n).moment_mem) hmemV (fun n => (hA n).finite_positive) hfiniteV
      2 (fun n => (hA n).index_le_two) hindexV
  have hdetV := shifted_deterministic_of_jointLaw_L2_limit A V (fun n => m (φ n)) m₀ hm₀
    hweak hmult (fun n => (hA n).deterministic) (fun n => (hA n).moment_mem) hmemV hL2
  have hclassV : FullStationaryClass d c V m₀ :=
    ⟨hfullV, hdV, hcV, (hclass 0).optimal, hm₀, hdetV, hmemV,
      shifted_complementary_of_deterministic V m₀ hdetV, hrowV, hfiniteV, hindexV⟩
  have hJ : Tendsto (fun n => stationaryEnergy (W (φ n)) (m (φ n))) atTop
      (𝓝 (stationaryEnergy V m₀)) := by
    have h := shiftedMoment_sq_integral_tendsto A V (fun n => m (φ n)) m₀
      (fun n => (hA n).moment_mem) hmemV hL2
    change Tendsto (fun n => stationaryEnergy (A n) (m (φ n))) atTop
      (𝓝 (stationaryEnergy V m₀)) at h
    simpa only [A, stationaryEnergy_pullback] using h
  exact ⟨V, φ, hφ, e, he, m₀, hclassV, hweak, hcut, htests, hmult, hop, hL2, hJ⟩

/-- Limits of the two actual scalar selection coordinates retain an actual
full stationary optimizer witnessing both limits. -/
theorem exists_fullStationary_limit_of_scalar_limits (d c : ℝ)
    (W : ℕ → Model Ω μ) (m : ℕ → ℝ)
    (hclass : ∀ n, FullStationaryClass d c (W n) (m n))
    (m₀ J₀ : ℝ) (hm : Tendsto m atTop (𝓝 m₀))
    (hJ : Tendsto (fun n => stationaryEnergy (W n) (m n)) atTop (𝓝 J₀)) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m₀ ∧ stationaryEnergy V m₀ = J₀ := by
  obtain ⟨V, φ, hφ, e, he, m', hV, _, _, _, hmult, _, _, henergy⟩ :=
    exists_aligned_fullStationary_limit d c W m hclass
  have hm' : m' = m₀ := tendsto_nhds_unique hmult (hm.comp hφ.tendsto_atTop)
  have hJ' : stationaryEnergy V m' = J₀ := tendsto_nhds_unique henergy (hJ.comp hφ.tendsto_atTop)
  exact ⟨V, hm' ▸ hV, hm' ▸ hJ'⟩

end Erdos1017.CappedModel

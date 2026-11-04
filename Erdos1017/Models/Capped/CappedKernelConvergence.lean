module

public import Erdos1017.Models.Kernel.KernelCutConvergence
public import Erdos1017.Models.Kernel.KernelSpectralConvergence
public import Erdos1017.Models.Capped.CappedRegularKernel
public import Erdos1017.Models.Decorated.DecoratedCompactness

/-!
# Operator convergence of capped kernels under moment cut convergence

Moment differences have the rectangle cut norm of their normalized moment
graphon difference, so aligned moment cut convergence gives operator-norm
convergence of the adjacency, charge and shifted operators, and decorated
compactness supplies one subsequence and alignments on which they converge.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.DecoratedKernel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  [TopologicalSpace C] [OpensMeasurableSpace C]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual moment difference has exactly the rectangle cut norm of its
normalized moment graphon difference. -/
theorem kernelCutNorm_moment_sub (W V : DecoratedKernel Ω C μ)
    (f : C(C, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) :
    KernelOperator.kernelCutNorm (μ := μ) (fun x y => W.moment f (x, y) - V.moment f (x, y)) =
      Graphon.cutNormDiff (W.momentGraphon f f.continuous.stronglyMeasurable hf)
        (V.momentGraphon f f.continuous.stronglyMeasurable hf) := by
  have hnorm (U Z : Graphon Ω μ) :
      KernelOperator.kernelCutNorm (μ := μ) (KernelOperator.graphonDifference U Z) =
        Graphon.cutNormDiff U Z := rfl
  have hW := AEEqFun.coeFn_mk (μ := μ.prod μ) (W.moment f)
    (W.stronglyMeasurable_moment f.continuous.stronglyMeasurable).aestronglyMeasurable
  have hV := AEEqFun.coeFn_mk (μ := μ.prod μ) (V.moment f)
    (V.stronglyMeasurable_moment f.continuous.stronglyMeasurable).aestronglyMeasurable
  have heq : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
      W.moment f p - V.moment f p =
        KernelOperator.graphonDifference (W.momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) p.1 p.2 := by
    filter_upwards [hW, hV] with p hp hq
    exact congrArg₂ (· - ·) hp.symm hq.symm
  exact (KernelOperator.kernelCutNorm_congr heq).trans (hnorm _ _)

/-- The actual compactness epsilon bounds give convergence of each moment
cut norm on that same aligned carrier. -/
theorem momentCutNorm_tendsto (W : ℕ → DecoratedKernel Ω C μ) (V : DecoratedKernel Ω C μ)
    (f : C(C, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1)
    (hcut : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff ((W n).momentGraphon f f.continuous.stronglyMeasurable hf)
        (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε) :
    Tendsto (fun n => KernelOperator.kernelCutNorm (μ := μ)
      (fun x y => (W n).moment f (x, y) - V.moment f (x, y))) atTop (𝓝 0) := by
  simp_rw [fun n => kernelCutNorm_moment_sub (W n) V f hf]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le (Graphon.cutNormDiff_nonneg _ _))
  · intro a ha
    obtain ⟨N, hN⟩ := hcut a ha
    exact (eventually_ge_atTop N).mono (fun n hn => hN n hn)

end Erdos1017.DecoratedKernel

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The adjacency moment is already a normalized continuous cut test. -/
def adjacencyCutTest : C(CappedColor, ℝ) :=
  ⟨CappedColor.adjacency, CappedColor.continuous_adjacency⟩

/-- The signed charge is encoded by one normalized continuous cut test. -/
def chargeCutTest : C(CappedColor, ℝ) :=
  ⟨fun c => (CappedColor.charge c + 3) / 4, by fun_prop⟩

theorem adjacencyCutTest_mem (c : CappedColor) : adjacencyCutTest c ∈ Set.Icc 0 1 :=
  CappedColor.adjacency_mem c

theorem chargeCutTest_mem (c : CappedColor) : chargeCutTest c ∈ Set.Icc 0 1 := by
  change (CappedColor.charge c + 3) / 4 ∈ Set.Icc 0 1
  constructor <;> linarith [(CappedColor.charge_mem c).1, (CappedColor.charge_mem c).2]

omit [IsProbabilityMeasure μ] in
/-- Signed charge differences are exactly four times the normalized test
moment differences; the constant term cancels. -/
theorem chargeKernel_sub_eq_moment_sub (W V : Model Ω μ) (x y : Ω) :
    chargeKernel W x y - chargeKernel V x y =
      4 * (W.moment chargeCutTest (x, y) - V.moment chargeCutTest (x, y)) := by
  have hm (U : Model Ω μ) : U.moment chargeCutTest (x, y) =
      (U.moment CappedColor.charge (x, y) + 3) / 4 := by
    dsimp only [DecoratedKernel.moment, chargeCutTest, ContinuousMap.coe_mk]
    rw [integral_div, integral_add (integrable_color_charge U (x, y)) (integrable_const 3)]
    simp
  rw [hm W, hm V]
  dsimp only [chargeKernel]
  ring

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual aligned moment cut convergence implies adjacency-operator
convergence in operator norm. -/
theorem adjacencyOperator_tendsto_of_moment_cut
    (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (hcut : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff ((W n).momentGraphon adjacencyCutTest
        adjacencyCutTest.continuous.stronglyMeasurable adjacencyCutTest_mem)
        (V.momentGraphon adjacencyCutTest adjacencyCutTest.continuous.stronglyMeasurable adjacencyCutTest_mem) < ε) :
    Tendsto (fun n => adjacencyOperator (W n)) atTop (𝓝 (adjacencyOperator V)) := by
  have h := DecoratedKernel.momentCutNorm_tendsto W V adjacencyCutTest adjacencyCutTest_mem hcut
  exact KernelOperator.tendsto_operator_of_cutNorm (fun n => adjacencyKernel (W n)) (adjacencyKernel V)
    (by norm_num : (0 : ℝ) < 1) (fun n => adjacencyKernel_measurable (W n)) (adjacencyKernel_measurable V)
    (fun n => adjacencyKernel_bound (W n)) (adjacencyKernel_bound V)
    (fun n => adjacencyKernel_symm (W n)) (adjacencyKernel_symm V) h

/-- Actual normalized charge-moment cut convergence controls the signed
charge integral operators, without discarding their negative values. -/
theorem chargeOperator_tendsto_of_moment_cut
    (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (hcut : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff ((W n).momentGraphon chargeCutTest
        chargeCutTest.continuous.stronglyMeasurable chargeCutTest_mem)
        (V.momentGraphon chargeCutTest chargeCutTest.continuous.stronglyMeasurable chargeCutTest_mem) < ε) :
    Tendsto (fun n => chargeOperator (W n)) atTop (𝓝 (chargeOperator V)) := by
  have h := DecoratedKernel.momentCutNorm_tendsto W V chargeCutTest chargeCutTest_mem hcut
  have heq (n : ℕ) : KernelOperator.kernelCutNorm (μ := μ)
      (fun x y => chargeKernel (W n) x y - chargeKernel V x y) =
        4 * KernelOperator.kernelCutNorm (μ := μ)
          (fun x y => (W n).moment chargeCutTest (x, y) - V.moment chargeCutTest (x, y)) := by
    simp_rw [chargeKernel_sub_eq_moment_sub]
    exact KernelOperator.kernelCutNorm_const_mul _ 4 (by norm_num)
  have hcharge : Tendsto (fun n => KernelOperator.kernelCutNorm (μ := μ)
      (fun x y => chargeKernel (W n) x y - chargeKernel V x y)) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa only [mul_zero] using tendsto_const_nhds.mul h
  exact KernelOperator.tendsto_operator_of_cutNorm (fun n => chargeKernel (W n)) (chargeKernel V)
    (by norm_num : (0 : ℝ) < 3) (fun n => chargeKernel_measurable (W n)) (chargeKernel_measurable V)
    (fun n => chargeKernel_bound (W n)) (chargeKernel_bound V)
    (fun n => chargeKernel_symm (W n)) (chargeKernel_symm V) hcharge

/-- On one common carrier, actual moment cut convergence and scalar
multiplier convergence give convergence of the actual shifted operators. -/
theorem shiftedOperator_tendsto_of_moment_cut
    (W : ℕ → Model Ω μ) (V : Model Ω μ) (m : ℕ → ℝ) (m₀ : ℝ)
    (hcut : ∀ (f : C(CappedColor, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) ε,
      0 < ε → ∃ N, ∀ n ≥ N,
        Graphon.cutNormDiff ((W n).momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε)
    (hm : Tendsto m atTop (𝓝 m₀)) :
    Tendsto (fun n => shiftedOperator (W n) (m n)) atTop (𝓝 (shiftedOperator V m₀)) := by
  simp_rw [shiftedOperator_eq]
  exact (chargeOperator_tendsto_of_moment_cut W V (hcut chargeCutTest chargeCutTest_mem)).sub
    (hm.smul (adjacencyOperator_tendsto_of_moment_cut W V (hcut adjacencyCutTest adjacencyCutTest_mem)))

/-- Actual selected shifted kernels with uniformly bounded positive rank
converge in squared kernel L2 once their aligned moments and multipliers
converge. The spectral representations and absolute sums are derived from
the displayed finite positive rank hypotheses. -/
theorem shiftedKernel_sq_tendsto_of_moment_cut
    (W : ℕ → Model Ω μ) (V : Model Ω μ) (m : ℕ → ℝ) (m₀ : ℝ)
    (hcut : ∀ (f : C(CappedColor, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) ε,
      0 < ε → ∃ N, ∀ n ≥ N,
        Graphon.cutNormDiff ((W n).momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε)
    (hm : Tendsto m atTop (𝓝 m₀))
    (hWmem : ∀ n, ∀ᵐ p ∂μ.prod μ, shiftedMoment (W n) (m n) p ∈ Set.Icc 0 4)
    (hVmem : ∀ᵐ p ∂μ.prod μ, shiftedMoment V m₀ p ∈ Set.Icc 0 4)
    (hWfinite : ∀ n, FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (W n) (m n))))
    (hVfinite : FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)))
    (r : ℕ)
    (hWrank : ∀ n, Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (W n) (m n))) ≤ r)
    (hVrank : Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)) ≤ r) :
    Tendsto (fun n => ∫ p : Ω × Ω,
      (shiftedKernel (W n) (m n) p.1 p.2 - shiftedKernel V m₀ p.1 p.2) ^ 2 ∂μ.prod μ)
      atTop (𝓝 0) := by
  have hWbound (n : ℕ) : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel (W n) (m n) p.1 p.2‖ ≤ 4 := by
    filter_upwards [hWmem n] with p hp
    change ‖shiftedMoment (W n) (m n) p‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hVbound : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel V m₀ p.1 p.2‖ ≤ 4 := by
    filter_upwards [hVmem] with p hp
    change ‖shiftedMoment V m₀ p‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have heq (n : ℕ) := shiftedOperator_eq_of_bound (W n) (m n) (by norm_num : (0 : ℝ) ≤ 4) (hWbound n)
  have heqV := shiftedOperator_eq_of_bound V m₀ (by norm_num : (0 : ℝ) ≤ 4) hVbound
  have hop := tendsto_iff_norm_sub_tendsto_zero.mp (shiftedOperator_tendsto_of_moment_cut W V m m₀ hcut hm)
  have hop' : Tendsto (fun n =>
      ‖KernelOperator.operator (shiftedKernel (W n) (m n)) (by norm_num : (0 : ℝ) ≤ 4)
          (shiftedKernel_measurable (W n) (m n)) (hWbound n) -
        KernelOperator.operator (shiftedKernel V m₀) (by norm_num : (0 : ℝ) ≤ 4)
          (shiftedKernel_measurable V m₀) hVbound‖) atTop (𝓝 0) := by
    simpa only [← heq, ← heqV] using hop
  apply KernelOperator.tendsto_integral_sq_sub_of_positive_rank
    (fun n => shiftedKernel (W n) (m n)) (shiftedKernel V m₀) (by norm_num : (0 : ℝ) ≤ 4)
    (fun n => shiftedKernel_measurable (W n) (m n)) (shiftedKernel_measurable V m₀)
    hWbound hVbound
    (fun n => (hWmem n).mono (fun _ hp => hp.1)) (hVmem.mono (fun _ hp => hp.1))
    (fun n => (shiftedMoment_symm (W n) (m n)).mono (fun _ hp => hp.symm))
    ((shiftedMoment_symm V m₀).mono (fun _ hp => hp.symm))
    (fun n => by rw [← heq n]; exact hWfinite n) (by rw [← heqV]; exact hVfinite)
    r (fun n => by rw [← heq n]; exact hWrank n) (by rw [← heqV]; exact hVrank) hop'

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- Actual decorated compactness supplies one subsequence and one sequence
of measure-preserving alignments on which the actual adjacency and charge
operators converge. Every convergent multiplier sequence then gives shifted
operator convergence in that same frame. -/
theorem exists_aligned_operator_limit (W : ℕ → Model Ω μ) :
    ∃ (V : Model Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ),
        let A := fun n => (W (φ n)).pullback (e n) (he n)
        Tendsto (fun n => (A n).jointLaw) atTop (𝓝 V.jointLaw) ∧
        (∀ (f : C(CappedColor, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) ε,
          0 < ε → ∃ N, ∀ n ≥ N,
            Graphon.cutNormDiff ((A n).momentGraphon f f.continuous.stronglyMeasurable hf)
              (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε) ∧
        Tendsto (fun n => adjacencyOperator (A n)) atTop (𝓝 (adjacencyOperator V)) ∧
        Tendsto (fun n => chargeOperator (A n)) atTop (𝓝 (chargeOperator V)) ∧
        ∀ (m : ℕ → ℝ) (m₀ : ℝ), Tendsto m atTop (𝓝 m₀) →
          Tendsto (fun n => shiftedOperator (A n) (m n)) atTop (𝓝 (shiftedOperator V m₀)) := by
  have : Nonempty CappedColor := ⟨CappedColor.absent⟩
  obtain ⟨V, φ, hφ, e, he, hweak, hcut⟩ := DecoratedKernel.compact_moments W
  let A := fun n => (W (φ n)).pullback (e n) (he n)
  have hcut' : ∀ (f : C(CappedColor, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) ε,
      0 < ε → ∃ N, ∀ n ≥ N,
        Graphon.cutNormDiff ((A n).momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε := by
    intro f hf ε hε
    simpa only [A, DecoratedKernel.momentGraphon_pullback] using hcut f hf ε hε
  exact ⟨V, φ, hφ, e, he, hweak, hcut',
    adjacencyOperator_tendsto_of_moment_cut A V (hcut' adjacencyCutTest adjacencyCutTest_mem),
    chargeOperator_tendsto_of_moment_cut A V (hcut' chargeCutTest chargeCutTest_mem),
    fun m m₀ hm => shiftedOperator_tendsto_of_moment_cut A V m m₀ hcut' hm⟩

/-- Bounded actual multipliers can be selected together with the genuine
decorated compactness frame. The shifted operator limit is derived on that
same frame, rather than supplied as an approximation hypothesis. -/
theorem exists_aligned_shifted_operator_limit (W : ℕ → Model Ω μ) (m : ℕ → ℝ)
    (hm : ∀ n, m n ∈ Set.Icc (-3 : ℝ) 1) :
    ∃ (V : Model Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ) (m₀ : ℝ),
        m₀ ∈ Set.Icc (-3 : ℝ) 1 ∧
        let A := fun n => (W (φ n)).pullback (e n) (he n)
        Tendsto (fun n => (A n).jointLaw) atTop (𝓝 V.jointLaw) ∧
        (∀ (f : C(CappedColor, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) ε,
          0 < ε → ∃ N, ∀ n ≥ N,
            Graphon.cutNormDiff ((A n).momentGraphon f f.continuous.stronglyMeasurable hf)
              (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε) ∧
        Tendsto (fun n => m (φ n)) atTop (𝓝 m₀) ∧
        Tendsto (fun n => shiftedOperator (A n) (m (φ n))) atTop (𝓝 (shiftedOperator V m₀)) := by
  obtain ⟨V, φ, hφ, e, he, hweak, hcut, _, _, _⟩ := exists_aligned_operator_limit W
  obtain ⟨m₀, hm₀, ψ, hψ, hmult⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-3 : ℝ) 1)).tendsto_subseq (fun n => hm (φ n))
  let A := fun n => (W (φ (ψ n))).pullback (e (ψ n)) (he (ψ n))
  have hcut' : ∀ (f : C(CappedColor, ℝ)) (hf : ∀ c, f c ∈ Set.Icc 0 1) ε,
      0 < ε → ∃ N, ∀ n ≥ N,
        Graphon.cutNormDiff ((A n).momentGraphon f f.continuous.stronglyMeasurable hf)
          (V.momentGraphon f f.continuous.stronglyMeasurable hf) < ε := by
    intro f hf ε hε
    obtain ⟨N, hN⟩ := hcut f hf ε hε
    exact ⟨N, fun n hn => hN (ψ n) (hn.trans (hψ.id_le n))⟩
  refine ⟨V, φ ∘ ψ, hφ.comp hψ, e ∘ ψ, (fun n => he (ψ n)), m₀, hm₀,
    hweak.comp hψ.tendsto_atTop, hcut', hmult, ?_⟩
  exact shiftedOperator_tendsto_of_moment_cut A V (m ∘ φ ∘ ψ) m₀ hcut' hmult

end Erdos1017.CappedModel

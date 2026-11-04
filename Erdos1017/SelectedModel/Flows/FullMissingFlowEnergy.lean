module

public import Erdos1017.SelectedModel.Flows.MissingFlowFeatureEnergy
public import Erdos1017.SelectedModel.StationaryFeature
public import Erdos1017.Models.Kernel.FeatureDiagonal

/-!
# Nonnegative energy of oriented missing flows

In a full strict-gap model, oriented missing flows have nonnegative mutual and
self shifted energy, with directions that may be unbounded and merely
integrable, and nonnegative subdensities have no larger energy
(`missing_flow_energy_mono`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual oriented missing flows in the same full strict-gap model have
nonnegative mutual shifted energy. The bounded signed spectral feature,
its nonnegative diagonal, and the original degree-tangent inequality are
derived from this model before passing to its joint feature-degree law. -/
theorem FullStationaryClass.missing_flow_pairing_nonnegative
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hr0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ r p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2)
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    0 ≤ KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ q) (MissingFlow.direction μ r) := by
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hs.positive_eigenvector
  have hB : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hW.moment_mem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hfour := shiftedOperator_eq_of_bound W m (by norm_num : (0 : ℝ) ≤ 4) hB
  have hfinite : FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (KernelOperator.operator (shiftedKernel W m)
        (by norm_num) (shiftedKernel_measurable W m) hB)) := by
    rw [← hfour]
    exact hW.finite_positive
  have hindex : Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (KernelOperator.operator (shiftedKernel W m)
        (by norm_num) (shiftedKernel_measurable W m) hB)) ≤ 2 := by
    rw [← hfour]
    exact hW.index_le_two
  have heigenFour : KernelOperator.operator (shiftedKernel W m)
      (by norm_num) (shiftedKernel_measurable W m) hB w = σ • w := by
    rw [← hfour]
    exact heigen
  have hsym : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  obtain ⟨ι, hcount, F₀, J, hF₀, hFbound, hJsym, hrep₀⟩ :=
    KernelOperator.exists_uniform_feature_of_stationary_positive_index_two
      (shiftedKernel W m) (shiftedKernel_measurable W m) hB
      (hW.moment_mem.mono (fun _ hp => hp.1)) hsym
      (2 * (c - m * d)) hs.stationary_pos hW.stationary hfinite hindex
      w hw hmean σ σ hσ le_rfl heigenFour
  let := hcount
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  let F := hF₀.mk F₀
  have hFm : StronglyMeasurable F := hF₀.stronglyMeasurable_mk
  have hFe : F₀ =ᵐ[μ] F := hF₀.ae_eq_mk
  have hpairEq : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = ⟪J (F p.1), F p.2⟫ := by
    filter_upwards [hrep₀,
      Measure.quasiMeasurePreserving_fst.ae hFe,
      Measure.quasiMeasurePreserving_snd.ae hFe] with p hp hfst hsnd
    rwa [← hfst, ← hsnd]
  have hpairBound : ∀ᵐ p ∂μ.prod μ,
      0 ≤ ⟪J (F p.1), F p.2⟫ ∧ ⟪J (F p.1), F p.2⟫ ≤ 4 := by
    filter_upwards [hpairEq, hW.moment_mem] with p hp hb
    rw [← hp]
    exact hb
  have hdiag : ∀ᵐ x ∂μ, 0 ≤ ⟪J (F x), F x⟫ :=
    (KernelOperator.feature_diagonal_bounds F hFm.aestronglyMeasurable J 0 4
      hpairBound).mono (fun _ hx => hx.1)
  have hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt (8 + 32 / σ) := by
    filter_upwards [hFbound, hFe] with x hx he
    rwa [← he]
  let H := lp (fun _ : ι => ℝ) 2
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hgBound : g ∈ KernelOperator.boundedL2Submodule μ :=
    KernelOperator.operator_range_bounded _ _ _ _ _
  obtain ⟨Cg, _, hgBound⟩ := hgBound
  let Ψ : Ω → H × ℝ := fun x => (F x, g x)
  let P : H × ℝ →L[ℝ] H := ContinuousLinearMap.fst ℝ H ℝ
  let B : (H × ℝ) →L[ℝ] (H × ℝ) →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (J.toContinuousLinearMap.comp P) P
  let ℓ : H × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ H ℝ
  have hΨ : StronglyMeasurable Ψ := hFm.prodMk (Lp.stronglyMeasurable g)
  have hΨbound : ∀ᵐ x ∂μ, ‖Ψ x‖ ≤ max (Real.sqrt (8 + 32 / σ)) Cg := by
    filter_upwards [hbound, hgBound] with x hx hg
    exact max_le (hx.trans (le_max_left _ _)) (hg.trans (le_max_right _ _))
  have hBsym : ∀ x y, B x y = B y x := by
    intro x y
    exact (hJsym x.1 y.1).trans (real_inner_comm x.1 (J y.1)).symm
  exact MissingFlow.kernelPairing_directions_nonnegative (shiftedKernel W m) Ψ hΨ hΨbound
    B hBsym ℓ hpairEq hdiag (hW.integrable_tangent_nonpositive_of_strict_gap hd hgap)
    q r hq hr hq0 hr0 hqs hrs

/-- Every actual oriented missing flow has nonnegative original shifted
self-energy; its direction may be unbounded and merely integrable. -/
theorem FullStationaryClass.missing_flow_energy_nonnegative
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) :=
  hW.missing_flow_pairing_nonnegative hd hgap q q hq hq hq0 hq0 hqs hqs

/-- Arbitrary nonnegative subdensities of an actual oriented missing flow
have no larger original shifted energy. Support of the subflow and residual
is derived from domination, with no decomposition of the original model. -/
theorem FullStationaryClass.missing_flow_energy_mono
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hqr : ∀ᵐ p ∂μ.prod μ, q p ≤ r p)
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ r) := by
  have hres : ∀ᵐ p ∂μ.prod μ, 0 ≤ (r - q) p := by
    filter_upwards [hqr] with p hp
    exact sub_nonneg.mpr hp
  have hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
    filter_upwards [hq0, hqr, hrs] with p hp hle hs hne
    apply hs
    exact ((lt_of_le_of_ne hp (Ne.symm hne)).trans_le hle).ne'
  have hress : ∀ᵐ p ∂μ.prod μ, (r - q) p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
    filter_upwards [hq0, hqr, hrs] with p hp hle hs hne
    apply hs
    intro hz
    apply hne
    change r p - q p = 0
    have : q p = 0 := le_antisymm (by simpa only [hz] using hle) hp
    rw [hz, this, sub_self]
  have hcross := hW.missing_flow_pairing_nonnegative hd hgap q (r - q)
    hq (hr.sub hq) hq0 hres hqs hress
  have hself := hW.missing_flow_energy_nonnegative hd hgap (r - q) (hr.sub hq) hres hress
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hexpand := KernelOperator.kernelEnergy_sub_mul (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    (MissingFlow.direction μ q) (MissingFlow.direction μ (r - q))
    (MissingFlow.integrable_direction hq) (MissingFlow.integrable_direction (hr.sub hq)) (-1)
  have hadd : MissingFlow.direction μ r =ᵐ[μ]
      fun x => MissingFlow.direction μ q x - -1 * MissingFlow.direction μ (r - q) x := by
    have heq : q + (r - q) = r := by funext p; simp only [Pi.add_apply, Pi.sub_apply]; ring
    filter_upwards [MissingFlow.direction_add hq (hr.sub hq)] with x hx
    rw [heq] at hx
    simpa only [Pi.add_apply, neg_mul, one_mul, sub_neg_eq_add] using hx
  have henergy : KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ r) = KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (fun x => MissingFlow.direction μ q x - -1 * MissingFlow.direction μ (r - q) x) := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hadd,
      Measure.quasiMeasurePreserving_snd.ae hadd] with p hp hq
    rw [hp, hq]
  rw [henergy, hexpand]
  nlinarith

end Erdos1017.CappedModel

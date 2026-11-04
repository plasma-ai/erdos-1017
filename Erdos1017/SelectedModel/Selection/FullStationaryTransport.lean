module

public import Erdos1017.Models.Selection.FullStationaryCompactness
public import Erdos1017.SelectedModel.KernelMeasureTransport

/-!
# Transport of a stationary optimizer between laws

Transport of a full stationary optimizer from a changed probability law back to
the original law, retaining its recorded multiplier and energy. The needed
measurable equivalence is constructed from the proved atomless standard-Borel
mod-0 isomorphisms and their everywhere upgrade.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The actual shifted operators for the two measures are intertwined by
the derived surjective L2 isometry. -/
theorem shiftedOperator_measureTransport_intertwines (W : Model Ω ν) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) (f : Lp ℝ 2 ν) :
    shiftedOperator (W.pullback e he) m (KernelOperator.measureTransportL2 e he f) =
      KernelOperator.measureTransportL2 e he (shiftedOperator W m f) := by
  exact KernelOperator.operator_measureTransport_intertwines (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) e he f

/-- Positive finite dimension is transported, not assumed for the new law. -/
theorem finiteDimensional_positive_shiftedOperator_transport (W : Model Ω ν) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν)
    [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))] :
    FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (W.pullback e he) m)) :=
  KernelOperator.finiteDimensional_positive_of_cross_intertwines _ _
    (KernelOperator.measureTransportL2 e he).toLinearEquiv
    (shiftedOperator_measureTransport_intertwines W m e he)

/-- The two actual shifted operators have exactly the same positive index. -/
theorem finrank_positive_shiftedOperator_transport (W : Model Ω ν) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) :
    Module.finrank ℝ
        (KernelOperator.positiveSpectralSubspace (shiftedOperator (W.pullback e he) m)) =
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) :=
  KernelOperator.finrank_positive_eq_of_cross_intertwines _ _
    (KernelOperator.measureTransportL2 e he).toLinearEquiv
    (shiftedOperator_measureTransport_intertwines W m e he)

/-- Every defining identity of the actual full stationary class survives
transport between the two measures, including the spectral index bound. -/
theorem FullStationaryClass.transport {d c m : ℝ} {W : Model Ω ν}
    (hW : FullStationaryClass d c W m) (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) :
    FullStationaryClass d c (W.pullback e he) m := by
  have hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂(W.pullback e he).kernel p,
      shiftedColor m z = shiftedMoment (W.pullback e he) m p :=
    (he.prod he).quasiMeasurePreserving.ae hW.deterministic
  have hrow : ∀ᵐ x ∂μ,
      (∫ y, shiftedKernel (W.pullback e he) m x y ∂μ) = 2 * (c - m * d) := by
    filter_upwards [he.quasiMeasurePreserving.ae hW.stationary] with x hx
    change (∫ y, shiftedKernel W m (e x) (e y) ∂μ) = 2 * (c - m * d)
    rw [he.integral_comp' (fun y => shiftedKernel W m (e x) y)]
    exact hx
  refine ⟨fun r => feasible_pullback W (hW.full r) e he, ?_, ?_, hW.optimal,
    hW.multiplier_mem, hdet, ?_, shifted_complementary_of_deterministic _ _ hdet,
    hrow, ?_, ?_⟩
  · rw [density_pullback]
    exact hW.density_eq
  · rw [objective_pullback]
    exact hW.objective_eq
  · exact (he.prod he).quasiMeasurePreserving.ae hW.moment_mem
  · let _ := hW.finite_positive
    exact finiteDimensional_positive_shiftedOperator_transport W m e he
  · rw [finrank_positive_shiftedOperator_transport]
    exact hW.index_le_two

omit [IsProbabilityMeasure ν] in
/-- The actual energy is preserved by transport between the two measures. -/
theorem stationaryEnergy_transport (W : Model Ω ν) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) :
    stationaryEnergy (W.pullback e he) m = stationaryEnergy W m := by
  exact (he.prod he).integral_comp (e.prodCongr e).measurableEmbedding
    (fun p : Ω × Ω => (shiftedMoment W m p) ^ 2)

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- Canonical mod-0 isomorphisms and the proved everywhere upgrade give
an actual measure-preserving equivalence between the two atomless laws. -/
theorem exists_measurePreserving_equiv [NullSingletonClass ν] :
    ∃ e : Ω ≃ᵐ Ω, MeasurePreserving e μ ν := by
  obtain ⟨a⟩ := Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval Ω μ
  obtain ⟨b⟩ := Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval Ω ν
  let b' : Graphon.MeasureIso.Mod0MeasureIso ℝ Ω (volume.restrict (Set.Icc 0 1)) ν := {
    toFun := b.invFun
    invFun := b.toFun
    measurable_toFun := b.measurable_invFun
    measurable_invFun := b.measurable_toFun
    map_toFun := b.map_invFun
    map_invFun := b.map_toFun
    left_inv_ae := b.right_inv_ae
    right_inv_ae := b.left_inv_ae }
  obtain ⟨e, he, _, _⟩ := (a.trans b').toMeasurableEquiv
  exact ⟨e, he⟩

/-- An actual stationary-class competitor under an atomless probability law
has an actual original-law realization with the same multiplier and energy. -/
theorem exists_fullStationary_transport [NullSingletonClass ν]
    {d c m : ℝ} {W : Model Ω ν} (hW : FullStationaryClass d c W m) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      stationaryEnergy V m = stationaryEnergy W m := by
  obtain ⟨e, he⟩ := exists_measurePreserving_equiv (μ := μ) (ν := ν)
  exact ⟨W.pullback e he, hW.transport e he, stationaryEnergy_transport W m e he⟩

/-- Absolute continuity of a changed probability law supplies atomlessness
internally; no spectral transport or realization certificate is required. -/
theorem exists_fullStationary_transport_of_ac (hνμ : ν ≪ μ)
    {d c m : ℝ} {W : Model Ω ν} (hW : FullStationaryClass d c W m) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      stationaryEnergy V m = stationaryEnergy W m := by
  have : NullSingletonClass ν := ⟨fun x => hνμ (measure_singleton x)⟩
  exact exists_fullStationary_transport hW

end Erdos1017.CappedModel

module

public import Erdos1017.Models.Decorated.DecoratedPullback
public import Erdos1017.Models.Capped.CappedModel
public import Graphon.MeasureIso

/-!
# Transport of capped models along measure-preserving maps

A common measure-preserving latent map preserves every imposed sampled clique
test, density and objective; two atomless standard Borel probability laws admit
such a map, so fixed-measure capped maximality on an atomless standard Borel
space already compares every absolutely continuous latent reweighting.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
  {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- A common measure-preserving latent map preserves every imposed sampled
clique test, with exactly the old conditional color law. -/
theorem feasible_pullback (W : Model Λ ν) {r : ℕ} (hW : Feasible r W)
    (h : Ω → Λ) (hh : MeasurePreserving h μ ν) : Feasible r (W.pullback h hh) := by
  intro n hn hnr
  have hpi := measurePreserving_pi (fun _ : Fin n => μ) (fun _ : Fin n => ν) (fun _ => hh)
  have he := hpi.quasiMeasurePreserving.ae (hW n hn hnr)
  exact he

omit [IsProbabilityMeasure ν] in
theorem density_pullback (W : Model Λ ν) (h : Ω → Λ) (hh : MeasurePreserving h μ ν) :
    density (W.pullback h hh) = density W := by
  unfold density
  rw [DecoratedKernel.integral_moment_pullback W h hh _
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable]

omit [IsProbabilityMeasure ν] in
theorem objective_pullback (W : Model Λ ν) (h : Ω → Λ) (hh : MeasurePreserving h μ ν) :
    objective (W.pullback h hh) = objective W := by
  unfold objective
  rw [DecoratedKernel.integral_moment_pullback W h hh _
    CappedColor.continuous_charge.measurable.stronglyMeasurable]

/-- Two atomless standard-Borel probability laws admit an actual measurable
measure-preserving map, obtained by composing their unit-interval maps. -/
theorem exists_measurePreserving [StandardBorelSpace Ω] [StandardBorelSpace Λ]
    [NullSingletonClass μ] [NullSingletonClass ν] :
    ∃ h : Ω → Λ, MeasurePreserving h μ ν := by
  obtain ⟨e⟩ := Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval Ω μ
  obtain ⟨f⟩ := Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval Λ ν
  refine ⟨f.invFun ∘ e.toFun, ?_⟩
  exact (show MeasurePreserving f.invFun _ ν from ⟨f.measurable_invFun, f.map_invFun⟩).comp
    (show MeasurePreserving e.toFun μ _ from ⟨e.measurable_toFun, e.map_toFun⟩)

/-- Fixed-measure capped maximality on an atomless standard-Borel space
already compares every absolutely continuous latent reweighting. Each
competitor is explicitly transported back to the original probability law. -/
theorem isMaximizer_of_isFixedMeasureMaximizer [StandardBorelSpace Ω] [NullSingletonClass μ]
    (W : Model Ω μ) {r : ℕ} (hW : IsFixedMeasureMaximizer r W) : IsMaximizer r W := by
  refine ⟨hW.1, ?_⟩
  intro ξ hξ hξμ V hV hd
  have : NullSingletonClass ξ := ⟨fun x => hξμ (measure_singleton x)⟩
  obtain ⟨h, hh⟩ := exists_measurePreserving (μ := μ) (ν := ξ)
  have hc := hW.2 (V.pullback h hh) (feasible_pullback V hV h hh)
    ((density_pullback V h hh).trans hd)
  rwa [objective_pullback V h hh] at hc

end Erdos1017.CappedModel

module

public import Erdos1017.Models.Selection.FullStationaryCompactness
public import Erdos1017.Models.Selection.FullGlobalExcess
public import Mathlib.Topology.Sequences

/-!
# Selecting a full stationary optimizer

The multiplier and squared-energy pairs of full stationary models form a compact
set, allowing selection of the minimum multiplier and the maximum squared kernel
norm in its fiber; a failure of the benchmark bound yields a model selected by
both extrema at a positive global excess maximum.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual recorded multiplier and squared-energy pairs, with their original
full stationary model witnesses retained. -/
def fullStationaryValues (d c : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ W : Model Ω μ, FullStationaryClass d c W z.1 ∧ stationaryEnergy W z.1 = z.2}

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual aligned full-class limit closes its attainable scalar pairs. -/
theorem isClosed_fullStationaryValues (d c : ℝ) :
    IsClosed (fullStationaryValues (Ω := Ω) (μ := μ) d c) := by
  apply IsSeqClosed.isClosed
  intro z z₀ hz hzlim
  choose W hclass henergy using hz
  have hm : Tendsto (fun n => (z n).1) atTop (nhds z₀.1) :=
    (continuous_fst.tendsto z₀).comp hzlim
  have hsnd : Tendsto (fun n => (z n).2) atTop (nhds z₀.2) :=
    (continuous_snd.tendsto z₀).comp hzlim
  have hJ : Tendsto (fun n => stationaryEnergy (W n) (z n).1) atTop (nhds z₀.2) := by
    simpa only [henergy] using hsnd
  obtain ⟨V, hV, hJV⟩ := exists_fullStationary_limit_of_scalar_limits
    d c W (fun n => (z n).1) hclass z₀.1 z₀.2 hm hJ
  exact ⟨V, hV, hJV⟩

/-- Multiplier bounds and the actual pointwise shifted-kernel bound place
the closed attainable pairs in a compact rectangle. -/
theorem isCompact_fullStationaryValues (d c : ℝ) :
    IsCompact (fullStationaryValues (Ω := Ω) (μ := μ) d c) := by
  have hbox : IsCompact ((Set.Icc (-3 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 16)) :=
    isCompact_Icc.prod isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_fullStationaryValues d c)
  rintro z ⟨W, hW, hJ⟩
  exact ⟨hW.multiplier_mem, hJ ▸ hW.energy_mem⟩

/-- Select the minimum recorded m, equivalently the maximum ell = -m,
then the maximum actual squared kernel norm in that same multiplier fiber. -/
theorem exists_fullStationary_selection (d c : ℝ)
    (hne : ∃ (W : Model Ω μ) (m : ℝ), FullStationaryClass d c W m) :
    ∃ (W : Model Ω μ) (m : ℝ), FullStationaryClass d c W m ∧
      (∀ (V : Model Ω μ) (n : ℝ), FullStationaryClass d c V n → m ≤ n) ∧
      ∀ V : Model Ω μ, FullStationaryClass d c V m → stationaryEnergy V m ≤ stationaryEnergy W m := by
  let A := fullStationaryValues (Ω := Ω) (μ := μ) d c
  have hA : IsCompact A := isCompact_fullStationaryValues d c
  have hneA : A.Nonempty := by
    obtain ⟨W, m, hW⟩ := hne
    exact ⟨(m, stationaryEnergy W m), W, hW, rfl⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hA.exists_isMinOn hneA continuous_fst.continuousOn
  have hfiber : IsCompact (A ∩ {z : ℝ × ℝ | z.1 = z₀.1}) :=
    hA.inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨z, hz, hmax⟩ := hfiber.exists_isMaxOn ⟨z₀, hz₀, rfl⟩ continuous_snd.continuousOn
  obtain ⟨W, hW, hJ⟩ := hz.1
  refine ⟨W, z.1, hW, ?_, ?_⟩
  · intro V n hV
    rw [hz.2]
    exact hmin (show (n, stationaryEnergy V n) ∈ A from ⟨V, hV, rfl⟩)
  · intro V hV
    have h := hmax (show (z.1, stationaryEnergy V z.1) ∈ A ∩ {z : ℝ × ℝ | z.1 = z₀.1} from
      ⟨⟨V, hV, rfl⟩, hz.2⟩)
    change stationaryEnergy V z.1 ≤ z.2 at h
    rwa [← hJ] at h

/-- Actual full attainment populates the class before either selection.
Neither compactness nor an optimizer is a premise. -/
theorem exists_selected_fullStationary (d : ℝ) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ (W : Model Ω μ) (m : ℝ), FullStationaryClass d (FractionalGraph.densityLimit d) W m ∧
      (∀ (V : Model Ω μ) (n : ℝ),
        FullStationaryClass d (FractionalGraph.densityLimit d) V n → m ≤ n) ∧
      ∀ V : Model Ω μ, FullStationaryClass d (FractionalGraph.densityLimit d) V m →
        stationaryEnergy V m ≤ stationaryEnergy W m :=
  exists_fullStationary_selection d _ (fullStationaryClass_nonempty d hd)

/-- A real failure of the benchmark bound yields an actual model selected
by both extrema at a positive global excess maximum. Every comparison is
against actual fully feasible models under arbitrary probability laws. -/
theorem exists_selected_full_positive_global_excess
    (hfailure : ∃ d ∈ Set.Icc (0 : ℝ) (1 / 2),
      benchmark d < FractionalGraph.densityLimit d) :
    ∃ (d : ℝ) (W : Model Ω μ) (m : ℝ), d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧
      FullStationaryClass d (FractionalGraph.densityLimit d) W m ∧
      0 < objective W - benchmark (density W) ∧
      (∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
        FullFeasible V → objective V - benchmark (density V) ≤
          objective W - benchmark (density W)) ∧
      (∀ (V : Model Ω μ) (n : ℝ),
        FullStationaryClass d (FractionalGraph.densityLimit d) V n → m ≤ n) ∧
      ∀ V : Model Ω μ, FullStationaryClass d (FractionalGraph.densityLimit d) V m →
        stationaryEnergy V m ≤ stationaryEnergy W m := by
  obtain ⟨U, _, hd, hU, hpositive, hglobal, _⟩ := exists_full_positive_global_excess
    (Ω := Ω) (μ := μ) hfailure
  obtain ⟨W, m, hW, hmin, hmax⟩ := exists_selected_fullStationary (Ω := Ω) (μ := μ) (density U)
    ⟨by linarith [hd.1], hd.2⟩
  have hc : objective W = objective U := hW.objective_eq.trans hU.symm
  refine ⟨density U, W, m, hd, hW, ?_, ?_, hmin, hmax⟩
  · rwa [hc, hW.density_eq]
  · intro ν _ V hV
    simpa only [hc, hW.density_eq] using hglobal ν V hV

end Erdos1017.CappedModel

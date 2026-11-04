module

public import Erdos1017.Models.Decorated.DecoratedCappedCompactness
public import Erdos1017.Models.Capped.CappedDensityRestoration
public import Mathlib.Topology.Order.IsLUB

/-!
# Attainment of the capped value

The capped value (`capValue`) is the supremum of the charge objective over
feasible capped models at a prescribed density; every admissible density has a
zero-charge competitor, and the fixed-density objective is attained by a
feasible decorated kernel (`exists_fixedMeasureMaximizer`, `exists_maximizer`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual supremum of the charge objective over feasible capped models
with exactly the prescribed edge density. -/
def capValue (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (r : ℕ) (d : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ W : Model Ω μ, Feasible r W ∧ density W = d ∧ objective W = v}

private def neutralPresent : CappedColor := CappedColor.present 0 (by norm_num)

/-- The constant present color with zero charge is feasible at every order. -/
private def neutralPresentModel : Model Ω μ where
  kernel := Kernel.const (Ω × Ω) (Measure.dirac neutralPresent)
  markov := by infer_instance
  symm := Filter.Eventually.of_forall (fun _ => by simp [Kernel.const_apply])

private theorem neutralPresentModel_feasible (r : ℕ) :
    Feasible r (neutralPresentModel (Ω := Ω) (μ := μ)) := by
  intro n _ _
  filter_upwards with x
  have hcolors : ∀ᵐ c ∂cliqueLaw (neutralPresentModel (Ω := Ω) (μ := μ)) x,
      c = fun _ => neutralPresent := by
    change ∀ᵐ c ∂Measure.pi (fun _ : CliquePair n => Measure.dirac neutralPresent),
      c = fun _ => neutralPresent
    have h := Measure.ae_eq_pi
      (μ := fun _ : CliquePair n => Measure.dirac neutralPresent)
      (f := fun _ => id) (f' := fun _ _ => neutralPresent)
      (fun _ => ae_eq_dirac (fun c : CappedColor => c))
    filter_upwards [h] with c hc
    exact hc
  filter_upwards [hcolors] with c hc
  subst c
  simp [violation, neutralPresent, CappedColor.charge, CappedColor.present]

private theorem neutralPresentModel_density [IsProbabilityMeasure μ] :
    density (neutralPresentModel (Ω := Ω) (μ := μ)) = 1 / 2 := by
  simp [density, neutralPresentModel, neutralPresent, DecoratedKernel.moment,
    Kernel.const_apply, CappedColor.adjacency, CappedColor.present]

private theorem neutralPresentModel_objective [IsProbabilityMeasure μ] :
    objective (neutralPresentModel (Ω := Ω) (μ := μ)) = 0 := by
  simp [objective, neutralPresentModel, neutralPresent, DecoratedKernel.moment,
    Kernel.const_apply, CappedColor.charge, CappedColor.present]

/-- Every admissible density has a feasible zero-charge competitor. -/
theorem exists_zeroCharge_competitor [IsProbabilityMeasure μ] (r : ℕ) (d : ℝ)
    (hd : d ∈ Icc 0 (1 / 2)) :
    ∃ W : Model Ω μ, Feasible r W ∧ density W = d ∧ objective W = 0 := by
  let t : unitInterval := ⟨1 - 2 * d, by linarith [hd.2], by linarith [hd.1]⟩
  refine ⟨thin (neutralPresentModel (Ω := Ω) (μ := μ)) t,
    feasible_thin _ (neutralPresentModel_feasible r) t, ?_, ?_⟩
  · rw [density_thin, neutralPresentModel_density]
    change (1 - (1 - 2 * d)) * (1 / 2 : ℝ) = d
    ring
  · rw [objective_thin, neutralPresentModel_objective]
    ring

variable [IsProbabilityMeasure μ] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [NullSingletonClass μ]

/-- The fixed-density capped objective is attained by an actual feasible
decorated kernel. This holds at every order, including the imposed orders
`r ≥ 2`. -/
theorem exists_fixedMeasureMaximizer (r : ℕ) (d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    ∃ W : Model Ω μ, Feasible r W ∧ density W = d ∧
      objective W = capValue Ω μ r d ∧ IsFixedMeasureMaximizer r W := by
  let S : Set ℝ :=
    {v | ∃ W : Model Ω μ, Feasible r W ∧ density W = d ∧ objective W = v}
  have hnonempty : S.Nonempty := by
    obtain ⟨W, hW, hdW, hoW⟩ := exists_zeroCharge_competitor (μ := μ) r d hd
    exact ⟨0, W, hW, hdW, hoW⟩
  have hbdd : BddAbove S := by
    refine ⟨d, ?_⟩
    rintro v ⟨W, _, hdW, rfl⟩
    exact (objective_le_density W).trans_eq hdW
  obtain ⟨v, _, hvlim, hvS⟩ := exists_seq_tendsto_sSup hnonempty hbdd
  choose W hW hdW hoW using hvS
  obtain ⟨V, φ, hφ, hV, _, hdenlim, hobjlim⟩ :=
    exists_feasible_sampledTest_limit W r hW
  have hdlim : Tendsto (fun _ : ℕ => d) atTop (𝓝 (density V)) := by
    simpa only [hdW] using hdenlim
  have hdV : density V = d :=
    tendsto_nhds_unique hdlim tendsto_const_nhds
  have hvl : Tendsto (fun k => v (φ k)) atTop (𝓝 (sSup S)) :=
    hvlim.comp hφ.tendsto_atTop
  have holim : Tendsto (fun k => v (φ k)) atTop (𝓝 (objective V)) := by
    simpa only [hoW] using hobjlim
  have hoV : objective V = capValue Ω μ r d := by
    change objective V = sSup S
    exact tendsto_nhds_unique holim hvl
  refine ⟨V, hV, hdV, hoV, ⟨hV, ?_⟩⟩
  intro U hU hdU
  have hmem : objective U ∈ S := ⟨U, hU, hdU.trans hdV, rfl⟩
  rw [hoV]
  exact le_csSup hbdd hmem

/-- On an atomless standard-Borel presentation, the attained model also
compares all absolutely continuous latent probability laws. -/
theorem exists_maximizer [StandardBorelSpace Ω] (r : ℕ) (d : ℝ)
    (hd : d ∈ Icc 0 (1 / 2)) :
    ∃ W : Model Ω μ, IsMaximizer r W ∧ density W = d ∧
      objective W = capValue Ω μ r d := by
  obtain ⟨W, _, hdW, hoW, hm⟩ := exists_fixedMeasureMaximizer (μ := μ) r d hd
  exact ⟨W, isMaximizer_of_isFixedMeasureMaximizer W hm, hdW, hoW⟩

end Erdos1017.CappedModel

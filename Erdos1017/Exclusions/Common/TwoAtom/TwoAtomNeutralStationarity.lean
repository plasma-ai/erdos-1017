module

public import Erdos1017.Exclusions.Common.TwoAtom.SelectedTwoAtomChargeBox
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomPhysicalStationarity

/-!
# Strict demand order from neutral stationarity

At `u = b` the neutral competitor receives its own model and stationary rows, so
the weak demand order `u ≤ b` becomes strict for the entry or any represented
active model.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.TwoAtomCountGate

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m : ℝ}

/-- At u=b the genuine neutral competitor receives its own actual model
and stationary rows, even though its AB charge leaves the sliced family. -/
theorem exists_neutral_own_rows (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2))
    (delta : ℝ) (hdelta : 0 ≤ delta) (hdh : delta ≤ x 0) (hdp : delta ≤ x 2)
    (hub : μ.real (label ⁻¹' {2}) = μ.real (label ⁻¹' {1})) :
    ∃ ell nu, FourRegionShiftedRows x
      (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3}))
      (1 - delta) (-x 0 + delta) ell nu := by
  have hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hcost : FiniteCappedSamplingCost.physicalObjective μ
      (fun z w => neutralBlockCharge x delta (label z) (label w)) = CappedModel.objective W := by
    have hgain : μ.real (label ⁻¹' {0}) *
        (μ.real (label ⁻¹' {2}) - μ.real (label ⁻¹' {1})) * delta = 0 := by rw [hub]; ring
    rw [neutral_physicalObjective label hlabel x delta, hgain, add_zero]
    rw [← block_physicalObjective (μ := μ) label hlabel x]
    unfold CappedModel.objective FiniteCappedSamplingCost.physicalObjective
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
  obtain ⟨hGsym, _, _⟩ := block_charge_properties x
  obtain ⟨hysym, hyzero⟩ := neutral_block_charge_properties x delta
  obtain ⟨V, m', hV, hmomV, _, _⟩ :=
    exists_finite_block_fullStationaryClass_of_full_scalar_optimum W hW.full hopt hphysical
      (by rwa [hW.density_eq]) (by rwa [hW.density_eq, hW.objective_eq])
      label hlabel hpositive blockAdjacency hGsym (blockCharge x) (neutralBlockCharge x delta)
      (Eventually.of_forall hmom) hysym hyzero
      (neutral_full_scalar_tests x hx delta hdelta hdh hdp μ label) hcost
  have hV' : FullStationaryClass d c V m' := by
    rwa [hW.density_eq, hW.objective_eq] at hV
  exact ⟨-m', 2 * (c - m' * d),
    fourRegionShiftedRows_of_neutral_stationary hV' label hlabel hpositive x delta hmomV⟩

/-- The weak original demand order becomes strict for the actual entry
or any represented active model. The neutral model is constructed inside;
its multiplier and row constant are never transferred from the old dual. -/
theorem u_lt_b_of_fullStationaryClass (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hh : 0 < x 0)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2))
    (hub : μ.real (label ⁻¹' {2}) ≤ μ.real (label ⁻¹' {1})) :
    μ.real (label ⁻¹' {2}) < μ.real (label ⁻¹' {1}) := by
  have hrows := fourRegionShiftedRows_of_block_stationary hW label hlabel hpositive x hmom
  have ha : 0 < μ.real (label ⁻¹' {0}) :=
    ENNReal.toReal_pos (hpositive 0).ne' (measure_ne_top _ _)
  have he : 0 < μ.real (label ⁻¹' {3}) :=
    ENNReal.toReal_pos (hpositive 3).ne' (measure_ne_top _ _)
  apply u_lt_b_of_neutral_stationarity hx hh ha he hub hrows
  intro delta hdelta hdh hdp heq
  exact exists_neutral_own_rows hW hd hgap hphysical label hlabel hpositive x hx hmom
    delta hdelta.le hdh hdp heq

end Erdos1017.TwoAtomCountGate

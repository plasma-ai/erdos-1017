module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomE2OwnData
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomContactGate
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomNeutralStationarity
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFourRegionEntry
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredWeakMassOrder
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredActiveMoments

/-!
# Zero-body two-atom gate at the `E₂` contact

The saturated zero-body two-atom model cannot have both diffuse regions positive
at an `E₂` contact with `0 < q ≤ 2/9`; one original physical primal supplies
every active dual (`no_e2_zero_body_of_two_atoms`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The actual saturated zero-body two-atom model cannot have both diffuse
regions positive at the stated E2 contact. One original physical primal
supplies every active dual's tight residual count law; each active dual
separately receives its own model, multiplier and stationary rows.
Exterior elimination and benchmark contact remain explicit inputs. -/
theorem no_e2_zero_body_of_two_atoms
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    hdq ▸ LowerE2Scalar.contact_density_mem hq
  let label := S.coveredFourLabel a
  have hlabel : Measurable label := S.measurable_coveredFourLabel a
  have hpositive : ∀ i, 0 < μ (label ⁻¹' {i}) :=
    S.coveredFourLabel_fibers_positive r a hpair.1 hatoms hR hE
  obtain ⟨hA, hB, hRl, hEl⟩ := S.coveredFourLabel_fibers r a hpair.1 hatoms
  let aMass := μ.real (label ⁻¹' {0})
  let bMass := μ.real (label ⁻¹' {1})
  let uMass := μ.real (label ⁻¹' {2})
  let eMass := μ.real (label ⁻¹' {3})
  have hpos (i : Fin 4) : 0 < μ.real (label ⁻¹' {i}) :=
    ENNReal.toReal_pos (hpositive i).ne' (measure_ne_top _ _)
  have hb : 0 < bMass := hpos 1
  have hu : 0 < uMass := hpos 2
  have he : 0 < eMass := hpos 3
  obtain ⟨V, hV, hmom, hphysical, hh, hx, hentryValue⟩ :=
    S.exists_covered_four_region_entry r a hW hd hgap hpair hzero hR hE hatoms
  have hrows := TwoAtomCountGate.fourRegionShiftedRows_of_block_stationary
    hV label hlabel hpositive (S.coveredEntry r a) hmom
  obtain ⟨hAR, _, _, _, hBE, _⟩ := TwoAtomCountGate.own_block_present_floors
    hV hd hgap label hpositive (S.coveredEntry r a) hmom
  have hab : aMass < bMass := hrows.a_lt_b hh hu.le he (by linarith) hBE
  have hweak : uMass ≤ bMass := by
    change μ.real (label ⁻¹' {2}) ≤ μ.real (label ⁻¹' {1})
    rw [hRl, hB]
    exact S.covered_R_mass_le_root r a hW hd hgap hpair hzero
  have hbu : uMass < bMass := TwoAtomCountGate.u_lt_b_of_fullStationaryClass
    hV hd hgap hphysical label hlabel hpositive (S.coveredEntry r a) hx hh hmom hweak
  have hopt : objective V = FractionalGraph.densityLimit (density V) := by
    rw [hV.objective_eq, hV.density_eq]
    exact hV.optimal
  have hmax (x : TwoAtomCountGate.Coefficients) (hx : x ∈ TwoAtomCountGate.feasible) :
      TwoAtomCountGate.objective aMass bMass uMass eMass x ≤ c := by
    have h := TwoAtomCountGate.block_objective_le_full_optimum V hopt label hlabel
      (Eventually.of_forall (fun p => (hmom p).1)) x hx
    rwa [hV.objective_eq] at h
  have hentryCost : TwoAtomCountGate.objective aMass bMass uMass eMass
      (S.coveredEntry r a) = c := by
    dsimp only [aMass, bMass, uMass, eMass, label]
    rw [hA, hB, hRl, hEl]
    exact hentryValue
  have hgraph := S.ae_covered_four_graph r a hW hd hgap hpair hzero hatoms
  obtain ⟨P, hdata⟩ := S.exists_covered_active_tight_moment_data r a hW hd hgap
    hpair hzero hR hE label hlabel hA hB hRl hEl hgraph
  apply TwoAtomCountGate.no_optimal_face_with_own_rows_moments hab hb hu he hbu
    ⟨S.coveredEntry r a, ⟨hx, hentryCost⟩, hh⟩ hmax
  intro x hx hh
  obtain ⟨U, m', hU, hmomU, _, _⟩ :=
    TwoAtomCountGate.exists_active_block_fullStationaryClass V hV.full hopt hphysical
      (by rwa [hV.density_eq]) (by rwa [hV.density_eq, hV.objective_eq])
      label hlabel hpositive (TwoAtomCountGate.blockCharge (S.coveredEntry r a))
      (Eventually.of_forall hmom) x hx.1
      (by simpa only [hV.objective_eq] using hx.2)
  have hU' : FullStationaryClass d c U m' := by
    rwa [hV.density_eq, hV.objective_eq] at hU
  have hglobalU : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective U - benchmark (density U) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hU'.objective_eq, hU'.density_eq] using
      hglobal ν T hT
  obtain ⟨hguards, hownRows⟩ := TwoAtomCountGate.e2_own_count_data hU'
    hq hdq hvalue hderiv hgap hglobalU label hlabel hpositive x hx.1 hh hmomU hbu
  have hcost : TwoAtomCountGate.objective
      (μ.real {v | S.ρ v = a.val}) (μ.real {v | S.ρ v = r.val})
      (μ.real (S.D ∩ S.rootNeighborhood a)) (μ.real (S.D \ S.rootNeighborhood a)) x = c := by
    have h := hx.2
    dsimp only [aMass, bMass, uMass, eMass, label] at h
    rwa [hA, hB, hRl, hEl] at h
  obtain ⟨D, hDlaw⟩ := hdata x hx.1 hcost
  have hfixedLaw : D.law = PhysicalPrimal.countMeasure P.orderCap
      (PhysicalPrimal.withoutRegion P.laws {v | S.ρ v = a.val})
      (S.D ∩ S.rootNeighborhood a) (S.D \ S.rootNeighborhood a) := hDlaw
  refine ⟨-m', hguards, hownRows, ?_⟩
  rw [← hA, ← hB, ← hRl, ← hEl] at D
  exact ⟨D⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

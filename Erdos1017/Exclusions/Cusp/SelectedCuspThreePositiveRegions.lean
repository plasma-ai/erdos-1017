module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomOwnCountData
public import Erdos1017.Exclusions.Cusp.SelectedCuspAtomGuards
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNoExterior
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomContactGate
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomNeutralStationarity
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFourRegionEntry
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredWeakMassOrder
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredActiveMoments

/-!
# Zero-body third-cusp case with both diffuse regions positive

The saturated zero-body third-cusp case is impossible with both diffuse regions
positive: the two-atom model is ruled out by one original physical primal, and
the own contact guards eliminate exterior atoms first.
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

/-- The actual third-cusp saturated zero-body two-atom model cannot have
both diffuse regions positive. One original physical primal
supplies every active dual's tight residual count law; each active dual
separately receives its own model, multiplier and stationary rows.
Exterior elimination and benchmark contact remain explicit inputs. -/
theorem no_cusp_three_zero_body_of_two_atoms
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
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
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
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
  let I := label ⁻¹' {1}
  have hI : MeasurableSet I := hlabel (measurableSet_singleton 1)
  have hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I),
      adjacencyKernel U p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hI.prod hI)).mpr
    exact Eventually.of_forall (fun p hp => by
      have hi : label p.1 = 1 := hp.1
      have hj : label p.2 = 1 := hp.2
      change U.moment CappedColor.adjacency p = 0
      simp [(hmomU p).1, hi, hj, TwoAtomCountGate.blockAdjacency])
  obtain ⟨_, hell, _, _, _, _, hbonus, _⟩ :=
    hU'.cusp_independent_set_contact_guards 3 (by omega) (by norm_num; exact hdk)
      hgap hglobalU I hI hind
  obtain ⟨hguards, hownRows⟩ := TwoAtomCountGate.own_count_data_of_half_slope_bonus hU'
    hd hgap label hlabel hpositive x hx.1 hh hmomU hbu (by linarith [hell.1]) hbonus
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

/-- The original saturated zero-body third-cusp case is impossible with both
diffuse regions positive. Actual own contact guards eliminate exterior
atoms before the original physical all-count moment contradiction applies. -/
theorem no_cusp_three_zero_body_of_positive_regions
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  obtain ⟨_, hell, _, _, _, _, hbonus, _⟩ :=
    S.cusp_atom_contact_guards r hW 3 (by omega) (by norm_num; exact hdk) hgap hglobal
  have hatoms := S.covered_atoms_eq_root_or_saturated r a hW hd hgap hpair hzero hR hE
    (by linarith [hell.1]) hbonus
  exact S.no_cusp_three_zero_body_of_two_atoms r a hW hdk hgap hglobal
    hpair hzero hR hE hatoms

end Erdos1017.CappedModel.SelectedHighLowStructure

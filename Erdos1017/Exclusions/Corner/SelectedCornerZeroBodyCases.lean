module

public import Erdos1017.Exclusions.Corner.SelectedCornerAtomGuards
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomOwnCountData
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomContactGate
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomNeutralStationarity
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFourRegionEntry
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredWeakMassOrder
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredActiveMoments
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNoExterior
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedZeroBody

/-!
# Cases of zero body energy at the corner

Corner contact excludes zero body energy when the root has no saturated partner,
using its own half slope and strict bonus, and the saturated case cannot have
both diffuse regions positive, exterior atoms being eliminated by the own corner
bonus.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original corner contact excludes zero body energy when the root
has no saturated partner. Its own half-slope and strict bonus are derived
from the actual one-sided corner bracket, without a smooth derivative. -/
theorem not_corner_zero_body_of_no_saturated_partner
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hnosat : ∀ u : S.I, u ≠ r → ¬S.IsSaturatedAtomPair r u) : False := by
  obtain ⟨hell, _, _, hbonus, _⟩ :=
    S.corner_atom_contact_guards r hW hd hgap he heq hglobal
  exact S.not_zero_body_of_no_saturated_partner r hW hd hgap hell.1 hzero hbonus hnosat

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

private theorem no_corner_zero_body_of_two_atoms
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) : False := by
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
  have hEpos : 0 < eMass := hpos 3
  obtain ⟨V, hV, hmom, hphysical, hh, hx, hentryValue⟩ :=
    S.exists_covered_four_region_entry r a hW hd hgap hpair hzero hR hE hatoms
  have hrows := TwoAtomCountGate.fourRegionShiftedRows_of_block_stationary
    hV label hlabel hpositive (S.coveredEntry r a) hmom
  obtain ⟨hAR, _, _, _, hBE, _⟩ := TwoAtomCountGate.own_block_present_floors
    hV hd hgap label hpositive (S.coveredEntry r a) hmom
  have hab : aMass < bMass := hrows.a_lt_b hh hu.le hEpos (by linarith) hBE
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
  apply TwoAtomCountGate.no_optimal_face_with_own_rows_moments hab hb hu hEpos hbu
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
  have hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), adjacencyKernel U p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hI.prod hI)).mpr
    exact Eventually.of_forall (fun p hp => by
      have hi : label p.1 = 1 := hp.1
      have hj : label p.2 = 1 := hp.2
      change U.moment CappedColor.adjacency p = 0
      simp [(hmomU p).1, hi, hj, TwoAtomCountGate.blockAdjacency])
  obtain ⟨hell, _, _, hbonus, _⟩ :=
    hU'.corner_independent_set_contact_guards hd hgap he heq hglobalU I hI hind
  obtain ⟨hguards, hownRows⟩ := TwoAtomCountGate.own_count_data_of_half_slope_bonus
    hU' hd hgap label hlabel hpositive x hx.1 hh hmomU hbu hell.1 hbonus
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

/-- At the actual W/E2 corner, the original saturated zero-body case
cannot have both diffuse regions positive. Exterior atoms are eliminated
by the derived own corner bonus before the fixed original count law is
combined with every active dual's own rows. Null regions are not covered here. -/
theorem no_corner_zero_body_of_positive_regions
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : False := by
  obtain ⟨hell, _, _, hbonus, _⟩ :=
    S.corner_atom_contact_guards r hW hd hgap he heq hglobal
  have hatoms := S.covered_atoms_eq_root_or_saturated r a hW hd hgap hpair hzero hR hE
    hell.1 hbonus
  exact no_corner_zero_body_of_two_atoms S r a hW hd hgap he heq hglobal
    hpair hzero hR hE hatoms

end Erdos1017.CappedModel.SelectedHighLowStructure

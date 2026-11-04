module

public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedBareRepeat
public import Erdos1017.Exclusions.Common.Physical.IndependentStarPerturbationIntegrals

/-!
# Degree of an unsaturated exterior atom

Two-sided signed star edits pass every clique test for an unsaturated exterior
atom, forcing its outside neighbor mass to equal the root mass and its
neighborhood degree to be exactly twice the root mass, and the degree-separation
rule then merges any two such atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Actual absence of saturation and the bare-repeat threshold give the
strict two-sided radius. Half of the original delta is already a uniform
body penalty, so no reciprocal root mass or edited multiplier is needed. -/
theorem unsaturated_atom_star_margin (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnot : ¬S.IsSaturatedAtomPair r u) :
    0 < 1 - S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) ∧
      1 - S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) < (1 + m) / 2 := by
  have hbare := S.zero_body_bare_repeat r u hru hW hd hgap hell hzero hratio
  have heq := S.ae_atomic_rootChargeRow r u hW hd hgap
  have hlt := S.ae_rootChargeRow_lt_one_of_not_saturated r u hru hW hd hgap hnot
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' (heq.and hlt)
  have ht := hx.2
  rw [hx.1] at ht
  constructor <;> linarith

/-- Both signed star edits satisfy every actual original clique test.
All geometric and coefficient inputs to the generic edit are derived from
the same original selected model and its original multiplier. -/
theorem unsaturated_atom_star_full_tests
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnot : ¬S.IsSaturatedAtomPair r u) (eps : ℝ)
    (heps : |eps| ≤ IndependentStarPerturbation.radius
      (S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u)) ((1 + m) / 2)) :
    ∀ n, FiniteArity.FeasibleOrder μ (PhysicalRepresentative.adjacency W m)
      (IndependentStarPerturbation.charge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val} {x | S.ρ x = u.val} eps) n := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨ht, hp⟩ := S.unsaturated_atom_star_margin r u hru hW hd hgap hell hzero hratio hnot
  have hdisj : Disjoint {x | S.ρ x = r.val} {x | S.ρ x = u.val} := by
    apply Set.disjoint_left.mpr
    exact fun x hx hy => hru (Subtype.ext (hx.symm.trans hy))
  have hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
      Y p.1 p.2 = S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) := by
    filter_upwards [S.ae_atomic_charge_block r u hW,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hb hy hx hz
    exact hy.trans (hb hx hz)
  have hbody : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      A p.1 p.2 = true → Y p.1 p.2 ≤ -((1 + m) / 2) := by
    filter_upwards [S.ae_body_penalty_gt_half_delta_of_zero_body r hW hd hgap hzero hratio,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hp hg hy hx hz ha
    have hG : adjacencyKernel W p.1 p.2 = 1 := by
      change W.moment CappedColor.adjacency p = 1
      change PhysicalRepresentative.adjacency W m p.1 p.2 = true at ha
      simpa only [ha, ite_true] using hg
    change Y p.1 p.2 = chargeKernel W p.1 p.2 at hy
    linarith [hp hx hz hG]
  exact IndependentStarPerturbation.full_feasible μ A Y
    (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m)
    _ _ hdisj _ _ eps (by linarith) hp heps
    (S.ae_root_fiber_physical_independent r hW hd hgap)
    (S.ae_root_fiber_physical_independent u hW hd hgap) hstar hbody
    (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic)

/-- The genuine bounded signed scalar comparison bounds both edits by
this original optimum. The new charges may leave the compact color box. -/
theorem unsaturated_atom_star_objective_le
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnot : ¬S.IsSaturatedAtomPair r u) (eps : ℝ)
    (heps : |eps| ≤ IndependentStarPerturbation.radius
      (S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u)) ((1 + m) / 2)) :
    FiniteCappedSamplingCost.physicalObjective μ
      (IndependentStarPerturbation.charge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val} {x | S.ρ x = u.val} eps) ≤ c := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = u.val}
  have hs := hW.strict_gap_structure hd hgap
  have hjoined : ∀ᵐ p ∂μ.prod μ,
      (p.1 ∈ I ∧ p.2 ∈ J) ∨ (p.2 ∈ I ∧ p.1 ∈ J) → A p.1 p.2 = true := by
    have hu := S.ae_root_universal_of_zero_body r hW hd hgap hzero
    filter_upwards [hu,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hu]
      with p hp hq h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact (hp hx).mpr (fun he => hru (Subtype.ext (he.symm.trans hy)))
    · exact (PhysicalRepresentative.adjacency_symm W m p.1 p.2).trans
        ((hq hx).mpr (fun he => hru (Subtype.ext (he.symm.trans hy))))
  have hB (p : Ω × Ω) : ‖IndependentStarPerturbation.charge A Y I J eps p.1 p.2‖ ≤ 3 + |eps| := by
    rw [Real.norm_eq_abs]
    exact IndependentStarPerturbation.charge_abs_bound A Y I J eps 3
      (fun x y => PhysicalRepresentative.charge_bound W m x y) p.1 p.2
  have hbound := FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    A (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.measurable_adjacency W m)
    (IndependentStarPerturbation.charge A Y I J eps)
    (IndependentStarPerturbation.measurable_charge A (PhysicalRepresentative.measurable_adjacency W m)
      Y (PhysicalRepresentative.measurable_charge W m) I J
      (S.hfibers r.val r.property).1 (S.hfibers u.val u.property).1 eps)
    (3 + |eps|) hB
    (Eventually.of_forall (fun p => IndependentStarPerturbation.charge_symm A Y
      (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m) I J eps _ _))
    (IndependentStarPerturbation.charge_zero_ae μ A Y I J eps
      (Eventually.of_forall (fun p => PhysicalRepresentative.charge_zero_of_nonedge W m _ _)) hjoined)
    (S.unsaturated_atom_star_full_tests r u hru hW hd hgap hell hzero hratio hnot eps heps)
  rw [PhysicalRepresentative.density_eq W m hs.strict_support, hW.density_eq, ← hW.optimal] at hbound
  exact hbound

/-- The original whole cell has its literal original outside-neighbor
section mass. Homogeneity is taken from the same physical row event. -/
theorem ae_atom_outside_neighbor_mass (S : SelectedHighLowStructure W m) (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, S.ρ x = u.val → IndependentStarPerturbation.outsideNeighborMass μ
      (PhysicalRepresentative.adjacency W m) {x | S.ρ x = r.val} {x | S.ρ x = u.val} x =
        μ.real (S.rootNeighborhood u \ {x | S.ρ x = r.val}) := by
  filter_upwards [Measure.ae_ae_of_ae_prod (S.ae_root_adjacency u hW hd hgap)] with x hx hu
  have he : IndependentStarPerturbation.outsideNeighbors (PhysicalRepresentative.adjacency W m)
      {x | S.ρ x = r.val} {x | S.ρ x = u.val} x =ᵐ[μ]
        S.rootNeighborhood u \ {x | S.ρ x = r.val} := by
    filter_upwards [hx] with y hy
    apply propext
    have ha := hy hu
    change (y ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val} ∧
      PhysicalRepresentative.adjacency W m x y = true) ↔
      y ∈ S.rootNeighborhood u ∧ S.ρ y ≠ r.val
    rw [ha]
    have hn : y ∈ S.rootNeighborhood u → S.ρ y ≠ u.val := fun h => h.1
    simp only [mem_union, mem_ofPred_eq, not_or]
    tauto
  unfold IndependentStarPerturbation.outsideNeighborMass
  exact congrArg ENNReal.toReal (measure_congr he)

/-- Genuine two-sided scalar comparisons force the original outside
neighbor mass of each unsaturated exterior atom to equal the root mass. -/
theorem unsaturated_atom_outside_mass_eq (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnot : ¬S.IsSaturatedAtomPair r u) :
    μ.real (S.rootNeighborhood u \ {x | S.ρ x = r.val}) = μ.real {x | S.ρ x = r.val} := by
  let t := S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u)
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = u.val}
  let s := μ.real (S.rootNeighborhood u \ I)
  obtain ⟨ht, hp⟩ := S.unsaturated_atom_star_margin r u hru hW hd hgap hell hzero hratio hnot
  have hrad : 0 < IndependentStarPerturbation.radius t ((1 + m) / 2) :=
    IndependentStarPerturbation.radius_pos (by dsimp [t]; linarith) hp
  let eps := IndependentStarPerturbation.radius t ((1 + m) / 2) / 2
  have heps : 0 < eps := half_pos hrad
  have hepsB : |eps| ≤ IndependentStarPerturbation.radius t ((1 + m) / 2) := by
    rw [abs_of_pos heps]
    dsimp [eps]
    linarith
  have hdisj : Disjoint I J := by
    apply Set.disjoint_left.mpr
    exact fun x hx hy => hru (Subtype.ext (hx.symm.trans hy))
  have hY : Integrable (Function.uncurry Y) (μ.prod μ) := Integrable.of_bound
    (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    (Eventually.of_forall (fun p => by
      change ‖Y p.1 p.2‖ ≤ 3
      rw [Real.norm_eq_abs]
      exact PhysicalRepresentative.charge_bound W m p.1 p.2))
  have hobj : FiniteCappedSamplingCost.physicalObjective μ Y = c :=
    (PhysicalRepresentative.objective_eq W m (hW.strict_gap_structure hd hgap).strict_support).trans
      hW.objective_eq
  have hform (e : ℝ) := IndependentStarPerturbation.physicalObjective_charge_of_constant_outside
    A (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.adjacency_symm W m)
    Y hY I J (S.hfibers r.val r.property).1 (S.hfibers u.val u.property).1 hdisj e s
    (S.ae_atom_outside_neighbor_mass r u hW hd hgap)
  have hplus := S.unsaturated_atom_star_objective_le r u hru hW hd hgap hell hzero hratio hnot
    eps hepsB
  have hminus := S.unsaturated_atom_star_objective_le r u hru hW hd hgap hell hzero hratio hnot
    (-eps) (by simpa only [abs_neg] using hepsB)
  rw [hform eps, hobj] at hplus
  rw [hform (-eps), hobj] at hminus
  have hJ : 0 < μ.real J := ENNReal.toReal_pos (S.hfibers u.val u.property).2.1.ne'
    (measure_ne_top _ _)
  have hgain : eps * μ.real J * (μ.real I - s) = 0 := by
    apply le_antisymm
    · linarith only [hplus]
    · nlinarith only [hminus]
  have hdiff := (mul_eq_zero.mp hgain).resolve_left (mul_ne_zero heps.ne' hJ.ne')
  change s = μ.real I
  linarith only [hdiff]

/-- Original universality of the root includes its whole positive fiber
in every exterior atom's actual neighborhood, on one original vertex event. -/
theorem ae_root_mem_exterior_neighborhood (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ x ∂μ, S.ρ x = r.val → x ∈ S.rootNeighborhood u := by
  have hroot := S.neutral_atom_adjacency r hW hd hgap
    (S.root_neutral_of_zero_body r hW hd hgap hzero)
  have hblock : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = if true = true then 1 else 0 := by
    filter_upwards [(Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      hroot, adjacencyKernel_symm W] with p hr hsym hx hy
    have hn : S.ρ p.1 ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans hx))
    exact hsym.trans ((hr hy).trans (ite_eq_right hn))
  exact (S.ae_rootNeighborhood_on_constant_block u r hW hd hgap true hblock).mono
    (fun x hx hr => (hx hr).mpr rfl)

/-- The actual original neighborhood degree of every unsaturated exterior
atom is exactly twice the same original root mass. -/
theorem unsaturated_atom_neighborhood_mass_eq_twice
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnot : ¬S.IsSaturatedAtomPair r u) :
    μ.real (S.rootNeighborhood u) = 2 * μ.real {x | S.ρ x = r.val} := by
  have hs := S.unsaturated_atom_outside_mass_eq r u hru hW hd hgap hell hzero hratio hnot
  have he : S.rootNeighborhood u ∩ {x | S.ρ x = r.val} =ᵐ[μ] {x | S.ρ x = r.val} := by
    filter_upwards [S.ae_root_mem_exterior_neighborhood r u hru hW hd hgap hzero] with x hx
    exact propext ⟨fun h => h.2, fun h => ⟨hx h, h⟩⟩
  have hmass : μ.real (S.rootNeighborhood u ∩ {x | S.ρ x = r.val}) = μ.real {x | S.ρ x = r.val} :=
    congrArg ENNReal.toReal (measure_congr he)
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := S.rootNeighborhood u)
    (S.hfibers r.val r.property).1
  rw [hmass, hs] at hsplit
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The original selected degree value equals the original whole
neighborhood mass, without choosing a diagonal row representative. -/
theorem wholeRowDegree_eq_neighborhood_mass (S : SelectedHighLowStructure W m) (u : S.I) :
    wholeRowDegree u.val = μ.real (S.rootNeighborhood u) := by
  unfold wholeRowDegree
  have he : (fun y => if 0 < u.val y then (1 : ℝ) else 0) =ᵐ[μ]
      (S.rootNeighborhood u).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [S.ae_rootNeighborhood_iff u] with y hy
    by_cases h : y ∈ S.rootNeighborhood u
    · simp [h, hy.mp h]
    · have hn : ¬0 < u.val y := fun hp => h (hy.mpr hp)
      simp only [hn, ite_false, indicator_of_notMem h]
  rw [integral_congr_ae he, integral_indicator (S.measurableSet_rootNeighborhood u), setIntegral_const]
  simp

/-- Actual degree equality is recorded on each original positive whole
fiber, for use with the selected structure's same degree-separation event. -/
theorem ae_unsaturated_atom_degree_eq_twice
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnot : ¬S.IsSaturatedAtomPair r u) :
    ∀ᵐ x ∂μ, S.ρ x = u.val → adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x =
      2 * μ.real {x | S.ρ x = r.val} := by
  have hdg := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
    (wholeRowFiber_degree W m S.ρ u.val (S.hfibers u.val u.property).2.2.2)
  have he := S.wholeRowDegree_eq_neighborhood_mass u
  rw [S.unsaturated_atom_neighborhood_mass_eq_twice r u hru hW hd hgap hell hzero hratio hnot] at he
  exact hdg.mono (fun x hx hu => (hx hu).trans he)

/-- The original selected degree-separation rule merges any two exterior
atoms after their genuine signed variations have paid degree2A. No new
minimum-multiplier premise or selected structure is supplied. -/
theorem unsaturated_exterior_atom_unique
    (S : SelectedHighLowStructure W m) (r u v : S.I) (hru : r ≠ u) (hrv : r ≠ v)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnotu : ¬S.IsSaturatedAtomPair r u) (hnotv : ¬S.IsSaturatedAtomPair r v) : u = v := by
  by_contra huv
  have hs := hW.strict_gap_structure hd hgap
  have hfalse : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 = v.val → False := by
    filter_upwards [S.ae_exterior_atomic_blocks_missing_of_zero_body r u v hru hrv
        hW hd hgap hell hzero hratio,
      Measure.quasiMeasurePreserving_fst.ae
        (S.ae_unsaturated_atom_degree_eq_twice r u hru hW hd hgap hell hzero hratio hnotu),
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_unsaturated_atom_degree_eq_twice r v hrv hW hd hgap hell hzero hratio hnotv),
      S.hdegreeNe, hs.strict_support, hW.moment_mem] with p hg hu hv hn hsupport hmem hx hy
    have hG := hg hx hy
    have hM : shiftedMoment W m p = 0 := by
      have hnpos : ¬0 < shiftedMoment W m p := by
        intro hp
        rw [ite_eq_left hp] at hsupport
        change W.moment CappedColor.adjacency p = 0 at hG
        linarith
      exact le_antisymm (le_of_not_gt hnpos) hmem.1
    have hneq : S.ρ p.1 ≠ S.ρ p.2 := fun he => huv (Subtype.ext (hx.symm.trans (he.trans hy)))
    have hrel : p ∈ actualZeroRelation W m S.ρ := ⟨hM, hneq⟩
    exact hn hrel ((hu hx).trans (hv hy).symm)
  have hurest := ae_restrict_of_ae (s := {x | S.ρ x = u.val}) (Measure.ae_ae_of_ae_prod hfalse)
  obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' hurest
  obtain ⟨y, hy, hxy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers v.val v.property).2.1.ne' (ae_restrict_of_ae hrow)
  exact hxy hx hy

end Erdos1017.CappedModel.SelectedHighLowStructure

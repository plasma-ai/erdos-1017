module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoExteriorPartition
public import Erdos1017.Exclusions.Common.CappedConditionalAveragingStationarity
public import Erdos1017.Exclusions.Common.StationaryMultiplierUniqueness
public import Erdos1017.Exclusions.Common.ConditionalRootedCounts

/-!
# Entry coordinates of the two-exterior `R`-null boundary

This module defines the conditional coefficients on the five positive boundary
cells and the entry `coveredTwoBoundaryEntry` with coordinates `BC1`, `BC2`,
`BE`, `-C1C2`, `-C1E`, `-C2E`, `-EE`, and shows the null-`R` boundary average
has its own stationary record at the proved `m`, with `D` as its `E` cell.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Original conditional coefficients on the five positive boundary cells. -/
def coveredTwoBoundaryCoefficient (S : SelectedHighLowStructure W m) (r a z1 : S.I)
    (i j : Fin 5) : ℝ :=
  FiniteArity.regionPairCharge μ (chargeKernel W)
    (fun i => S.coveredTwoBoundaryLabel r a z1 ⁻¹' {i}) i j

/-- The coordinates are BC1, BC2, BE, minus C1C2, minus C1E, minus C2E, minus EE. -/
def coveredTwoBoundaryEntry (S : SelectedHighLowStructure W m) (r a z1 : S.I) :
    VertexClassification.Coefficients :=
  ![S.coveredTwoBoundaryCoefficient r a z1 1 2, S.coveredTwoBoundaryCoefficient r a z1 1 3,
    S.coveredTwoBoundaryCoefficient r a z1 1 4, -S.coveredTwoBoundaryCoefficient r a z1 2 3,
    -S.coveredTwoBoundaryCoefficient r a z1 2 4, -S.coveredTwoBoundaryCoefficient r a z1 3 4,
    -S.coveredTwoBoundaryCoefficient r a z1 4 4]

theorem coveredTwoBoundaryCoefficient_symm (S : SelectedHighLowStructure W m) (r a z1 : S.I)
    (i j : Fin 5) : S.coveredTwoBoundaryCoefficient r a z1 i j =
      S.coveredTwoBoundaryCoefficient r a z1 j i := by
  unfold coveredTwoBoundaryCoefficient FiniteArity.regionPairCharge
  rw [← integral_prod_swap (fun p : Ω × Ω => chargeKernel W p.1 p.2)]
  apply integral_congr_ae
  exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
    (W.moment_symm CappedColor.charge)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The null-R boundary average has its own full stationary record at
proved original m. Its literal E cell is D, with no positive R requirement. -/
theorem exists_covered_two_boundary_stationary_average
    (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if CoveredTwoExterior.blockAdjacency
            (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2) = true
            then 1 else 0) ∧
        V.moment CappedColor.charge p = S.coveredTwoBoundaryCoefficient r a z1
          (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2)) ∧
      (∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d)) ∧
      ∀ p, ∀ᵐ w ∂V.kernel p,
        CappedColor.charge w = conditionalCharge V p * CappedColor.adjacency w := by
  have hpos :=
    S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms
      (hE.trans_le (measure_mono sdiff_subset))
  obtain ⟨V, hfull, hdV, hcV, hmom, hrow⟩ := exists_full_conditional_average_stationary
    W hW.full m (2 * (c - m * d)) hW.stationary (S.coveredTwoBoundaryLabel r a z1)
    (S.measurable_coveredTwoBoundaryLabel r a z1) hpos CoveredTwoExterior.blockAdjacency
    (CoveredTwoExterior.block_properties (S.coveredTwoBoundaryEntry r a z1)).1
    (S.ae_covered_two_boundary_graph r a z1 z2 hW hd hgap hpair hzero hR
      hz1r hz1a hz2r hz2a hz12 hatoms)
  have hdU : density (averaged V) = d := (density_averaged V).trans (hdV.trans hW.density_eq)
  have hcU : objective (averaged V) = c :=
    (objective_averaged V).trans (hcV.trans hW.objective_eq)
  have hfullU : FullFeasible (averaged V) := fun n => feasible_averaged V (hfull n)
  have hphysical : ∀ p, ∀ᵐ w ∂(averaged V).kernel p,
      CappedColor.charge w = conditionalCharge (averaged V) p * CappedColor.adjacency w := by
    intro p
    rw [conditionalCharge_averaged]
    exact averaged_deterministic V p
  have hrowU (x : Ω) : (∫ y, shiftedKernel (averaged V) m x y ∂μ) = 2 * (c - m * d) := by
    convert hrow x using 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [shiftedKernel, shiftedMoment_eq, charge_moment_averaged, adjacency_moment_averaged]
  have hopt : objective (averaged V) = FractionalGraph.densityLimit (density (averaged V)) := by
    rw [hdU, hcU]; exact hW.optimal
  obtain ⟨hclass, _⟩ := fullStationaryClass_of_recorded_rows (averaged V) hfullU hopt
    hphysical (hdU ▸ hd) (by rw [hdU, hcU]; exact hgap) m (2 * (c - m * d))
    (Eventually.of_forall hrowU)
  rw [hdU, hcU] at hclass
  refine ⟨averaged V, hclass, ?_, hrowU, hphysical⟩
  intro p
  exact ⟨(adjacency_moment_averaged V p).trans (hmom p).1,
    (charge_moment_averaged V p).trans (hmom p).2⟩

/-- The boundary charge table is forced by saturation, absent-edge
zero charge, and symmetry of the actual conditional averages. -/
theorem coveredTwoBoundaryEntry_table (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) (i j : Fin 5) :
    S.coveredTwoBoundaryCoefficient r a z1 i j =
      CoveredTwoExterior.blockCharge (S.coveredTwoBoundaryEntry r a z1) i j := by
  have hpos :=
    S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms
      (hE.trans_le (measure_mono sdiff_subset))
  obtain ⟨V, _, hmom, _⟩ :=
    S.exists_covered_two_boundary_stationary_average r a z1 z2 hW hd hgap hpair hzero hR hE
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hz (u v : Fin 5) (huv : CoveredTwoExterior.blockAdjacency u v = false) :
      S.coveredTwoBoundaryCoefficient r a z1 u v = 0 := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (hpos u).ne'
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (hpos v).ne'
    change S.coveredTwoBoundaryLabel r a z1 x = u at hx
    change S.coveredTwoBoundaryLabel r a z1 y = v at hy
    have hG := (hmom (x, y)).1
    have hY := (hmom (x, y)).2
    rw [hx, hy, huv] at hG
    simp only [Bool.false_eq_true, ↓reduceIte] at hG
    rw [hx, hy] at hY
    have hlo := neg_three_adjacency_moment_le_charge V (x, y)
    have hhi := charge_moment_le_adjacency V (x, y)
    rw [hG, hY] at hlo hhi
    linarith
  have hBA : S.coveredTwoBoundaryCoefficient r a z1 1 0 = 1 := by
    obtain ⟨h0, h1, _⟩ :=
      S.coveredTwoBoundaryLabel_fibers r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms
    let I := {x | S.ρ x = r.val}
    let A := {x | S.ρ x = a.val}
    let : IsProbabilityMeasure (cond μ I) :=
      cond_isProbabilityMeasure (S.hfibers r.val r.property).2.1.ne'
    let : IsProbabilityMeasure (cond μ A) :=
      cond_isProbabilityMeasure (S.hfibers a.val a.property).2.1.ne'
    unfold coveredTwoBoundaryCoefficient FiniteArity.regionPairCharge
    dsimp only
    rw [h0, h1]
    have he : (fun p : Ω × Ω => chargeKernel W p.1 p.2) =ᵐ[(cond μ I).prod (cond μ A)]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le hpair.2,
        Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (S.hfibers r.val r.property).1),
        Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (S.hfibers a.val a.property).1)]
        with p hp hx hy
      exact hp hx hy
    rw [integral_congr_ae he]
    simp
  have hAB := (S.coveredTwoBoundaryCoefficient_symm r a z1 0 1).trans hBA
  have hAA := hz 0 0 rfl
  have hBB := hz 1 1 rfl
  have hCC := hz 2 2 rfl
  have hZZ := hz 3 3 rfl
  have hAC := hz 0 2 rfl
  have hCA := hz 2 0 rfl
  have hAZ := hz 0 3 rfl
  have hZA := hz 3 0 rfl
  have hAE := hz 0 4 rfl
  have hEA := hz 4 0 rfl
  have h21 := S.coveredTwoBoundaryCoefficient_symm r a z1 2 1
  have h31 := S.coveredTwoBoundaryCoefficient_symm r a z1 3 1
  have h41 := S.coveredTwoBoundaryCoefficient_symm r a z1 4 1
  have h32 := S.coveredTwoBoundaryCoefficient_symm r a z1 3 2
  have h42 := S.coveredTwoBoundaryCoefficient_symm r a z1 4 2
  have h43 := S.coveredTwoBoundaryCoefficient_symm r a z1 4 3
  fin_cases i <;> fin_cases j <;>
    simp_all [CoveredTwoExterior.blockCharge, coveredTwoBoundaryEntry]

end Erdos1017.CappedModel.SelectedHighLowStructure

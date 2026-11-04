module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredZeroExteriorPartition
public import Erdos1017.Exclusions.Common.CappedConditionalAveragingStationarity
public import Erdos1017.Exclusions.Common.StationaryMultiplierUniqueness
public import Erdos1017.Exclusions.Common.ConditionalRootedCounts

/-!
# Boundary entry with no exterior atom

The entry `coveredZeroBoundaryEntry` has coordinates `BE` and `-EE`, built from
the conditional coefficients on the three positive boundary cells; the null-`R`
boundary average has its own full stationary record, and its charge table is
forced by saturation, absent-edge zero charge and symmetry.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Original conditional coefficients on the three positive boundary cells. -/
def coveredZeroBoundaryCoefficient (S : SelectedHighLowStructure W m) (r a : S.I)
    (i j : Fin 3) : ℝ :=
  FiniteArity.regionPairCharge μ (chargeKernel W)
    (fun i => S.coveredZeroBoundaryLabel r a ⁻¹' {i}) i j

/-- The coordinates are BE and minus EE. -/
def coveredZeroBoundaryEntry (S : SelectedHighLowStructure W m) (r a : S.I) :
    CoveredZeroExterior.Coefficients :=
  ![S.coveredZeroBoundaryCoefficient r a 1 2, -S.coveredZeroBoundaryCoefficient r a 2 2]

theorem coveredZeroBoundaryCoefficient_symm (S : SelectedHighLowStructure W m) (r a : S.I)
    (i j : Fin 3) : S.coveredZeroBoundaryCoefficient r a i j =
      S.coveredZeroBoundaryCoefficient r a j i := by
  unfold coveredZeroBoundaryCoefficient FiniteArity.regionPairCharge
  rw [← integral_prod_swap (fun p : Ω × Ω => chargeKernel W p.1 p.2)]
  apply integral_congr_ae
  exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
    (W.moment_symm CappedColor.charge)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The null-R boundary average has its own full stationary record at
proved original m. Its literal E cell is D, with no positive R requirement. -/
theorem exists_covered_zero_boundary_stationary_average
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if CoveredZeroExterior.blockAdjacency
            (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2) = true
            then 1 else 0) ∧
        V.moment CappedColor.charge p = S.coveredZeroBoundaryCoefficient r a
          (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2)) ∧
      (∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d)) ∧
      ∀ p, ∀ᵐ w ∂V.kernel p,
        CappedColor.charge w = conditionalCharge V p * CappedColor.adjacency w := by
  have hpos := S.coveredZeroBoundaryLabel_fibers_positive r a hpair.1 hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  obtain ⟨V, hfull, hdV, hcV, hmom, hrow⟩ := exists_full_conditional_average_stationary
    W hW.full m (2 * (c - m * d)) hW.stationary (S.coveredZeroBoundaryLabel r a)
    (S.measurable_coveredZeroBoundaryLabel r a) hpos CoveredZeroExterior.blockAdjacency
    (CoveredZeroExterior.block_properties (S.coveredZeroBoundaryEntry r a)).1
    (S.ae_covered_zero_boundary_graph r a hW hd hgap hpair hzero hR hatoms)
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
theorem coveredZeroBoundaryEntry_table (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) (i j : Fin 3) :
    S.coveredZeroBoundaryCoefficient r a i j =
      CoveredZeroExterior.blockCharge (S.coveredZeroBoundaryEntry r a) i j := by
  have hpos := S.coveredZeroBoundaryLabel_fibers_positive r a hpair.1 hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  obtain ⟨V, _, hmom, _⟩ :=
    S.exists_covered_zero_boundary_stationary_average r a hW hd hgap hpair hzero hR hE hatoms
  have hz (u v : Fin 3) (huv : CoveredZeroExterior.blockAdjacency u v = false) :
      S.coveredZeroBoundaryCoefficient r a u v = 0 := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (hpos u).ne'
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (hpos v).ne'
    change S.coveredZeroBoundaryLabel r a x = u at hx
    change S.coveredZeroBoundaryLabel r a y = v at hy
    have hG := (hmom (x, y)).1
    have hY := (hmom (x, y)).2
    rw [hx, hy, huv] at hG
    simp only [Bool.false_eq_true, ↓reduceIte] at hG
    rw [hx, hy] at hY
    have hlo := neg_three_adjacency_moment_le_charge V (x, y)
    have hhi := charge_moment_le_adjacency V (x, y)
    rw [hG, hY] at hlo hhi
    linarith
  have hBA : S.coveredZeroBoundaryCoefficient r a 1 0 = 1 := by
    obtain ⟨h0, h1, _⟩ := S.coveredZeroBoundaryLabel_fibers r a hpair.1 hatoms
    let I := {x | S.ρ x = r.val}
    let A := {x | S.ρ x = a.val}
    let : IsProbabilityMeasure (cond μ I) :=
      cond_isProbabilityMeasure (S.hfibers r.val r.property).2.1.ne'
    let : IsProbabilityMeasure (cond μ A) :=
      cond_isProbabilityMeasure (S.hfibers a.val a.property).2.1.ne'
    unfold coveredZeroBoundaryCoefficient FiniteArity.regionPairCharge
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
  have hAB := (S.coveredZeroBoundaryCoefficient_symm r a 0 1).trans hBA
  have hAA := hz 0 0 rfl
  have hBB := hz 1 1 rfl
  have hAE := hz 0 2 rfl
  have hEA := hz 2 0 rfl
  have hEB := S.coveredZeroBoundaryCoefficient_symm r a 2 1
  fin_cases i <;> fin_cases j <;>
    simp_all [CoveredZeroExterior.blockCharge, coveredZeroBoundaryEntry]

end Erdos1017.CappedModel.SelectedHighLowStructure

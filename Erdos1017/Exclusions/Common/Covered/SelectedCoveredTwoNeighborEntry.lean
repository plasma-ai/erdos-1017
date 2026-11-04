module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoNeighborPartition
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoExteriorEntry
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFourRegionEntry

/-!
# Finite entry of the covered two-neighbor boundary

The `E`-null finite entry is the countable boundary average reindexed on the
original fibers, with the same multiplier, and its table keeps `AR = -BR`,
saturation, zero charge on absent blocks and the two exterior penalties
(`coveredTwoNeighborEntry_table`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The reused finite conditional means are exactly the countable
original atomic/D means, because their conditioning fibers are identical. -/
theorem coveredTwoNeighborCoefficient_countable (S : SelectedHighLowStructure W m)
    (r a z1 z2 : S.I) (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) (i j : Fin 5) :
    S.coveredTwoBoundaryCoefficient r a z1 i j = S.coveredCountableBoundaryCoefficient
      (S.coveredTwoNeighborIndex r a z1 z2 i) (S.coveredTwoNeighborIndex r a z1 z2 j) := by
  unfold coveredTwoBoundaryCoefficient coveredCountableBoundaryCoefficient FiniteArity.regionPairCharge
  dsimp only
  rw [S.coveredTwoNeighborIndex_fibers r a z1 z2 hra hz1r hz1a hz2r hz2a hz12 hatoms i,
    S.coveredTwoNeighborIndex_fibers r a z1 z2 hra hz1r hz1a hz2r hz2a hz12 hatoms j]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The E-null finite entry is the same genuine countable boundary
average, reindexed on exact original fibers. Its own multiplier is proved
identical to the recorded original m; no new selected structure is assigned. -/
theorem exists_covered_two_neighbor_stationary_average (S : SelectedHighLowStructure W m)
    (r a z1 z2 : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0) (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if CoveredTwoExteriorNeighbor.blockAdjacency
            (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2) = true
          then 1 else 0) ∧
        V.moment CappedColor.charge p = S.coveredTwoBoundaryCoefficient r a z1
          (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2)) ∧
      (∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d)) ∧
      ∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  obtain ⟨V, hV, hmom, hrow, hphysical⟩ :=
    S.exists_covered_countable_boundary_stationary_average true r a hW hd hgap hpair hzero
      (hR.trans_le (measure_mono inter_subset_left)) (by simpa using hE)
  refine ⟨V, hV, ?_, hrow, hphysical⟩
  intro p
  have hx := S.coveredTwoNeighborIndex_label r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms p.1
  have hy := S.coveredTwoNeighborIndex_label r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms p.2
  have hg := (hmom p).1
  rw [hx, hy, S.coveredGraph_twoNeighborIndex r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12] at hg
  have hc := (hmom p).2
  rw [hx, hy, ← S.coveredTwoNeighborCoefficient_countable r a z1 z2 hpair.1
    hz1r hz1a hz2r hz2a hz12 hatoms] at hc
  exact ⟨hg, hc⟩

omit [BorelSpace Ω] in
private theorem countable_root_diffuse_coefficient (S : SelectedHighLowStructure W m)
    (k : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hD : 0 < μ S.D) :
    S.coveredCountableBoundaryCoefficient (Sum.inl k) (Sum.inr ()) =
      ∫ y, S.rootChargeRow k y ∂cond μ S.D := by
  let I := {x | S.ρ x = k.val}
  let : IsProbabilityMeasure (cond μ I) := cond_isProbabilityMeasure (S.hfibers k.val k.property).2.1.ne'
  let : IsProbabilityMeasure (cond μ S.D) := cond_isProbabilityMeasure hD.ne'
  have hi : Integrable (Function.uncurry (PhysicalRepresentative.charge W m))
      ((cond μ I).prod (cond μ S.D)) := Integrable.of_bound
    (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2))
  unfold coveredCountableBoundaryCoefficient FiniteArity.regionPairCharge
  dsimp only
  rw [S.coveredCountableBoundaryLabel_fiber_inl k, S.coveredCountableBoundaryLabel_fiber_inr]
  have he : (fun p : Ω × Ω => PhysicalRepresentative.charge W m p.1 p.2)
      =ᵐ[(cond μ I).prod (cond μ S.D)] (fun p => chargeKernel W p.1 p.2) :=
    (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
      (PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support)
  rw [← integral_congr_ae he]
  exact integral_prod_symm _ hi

/-- Actual saturated-head cancellation survives conditioning on the
entire D cell under E-null. It is not inferred from stationary row totals. -/
theorem coveredTwoNeighborCoefficient_head_R (S : SelectedHighLowStructure W m)
    (r a z1 z2 : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0) (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    S.coveredTwoBoundaryCoefficient r a z1 0 4 = -S.coveredTwoBoundaryCoefficient r a z1 1 4 := by
  have hD := hR.trans_le (measure_mono inter_subset_left)
  rw [S.coveredTwoNeighborCoefficient_countable r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms,
    S.coveredTwoNeighborCoefficient_countable r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms]
  change S.coveredCountableBoundaryCoefficient (Sum.inl a) (Sum.inr ()) =
    -S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inr ())
  rw [countable_root_diffuse_coefficient S r hW hd hgap hD]
  let A := {x | S.ρ x = a.val}
  let : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure (S.hfibers a.val a.property).2.1.ne'
  let : IsProbabilityMeasure (cond μ S.D) := cond_isProbabilityMeasure hD.ne'
  have hc := S.ae_saturated_head_charge_cancel_of_zero_body r a hW hd hgap
    (S.root_neutral_of_zero_body r hW hd hgap hzero) hpair hzero
  have he : (fun p : Ω × Ω => chargeKernel W p.1 p.2) =ᵐ[(cond μ A).prod (cond μ S.D)]
      (fun p => -S.rootChargeRow r p.2) := by
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le hc,
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
        (S.ae_original_root_adjacency a hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (S.hfibers a.val a.property).1),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem S.hD),
      Measure.quasiMeasurePreserving_snd.ae (cond_absolutelyContinuous.ae_le
        (measure_eq_zero_iff_ae_notMem.mp hE))] with p hp hg hx hy hn
    have hN : p.2 ∈ S.rootNeighborhood a := by by_contra hnot; exact hn ⟨hy, hnot⟩
    have hG : adjacencyKernel W p.1 p.2 = 1 := by simpa [hN] using hg hx
    have hh := hp hx (S.row_ne_atom_of_mem_diffuse p.2 hy r) hG
    linarith
  unfold coveredCountableBoundaryCoefficient FiniteArity.regionPairCharge
  dsimp only
  rw [S.coveredCountableBoundaryLabel_fiber_inl a, S.coveredCountableBoundaryLabel_fiber_inr,
    integral_congr_ae he, integral_neg, integral_fun_snd]
  simp

/-- The complete E-null table retains AR=-BR, as well as saturation,
absent-block zero charge and the two exterior penalties. -/
theorem coveredTwoNeighborEntry_table (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0) (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) (i j : Fin 5) :
    S.coveredTwoBoundaryCoefficient r a z1 i j =
      CoveredTwoExteriorNeighbor.blockCharge (S.coveredTwoBoundaryEntry r a z1) i j := by
  have hpos := S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1
    hz1r hz1a hz2r hz2a hz12 hatoms (hR.trans_le (measure_mono inter_subset_left))
  obtain ⟨V, _, hmom, _⟩ := S.exists_covered_two_neighbor_stationary_average r a z1 z2
    hW hd hgap hpair hzero hE hR hz1r hz1a hz2r hz2a hz12 hatoms
  have hz (u v : Fin 5) (huv : CoveredTwoExteriorNeighbor.blockAdjacency u v = false) :
      S.coveredTwoBoundaryCoefficient r a z1 u v = 0 := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (hpos u).ne'
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (hpos v).ne'
    have hG := (hmom (x, y)).1
    have hY := (hmom (x, y)).2
    change S.coveredTwoBoundaryLabel r a z1 x = u at hx
    change S.coveredTwoBoundaryLabel r a z1 y = v at hy
    rw [hx, hy, huv] at hG
    simp only [Bool.false_eq_true, ↓reduceIte] at hG
    rw [hx, hy] at hY
    have hlo := neg_three_adjacency_moment_le_charge V (x, y)
    have hhi := charge_moment_le_adjacency V (x, y)
    rw [hG, hY] at hlo hhi
    linarith
  have hBA : S.coveredTwoBoundaryCoefficient r a z1 1 0 = 1 := by
    rw [S.coveredTwoNeighborCoefficient_countable r a z1 z2 hpair.1
      hz1r hz1a hz2r hz2a hz12 hatoms]
    change S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl a) = 1
    rw [S.coveredCountableBoundaryCoefficient_atoms a r a]
    exact S.coveredCoefficient_saturated r a hpair
  have hAB := (S.coveredTwoBoundaryCoefficient_symm r a z1 0 1).trans hBA
  have hAR := S.coveredTwoNeighborCoefficient_head_R r a z1 z2 hW hd hgap hpair hzero hE hR
    hz1r hz1a hz2r hz2a hz12 hatoms
  have hRA := S.coveredTwoBoundaryCoefficient_symm r a z1 4 0
  have hAA := hz 0 0 rfl
  have hBB := hz 1 1 rfl
  have hCC := hz 2 2 rfl
  have hZZ := hz 3 3 rfl
  have hAC := hz 0 2 rfl
  have hCA := hz 2 0 rfl
  have hAZ := hz 0 3 rfl
  have hZA := hz 3 0 rfl
  have h21 := S.coveredTwoBoundaryCoefficient_symm r a z1 2 1
  have h31 := S.coveredTwoBoundaryCoefficient_symm r a z1 3 1
  have h41 := S.coveredTwoBoundaryCoefficient_symm r a z1 4 1
  have h32 := S.coveredTwoBoundaryCoefficient_symm r a z1 3 2
  have h42 := S.coveredTwoBoundaryCoefficient_symm r a z1 4 2
  have h43 := S.coveredTwoBoundaryCoefficient_symm r a z1 4 3
  fin_cases i <;> fin_cases j <;>
    simp_all [CoveredTwoExteriorNeighbor.blockCharge, coveredTwoBoundaryEntry]

end Erdos1017.CappedModel.SelectedHighLowStructure

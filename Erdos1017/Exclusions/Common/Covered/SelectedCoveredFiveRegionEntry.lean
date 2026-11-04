module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFiveRegion
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFourRegionEntry

/-!
# The five-region entry model

This module defines the `C` entry `coveredCEntry` from the conditional pair
averages `BC`, `-CR`, `-CE`, derives the five-region charge table from
saturation, head cancellation, absent-block zero charge and symmetry, and shows
that with exactly one exterior atom the conditional average is this five-region
model with its proved own multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The remaining C star and penalties are original conditional pair
averages, in the order BC, minus CR, minus CE. -/
def coveredCEntry (S : SelectedHighLowStructure W m) (r a z : S.I) : Fin 3 → ℝ :=
  ![S.coveredCoefficient a (Sum.inl r) (Sum.inl z),
    -S.coveredCoefficient a (Sum.inl z) (Sum.inr true),
    -S.coveredCoefficient a (Sum.inl z) (Sum.inr false)]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The full five-region charge table follows from actual saturation,
head cancellation, absent-block zero charge and symmetry. -/
theorem coveredCEntry_table (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hzr : z ≠ r) (i j : Fin 5) :
    S.coveredCoefficient a (S.coveredFiveIndex r a z i) (S.coveredFiveIndex r a z j) =
      CoveredC.blockCharge (S.coveredEntry r a)
        (S.coveredCEntry r a z 0) (S.coveredCEntry r a z 1) (S.coveredCEntry r a z 2) i j := by
  obtain ⟨V, _, hmom, _, _⟩ :=
    S.exists_covered_stationary_average r a hW hd hgap hpair hzero hR hE
  have hz (u v : S.I ⊕ Bool) (huv : S.coveredGraph r a u v = false) :
      S.coveredCoefficient a u v = 0 := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero
      (S.coveredLabel_fibers_positive a hR hE u).ne'
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero
      (S.coveredLabel_fibers_positive a hR hE v).ne'
    have hG := (hmom (x, y)).1
    change S.coveredLabel a x = u at hx
    change S.coveredLabel a y = v at hy
    rw [hx, hy, huv] at hG
    simp only [Bool.false_eq_true, ↓reduceIte] at hG
    have hY := (hmom (x, y)).2
    change V.moment CappedColor.charge (x, y) =
      S.coveredCoefficient a (S.coveredLabel a x) (S.coveredLabel a y) at hY
    rw [hx, hy] at hY
    have hlo := neg_three_adjacency_moment_le_charge V (x, y)
    have hhi := charge_moment_le_adjacency V (x, y)
    rw [hG, hY] at hlo hhi
    linarith
  have hAC := hz (Sum.inl a) (Sum.inl z)
    (by simp [coveredGraph, hzr])
  have hCC := hz (Sum.inl z) (Sum.inl z) (by simp [coveredGraph])
  have h4 := S.coveredEntry_table r a hW hd hgap hpair hzero hR hE
  fin_cases i <;> fin_cases j
  · exact h4 0 0
  · exact h4 0 1
  · exact hAC
  · exact h4 0 2
  · exact h4 0 3
  · exact h4 1 0
  · exact h4 1 1
  · rfl
  · exact h4 1 2
  · exact h4 1 3
  · exact (S.coveredCoefficient_symm a (Sum.inl z) (Sum.inl a)).trans hAC
  · exact S.coveredCoefficient_symm a (Sum.inl z) (Sum.inl r)
  · exact hCC
  · simp [coveredFiveIndex, CoveredC.blockCharge, coveredCEntry]
  · simp [coveredFiveIndex, CoveredC.blockCharge, coveredCEntry]
  · exact h4 2 0
  · exact h4 2 1
  · simpa [coveredFiveIndex, CoveredC.blockCharge, coveredCEntry] using
      S.coveredCoefficient_symm a (Sum.inr true) (Sum.inl z)
  · exact h4 2 2
  · exact h4 2 3
  · exact h4 3 0
  · exact h4 3 1
  · simpa [coveredFiveIndex, CoveredC.blockCharge, coveredCEntry] using
      S.coveredCoefficient_symm a (Sum.inr false) (Sum.inl z)
  · exact h4 3 2
  · exact h4 3 3

/-- All actual five-region blocks lie in the original capped charge box. -/
theorem coveredCEntry_block_mem (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r)
    (i j : Fin 5) :
    CoveredC.blockCharge (S.coveredEntry r a)
      (S.coveredCEntry r a z 0) (S.coveredCEntry r a z 1) (S.coveredCEntry r a z 2) i j ∈
        Icc (-3 : ℝ) 1 := by
  rw [← S.coveredCEntry_table r a z hW hd hgap hpair hzero hR hE hzr i j]
  exact S.coveredCoefficient_mem a hR hE _ _

/-- With exactly one exterior atom retained, the actual conditional
average is the literal five-region model with its proved own multiplier. -/
theorem exists_covered_five_region_entry (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if CoveredC.blockAdjacency
            (S.coveredFiveLabel r a p.1) (S.coveredFiveLabel r a p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p = CoveredC.blockCharge (S.coveredEntry r a)
          (S.coveredCEntry r a z 0) (S.coveredCEntry r a z 1) (S.coveredCEntry r a z 2)
          (S.coveredFiveLabel r a p.1) (S.coveredFiveLabel r a p.2)) ∧
      (∀ p, ∀ᵐ w ∂V.kernel p,
        CappedColor.charge w = conditionalCharge V p * CappedColor.adjacency w) ∧
      (∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d)) ∧
      0 < S.coveredEntry r a 0 ∧ S.coveredEntry r a ∈ TwoAtomCountGate.feasible := by
  obtain ⟨V, hV, hmom, hrow, hphysical⟩ :=
    S.exists_covered_stationary_average r a hW hd hgap hpair hzero hR hE
  have he (x : Ω) : S.coveredLabel a x =
      S.coveredFiveIndex r a z (S.coveredFiveLabel r a x) :=
    (S.coveredFiveIndex_code r a z hatoms (S.coveredLabel a x)).symm
  refine ⟨V, hV, ?_, hphysical, hrow,
    S.coveredEntry_h_pos r a hW hd hgap hzero hR hE,
    S.coveredEntry_feasible r a hW hd hgap hzero hR hE⟩
  intro p
  have hg := (hmom p).1
  rw [he p.1, he p.2, S.coveredGraph_fiveIndex r a z hpair.1 hzr hza] at hg
  have hy := (hmom p).2
  change V.moment CappedColor.charge p =
    S.coveredCoefficient a (S.coveredLabel a p.1) (S.coveredLabel a p.2) at hy
  rw [he p.1, he p.2,
    S.coveredCEntry_table r a z hW hd hgap hpair hzero hR hE hzr] at hy
  exact ⟨hg, hy⟩

/-- The exact original objective retains the C contribution. It is not
the C-free five-coordinate objective until that exterior atom is eliminated. -/
theorem covered_five_objective (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    TwoAtomCountGate.objective (μ.real {v | S.ρ v = a.val})
      (μ.real {v | S.ρ v = r.val}) (μ.real (S.D ∩ S.rootNeighborhood a))
      (μ.real (S.D \ S.rootNeighborhood a)) (S.coveredEntry r a) +
        μ.real {v | S.ρ v = z.val} *
          (μ.real {v | S.ρ v = r.val} * S.coveredCEntry r a z 0 -
            μ.real (S.D ∩ S.rootNeighborhood a) * S.coveredCEntry r a z 1 -
            μ.real (S.D \ S.rootNeighborhood a) * S.coveredCEntry r a z 2) = c := by
  obtain ⟨V, hV, hmom, _⟩ :=
    S.exists_covered_five_region_entry r a z hW hd hgap hpair hzero hR hE hzr hza hatoms
  have hi := CoveredC.physicalObjective (μ := μ)
    (S.coveredFiveLabel r a) (S.measurable_coveredFiveLabel r a)
    (S.coveredEntry r a) (S.coveredCEntry r a z 0)
    (S.coveredCEntry r a z 1) (S.coveredCEntry r a z 2)
  obtain ⟨h0, h1, h2, h3, h4⟩ := S.coveredFiveLabel_fibers r a z hpair.1 hzr hza hatoms
  dsimp only at hi
  rw [h0, h1, h2, h3, h4] at hi
  rw [← hi, ← hV.objective_eq]
  change (∫ p : Ω × Ω, CoveredC.blockCharge (S.coveredEntry r a)
    (S.coveredCEntry r a z 0) (S.coveredCEntry r a z 1) (S.coveredCEntry r a z 2)
      (S.coveredFiveLabel r a p.1) (S.coveredFiveLabel r a p.2) ∂μ.prod μ) / 2 =
      (∫ p, V.moment CappedColor.charge p ∂μ.prod μ) / 2
  congr 1
  exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))

end Erdos1017.CappedModel.SelectedHighLowStructure

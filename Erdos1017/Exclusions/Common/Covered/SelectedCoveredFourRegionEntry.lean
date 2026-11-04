module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFourRegion
public import Erdos1017.Exclusions.Common.Covered.CoveredCoefficientBounds
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockMoments
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredConditionalCounts

/-!
# The four-region entry model

This module defines `coveredEntry` from the conditional pair averages, shows it
is feasible for the complete signed slice with nonnegative coordinates and
positive `BR` coordinate, and that once exterior atoms are absent the averaged
optimum is this entry model with its own `m` record.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The entry coordinates are literal original conditional pair averages. -/
def coveredEntry (S : SelectedHighLowStructure W m) (r a : S.I) :
    TwoAtomCountGate.Coefficients :=
  ![S.coveredCoefficient a (Sum.inl r) (Sum.inr true),
    S.coveredCoefficient a (Sum.inl r) (Sum.inr false),
    -S.coveredCoefficient a (Sum.inr true) (Sum.inr true),
    -S.coveredCoefficient a (Sum.inr false) (Sum.inr false),
    -S.coveredCoefficient a (Sum.inr true) (Sum.inr false)]

/-- Saturation survives conditioning on the actual two positive atoms. -/
theorem coveredCoefficient_saturated (S : SelectedHighLowStructure W m) (r a : S.I)
    (hpair : S.IsSaturatedAtomPair r a) :
    S.coveredCoefficient a (Sum.inl r) (Sum.inl a) = 1 := by
  let I := {x | S.ρ x = r.val}
  let A := {x | S.ρ x = a.val}
  let : IsProbabilityMeasure (cond μ I) :=
    cond_isProbabilityMeasure (S.hfibers r.val r.property).2.1.ne'
  let : IsProbabilityMeasure (cond μ A) :=
    cond_isProbabilityMeasure (S.hfibers a.val a.property).2.1.ne'
  unfold coveredCoefficient FiniteArity.regionPairCharge
  dsimp only
  rw [S.coveredLabel_fiber_inl a r, S.coveredLabel_fiber_inl a a]
  have he : (fun p : Ω × Ω => chargeKernel W p.1 p.2) =ᵐ[(cond μ I).prod (cond μ A)]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le hpair.2,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (S.hfibers r.val r.property).1),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (S.hfibers a.val a.property).1)]
      with p hp hx hy
    exact hp hx hy
  rw [integral_congr_ae he]
  simp

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A root block coefficient is the original root row averaged only over
its second region. Both conditional laws are the original ones. -/
theorem coveredCoefficient_root_row (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (j : S.I ⊕ Bool) :
    S.coveredCoefficient a (Sum.inl r) j =
      ∫ y, S.rootChargeRow r y ∂cond μ (S.coveredLabel a ⁻¹' {j}) := by
  let I := {x | S.ρ x = r.val}
  let T := S.coveredLabel a ⁻¹' {j}
  let : IsProbabilityMeasure (cond μ I) :=
    cond_isProbabilityMeasure (S.hfibers r.val r.property).2.1.ne'
  let : IsProbabilityMeasure (cond μ T) :=
    cond_isProbabilityMeasure (S.coveredLabel_fibers_positive a hR hE j).ne'
  have hi : Integrable (Function.uncurry (PhysicalRepresentative.charge W m))
      ((cond μ I).prod (cond μ T)) := Integrable.of_bound
    (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2))
  unfold coveredCoefficient FiniteArity.regionPairCharge
  dsimp only
  rw [S.coveredLabel_fiber_inl a r]
  have he : (fun p : Ω × Ω => PhysicalRepresentative.charge W m p.1 p.2)
      =ᵐ[(cond μ I).prod (cond μ T)] (fun p => chargeKernel W p.1 p.2) :=
    (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
      (PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support)
  rw [← integral_congr_ae he]
  exact integral_prod_symm _ hi

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Saturated-head cancellation gives the exact AR=-BR entry identity. -/
theorem coveredCoefficient_head_R (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) :
    S.coveredCoefficient a (Sum.inl a) (Sum.inr true) =
      -S.coveredCoefficient a (Sum.inl r) (Sum.inr true) := by
  let A := {x | S.ρ x = a.val}
  let R := S.D ∩ S.rootNeighborhood a
  let : IsProbabilityMeasure (cond μ A) :=
    cond_isProbabilityMeasure (S.hfibers a.val a.property).2.1.ne'
  let : IsProbabilityMeasure (cond μ R) := cond_isProbabilityMeasure hR.ne'
  have hcancel := S.ae_saturated_head_charge_cancel_of_zero_body r a hW hd hgap
    (S.root_neutral_of_zero_body r hW hd hgap hzero) hpair hzero
  have he : (fun p : Ω × Ω => chargeKernel W p.1 p.2) =ᵐ[(cond μ A).prod (cond μ R)]
      (fun p => -S.rootChargeRow r p.2) := by
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le hcancel,
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
        (S.ae_original_root_adjacency a hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (S.hfibers a.val a.property).1),
      Measure.quasiMeasurePreserving_snd.ae
        (ae_cond_mem (S.hD.inter (S.measurableSet_rootNeighborhood a)))] with p hc hg hx hy
    have hG : adjacencyKernel W p.1 p.2 = 1 := by simpa [hy.2] using hg hx
    have hh := hc hx (S.row_ne_atom_of_mem_diffuse p.2 hy.1 r) hG
    linarith
  rw [S.coveredCoefficient_root_row r a hW hd hgap hR hE (Sum.inr true)]
  unfold coveredCoefficient FiniteArity.regionPairCharge
  dsimp only
  rw [S.coveredLabel_fiber_inl a a, S.coveredLabel_fiber_true a]
  rw [integral_congr_ae he, integral_neg, integral_fun_snd]
  simp [R]

omit [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
/-- The entry's BR coordinate is strictly positive because the original
zero-body root row is positive throughout its actual diffuse region. -/
theorem coveredEntry_h_pos (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) : 0 < S.coveredEntry r a 0 := by
  change 0 < S.coveredCoefficient a (Sum.inl r) (Sum.inr true)
  rw [S.coveredCoefficient_root_row r a hW hd hgap hR hE (Sum.inr true),
    S.coveredLabel_fiber_true a]
  let R := S.D ∩ S.rootNeighborhood a
  let : IsProbabilityMeasure (cond μ R) := cond_isProbabilityMeasure hR.ne'
  have hi : Integrable (S.rootChargeRow r) (cond μ R) := Integrable.of_bound
    (S.measurable_rootChargeRow r).aestronglyMeasurable 3 (Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(S.rootChargeRow_mem_Icc r y).1,
        (S.rootChargeRow_mem_Icc r y).2.trans (by norm_num)⟩))
  have hp : ∀ᵐ y ∂cond μ R, 0 < S.rootChargeRow r y := by
    filter_upwards [cond_absolutelyContinuous.ae_le
      (S.ae_rootChargeRow_pos_of_zero_body r hW hd hgap hzero),
      ae_cond_mem (S.hD.inter (S.measurableSet_rootNeighborhood a))] with y hy hm
    exact hy (S.row_ne_atom_of_mem_diffuse y hm.1 r)
  by_contra hn
  have hz : (∫ y, S.rootChargeRow r y ∂cond μ R) = 0 :=
    le_antisymm (le_of_not_gt hn) (integral_nonneg_of_ae (hp.mono (fun _ h => h.le)))
  have he := (integral_eq_zero_iff_of_nonneg_ae (hp.mono (fun _ h => h.le)) hi).mp hz
  obtain ⟨y, hy, he⟩ := (hp.and he).exists
  exact (ne_of_gt hy) he

/-- The full signed table is derived from original saturation,
head cancellation, absent-block zero charge and actual symmetry. -/
theorem coveredEntry_table (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i j : Fin 4) :
    S.coveredCoefficient a (S.coveredFourIndex r a i) (S.coveredFourIndex r a j) =
      TwoAtomCountGate.blockCharge (S.coveredEntry r a) i j := by
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
  have hAA := hz (Sum.inl a) (Sum.inl a) (by simp [coveredGraph])
  have hBB := hz (Sum.inl r) (Sum.inl r) (by simp [coveredGraph])
  have hAE := hz (Sum.inl a) (Sum.inr false) (by simp [coveredGraph])
  have hEA := (S.coveredCoefficient_symm a (Sum.inr false) (Sum.inl a)).trans hAE
  have hBA := S.coveredCoefficient_saturated r a hpair
  have hAB := (S.coveredCoefficient_symm a (Sum.inl a) (Sum.inl r)).trans hBA
  have hAR := S.coveredCoefficient_head_R r a hW hd hgap hpair hzero hR hE
  have hRA := (S.coveredCoefficient_symm a (Sum.inr true) (Sum.inl a)).trans hAR
  have hRB := S.coveredCoefficient_symm a (Sum.inr true) (Sum.inl r)
  have hEB := S.coveredCoefficient_symm a (Sum.inr false) (Sum.inl r)
  have hER := S.coveredCoefficient_symm a (Sum.inr false) (Sum.inr true)
  fin_cases i <;> fin_cases j <;>
    simp [coveredFourIndex, TwoAtomCountGate.blockCharge, coveredEntry,
      hAA, hBB, hAE, hEA, hBA, hAB, hAR, hRA, hRB, hEB, hER]

omit [BorelSpace Ω] in
/-- The literal entry agrees with the previously sampled rooted
coefficients, including the physical-to-original AE charge conversion. -/
theorem coveredEntry_eq_rooted_coefficients (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    S.coveredEntry r a = FiniteArity.rootedRegionCoefficients μ
      (PhysicalRepresentative.charge W m)
      ![{x | S.ρ x = r.val}, S.D ∩ S.rootNeighborhood a, S.D \ S.rootNeighborhood a] := by
  have he (T U : Set Ω) :
      (∫ p, chargeKernel W p.1 p.2 ∂(cond μ T).prod (cond μ U)) =
        ∫ p, PhysicalRepresentative.charge W m p.1 p.2 ∂(cond μ T).prod (cond μ U) := by
    apply integral_congr_ae
    exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
      ((PhysicalRepresentative.charge_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support).mono (fun _ hp => hp.symm))
  funext i
  fin_cases i <;>
    simp [coveredEntry, coveredCoefficient, FiniteArity.rootedRegionCoefficients,
      FiniteArity.regionPairCharge, S.coveredLabel_fiber_inl, S.coveredLabel_fiber_true,
      S.coveredLabel_fiber_false, he]

omit [BorelSpace Ω] in
/-- The actual entry satisfies the complete signed feasible slice,
including every unanchored and A-rooted count. -/
theorem coveredEntry_feasible (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) :
    S.coveredEntry r a ∈ TwoAtomCountGate.feasible := by
  rw [S.coveredEntry_eq_rooted_coefficients r a hW hd hgap]
  obtain ⟨hn, ht⟩ := S.covered_region_coefficients_of_zero_body r a hW hd hgap hzero hR hE
  apply TwoAtomCountGate.mem_feasible_of_nonnegative _ hn
  intro k l
  simpa only [TwoAtomCountGate.countTest_apply] using ht k l

/-- Every literal entry block is in the actual capped charge box. -/
theorem coveredEntry_block_mem (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i j : Fin 4) :
    TwoAtomCountGate.blockCharge (S.coveredEntry r a) i j ∈ Icc (-3 : ℝ) 1 := by
  rw [← S.coveredEntry_table r a hW hd hgap hpair hzero hR hE i j]
  exact S.coveredCoefficient_mem a hR hE _ _

omit [BorelSpace Ω] in
/-- Original zero-body signs give nonnegative entry coordinates before
any optimal-face selection is made. -/
theorem coveredEntry_nonnegative (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i : Fin 5) : 0 ≤ S.coveredEntry r a i := by
  rw [S.coveredEntry_eq_rooted_coefficients r a hW hd hgap]
  exact (S.covered_region_coefficients_of_zero_body r a hW hd hgap hzero hR hE).1 i

/-- Once exterior atoms are absent, the actual averaged optimum is
literally the four-region entry model, with its own original-m record. -/
theorem exists_covered_four_region_entry (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if TwoAtomCountGate.blockAdjacency
            (S.coveredFourLabel a p.1) (S.coveredFourLabel a p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p = TwoAtomCountGate.blockCharge (S.coveredEntry r a)
          (S.coveredFourLabel a p.1) (S.coveredFourLabel a p.2)) ∧
      (∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z) ∧
      0 < S.coveredEntry r a 0 ∧ S.coveredEntry r a ∈ TwoAtomCountGate.feasible ∧
      TwoAtomCountGate.objective (μ.real {v | S.ρ v = a.val})
        (μ.real {v | S.ρ v = r.val}) (μ.real (S.D ∩ S.rootNeighborhood a))
        (μ.real (S.D \ S.rootNeighborhood a)) (S.coveredEntry r a) = c := by
  obtain ⟨V, hV, hmom, _, hphysical⟩ :=
    S.exists_covered_stationary_average r a hW hd hgap hpair hzero hR hE
  have he (x : Ω) : S.coveredLabel a x =
      S.coveredFourIndex r a (S.coveredFourLabel a x) :=
    (S.coveredFourIndex_code r a hatoms (S.coveredLabel a x)).symm
  have htable (p : Ω × Ω) := S.coveredEntry_table r a hW hd hgap hpair hzero hR hE
    (S.coveredFourLabel a p.1) (S.coveredFourLabel a p.2)
  have hmom' (p : Ω × Ω) :
      V.moment CappedColor.adjacency p =
        (if TwoAtomCountGate.blockAdjacency
          (S.coveredFourLabel a p.1) (S.coveredFourLabel a p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = TwoAtomCountGate.blockCharge (S.coveredEntry r a)
        (S.coveredFourLabel a p.1) (S.coveredFourLabel a p.2) := by
    have hg := (hmom p).1
    rw [he p.1, he p.2, S.coveredGraph_fourIndex r a hpair.1] at hg
    have hy := (hmom p).2
    change V.moment CappedColor.charge p =
      S.coveredCoefficient a (S.coveredLabel a p.1) (S.coveredLabel a p.2) at hy
    rw [he p.1, he p.2, htable p] at hy
    exact ⟨hg, hy⟩
  refine ⟨V, hV, hmom', hphysical, S.coveredEntry_h_pos r a hW hd hgap hzero hR hE,
    S.coveredEntry_feasible r a hW hd hgap hzero hR hE, ?_⟩
  have hi := TwoAtomCountGate.block_physicalObjective
    (μ := μ) (S.coveredFourLabel a) (S.measurable_coveredFourLabel a) (S.coveredEntry r a)
  obtain ⟨h0, h1, h2, h3⟩ := S.coveredFourLabel_fibers r a hpair.1 hatoms
  dsimp only at hi
  rw [h0, h1, h2, h3] at hi
  rw [← hi, ← hV.objective_eq]
  change (∫ p : Ω × Ω, TwoAtomCountGate.blockCharge (S.coveredEntry r a)
    (S.coveredFourLabel a p.1) (S.coveredFourLabel a p.2) ∂μ.prod μ) / 2 =
      (∫ p, V.moment CappedColor.charge p ∂μ.prod μ) / 2
  congr 1
  exact integral_congr_ae (Eventually.of_forall (fun p => (hmom' p).2.symm))

end Erdos1017.CappedModel.SelectedHighLowStructure

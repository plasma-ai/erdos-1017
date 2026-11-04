module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredZeroExteriorEntry
public import Erdos1017.Exclusions.Common.Covered.CoveredZeroExteriorOptimal

/-!
# Covered counts with no exterior atom

On the `R`-null boundary the optimum is a represented feasible two-coordinate
entry with its own stationary record, the original objective equals `AB` plus
the child objective, and an explicit adjacent-count optimum is constructed with
its own multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Actual signs and every natural-E test follow from original
positive conditional laws. The independent B fiber is sampled only once. -/
theorem coveredZeroBoundaryEntry_feasible (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    S.coveredZeroBoundaryEntry r a ∈ CoveredZeroExterior.feasible := by
  let label := S.coveredZeroBoundaryLabel r a
  let T : Fin 2 → Set Ω := fun i => label ⁻¹' {i.succ}
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hlabel := S.measurable_coveredZeroBoundaryLabel r a
  have hpos3 := S.coveredZeroBoundaryLabel_fibers_positive r a hpair.1 hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  have hT (i : Fin 2) : MeasurableSet (T i) := hlabel (measurableSet_singleton i.succ)
  have hpos (i : Fin 2) : 0 < μ (T i) := hpos3 i.succ
  obtain ⟨_, hB, hD⟩ := S.coveredZeroBoundaryLabel_fibers r a hpair.1 hatoms
  have hroot : T 0 = {x | S.ρ x = r.val} := hB
  have hout (i : Fin 2) (hi : i ≠ 0) (x : Ω) (hx : x ∈ T i) : S.ρ x ≠ r.val := by
    fin_cases i
    · exact False.elim (hi rfl)
    · change x ∈ label ⁻¹' {2} at hx
      rw [hD] at hx
      exact S.row_ne_atom_of_mem_diffuse x hx r
  have hs := hW.strict_gap_structure hd hgap
  have heY := PhysicalRepresentative.charge_ae_eq W m hs.strict_support
  have heG := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hg := S.ae_covered_zero_boundary_graph r a hW hd hgap hpair hzero hR hatoms
  have hcoef (i j : Fin 2) : FiniteArity.regionPairCharge μ Y T i j =
      S.coveredZeroBoundaryCoefficient r a i.succ j.succ := by
    exact integral_congr_ae
      ((cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le heY)
  have havg (i j : Fin 2) (h : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T i → p.2 ∈ T j → 0 ≤ Y p.1 p.2) :
      0 ≤ FiniteArity.regionPairCharge μ Y T i j := by
    apply integral_nonneg_of_ae
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le h,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hT i)),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hT j))] with p hp hi hj
    exact hp hi hj
  have hstar (j : Fin 2) (hj : j ≠ 0) :
      0 ≤ FiniteArity.regionPairCharge μ Y T 0 j := by
    apply havg
    filter_upwards [S.ae_root_charge r hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_rootChargeRow_pos_of_zero_body r hW hd hgap hzero)] with p hp ht hx hy
    rw [hroot] at hx
    exact (hp hx).trans_ge (ht (hout j hj p.2 hy)).le
  have hbody (i j : Fin 2) (hi : i ≠ 0) (hj : j ≠ 0) :
      FiniteArity.regionPairCharge μ Y T i j ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
        (S.zero_body_ae_charge_nonpositive r hzero),
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le heY,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hT i)),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hT j))] with p hp he hx hy
    exact he.trans_le (hp (hout i hi p.1 hx) (hout j hj p.2 hy))
  have h01 := hstar 1 (by decide)
  have h11 := hbody 1 1 (by decide) (by decide)
  rw [hcoef] at h01 h11
  refine ⟨h01, neg_nonneg.mpr h11, ?_⟩
  intro n
  let k : Fin 2 → ℕ := ![1, n]
  have hclique (i j : Fin 2)
      (hij : CoveredZeroExterior.blockAdjacency i.succ j.succ = true) :
      ∀ᵐ p ∂μ.prod μ, p.1 ∈ T i → p.2 ∈ T j → A p.1 p.2 = true := by
    filter_upwards [hg, heG] with p hp he hx hy
    change label p.1 = i.succ at hx
    change label p.2 = j.succ at hy
    change W.moment CappedColor.adjacency p =
      (if CoveredZeroExterior.blockAdjacency (label p.1) (label p.2) = true then 1 else 0) at hp
    rw [hx, hy, hij] at hp
    cases ha : A p.1 p.2 <;> simp_all [A]
  have ht := FiniteArity.conditional_multiplicity_average_le_one T hT hpos A Y
    (PhysicalRepresentative.measurable_charge W m) 3 (PhysicalRepresentative.charge_bound W m)
    k (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic _)
    (fun i hi => by
      fin_cases i
      · simp [k] at hi
      · exact hclique 1 1 rfl)
    (fun i j hij _ _ => by
      apply hclique
      fin_cases i <;> fin_cases j <;> simp_all [CoveredZeroExterior.blockAdjacency])
  change FiniteArity.multiplicityCharge (FiniteArity.regionPairCharge μ Y T) k ≤ 1 at ht
  have he : (FiniteArity.regionPairCharge μ Y T) =
      fun i j => S.coveredZeroBoundaryCoefficient r a i.succ j.succ :=
    funext (fun i => funext (hcoef i))
  rw [he] at ht
  simp_rw [S.coveredZeroBoundaryEntry_table r a hW hd hgap hpair hzero hR hE hatoms] at ht
  simp [coveredZeroBoundaryEntry,
    FiniteArity.multiplicityCharge, k, Fin.sum_univ_two,
    CoveredZeroExterior.blockCharge] at ht ⊢
  nlinarith only [ht]

/-- The actual R-null boundary optimum is a represented feasible two-coordinate
entry with its own stationary record. No exterior atom remains. -/
theorem exists_covered_zero_exterior_entry (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    S.coveredZeroBoundaryEntry r a ∈ CoveredZeroExterior.feasible ∧
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if CoveredZeroExterior.blockAdjacency
            (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2) = true
            then 1 else 0) ∧
        V.moment CappedColor.charge p = CoveredZeroExterior.blockCharge
          (S.coveredZeroBoundaryEntry r a)
          (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2)) ∧
      (∀ p, ∀ᵐ w ∂V.kernel p,
        CappedColor.charge w = conditionalCharge V p * CappedColor.adjacency w) ∧
      ∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d) := by
  obtain ⟨V, hV, hmom, hrow, hphysical⟩ :=
    S.exists_covered_zero_boundary_stationary_average r a hW hd hgap hpair hzero hR hE hatoms
  refine ⟨S.coveredZeroBoundaryEntry_feasible r a hW hd hgap hpair hzero hR hE hatoms,
    V, hV, ?_, hphysical, hrow⟩
  intro p
  exact ⟨(hmom p).1, (hmom p).2.trans
    (S.coveredZeroBoundaryEntry_table r a hW hd hgap hpair hzero hR hE hatoms _ _)⟩

/-- The unchanged original objective is exactly AB plus the child
objective, with the whole original diffuse mass as E. -/
theorem covered_zero_exterior_objective (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    μ.real {v | S.ρ v = a.val} * μ.real {v | S.ρ v = r.val} +
      CoveredZeroExterior.objective (μ.real {v | S.ρ v = r.val})
        (μ.real S.D) (S.coveredZeroBoundaryEntry r a) = c := by
  obtain ⟨_, V, hV, hmom, _⟩ :=
    S.exists_covered_zero_exterior_entry r a hW hd hgap hpair hzero hR hE hatoms
  have hi := CoveredZeroExterior.block_physicalObjective (μ := μ)
    (S.coveredZeroBoundaryLabel r a) (S.measurable_coveredZeroBoundaryLabel r a)
    (S.coveredZeroBoundaryEntry r a)
  obtain ⟨h0, h1, h2⟩ := S.coveredZeroBoundaryLabel_fibers r a hpair.1 hatoms
  dsimp only at hi
  rw [h0, h1, h2] at hi
  rw [← hi, ← hV.objective_eq]
  change (∫ p : Ω × Ω, CoveredZeroExterior.blockCharge (S.coveredZeroBoundaryEntry r a)
      (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2) ∂μ.prod μ) / 2 =
    (∫ p, V.moment CappedColor.charge p ∂μ.prod μ) / 2
  congr 1
  exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))

/-- The actual original zero-exterior boundary constructs an explicit
adjacent-count optimum and selects that model's own multiplier. -/
theorem exists_covered_zero_explicit_optimum (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    ∃ j : ℕ, 1 ≤ j ∧
      ((j : ℝ) - 1) * μ.real {x | S.ρ x = r.val} ≤ μ.real S.D ∧
      μ.real S.D ≤ j * μ.real {x | S.ρ x = r.val} ∧
      ∃ (V : Model Ω μ) (m' : ℝ), FullStationaryClass d c V m' ∧
        (∀ p : Ω × Ω,
          V.moment CappedColor.adjacency p =
            (if CoveredZeroExterior.blockAdjacency
              (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2) = true
              then 1 else 0) ∧
          V.moment CappedColor.charge p = CoveredZeroExterior.blockCharge
            (CoveredZeroExterior.explicitDual j)
            (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2)) ∧
        ∀ p, ∀ᵐ z ∂V.kernel p,
          CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  obtain ⟨hy, U, hU, hmom, _⟩ :=
    S.exists_covered_zero_exterior_entry r a hW hd hgap hpair hzero hR hE hatoms
  have hpositive := S.coveredZeroBoundaryLabel_fibers_positive r a hpair.1 hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  have h := CoveredZeroExterior.exists_explicit_stationary_model hU hd hgap
    (S.coveredZeroBoundaryLabel r a) (S.measurable_coveredZeroBoundaryLabel r a)
    hpositive (S.coveredZeroBoundaryEntry r a) hy hmom
  obtain ⟨_, hB, hD⟩ := S.coveredZeroBoundaryLabel_fibers r a hpair.1 hatoms
  rwa [hB, hD] at h

end Erdos1017.CappedModel.SelectedHighLowStructure

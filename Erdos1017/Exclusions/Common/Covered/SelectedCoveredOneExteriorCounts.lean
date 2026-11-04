module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredOneExteriorEntry
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorBlockMoments

/-!
# The `R`-null optimum as a one-exterior child entry

The `R`-null boundary optimum is a represented feasible child entry with its own
stationary record and the exterior atom retained; its signs and Boolean-`C`,
natural-`E` tests follow from the positive conditional laws, and its objective
is `AB` plus the child objective.
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

/-- Actual signs and every Boolean-C, natural-E test follow from original
positive conditional laws. The independent C fiber is never sampled twice. -/
theorem coveredBoundaryEntry_feasible (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    S.coveredBoundaryEntry r a ∈ CoveredOneExterior.feasible := by
  let label := S.coveredBoundaryLabel r a
  let T : Fin 3 → Set Ω := fun i => label ⁻¹' {i.succ}
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hlabel := S.measurable_coveredBoundaryLabel r a
  have hpos4 := S.coveredBoundaryLabel_fibers_positive r a z hpair.1 hzr hza hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  have hT (i : Fin 3) : MeasurableSet (T i) := hlabel (measurableSet_singleton i.succ)
  have hpos (i : Fin 3) : 0 < μ (T i) := hpos4 i.succ
  obtain ⟨_, hB, hC, hD⟩ := S.coveredBoundaryLabel_fibers r a z hpair.1 hzr hza hatoms
  have hroot : T 0 = {x | S.ρ x = r.val} := hB
  have hout (i : Fin 3) (hi : i ≠ 0) (x : Ω) (hx : x ∈ T i) : S.ρ x ≠ r.val := by
    fin_cases i
    · exact False.elim (hi rfl)
    · change x ∈ label ⁻¹' {2} at hx
      rw [hC] at hx
      exact fun he => hzr (Subtype.ext (hx.symm.trans he))
    · change x ∈ label ⁻¹' {3} at hx
      rw [hD] at hx
      exact S.row_ne_atom_of_mem_diffuse x hx r
  have hs := hW.strict_gap_structure hd hgap
  have heY := PhysicalRepresentative.charge_ae_eq W m hs.strict_support
  have heG := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hg := S.ae_covered_boundary_graph r a z hW hd hgap hpair hzero hR hzr hza hatoms
  have hcoef (i j : Fin 3) : FiniteArity.regionPairCharge μ Y T i j =
      S.coveredBoundaryCoefficient r a i.succ j.succ := by
    exact integral_congr_ae
      ((cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le heY)
  have havg (i j : Fin 3) (h : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T i → p.2 ∈ T j → 0 ≤ Y p.1 p.2) :
      0 ≤ FiniteArity.regionPairCharge μ Y T i j := by
    apply integral_nonneg_of_ae
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le h,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hT i)),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hT j))] with p hp hi hj
    exact hp hi hj
  have hstar (j : Fin 3) (hj : j ≠ 0) :
      0 ≤ FiniteArity.regionPairCharge μ Y T 0 j := by
    apply havg
    filter_upwards [S.ae_root_charge r hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_rootChargeRow_pos_of_zero_body r hW hd hgap hzero)] with p hp ht hx hy
    rw [hroot] at hx
    exact (hp hx).trans_ge (ht (hout j hj p.2 hy)).le
  have hbody (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
      FiniteArity.regionPairCharge μ Y T i j ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
        (S.zero_body_ae_charge_nonpositive r hzero),
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le heY,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hT i)),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hT j))] with p hp he hx hy
    exact he.trans_le (hp (hout i hi p.1 hx) (hout j hj p.2 hy))
  refine ⟨?_, ?_⟩
  · intro i
    have h01 := hstar 1 (by decide)
    have h02 := hstar 2 (by decide)
    have h12 := hbody 1 2 (by decide) (by decide)
    have h22 := hbody 2 2 (by decide) (by decide)
    rw [hcoef] at h01 h02 h12 h22
    fin_cases i
    · exact h01
    · exact h02
    · exact neg_nonneg.mpr h12
    · exact neg_nonneg.mpr h22
  · intro s n
    let k : Fin 3 → ℕ := ![1, if s then 1 else 0, n]
    have hclique (i j : Fin 3)
        (hij : CoveredOneExterior.blockAdjacency i.succ j.succ = true) :
        ∀ᵐ p ∂μ.prod μ, p.1 ∈ T i → p.2 ∈ T j → A p.1 p.2 = true := by
      filter_upwards [hg, heG] with p hp he hx hy
      change label p.1 = i.succ at hx
      change label p.2 = j.succ at hy
      change W.moment CappedColor.adjacency p =
        (if CoveredOneExterior.blockAdjacency (label p.1) (label p.2) = true then 1 else 0) at hp
      rw [hx, hy, hij] at hp
      cases ha : A p.1 p.2 <;> simp_all [A]
    have ht := FiniteArity.conditional_multiplicity_average_le_one T hT hpos A Y
      (PhysicalRepresentative.measurable_charge W m) 3 (PhysicalRepresentative.charge_bound W m)
      k (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic _)
      (fun i hi => by
        fin_cases i
        · simp [k] at hi
        · cases s <;> simp [k] at hi
        · exact hclique 2 2 rfl)
      (fun i j hij _ _ => by
        apply hclique
        fin_cases i <;> fin_cases j <;> simp_all [CoveredOneExterior.blockAdjacency])
    change FiniteArity.multiplicityCharge (FiniteArity.regionPairCharge μ Y T) k ≤ 1 at ht
    have he : (FiniteArity.regionPairCharge μ Y T) =
        fun i j => S.coveredBoundaryCoefficient r a i.succ j.succ :=
      funext (fun i => funext (hcoef i))
    rw [he] at ht
    simp_rw [S.coveredBoundaryEntry_table r a z hW hd hgap hpair hzero hR hE hzr hza hatoms] at ht
    cases s <;>
      simp [FiniteArity.multiplicityCharge, k, Fin.sum_univ_three,
        CoveredOneExterior.blockCharge, CoveredOneExterior.test, CoveredOneExterior.constant,
        CoveredOneExterior.slope] at ht ⊢ <;> nlinarith only [ht]

/-- The actual R-null boundary optimum is a represented feasible child
entry with its own stationary record. The exterior atom is retained. -/
theorem exists_covered_one_exterior_entry (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    S.coveredBoundaryEntry r a ∈ CoveredOneExterior.feasible ∧
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if CoveredOneExterior.blockAdjacency
            (S.coveredBoundaryLabel r a p.1) (S.coveredBoundaryLabel r a p.2) = true
            then 1 else 0) ∧
        V.moment CappedColor.charge p = CoveredOneExterior.blockCharge
          (S.coveredBoundaryEntry r a)
          (S.coveredBoundaryLabel r a p.1) (S.coveredBoundaryLabel r a p.2)) ∧
      (∀ p, ∀ᵐ w ∂V.kernel p,
        CappedColor.charge w = conditionalCharge V p * CappedColor.adjacency w) ∧
      ∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d) := by
  obtain ⟨V, hV, hmom, hrow, hphysical⟩ :=
    S.exists_covered_boundary_stationary_average r a z hW hd hgap hpair hzero hR hE hzr hza hatoms
  refine ⟨S.coveredBoundaryEntry_feasible r a z hW hd hgap hpair hzero hR hE hzr hza hatoms,
    V, hV, ?_, hphysical, hrow⟩
  intro p
  exact ⟨(hmom p).1, (hmom p).2.trans
    (S.coveredBoundaryEntry_table r a z hW hd hgap hpair hzero hR hE hzr hza hatoms _ _)⟩

/-- The unchanged original objective is exactly AB plus the child
objective, with the whole original diffuse mass as E. -/
theorem covered_one_exterior_objective (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    μ.real {v | S.ρ v = a.val} * μ.real {v | S.ρ v = r.val} +
      CoveredOneExterior.objective (μ.real {v | S.ρ v = r.val})
        (μ.real {v | S.ρ v = z.val}) (μ.real S.D) (S.coveredBoundaryEntry r a) = c := by
  obtain ⟨_, V, hV, hmom, _⟩ :=
    S.exists_covered_one_exterior_entry r a z hW hd hgap hpair hzero hR hE hzr hza hatoms
  have hi := CoveredOneExterior.block_physicalObjective (μ := μ)
    (S.coveredBoundaryLabel r a) (S.measurable_coveredBoundaryLabel r a)
    (S.coveredBoundaryEntry r a)
  obtain ⟨h0, h1, h2, h3⟩ := S.coveredBoundaryLabel_fibers r a z hpair.1 hzr hza hatoms
  dsimp only at hi
  rw [h0, h1, h2, h3] at hi
  rw [← hi, ← hV.objective_eq]
  change (∫ p : Ω × Ω, CoveredOneExterior.blockCharge (S.coveredBoundaryEntry r a)
      (S.coveredBoundaryLabel r a p.1) (S.coveredBoundaryLabel r a p.2) ∂μ.prod μ) / 2 =
    (∫ p, V.moment CappedColor.charge p ∂μ.prod μ) / 2
  congr 1
  exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))

end Erdos1017.CappedModel.SelectedHighLowStructure

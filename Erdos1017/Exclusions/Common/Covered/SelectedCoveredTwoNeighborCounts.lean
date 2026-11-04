module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoNeighborEntry
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorNeighborBlockMoments
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoNeighborOwnRows

/-!
# Covered two-neighbor counts on the `E`-null boundary

On the `E`-null boundary the optimum is a represented feasible child entry with
its own stationary record, the original objective equals `AB` plus the child
objective, and the head masses satisfy `a < b`.
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

/-- Actual signs and every two-Boolean, natural-R test follow from original
positive conditional laws. Neither independent exterior fiber is sampled twice. -/
theorem coveredTwoNeighborEntry_feasible (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    S.coveredTwoBoundaryEntry r a z1 ∈ VertexClassification.feasible := by
  let label := S.coveredTwoBoundaryLabel r a z1
  let T : Fin 4 → Set Ω := fun i => label ⁻¹' {i.succ}
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hlabel := S.measurable_coveredTwoBoundaryLabel r a z1
  have hpos5 :=
    S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms
      (hR.trans_le (measure_mono inter_subset_left))
  have hT (i : Fin 4) : MeasurableSet (T i) := hlabel (measurableSet_singleton i.succ)
  have hpos (i : Fin 4) : 0 < μ (T i) := hpos5 i.succ
  obtain ⟨_, hB, hC1, hC2, hD⟩ :=
    S.coveredTwoBoundaryLabel_fibers r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms
  have hroot : T 0 = {x | S.ρ x = r.val} := hB
  have hout (i : Fin 4) (hi : i ≠ 0) (x : Ω) (hx : x ∈ T i) : S.ρ x ≠ r.val := by
    fin_cases i
    · exact False.elim (hi rfl)
    · change x ∈ label ⁻¹' {2} at hx
      rw [hC1] at hx
      exact fun he => hz1r (Subtype.ext (hx.symm.trans he))
    · change x ∈ label ⁻¹' {3} at hx
      rw [hC2] at hx
      exact fun he => hz2r (Subtype.ext (hx.symm.trans he))
    · change x ∈ label ⁻¹' {4} at hx
      rw [hD] at hx
      exact S.row_ne_atom_of_mem_diffuse x hx r
  have hs := hW.strict_gap_structure hd hgap
  have heY := PhysicalRepresentative.charge_ae_eq W m hs.strict_support
  have heG := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hg :=
    S.ae_covered_two_neighbor_graph r a z1 z2 hW hd hgap hpair hzero hE
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hcoef (i j : Fin 4) : FiniteArity.regionPairCharge μ Y T i j =
      S.coveredTwoBoundaryCoefficient r a z1 i.succ j.succ := by
    exact integral_congr_ae
      ((cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le heY)
  have havg (i j : Fin 4) (h : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T i → p.2 ∈ T j → 0 ≤ Y p.1 p.2) :
      0 ≤ FiniteArity.regionPairCharge μ Y T i j := by
    apply integral_nonneg_of_ae
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le h,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hT i)),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hT j))] with p hp hi hj
    exact hp hi hj
  have hstar (j : Fin 4) (hj : j ≠ 0) :
      0 ≤ FiniteArity.regionPairCharge μ Y T 0 j := by
    apply havg
    filter_upwards [S.ae_root_charge r hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_rootChargeRow_pos_of_zero_body r hW hd hgap hzero)] with p hp ht hx hy
    rw [hroot] at hx
    exact (hp hx).trans_ge (ht (hout j hj p.2 hy)).le
  have hbody (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
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
    have h03 := hstar 3 (by decide)
    have h12 := hbody 1 2 (by decide) (by decide)
    have h13 := hbody 1 3 (by decide) (by decide)
    have h23 := hbody 2 3 (by decide) (by decide)
    have h33 := hbody 3 3 (by decide) (by decide)
    rw [hcoef] at h01 h02 h03 h12 h13 h23 h33
    fin_cases i
    · exact h01
    · exact h02
    · exact h03
    · exact neg_nonneg.mpr h12
    · exact neg_nonneg.mpr h13
    · exact neg_nonneg.mpr h23
    · exact neg_nonneg.mpr h33
  · rintro ⟨⟨s1, s2⟩, n⟩
    let k : Fin 4 → ℕ := ![1, if s1 then 1 else 0, if s2 then 1 else 0, n]
    have hclique (i j : Fin 4)
        (hij : CoveredTwoExteriorNeighbor.blockAdjacency i.succ j.succ = true) :
        ∀ᵐ p ∂μ.prod μ, p.1 ∈ T i → p.2 ∈ T j → A p.1 p.2 = true := by
      filter_upwards [hg, heG] with p hp he hx hy
      change label p.1 = i.succ at hx
      change label p.2 = j.succ at hy
      change W.moment CappedColor.adjacency p =
        (if CoveredTwoExteriorNeighbor.blockAdjacency (label p.1) (label p.2) = true then 1 else 0) at hp
      rw [hx, hy, hij] at hp
      cases ha : A p.1 p.2 <;> simp_all [A]
    have ht := FiniteArity.conditional_multiplicity_average_le_one T hT hpos A Y
      (PhysicalRepresentative.measurable_charge W m) 3 (PhysicalRepresentative.charge_bound W m)
      k (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic _)
      (fun i hi => by
        fin_cases i
        · simp [k] at hi
        · cases s1 <;> simp [k] at hi
        · cases s2 <;> simp [k] at hi
        · exact hclique 3 3 rfl)
      (fun i j hij _ _ => by
        apply hclique
        fin_cases i <;> fin_cases j <;> simp_all [CoveredTwoExteriorNeighbor.blockAdjacency])
    change FiniteArity.multiplicityCharge (FiniteArity.regionPairCharge μ Y T) k ≤ 1 at ht
    have he : (FiniteArity.regionPairCharge μ Y T) =
        fun i j => S.coveredTwoBoundaryCoefficient r a z1 i.succ j.succ :=
      funext (fun i => funext (hcoef i))
    rw [he] at ht
    simp_rw [S.coveredTwoNeighborEntry_table r a z1 z2 hW hd hgap hpair hzero hE hR
      hz1r hz1a hz2r hz2a hz12 hatoms] at ht
    cases s1 <;> cases s2 <;>
      simp [FiniteArity.multiplicityCharge, k, Fin.sum_univ_succ,
        CoveredTwoExteriorNeighbor.blockCharge, VertexClassification.test, VertexClassification.constant,
        VertexClassification.slope] at ht ⊢ <;> nlinarith only [ht]

/-- The actual E-null boundary optimum is a represented feasible child
entry with its own stationary record. Both exterior atoms are retained. -/
theorem exists_covered_two_neighbor_entry (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    S.coveredTwoBoundaryEntry r a z1 ∈ VertexClassification.feasible ∧
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if CoveredTwoExteriorNeighbor.blockAdjacency
            (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2) = true
            then 1 else 0) ∧
        V.moment CappedColor.charge p = CoveredTwoExteriorNeighbor.blockCharge
          (S.coveredTwoBoundaryEntry r a z1)
          (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2)) ∧
      (∀ p, ∀ᵐ w ∂V.kernel p,
        CappedColor.charge w = conditionalCharge V p * CappedColor.adjacency w) ∧
      ∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d) := by
  obtain ⟨V, hV, hmom, hrow, hphysical⟩ :=
    S.exists_covered_two_neighbor_stationary_average r a z1 z2 hW hd hgap hpair hzero hE hR
      hz1r hz1a hz2r hz2a hz12 hatoms
  refine ⟨S.coveredTwoNeighborEntry_feasible r a z1 z2 hW hd hgap hpair hzero hE hR
    hz1r hz1a hz2r hz2a hz12 hatoms,
    V, hV, ?_, hphysical, hrow⟩
  intro p
  exact ⟨(hmom p).1, (hmom p).2.trans
    (S.coveredTwoNeighborEntry_table r a z1 z2 hW hd hgap hpair hzero hE hR
      hz1r hz1a hz2r hz2a hz12 hatoms _ _)⟩

/-- The unchanged original objective is exactly AB plus the child
objective, with the whole original diffuse mass as R. -/
theorem covered_two_neighbor_objective (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    μ.real {v | S.ρ v = a.val} * μ.real {v | S.ρ v = r.val} +
      CoveredTwoExteriorNeighbor.objective (μ.real {v | S.ρ v = a.val})
        (μ.real {v | S.ρ v = r.val})
        (μ.real {v | S.ρ v = z1.val}) (μ.real {v | S.ρ v = z2.val}) (μ.real S.D)
        (S.coveredTwoBoundaryEntry r a z1) = c := by
  obtain ⟨_, V, hV, hmom, _⟩ :=
    S.exists_covered_two_neighbor_entry r a z1 z2 hW hd hgap hpair hzero hE hR
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hi := CoveredTwoExteriorNeighbor.block_physicalObjective (μ := μ)
    (S.coveredTwoBoundaryLabel r a z1) (S.measurable_coveredTwoBoundaryLabel r a z1)
    (S.coveredTwoBoundaryEntry r a z1)
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    S.coveredTwoBoundaryLabel_fibers r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms
  rw [h0, h1, h2, h3, h4] at hi
  rw [← hi, ← hV.objective_eq]
  change (∫ p : Ω × Ω, CoveredTwoExteriorNeighbor.blockCharge (S.coveredTwoBoundaryEntry r a z1)
      (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2) ∂μ.prod μ) / 2 =
    (∫ p, V.moment CappedColor.charge p ∂μ.prod μ) / 2
  congr 1
  exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))

/-- The actual entry has a<b before any corrected compact-face selection.
The positive R row of its own model proves the ordering internally. -/
theorem covered_two_neighbor_head_mass_lt (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a)) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a)
    (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    μ.real {x | S.ρ x = a.val} < μ.real {x | S.ρ x = r.val} := by
  obtain ⟨hx, V, hV, hmom, _⟩ :=
    S.exists_covered_two_neighbor_entry r a z1 z2 hW hd hgap hpair hzero hE hR
      hz1r hz1a hz2r hz2a hz12 hatoms
  have hpos := S.coveredTwoBoundaryLabel_fibers_positive r a z1 z2 hpair.1
    hz1r hz1a hz2r hz2a hz12 hatoms (hR.trans_le (measure_mono inter_subset_left))
  have hab := CoveredTwoExteriorNeighbor.a_lt_b_of_fullStationaryClass hV hd hgap
    (S.coveredTwoBoundaryLabel r a z1) (S.measurable_coveredTwoBoundaryLabel r a z1)
    hpos (S.coveredTwoBoundaryEntry r a z1) hx hmom
  obtain ⟨h0, h1, _⟩ := S.coveredTwoBoundaryLabel_fibers r a z1 z2 hpair.1
    hz1r hz1a hz2r hz2a hz12 hatoms
  rwa [h0, h1] at hab

end Erdos1017.CappedModel.SelectedHighLowStructure

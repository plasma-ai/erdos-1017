module

public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerBadRegion
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairCapacity
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalNegative
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalOccupation
public import Erdos1017.Exclusions.Common.Physical.PhysicalCountMeasure

/-!
# Rootless quota of the empty-source saturated corner

This module defines the partner, hole and common parent events, shows a
bounded-order weighted leaf integral is a finite same-law sum, that the unique
saturated pair exhausts the order-two stock, and that the rootless columns use
one negative inventory with its degree cap and partner-column payment.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The actual original parent has no universal root and contains its saturated partner. -/
def emptySatPartnerEvent (S : SelectedHighLowStructure W m) (r p : S.I) (n : ℕ) :
    Set (Fin n → Ω) :=
  {v | (∀ i, S.ρ (v i) ≠ r.val) ∧ ∃ i, S.ρ (v i) = p.val}

/-- The actual original parent avoids both heads and meets the partner hole. -/
def emptySatHoleEvent (S : SelectedHighLowStructure W m) (r p : S.I) (n : ℕ) :
    Set (Fin n → Ω) :=
  {v | (∀ i, S.ρ (v i) ≠ r.val ∧ S.ρ (v i) ≠ p.val) ∧
    ∃ i, v i ∈ S.universalPartnerHoleRegion r p}

/-- Every coordinate lies in the original common-neighbor region. -/
def emptySatCommonEvent (S : SelectedHighLowStructure W m) (r p : S.I) (n : ℕ) :
    Set (Fin n → Ω) := {v | ∀ i, v i ∈ S.universalPartnerCommonRegion r p}

theorem measurableSet_emptySatPartnerEvent (S : SelectedHighLowStructure W m)
    (r p : S.I) (n : ℕ) : MeasurableSet (S.emptySatPartnerEvent r p n) := by
  have hfirst := MeasurableSet.iInter (fun i : Fin n =>
    ((S.hfibers r.val r.property).1.preimage (measurable_pi_apply i)).compl)
  have hsecond := MeasurableSet.iUnion (fun i : Fin n =>
    (S.hfibers p.val p.property).1.preimage (measurable_pi_apply i))
  convert hfirst.inter hsecond using 1
  ext v
  simp [emptySatPartnerEvent]

theorem measurableSet_emptySatHoleEvent (S : SelectedHighLowStructure W m)
    (r p : S.I) (n : ℕ) : MeasurableSet (S.emptySatHoleEvent r p n) := by
  have hfirst := MeasurableSet.iInter (fun i : Fin n =>
    (((S.hfibers r.val r.property).1.preimage (measurable_pi_apply i)).compl).inter
      (((S.hfibers p.val p.property).1.preimage (measurable_pi_apply i)).compl))
  have hsecond := MeasurableSet.iUnion (fun i : Fin n =>
    (S.measurableSet_universalPartnerHoleRegion r p).preimage (measurable_pi_apply i))
  convert hfirst.inter hsecond using 1
  ext v
  simp [emptySatHoleEvent]

theorem measurableSet_emptySatCommonEvent (S : SelectedHighLowStructure W m)
    (r p : S.I) (n : ℕ) : MeasurableSet (S.emptySatCommonEvent r p n) := by
  have h := MeasurableSet.iInter (fun i : Fin n =>
    (S.measurableSet_universalPartnerCommonRegion r p).preimage (measurable_pi_apply i))
  convert h using 1
  ext v
  simp [emptySatCommonEvent]

/-- Negative original universal-root charge, counted on every old parent coordinate. -/
def emptySatNegativeLoad (S : SelectedHighLowStructure W m) (r : S.I)
    (n : ℕ) (v : Fin n → Ω) : ℝ := ∑ i, max (-S.rootChargeRow r (v i)) 0

/-- The signed two-head deficit is counted only in the actual common region. -/
def emptySatSigmaLoad (S : SelectedHighLowStructure W m) (r p : S.I)
    (n : ℕ) (v : Fin n → Ω) : ℝ :=
  ∑ i, (S.universalPartnerCommonRegion r p).indicator
    (fun x => -(S.rootChargeRow r x + S.rootChargeRow p x)) (v i)

/-- Original negative charge weighted by its retained physical degree budget. -/
def emptySatNegativeDegreeLoad (S : SelectedHighLowStructure W m) (r p : S.I) : ℝ :=
  ∫ x in S.universalNegativeRegion r p, -S.rootChargeRow r x *
    ((∫ y, adjacencyKernel W x y ∂μ) - 3 * S.originalAtomMass r +
      S.originalAtomMass p) ∂μ

namespace UniversalPhysicalPrimal

variable {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- Restriction of the same attained parent laws to no-I/some-P columns. -/
def emptySatPartnerLaws (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    PhysicalPrimal.Laws Ω := fun n => (P.laws n).restrict (S.emptySatPartnerEvent r p n)

/-- Restriction of the same attained parent laws to headless columns meeting H. -/
def emptySatHoleLaws (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    PhysicalPrimal.Laws Ω := fun n => (P.laws n).restrict (S.emptySatHoleEvent r p n)

/-- Restriction of the same attained parent laws to U-only columns. -/
def emptySatCommonLaws (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    PhysicalPrimal.Laws Ω := fun n => (P.laws n).restrict (S.emptySatCommonEvent r p n)

instance (P : S.UniversalPhysicalPrimal r c) (p : S.I) (n : ℕ) :
    IsFiniteMeasure (P.emptySatPartnerLaws p n) := by
  have := P.finite n
  dsimp [emptySatPartnerLaws]
  infer_instance

instance (P : S.UniversalPhysicalPrimal r c) (p : S.I) (n : ℕ) :
    IsFiniteMeasure (P.emptySatHoleLaws p n) := by
  have := P.finite n
  dsimp [emptySatHoleLaws]
  infer_instance

instance (P : S.UniversalPhysicalPrimal r c) (p : S.I) (n : ℕ) :
    IsFiniteMeasure (P.emptySatCommonLaws p n) := by
  have := P.finite n
  dsimp [emptySatCommonLaws]
  infer_instance

/-- Actual rootless partner-column cost. -/
def emptySatPartnerCost (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  PhysicalPrimal.cost (P.emptySatPartnerLaws p)

/-- Actual headless hole-column cost. -/
def emptySatHoleCost (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  PhysicalPrimal.cost (P.emptySatHoleLaws p)

/-- Actual U-only column cost. -/
def emptySatCommonCost (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  PhysicalPrimal.cost (P.emptySatCommonLaws p)

/-- Negative load on the same rootless partner columns, retaining the order cap. -/
def emptySatPartnerNegativeLoad (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  ∑ n ∈ Finset.range (P.orderCap + 1),
    ∫ v, S.emptySatNegativeLoad r n v ∂P.emptySatPartnerLaws p n

/-- Sigma load on those same partner columns, with no second inventory. -/
def emptySatPartnerSigmaLoad (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  ∑ n ∈ Finset.range (P.orderCap + 1),
    ∫ v, S.emptySatSigmaLoad r p n v ∂P.emptySatPartnerLaws p n

end UniversalPhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
private theorem measurableSet_no_root {n : ℕ} (I : Set Ω) (hI : MeasurableSet I) :
    MeasurableSet {v : Fin n → Ω | ∀ i, v i ∉ I} := by
  have h := MeasurableSet.iInter (fun i : Fin n => (hI.preimage (measurable_pi_apply i)).compl)
  convert h using 1
  ext v
  simp

/-- Fresh independent sampling licenses the actual signed load of every
old rootless column, including singular parent laws. -/
theorem ae_emptySat_rootless_augmented_charge_le_one (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) (n : ℕ) :
    ∀ᵐ v ∂PhysicalRootReplacement.noRootLaw (P.laws n) {x | S.ρ x = r.val},
      PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v +
        ∑ i, S.rootChargeRow r (v i) ≤ 1 := by
  classical
  by_cases hn : 2 ≤ n
  · have : IsFiniteMeasure (P.laws n) := P.finite n
    let I := {x | S.ρ x = r.val}
    have hI : MeasurableSet I := (S.hfibers r.val r.property).1
    let ρ := PhysicalRootReplacement.noRootLaw (P.laws n) I
    have : IsFiniteMeasure ρ := by dsimp [ρ]; infer_instance
    let ν : Measure Ω := PhysicalRootReplacement.rootLaw μ I (S.hfibers r.val r.property).2.1.ne'
    have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    have hν : ν ≪ μ := PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous μ I
    have hνI : ∀ᵐ z ∂ν, z ∈ I := by
      change ∀ᵐ z ∂(μ I)⁻¹ • μ.restrict I, z ∈ I
      exact Measure.ae_smul_measure (ae_restrict_mem hI) _
    have hρ : ρ ≪ P.laws n := Measure.absolutelyContinuous_restrict
    have hdemand : PhysicalPrimal.graphDemand μ
        {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} ≪ μ.prod μ :=
      Measure.absolutelyContinuous_restrict
    have hpairs : ∀ i j : Fin n, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ := by
      intro i j hij
      exact (hρ.map ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).trans
        ((PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
          P.feasible.2.2.2 n ⟨(i, j), hij⟩).trans hdemand)
    let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
    let Y := Function.uncurry (PhysicalRepresentative.charge W m)
    have hs := hW.strict_gap_structure hd hgap
    have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
        PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
      intro k _
      filter_upwards [PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
        hW.deterministic k] with v hv hc
      change PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v ≤ 1
      rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
      exact hv hc
    have hfresh := PhysicalCliqueRepresentative.freshLaw_pairs_absolutelyContinuous μ hn
      ρ hpairs ν hν
    have hlicense := PhysicalCliqueRepresentative.ae_charge_le_of_pair_marginals μ
      (PhysicalRepresentative.measurable_adjacency W m)
      (PhysicalRepresentative.measurable_charge W m)
      3 (by norm_num) (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
      htest (PhysicalCliqueRepresentative.freshLaw ν ρ) hfresh
    have hlicenseProd := ae_of_ae_map
      PhysicalCliqueRepresentative.measurable_cons.aemeasurable hlicense
    have hrow : ∀ᵐ p ∂μ.prod μ,
        (S.ρ p.1 = r.val → (G p = true ↔ S.ρ p.2 ≠ r.val)) ∧
        (S.ρ p.1 = r.val → Y p = S.rootChargeRow r p.2) :=
      (S.neutral_atom_physical_adjacency r hW hd hgap hN).and (S.ae_root_charge r hW hd hgap)
    have hfacts : ∀ᵐ w ∂PhysicalCliqueRepresentative.freshLaw ν ρ,
        ∀ i j : Fin (n + 1), i ≠ j →
          (S.ρ (w i) = r.val → (G (w i, w j) = true ↔ S.ρ (w j) ≠ r.val)) ∧
          (S.ρ (w i) = r.val → Y (w i, w j) = S.rootChargeRow r (w j)) := by
      simp only [ae_all_iff]
      intro i j hij
      exact ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
        ((hfresh i j hij).ae_le hrow)
    have hfactsProd := ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hfacts
    have hnone : ∀ᵐ v ∂ρ, ∀ i, v i ∉ I :=
      ae_restrict_mem (measurableSet_no_root I hI)
    have hbound : ∀ᵐ p ∂ν.prod ρ,
        PhysicalPrimal.charge Y p.2 + ∑ i, S.rootChargeRow r (p.2 i) ≤ 1 := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hνI,
        Measure.quasiMeasurePreserving_snd.ae hnone,
        Measure.quasiMeasurePreserving_snd.ae (hρ.ae_le (P.feasible.2.2.1 n)),
        hlicenseProd, hfactsProd] with p hp hnoro hc hlic hfact
      have hnew (i : Fin n) : G (p.1, p.2 i) = true := by
        have h := hfact 0 i.succ (Fin.succ_ne_zero i).symm
        change (S.ρ p.1 = r.val → (G (p.1, p.2 i) = true ↔ S.ρ (p.2 i) ≠ r.val)) ∧ _ at h
        exact (h.1 hp).mpr (hnoro i)
      have hstar (i : Fin n) : Y (p.1, p.2 i) = S.rootChargeRow r (p.2 i) := by
        have h := hfact 0 i.succ (Fin.succ_ne_zero i).symm
        change _ ∧ (S.ρ p.1 = r.val → Y (p.1, p.2 i) = S.rootChargeRow r (p.2 i)) at h
        exact h.2 hp
      have hcl : PhysicalCliqueRepresentative.Clique G (Fin.cons p.1 p.2) := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact hnew j
        | succ i =>
          cases j using Fin.cases with
          | zero =>
            change PhysicalRepresentative.adjacency W m (p.2 i) p.1 = true
            rw [PhysicalRepresentative.adjacency_symm W m (p.2 i) p.1]
            exact hnew i
          | succ j => exact hc i j (fun h => hij (congrArg Fin.succ h))
      have hcap := hlic hcl
      rw [PhysicalTriangleExposure.charge_cons Y
        (PhysicalRepresentative.charge_symm W m) p.2 p.1] at hcap
      simpa only [hstar, add_comm] using hcap
    exact (Measure.ae_ae_of_ae_prod hbound).exists.choose_spec
  · have hn' : n ≤ 1 := by omega
    interval_cases n <;> simp [P.feasible.1, P.feasible.2.1, PhysicalRootReplacement.noRootLaw]

/-- Tightness converts the licensed original rootless inequality to a
nonpositive signed universal-root load on the same parent laws. -/
theorem ae_emptySat_rootless_rootLoad_nonpos (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) (n : ℕ) :
    ∀ᵐ v ∂PhysicalRootReplacement.noRootLaw (P.laws n) {x | S.ρ x = r.val},
      ∑ i, S.rootChargeRow r (v i) ≤ 0 := by
  filter_upwards [P.ae_emptySat_rootless_augmented_charge_le_one hW hd hgap hN n,
    ae_restrict_of_ae (P.tight_physical n)] with v hv ht
  linarith only [hv, ht]

end Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- The actual no-I/some-P columns retain the whole signed I-load and
pay one unit in P-leaf charge minus their same-column sigma correction. -/
theorem ae_emptySat_partner_charge_load (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) (n : ℕ) :
    ∀ᵐ v ∂P.emptySatPartnerLaws p n,
      (∑ i, S.rootChargeRow r (v i)) ≤ 0 ∧
        1 - S.emptySatSigmaLoad r p n v ≤ ∑ i, S.rootChargeRow p (v i) := by
  have hI := (S.hfibers r.val r.property).1
  have hP := (S.hfibers p.val p.property).1
  have hno : MeasurableSet {v : Fin n → Ω | ∀ i, S.ρ (v i) ≠ r.val} := by
    have h := MeasurableSet.iInter (fun i : Fin n =>
      (hI.preimage (measurable_pi_apply i)).compl)
    convert h using 1
    ext v
    simp
  have hroot := (ae_restrict_iff' hno).mp
    (P.ae_emptySat_rootless_rootLoad_nonpos hW hd hgap hN n)
  have hrP := (ae_restrict_iff' hP).mp
    (S.ae_rootChargeRow_on_constant_block r p hW hd hgap 1 hpair.2)
  have hhead : ∀ᵐ x ∂μ, S.ρ x = p.val →
      S.rootChargeRow r x = 1 ∧ S.rootChargeRow p x = 0 := by
    filter_upwards [hrP, S.rootChargeRow_zero_off_neighborhood p hW hd hgap] with x hr hp hx
    refine ⟨hr hx, hp ?_⟩
    intro hn
    exact hn.1 hx
  have hheadP := P.ae_original_vertices _ hhead n
  have hrow := P.ae_original_pairs _ (S.ae_root_adjacency p hW hd hgap) n
  filter_upwards [ae_restrict_of_ae hroot, ae_restrict_of_ae hheadP,
    ae_restrict_of_ae hrow, ae_restrict_of_ae (P.feasible.2.2.1 n),
    ae_restrict_of_ae (P.partner_unique_root p hW hd hgap n),
    ae_restrict_mem (S.measurableSet_emptySatPartnerEvent r p n)]
    with v hroot hhead hrow hclique hunique hv
  have hbeta : (∑ i, S.rootChargeRow r (v i)) ≤ 0 := hroot hv.1
  refine ⟨hbeta, ?_⟩
  obtain ⟨j, hj⟩ := hv.2
  have hcommon : ∀ i : Fin n, i ≠ j → v i ∈ S.universalPartnerCommonRegion r p := by
    intro i hij
    have hpi : S.ρ (v i) ≠ p.val := fun hi => hij (hunique i j hi hj)
    have hnp : v i ∈ S.rootNeighborhood p := (hrow j i hij.symm hj).mp (hclique j i hij.symm)
    intro hout
    rcases hout with (hr | hp) | hH
    · exact hv.1 i hr
    · exact hpi hp
    · exact hH (Or.inr hnp)
  let f : Fin n → ℝ := fun i => S.rootChargeRow r (v i) + S.rootChargeRow p (v i) +
    (S.universalPartnerCommonRegion r p).indicator
      (fun x => -(S.rootChargeRow r x + S.rootChargeRow p x)) (v i)
  have hsum : (∑ i, f i) = 1 := by
    rw [Finset.sum_eq_single j]
    · have hnot : v j ∉ S.universalPartnerCommonRegion r p :=
        fun h => h (Or.inl (Or.inr hj))
      dsimp [f]
      rw [(hhead j hj).1, (hhead j hj).2, indicator_of_notMem hnot]
      norm_num
    · intro i hi hij
      dsimp [f]
      rw [indicator_of_mem (hcommon i hij)]
      ring
    · simp
  have hid : (∑ i, f i) = (∑ i, S.rootChargeRow r (v i)) +
      (∑ i, S.rootChargeRow p (v i)) + S.emptySatSigmaLoad r p n v := by
    dsimp [f, emptySatSigmaLoad]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith only [hsum, hid, hbeta]

end Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A literal cap reduces every signed pair integral to the same finite
family of original joint parent laws. -/
theorem sum_integral_charge_of_cap (N : ℕ) (eta : Laws Ω)
    (hcap : ∀ n, N < n → eta n = 0) (K : Ω × Ω → ℝ)
    (hK : Integrable K (occupation eta)) :
    (∑ n ∈ Finset.range (N + 1), ∫ v, charge K v ∂eta n) =
      (∫ z, K z ∂occupation eta) / 2 := by
  have hi (n : ℕ) : Integrable K (orderOccupation n (eta n)) :=
    hK.mono_measure (Measure.le_sum (fun k => orderOccupation k (eta k)) n)
  have hord (n : ℕ) : (∫ v, charge K v ∂eta n) =
      (∫ z, K z ∂orderOccupation n (eta n)) / 2 :=
    (integral_charge n (eta n) K (hi n)).2
  simp_rw [hord]
  rw [← Finset.sum_div, ← integral_finsetSum_measure (fun n _ => hi n),
    ← occupation_eq_sum_of_cap N eta hcap]

omit [MeasurableSpace Ω] in
/-- Weighted root-to-leaf charge retains the actual diagonal subtraction. -/
theorem charge_weighted_root {n : ℕ} (I : Set Ω) (f : Ω → ℝ) (v : Fin n → Ω) :
    2 * PhysicalPrimal.charge (fun z => if z.1 ∈ I then f z.2 else 0) v =
      (PhysicalPrimal.tupleCount I v : ℝ) * (∑ i, f (v i)) -
        ∑ i, if v i ∈ I then f (v i) else 0 := by
  rw [show (fun z : Ω × Ω => if z.1 ∈ I then f z.2 else 0) =
      Function.uncurry (fun x y => if x ∈ I then f y else 0) from rfl,
    PhysicalPrimal.charge_uncurry_eq_tupleCharge]
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  have he (i j : Fin n) :
      (if i = j then 0 else if v i ∈ I then f (v j) else 0) =
        (if v i ∈ I then (1 : ℝ) else 0) * f (v j) -
          (if i = j then (if v i ∈ I then f (v i) else 0) else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hi : v i ∈ I <;> simp [hi]
    · by_cases hi : v i ∈ I <;> simp [hij, hi]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [PhysicalPrimal.tupleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  ring

end Erdos1017.PhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- The original primal's literal cap and exact ordered balance identify
all signed pair charges without changing any parent law. -/
theorem emptySat_sum_integral_charge (P : S.UniversalPhysicalPrimal r c)
    (K : Ω × Ω → ℝ) (hK : Integrable K (μ.prod μ)) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, PhysicalPrimal.charge K v ∂P.laws n) =
      (∫ z, K z ∂PhysicalPrimal.graphDemand μ
        {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true}) / 2 := by
  have hi : Integrable K (PhysicalPrimal.occupation P.laws) := by
    rw [P.feasible.2.2.2]
    exact hK.mono_measure Measure.restrict_le_self
  have h := PhysicalPrimal.sum_integral_charge_of_cap P.orderCap P.laws
    (fun n hn => P.capped n (Or.inr hn)) K hi
  rwa [P.feasible.2.2.2] at h

end Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded-order weighted leaf integral is the exact same-law finite
sum, including its diagonal correction and arbitrary signed weights. -/
theorem integral_rootLeaves_eq_sum_of_cap (N : ℕ) (eta : Laws Ω)
    (hcap : ∀ n, N < n → eta n = 0) (I : Set Ω) (hI : MeasurableSet I)
    (f : Ω → ℝ) (hf : Measurable f)
    (hK : Integrable (fun z : Ω × Ω => if z.1 ∈ I then f z.2 else 0) (occupation eta)) :
    (∫ x, f x ∂rootLeaves eta I) =
      ∑ n ∈ Finset.range (N + 1), ∫ v,
        (tupleCount I v : ℝ) * (∑ i, f (v i)) -
          (∑ i, if v i ∈ I then f (v i) else 0) ∂eta n := by
  let K : Ω × Ω → ℝ := fun z => if z.1 ∈ I then f z.2 else 0
  have hroot : (∫ x, f x ∂rootLeaves eta I) = ∫ z, K z ∂occupation eta := by
    rw [rootLeaves_eq_snd_restrict eta I hI, Measure.snd,
      integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
    have h := integral_indicator (μ := occupation eta) (f := fun z : Ω × Ω => f z.2)
      (hI.prod MeasurableSet.univ)
    simpa only [K, Set.indicator, mem_prod, mem_univ, and_true] using h.symm
  have hcharge := sum_integral_charge_of_cap N eta hcap K hK
  have hpoint (n : ℕ) (v : Fin n → Ω) :
      (tupleCount I v : ℝ) * (∑ i, f (v i)) -
        (∑ i, if v i ∈ I then f (v i) else 0) = 2 * charge K v :=
    (charge_weighted_root I f v).symm
  simp_rw [hpoint, integral_const_mul, ← Finset.mul_sum]
  rw [hcharge, hroot]
  ring

end Erdos1017.PhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- The unique original saturated pair exhausts the order-two stock, so the
same primal has no rootless two-point parents. -/
theorem emptySat_noRootLaw_two_eq_zero (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1) :
    PhysicalRootReplacement.noRootLaw (P.laws 2) {x | S.ρ x = r.val} = 0 := by
  have hsat : ∀ᵐ z ∂μ.prod μ, PhysicalRepresentative.charge W m z.1 z.2 = 1 →
      S.ρ z.1 = r.val ∨ S.ρ z.2 = r.val := by
    filter_upwards [hpair.ae_charge_one_iff_between_heads hW hd hgap hell,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
      with z hz he hy
    have h := hz.mp (he.symm.trans hy)
    exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  have hno : MeasurableSet {v : Fin 2 → Ω | ∀ i, S.ρ (v i) ≠ r.val} := by
    have h := MeasurableSet.iInter (fun i : Fin 2 =>
      (((S.hfibers r.val r.property).1).preimage (measurable_pi_apply i)).compl)
    convert h using 1
    ext v
    simp
  have hfalse : ∀ᵐ v ∂PhysicalRootReplacement.noRootLaw (P.laws 2) {x | S.ρ x = r.val},
      False := by
    filter_upwards [ae_restrict_mem hno,
      ae_restrict_of_ae (P.ae_original_pairs _ hsat 2),
      ae_restrict_of_ae (P.tight_physical 2)] with v hn hs ht
    have he : PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v =
        PhysicalRepresentative.charge W m (v 0) (v 1) := by
      rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
      simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
        Fin.sum_univ_succ, PhysicalRepresentative.charge_symm W m (v 1) (v 0)]
    have h := hs 0 1 (by decide) (he.symm.trans ht)
    exact h.elim (hn 0) (hn 1)
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, ofPred_true] using hfalse

end Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

private theorem clique_cons_of_symm {Ω : Type*} {n : ℕ} (G : Ω × Ω → Bool)
    (hsym : ∀ x y, G (x, y) = G (y, x)) (x : Ω) (v : Fin n → Ω)
    (hv : PhysicalCliqueRepresentative.Clique G v) (hx : ∀ i, G (x, v i) = true) :
    PhysicalCliqueRepresentative.Clique G (Fin.cons x v) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => exact hx j
  | succ i =>
    cases j using Fin.cases with
    | zero => exact (hsym (v i) x).trans (hx i)
    | succ j => exact hv i j (fun h => hij (congrArg Fin.succ h))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- Two genuinely independent fresh original heads license the signed
sigma budget on the same U-only parent laws, even when singular. -/
theorem ae_emptySat_common_augmented_charge_le_one (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) (n : ℕ) :
    ∀ᵐ (v : Fin n → Ω) ∂P.emptySatCommonLaws p n,
      PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v + 1 +
        (∑ i : Fin n, (S.rootChargeRow r (v i) + S.rootChargeRow p (v i))) ≤ 1 := by
  by_cases hn : 2 ≤ n
  · let rho := P.emptySatCommonLaws p n
    have : IsFiniteMeasure (P.laws n) := P.finite n
    have hrho : rho ≪ P.laws n := Measure.absolutelyContinuous_restrict
    let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
    let Y := Function.uncurry (PhysicalRepresentative.charge W m)
    have hpairs : ∀ i j : Fin n, i ≠ j → rho.map (fun v => (v i, v j)) ≪ μ.prod μ := by
      intro i j hij
      exact (hrho.map ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).trans
        ((PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
          P.feasible.2.2.2 n ⟨(i, j), hij⟩).trans Measure.absolutelyContinuous_restrict)
    let lambda := PhysicalCliqueRepresentative.freshLaw μ rho
    let lambda2 := PhysicalCliqueRepresentative.freshLaw μ lambda
    have hpairs1 := PhysicalCliqueRepresentative.freshLaw_pairs_absolutelyContinuous μ hn
      rho hpairs μ Measure.AbsolutelyContinuous.rfl
    have hpairs2 := PhysicalCliqueRepresentative.freshLaw_pairs_absolutelyContinuous μ
      (by omega : 2 ≤ n + 1) lambda hpairs1 μ Measure.AbsolutelyContinuous.rfl
    have hs := hW.strict_gap_structure hd hgap
    have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
        PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
      intro k hk
      filter_upwards [PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
        hW.deterministic k] with v hv hc
      rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
      exact hv hc
    have hlicense := PhysicalCliqueRepresentative.ae_charge_le_of_pair_marginals μ
      (PhysicalRepresentative.measurable_adjacency W m)
      (PhysicalRepresentative.measurable_charge W m) 3 (by norm_num)
      (fun z => PhysicalRepresentative.charge_bound W m z.1 z.2) htest lambda2 hpairs2
    have hrow : ∀ᵐ z ∂μ.prod μ,
        (S.ρ z.1 = r.val → (G z = true ↔ S.ρ z.2 ≠ r.val) ∧
          Y z = S.rootChargeRow r z.2) ∧
        (S.ρ z.1 = p.val → (G z = true ↔ z.2 ∈ S.rootNeighborhood p) ∧
          Y z = S.rootChargeRow p z.2) ∧
        (S.ρ z.1 = r.val → S.ρ z.2 = p.val → Y z = 1) := by
      filter_upwards [S.neutral_atom_physical_adjacency r hW hd hgap hN,
        S.ae_root_charge r hW hd hgap, S.ae_root_adjacency p hW hd hgap,
        S.ae_root_charge p hW hd hgap, hpair.2,
        PhysicalRepresentative.charge_ae_eq W m hs.strict_support]
        with z hGr hYr hGp hYp hsat hY
      exact ⟨fun hr => ⟨hGr hr, hYr hr⟩, fun hp => ⟨hGp hp, hYp hp⟩,
        fun hr hp => hY.trans (hsat hr hp)⟩
    have hfacts : ∀ᵐ w ∂lambda2, ∀ i j : Fin ((n + 1) + 1), i ≠ j →
        (S.ρ (w i) = r.val → (G (w i, w j) = true ↔ S.ρ (w j) ≠ r.val) ∧
          Y (w i, w j) = S.rootChargeRow r (w j)) ∧
        (S.ρ (w i) = p.val → (G (w i, w j) = true ↔ w j ∈ S.rootNeighborhood p) ∧
          Y (w i, w j) = S.rootChargeRow p (w j)) ∧
        (S.ρ (w i) = r.val → S.ρ (w j) = p.val → Y (w i, w j) = 1) := by
      simp only [ae_all_iff]
      intro i j hij
      exact ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
        ((hpairs2 i j hij).ae_le hrow)
    have houter := (ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable
      hlicense).and (ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hfacts)
    obtain ⟨x, hx, hxs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers r.val r.property).2.1.ne'
      (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod houter))
    have hinner := ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hxs
    obtain ⟨y, hy, hys⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers p.val p.property).2.1.ne'
      (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hinner))
    filter_upwards [hys, ae_restrict_mem (S.measurableSet_emptySatCommonEvent r p n),
      hrho.ae_le (P.feasible.2.2.1 n)] with v hv hU hc
    have hxp : S.ρ y ≠ r.val := fun he => hpair.1 (Subtype.ext (he.symm.trans hy))
    have hxy : G (x, y) = true :=
      ((hv.2 0 (Fin.succ 0) (Fin.succ_ne_zero 0).symm).1 hx).1.mpr hxp
    have hxyY : Y (x, y) = 1 :=
      (hv.2 0 (Fin.succ 0) (Fin.succ_ne_zero 0).symm).2.2 hx hy
    have hxr (i : Fin n) : G (x, v i) = true ∧ Y (x, v i) = S.rootChargeRow r (v i) := by
      have h := (hv.2 0 i.succ.succ (Fin.succ_ne_zero i.succ).symm).1 hx
      exact ⟨h.1.mpr (fun he => hU i (Or.inl (Or.inl he))), h.2⟩
    have hpr (i : Fin n) : G (y, v i) = true ∧ Y (y, v i) = S.rootChargeRow p (v i) := by
      have h := (hv.2 (Fin.succ 0) i.succ.succ (by
        intro he
        have hval := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_zero] at hval
        omega)).2.1 hy
      exact ⟨h.1.mpr (S.common_region_mem_rootNeighborhood r p (hU i)), h.2⟩
    have hsym : ∀ a b, G (a, b) = G (b, a) := PhysicalRepresentative.adjacency_symm W m
    have hclP := clique_cons_of_symm G hsym y v hc (fun i => (hpr i).1)
    have hclI := clique_cons_of_symm G hsym x (Fin.cons y v) hclP (by
      intro i
      cases i using Fin.cases with
      | zero => exact hxy
      | succ i => exact (hxr i).1)
    have hbound := hv.1 hclI
    rw [PhysicalTriangleExposure.charge_cons Y (PhysicalRepresentative.charge_symm W m),
      PhysicalTriangleExposure.charge_cons Y (PhysicalRepresentative.charge_symm W m),
      Fin.sum_univ_succ] at hbound
    simp only [Fin.cons_zero, Fin.cons_succ, hxyY, (hxr _).2, (hpr _).2] at hbound
    have hsum : (∑ i : Fin n, (S.rootChargeRow r (v i) + S.rootChargeRow p (v i))) =
        (∑ i, S.rootChargeRow r (v i)) + ∑ i, S.rootChargeRow p (v i) :=
      Finset.sum_add_distrib
    linarith only [hbound, hsum]
  · have hn' : n ≤ 1 := by omega
    interval_cases n <;> simp [emptySatCommonLaws, P.feasible.1, P.feasible.2.1]

end Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem weighted_root_stock (P : S.UniversalPhysicalPrimal r c)
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (hzero : ∀ x ∈ I, f x = 0) (hsupport : ∀ x ∉ J, f x = 0)
    (a : ℝ≥0∞) (hleaves : PhysicalPrimal.rootLeaves P.laws I = a • μ.restrict J) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PhysicalPrimal.tupleCount I v : ℝ) * (∑ i, f (v i)) ∂P.laws n) =
      a.toReal * ∫ x, f x ∂μ := by
  let K : Ω × Ω → ℝ := fun z => if z.1 ∈ I then f z.2 else 0
  have hfs : Integrable (fun z : Ω × Ω => f z.2) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hfi
  have hK : Integrable K (PhysicalPrimal.occupation P.laws) := by
    have hKi : Integrable K (μ.prod μ) := by
      convert hfs.indicator (hI.prod MeasurableSet.univ) using 1
      funext z
      simp only [K, Set.indicator, mem_prod, mem_univ, and_true]
    rw [P.feasible.2.2.2]
    exact hKi.mono_measure Measure.restrict_le_self
  have hstock := PhysicalPrimal.integral_rootLeaves_eq_sum_of_cap P.orderCap P.laws
    (fun n hn => P.capped n (Or.inr hn)) I hI f hf hK
  have hdiag (n : ℕ) (v : Fin n → Ω) :
      (∑ i, if v i ∈ I then f (v i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    split_ifs with hx
    · exact hzero (v i) hx
    · rfl
  simp_rw [hdiag, sub_zero] at hstock
  have hfun : J.indicator f = f := by
    funext x
    by_cases hx : x ∈ J
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx, hsupport x hx]
  have hintegral : (∫ x in J, f x ∂μ) = ∫ x, f x ∂μ := by
    rw [← integral_indicator hJ, hfun]
  rw [hleaves, integral_smul_measure, hintegral] at hstock
  simpa only [smul_eq_mul] using hstock.symm

private theorem negativePart_eq_common_negative (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    (fun x => max (-S.rootChargeRow r x) 0) =ᵐ[μ]
      (S.universalNegativeRegion r p).indicator (fun x => -S.rootChargeRow r x) := by
  let theta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hApos : 0 < S.originalAtomMass r := by linarith
  have htheta : 0 < theta := by
    have hdiv : 2 * (1 + m) < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r := by
      apply (lt_div_iff₀ hApos).mpr
      nlinarith only [hmargin]
    dsimp [theta]
    linarith [hell.2]
  have hP := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp
    (S.ae_rootChargeRow_on_constant_block r p hW hd hgap 1 hpair.2)
  have hH := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
    (P.ae_universal_upperE2_hole_star_threshold S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  filter_upwards [hP, hH, S.rootChargeRow_zero_off_neighborhood r hW hd hgap]
    with x hP hH hI
  by_cases hU : x ∈ S.universalPartnerCommonRegion r p
  · by_cases hbeta : S.rootChargeRow r x < 0
    · have hB : x ∈ S.universalNegativeRegion r p := ⟨hU, hbeta⟩
      rw [indicator_of_mem hB, max_eq_left (by linarith)]
    · have hB : x ∉ S.universalNegativeRegion r p := fun hx => hbeta hx.2
      rw [indicator_of_notMem hB, max_eq_right (by linarith)]
  · have hB : x ∉ S.universalNegativeRegion r p := fun hx => hU hx.1
    rw [indicator_of_notMem hB]
    apply max_eq_right
    by_cases hr : S.ρ x = r.val
    · have hz := hI (fun hn => hn.1 hr)
      linarith
    · by_cases hp : S.ρ x = p.val
      · rw [hP hp]
        norm_num
      · have hh : x ∈ S.universalPartnerHoleRegion r p := by
          by_contra hh
          exact hU (fun h => h.elim (fun h => h.elim hr hp) hh)
        have hbound : theta ≤ S.rootChargeRow r x := hH hh
        linarith

private theorem common_column_count {n : ℕ} (beta sigma : Fin n → ℝ)
    {ell eta : ℝ} (hell : 0 < ell) (heta : 0 < eta)
    (hthree : ell < 3 * eta) (hstep : ell - eta < 1 / 2)
    (hbeta : ∀ i, -ell < beta i)
    (hsigma : ∀ i, sigma i ≤ if eta ≤ beta i then max (ell - eta) 0 else 0)
    (hroot : (∑ i, beta i) ≤ 0) (htight : 1 ≤ ∑ i, sigma i) :
    5 ≤ n ∧ 3 * eta ≤ ∑ i, max (-beta i) 0 := by
  classical
  let G := Finset.univ.filter (fun i => eta ≤ beta i)
  let B := Finset.univ.filter (fun i => beta i < 0)
  let t := max (ell - eta) 0
  have ht : 0 ≤ t := le_max_right _ _
  have htHalf : t < 1 / 2 := max_lt hstep (by norm_num)
  have hsigmaSum : (∑ i, sigma i) ≤ (G.card : ℝ) * t := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsigma i)
    have hid : (∑ i : Fin n, if eta ≤ beta i then max (ell - eta) 0 else 0) =
        (G.card : ℝ) * t := by
      rw [← Finset.sum_filter]
      simp [G, t]
    exact h.trans_eq hid
  have hG : 3 ≤ G.card := by
    by_contra hbad
    have hcard : (G.card : ℝ) ≤ 2 := by exact_mod_cast (show G.card ≤ 2 by omega)
    have hmul := mul_le_mul_of_nonneg_right hcard ht
    linarith
  have hpositive : (G.card : ℝ) * eta ≤ ∑ i, max (beta i) 0 := by
    have h : ∀ i : Fin n, (if eta ≤ beta i then eta else 0) ≤ max (beta i) 0 := by
      intro i
      split_ifs with hi
      · exact hi.trans (le_max_left _ _)
      · exact le_max_right _ _
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
    have hid : (∑ i : Fin n, if eta ≤ beta i then eta else 0) = (G.card : ℝ) * eta := by
      rw [← Finset.sum_filter]
      simp [G]
    rwa [hid] at hsum
  have hid : (∑ i, beta i) = (∑ i, max (beta i) 0) - ∑ i, max (-beta i) 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : 0 ≤ beta i
    · rw [max_eq_left h, max_eq_right (by linarith : -beta i ≤ 0)]
      ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith : 0 ≤ -beta i)]
      ring
  have hF : 3 * eta ≤ ∑ i, max (-beta i) 0 := by
    have hcard : (3 : ℝ) ≤ G.card := by exact_mod_cast hG
    have hmul := mul_le_mul_of_nonneg_right hcard heta.le
    linarith
  refine ⟨?_, hF⟩
  have hsumB : (∑ i ∈ B, max (-beta i) 0) = ∑ i, max (-beta i) 0 := by
    dsimp only [B]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : beta i < 0
    · simp [h]
    · simp [h, max_eq_right (show -beta i ≤ 0 by linarith)]
  have hB : 2 ≤ B.card := by
    by_contra hbad
    have hcard : (B.card : ℝ) ≤ 1 := by exact_mod_cast (show B.card ≤ 1 by omega)
    have hnonempty : B.Nonempty := by
      by_contra hnot
      have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
      rw [he] at hsumB
      simp only [Finset.sum_empty] at hsumB
      linarith
    have hterm : ∀ i ∈ B, max (-beta i) 0 < ell := by
      intro i hi
      have hi' : beta i < 0 := (Finset.mem_filter.mp hi).2
      rw [max_eq_left (by linarith : 0 ≤ -beta i)]
      linarith only [hbeta i]
    have hsum : (∑ i ∈ B, max (-beta i) 0) < ∑ _ ∈ B, ell :=
      Finset.sum_lt_sum (fun i hi => (hterm i hi).le)
        (hnonempty.imp (fun i hi => ⟨hi, hterm i hi⟩))
    rw [hsumB] at hsum
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_right hcard hell.le
    linarith
  have hdis : Disjoint G B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    linarith
  have hcard := Finset.card_le_card (show G ∪ B ⊆ Finset.univ from Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdis, Finset.card_univ, Fintype.card_fin] at hcard
  omega


private theorem ae_common_sigma_cap (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
    ∀ᵐ x ∂μ, x ∈ S.universalPartnerCommonRegion r p →
      m < S.rootChargeRow r x ∧
      0 ≤ -(S.rootChargeRow r x + S.rootChargeRow p x) ∧
      -(S.rootChargeRow r x + S.rootChargeRow p x) ≤
        if eta ≤ S.rootChargeRow r x then max (-m - eta) 0 else 0 := by
  let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hzero := (ae_restrict_iff'
    (S.measurableSet_universalUpperE2BadRegion r p d c)).mp
    (P.ae_universalUpperE2Bad_score_eq_zero S r p hpair hW hd hgap hN hA hAhalf
      hell hmargin)
  filter_upwards [hzero, S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN,
    S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap,
    S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap,
    S.ae_universal_row_pos_on_outside r hW hd hgap hN]
    with x hz hscore hr hp hpos hx
  have hxr : S.ρ x ≠ r.val := fun h => hx (Or.inl (Or.inl h))
  have hxp : S.ρ x ≠ p.val := fun h => hx (Or.inl (Or.inr h))
  have hn := S.common_region_mem_rootNeighborhood r p hx
  have hrpos := hpos hxr
  have hppos := hn.2
  change 1 - S.rootChargeRow r x =
    1 - r.val x - m * (if 0 < r.val x then 1 else 0) at hr
  change 1 - S.rootChargeRow p x =
    1 - p.val x - m * (if 0 < p.val x then 1 else 0) at hp
  rw [ite_eq_left hrpos] at hr
  rw [ite_eq_left hppos] at hp
  have hrm : m < S.rootChargeRow r x := by linarith only [hr, hrpos]
  have hpm : m < S.rootChargeRow p x := by linarith only [hp, hppos]
  refine ⟨hrm, by linarith [hscore hxr hn], ?_⟩
  split_ifs with he
  · have h := le_max_left (-m - eta) 0
    dsimp only [eta] at *
    linarith only [hpm, he, h]
  · have hbad : x ∈ S.universalUpperE2BadRegion r p d c := by
      refine ⟨?_, lt_of_not_ge he⟩
      exact fun h => h.elim hxr hxp
    linarith only [hz hbad]


private theorem common_column_bounds (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (heta : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (hthree : -m < 3 * (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)))
    (hstep : -m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) < 1 / 2)
    (n : ℕ) :
    ∀ᵐ v ∂P.emptySatCommonLaws p n,
      5 ≤ n ∧ 3 * (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) ≤
        S.emptySatNegativeLoad r n v := by
  let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hI := (S.hfibers r.val r.property).1
  have hno : MeasurableSet {v : Fin n → Ω | ∀ i, S.ρ (v i) ≠ r.val} := by
    have h := MeasurableSet.iInter (fun i : Fin n =>
      (hI.preimage (measurable_pi_apply i)).compl)
    convert h using 1
    ext v
    simp
  have hroot := (ae_restrict_iff' hno).mp
    (P.ae_emptySat_rootless_rootLoad_nonpos hW hd hgap hN n)
  have hpoint := P.ae_original_vertices _
    (P.ae_common_sigma_cap p hpair hW hd hgap hN hA hAhalf hell hmargin) n
  filter_upwards [P.ae_emptySat_common_augmented_charge_le_one p hpair hW hd hgap hN n,
    ae_restrict_of_ae (P.tight_physical n), ae_restrict_of_ae hroot,
    ae_restrict_of_ae hpoint,
    ae_restrict_mem (S.measurableSet_emptySatCommonEvent r p n)]
    with v hcharge ht hr hp hU
  have hsumroot : (∑ i, S.rootChargeRow r (v i)) ≤ 0 :=
    hr (fun i hi => hU i (Or.inl (Or.inl hi)))
  have hsigma : 1 ≤ ∑ i : Fin n, -(S.rootChargeRow r (v i) + S.rootChargeRow p (v i)) := by
    rw [ht] at hcharge
    have hneg : (∑ i, -(S.rootChargeRow r (v i) + S.rootChargeRow p (v i))) =
        -(∑ i : Fin n, (S.rootChargeRow r (v i) + S.rootChargeRow p (v i))) :=
      by rw [Finset.sum_neg_distrib]
    linarith only [hcharge, hneg]
  exact common_column_count (fun i => S.rootChargeRow r (v i))
    (fun i => -(S.rootChargeRow r (v i) + S.rootChargeRow p (v i)))
    (by linarith [hell.1]) heta hthree hstep
    (fun i => by simpa only [neg_neg] using (hp i (hU i)).1)
    (fun i => (hp i (hU i)).2.2) hsumroot hsigma

private theorem negativeChargeMass_le_row (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    S.universalNegativeChargeMass r p ≤
      (2 * (c - m * d) - (1 - m) * S.originalAtomMass r) / 2 := by
  let B := S.universalNegativeRegion r p
  let U := S.universalPartnerCommonRegion r p
  let f := B.indicator (fun x => -S.rootChargeRow r x)
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hf : Integrable f μ :=
    (S.integrable_universalNegativeCharge r).indicator hB
  have hp : Integrable (p.val : Ω → ℝ) μ := (Lp.memLp p.val).integrable (by norm_num)
  have hcharge := (ae_restrict_iff' hB).mp
    (P.ae_universalNegative_partner_charge S r p hpair hW hd hgap hN hA hAhalf hell hmargin)
  have hnegative := (ae_restrict_iff' hB).mp
    (S.ae_universalNegativeCharge_mem_Ioo r p hW hd hgap hN)
  have hpoint : ∀ᵐ x ∂μ.restrict U, 2 * f x ≤ p.val x := by
    filter_upwards [ae_restrict_of_ae hcharge, ae_restrict_of_ae hnegative,
      ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row p hW hd hgap),
      S.ae_partner_row_pos_on_universalCommon r p]
      with x hq hn hr hpos
    by_cases hx : x ∈ B
    · change 1 - S.rootChargeRow p x =
        1 - p.val x - m * (if 0 < p.val x then 1 else 0) at hr
      rw [ite_eq_left hpos] at hr
      dsimp only [f]
      rw [indicator_of_mem hx]
      linarith only [hq hx, (hn hx).2, hr]
    · dsimp only [f]
      rw [indicator_of_notMem hx]
      linarith only [hpos]
  have hbound := integral_mono_ae (hf.const_mul 2).integrableOn hp.integrableOn hpoint
  rw [integral_const_mul, S.universal_partner_common_row_integral r p hpair hW] at hbound
  have hsupport : U.indicator f = f := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
    · have hnotB : x ∉ B := fun h => hx h.1
      rw [indicator_of_notMem hx]
      dsimp [f]
      rw [indicator_of_notMem hnotB]
  have hmass : (∫ x in U, f x ∂μ) = S.universalNegativeChargeMass r p := by
    rw [← integral_indicator hU, hsupport]
    exact integral_indicator hB
  rw [hmass] at hbound
  linarith only [hbound]


private theorem weighted_degree_stock (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (f : Ω → ℝ) (hfi : Integrable f μ) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      ((n : ℝ) - 1) * (∑ i, f (v i)) ∂P.laws n) =
      ∫ x, f x * (∫ y, adjacencyKernel W x y ∂μ) ∂μ := by
  have hs := hW.strict_gap_structure hd hgap
  let G : Set (Ω × Ω) := {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  have hG : MeasurableSet G :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  let K : Ω × Ω → ℝ := fun z => f z.2
  have hK : Integrable K (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hfi
  have hsum := P.emptySat_sum_integral_charge K hK
  have hcharge (n : ℕ) (v : Fin n → Ω) :
      PhysicalPrimal.charge K v = (((n : ℝ) - 1) * (∑ i, f (v i))) / 2 := by
    have h := PhysicalPrimal.charge_weighted_root (Set.univ : Set Ω) f v
    simp only [mem_univ, ite_true] at h
    have hc : (PhysicalPrimal.tupleCount (Set.univ : Set Ω) v : ℝ) = n := by
      simp [PhysicalPrimal.tupleCount]
    rw [hc] at h
    change 2 * PhysicalPrimal.charge K v = _ at h
    linarith only [h]
  simp_rw [hcharge, integral_div] at hsum
  rw [← Finset.sum_div] at hsum
  have hdemand : (∫ z, K z ∂PhysicalPrimal.graphDemand μ G) =
      ∫ x, f x * (∫ y, adjacencyKernel W x y ∂μ) ∂μ := by
    rw [PhysicalPrimal.graphDemand, ← integral_indicator hG]
    have heq : G.indicator K =ᵐ[μ.prod μ]
        (fun z => adjacencyKernel W z.1 z.2 * f z.2) := by
      filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support]
        with z hz
      dsimp only [G, K]
      simp only [Set.indicator, mem_ofPred_eq]
      change adjacencyKernel W z.1 z.2 = _ at hz
      rw [hz]
      split_ifs <;> simp_all
    rw [integral_congr_ae heq]
    have hsym : (fun z : Ω × Ω => adjacencyKernel W z.1 z.2 * f z.2) =ᵐ[μ.prod μ]
        (fun z => adjacencyKernel W z.2 z.1 * f z.2) := by
      filter_upwards [adjacencyKernel_symm W] with z hz
      rw [hz]
    rw [integral_congr_ae hsym]
    have hswap : (∫ z : Ω × Ω, adjacencyKernel W z.2 z.1 * f z.2 ∂μ.prod μ) =
        ∫ z : Ω × Ω, adjacencyKernel W z.1 z.2 * f z.1 ∂μ.prod μ := by
      simpa only [Prod.swap] using
        (integral_prod_swap (μ := μ) (ν := μ)
          (fun z : Ω × Ω => adjacencyKernel W z.1 z.2 * f z.1))
    rw [hswap]
    have hi : Integrable (fun z : Ω × Ω => adjacencyKernel W z.1 z.2 * f z.1)
        (μ.prod μ) := by
      have hfs : Integrable (fun z : Ω × Ω => f z.1) (μ.prod μ) := by
        simpa only [mul_one] using hfi.mul_prod (integrable_const (1 : ℝ))
      exact hfs.bdd_mul (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [] with x
    simp_rw [mul_comm (adjacencyKernel W _ _) (f x)]
    rw [integral_const_mul]
  rw [hdemand] at hsum
  linarith only [hsum]
private theorem ae_two_negativeLoad_zero (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ v ∂P.laws 2, S.emptySatNegativeLoad r 2 v = 0 := by
  have hsat := P.ae_original_pairs _
    (hpair.ae_charge_one_iff_between_heads hW hd hgap hell) 2
  have hrepr := P.ae_original_pairs _
    (PhysicalRepresentative.charge_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support) 2
  have hrP := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp
    (S.ae_rootChargeRow_on_constant_block r p hW hd hgap 1 hpair.2)
  have hhead : ∀ᵐ x ∂μ, (S.ρ x = r.val → S.rootChargeRow r x = 0) ∧
      (S.ρ x = p.val → S.rootChargeRow r x = 1) := by
    filter_upwards [S.rootChargeRow_zero_off_neighborhood r hW hd hgap, hrP]
      with x hr hp
    exact ⟨fun hx => hr (fun h => h.1 hx), hp⟩
  filter_upwards [hsat, hrepr, P.tight_physical 2, P.ae_original_vertices _ hhead 2]
    with v hsat hr ht hh
  have he : PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v =
      PhysicalRepresentative.charge W m (v 0) (v 1) := by
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
      Fin.sum_univ_succ, PhysicalRepresentative.charge_symm W m (v 1) (v 0)]
  have hone : chargeKernel W (v 0) (v 1) = 1 :=
    (hr 0 1 (by decide)).symm.trans (he.symm.trans ht)
  rcases (hsat 0 1 (by decide)).mp hone with h | h
  · simp [emptySatNegativeLoad, Fin.sum_univ_succ, (hh 0).1 h.1, (hh 1).2 h.2]
  · simp [emptySatNegativeLoad, Fin.sum_univ_succ, (hh 0).2 h.1, (hh 1).1 h.2]

private theorem negative_sum_ge_coordinate {n : ℕ} (beta : Fin n → ℝ)
    (hsum : (∑ i, beta i) ≤ 0) (j : Fin n) :
    beta j ≤ ∑ i, max (-beta i) 0 := by
  have hparts : (∑ i, max (beta i) 0) - (∑ i, max (-beta i) 0) = ∑ i, beta i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hb : 0 ≤ beta i
    · rw [max_eq_left hb, max_eq_right (neg_nonpos.mpr hb), sub_zero]
    · have hb' := le_of_not_ge hb
      rw [max_eq_right hb', max_eq_left (neg_nonneg.mpr hb')]
      ring
  have hterm : max (beta j) 0 ≤ ∑ i, max (beta i) 0 :=
    Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j)
  linarith only [hparts, hsum, hterm, le_max_left (beta j) 0]

private theorem ae_negative_stock (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (heta : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (hthree : -m < 3 * (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)))
    (hstep : -m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) < 1 / 2)
    (n : ℕ) :
    ∀ᵐ v ∂P.laws n,
      let F := S.emptySatNegativeLoad r n v
      (if v ∈ S.emptySatPartnerEvent r p n then 3 * F else 0) +
          (if v ∈ S.emptySatHoleEvent r p n then
            2 * (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) else 0) +
          (if v ∈ S.emptySatCommonEvent r p n then
            12 * (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) else 0) ≤
        ((n : ℝ) - 1) * F -
          3 * (PhysicalPrimal.tupleCount {x | S.ρ x = r.val} v : ℝ) * F +
          (PhysicalPrimal.tupleCount {x | S.ρ x = p.val} v : ℝ) * F := by
  let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = p.val}
  have hno (k : ℕ) : MeasurableSet {v : Fin k → Ω | ∀ i, S.ρ (v i) ≠ r.val} := by
    have h := MeasurableSet.iInter (fun i : Fin k =>
      ((S.hfibers r.val r.property).1.preimage (measurable_pi_apply i)).compl)
    convert h using 1
    ext v
    simp
  by_cases hn : 3 ≤ n
  · have hroot := (ae_restrict_iff' (hno n)).mp
      (P.ae_emptySat_rootless_rootLoad_nonpos hW hd hgap hN n)
    have hcommon := (ae_restrict_iff' (S.measurableSet_emptySatCommonEvent r p n)).mp
      (P.common_column_bounds p hpair hW hd hgap hN hA hAhalf hell hmargin
        heta hthree hstep n)
    have hthreshold := P.ae_original_vertices _
      ((ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
        (P.ae_universal_upperE2_hole_star_threshold S r p hpair hW hd hgap hN
          hA hAhalf hell hmargin)) n
    have hnegative : ∀ᵐ x ∂μ, S.rootChargeRow r x < 0 →
        x ∈ S.universalUpperE2BadRegion r p d c ∧ S.ρ x ≠ r.val := by
      filter_upwards [P.negativePart_eq_common_negative p hpair hW hd hgap hN
        hA hAhalf hell hmargin] with x hx hneg
      have hxB : x ∈ S.universalNegativeRegion r p := by
        by_contra hb
        rw [indicator_of_notMem hb] at hx
        have hp : 0 < max (-S.rootChargeRow r x) 0 := lt_of_lt_of_le (neg_pos.mpr hneg)
          (le_max_left _ _)
        linarith only [hx, hp]
      refine ⟨⟨?_, lt_trans hneg heta⟩, ?_⟩
      · exact fun h => hxB.1 (Or.inl h)
      · exact fun h => hxB.1 (Or.inl (Or.inl h))
    have hneg := P.ae_original_vertices _ hnegative n
    have hstock : ∀ᵐ v ∂P.laws n, n = 3 → ∀ i j : Fin n, i ≠ j →
        S.ρ (v i) = r.val → v j ∈ S.universalUpperE2BadRegion r p d c →
          ∃ k : Fin n, S.ρ (v k) = p.val := by
      by_cases he : n = 3
      · subst n
        filter_upwards [P.ae_universalUpperE2Bad_partner_stock S r p hpair hW hd hgap
          hN hA hAhalf hell hmargin] with v hv _ i j hij hi hj
        obtain ⟨k, _, _, hk⟩ := hv i j hij hi hj
        exact ⟨k, hk⟩
      · exact Filter.Eventually.of_forall (fun _ h => (he h).elim)
    filter_upwards [P.unique_root n, P.partner_unique_root p hW hd hgap n,
      hroot, hcommon, hthreshold, hneg, hstock]
      with v hI hJ hroot hcommon hthreshold hneg hstock
    dsimp only
    let F := S.emptySatNegativeLoad r n v
    have hF : 0 ≤ F := Finset.sum_nonneg (fun i _ => le_max_right _ _)
    have hcount (Q : Set Ω) (hq : ∀ i j, v i ∈ Q → v j ∈ Q → i = j) :
        PhysicalPrimal.tupleCount Q v = if ∃ i, v i ∈ Q then 1 else 0 := by
      split_ifs with he
      · obtain ⟨i, hi⟩ := he
        exact PhysicalPrimal.tupleCount_eq_one_of_unique Q v ⟨i, hi, fun j hj => hq j i hj hi⟩
      · apply Finset.sum_eq_zero
        intro i _
        have hi : v i ∉ Q := fun h => he ⟨i, h⟩
        simp only [ite_eq_right hi]
    have hcI := hcount I hI
    have hcJ := hcount J hJ
    by_cases hi : ∃ i, S.ρ (v i) = r.val
    · have hnp : v ∉ S.emptySatPartnerEvent r p n := fun h =>
        let ⟨i, hi⟩ := hi; h.1 i hi
      have hnh : v ∉ S.emptySatHoleEvent r p n := fun h =>
        let ⟨i, hi⟩ := hi; (h.1 i).1 hi
      have hnu : v ∉ S.emptySatCommonEvent r p n := fun h =>
        let ⟨i, hi⟩ := hi; h i (Or.inl (Or.inl hi))
      rw [ite_eq_right hnp, ite_eq_right hnh, ite_eq_right hnu]
      have hcI' : PhysicalPrimal.tupleCount I v = 1 := by
        simpa only [I, mem_ofPred_eq, hi, ite_true] using hcI
      rw [show {x | S.ρ x = r.val} = I from rfl, hcI']
      by_cases hfour : 4 ≤ n
      · have hnR : 3 ≤ (n : ℝ) - 1 := by exact_mod_cast (show 3 ≤ (n : ℤ) - 1 by omega)
        have hp := mul_nonneg (show 0 ≤ (n : ℝ) - 1 - 3 by linarith only [hnR]) hF
        have hq := mul_nonneg (show 0 ≤ (PhysicalPrimal.tupleCount J v : ℝ) by positivity) hF
        norm_num only [Nat.cast_one]
        dsimp only [F, J] at hp hq
        nlinarith only [hp, hq]
      · have hn3 : n = 3 := by omega
        have hnR : (n : ℝ) = 3 := by exact_mod_cast hn3
        rw [hnR]
        by_cases hFp : 0 < F
        · have hex : ∃ j : Fin n, 0 < max (-S.rootChargeRow r (v j)) 0 := by
            by_contra hnone
            push Not at hnone
            have hf0 : F ≤ 0 := Finset.sum_nonpos (fun i _ => hnone i)
            linarith only [hFp, hf0]
          obtain ⟨j, hj⟩ := hex
          have hjneg : S.rootChargeRow r (v j) < 0 := by
            exact neg_pos.mp ((lt_max_iff.mp hj).elim id (fun h => (lt_irrefl 0 h).elim))
          obtain ⟨i, hi⟩ := hi
          have hij : i ≠ j := fun he => (hneg j hjneg).2 (he ▸ hi)
          obtain ⟨k, hk⟩ := hstock hn3 i j hij hi (hneg j hjneg).1
          have hcJ' : PhysicalPrimal.tupleCount J v = 1 := by
            simpa only [show (∃ j, v j ∈ J) from ⟨k, hk⟩, ite_true] using hcJ
          rw [show {x | S.ρ x = p.val} = J from rfl, hcJ']
          norm_num only [Nat.cast_one]
          dsimp only [F] at hF
          nlinarith only [hF]
        · have hF0 : F = 0 := le_antisymm (le_of_not_gt hFp) hF
          change _ ≤ _ * F - 3 * _ * F + _ * F
          rw [hF0]
          norm_num
    · have hnoI : ∀ i, S.ρ (v i) ≠ r.val := fun i h => hi ⟨i, h⟩
      have hcI' : PhysicalPrimal.tupleCount I v = 0 := by
        simpa only [I, mem_ofPred_eq, hi, ite_false] using hcI
      rw [show {x | S.ρ x = r.val} = I from rfl, hcI']
      have hsum := hroot hnoI
      by_cases hj : ∃ j, S.ρ (v j) = p.val
      · have hnp : v ∈ S.emptySatPartnerEvent r p n := ⟨hnoI, hj⟩
        have hnh : v ∉ S.emptySatHoleEvent r p n := fun h =>
          let ⟨j, hj⟩ := hj; (h.1 j).2 hj
        have hnu : v ∉ S.emptySatCommonEvent r p n := fun h =>
          let ⟨j, hj⟩ := hj; h j (Or.inl (Or.inr hj))
        rw [ite_eq_left hnp, ite_eq_right hnh, ite_eq_right hnu]
        have hcJ' : PhysicalPrimal.tupleCount J v = 1 := by
          simpa only [J, mem_ofPred_eq, hj, ite_true] using hcJ
        rw [show {x | S.ρ x = p.val} = J from rfl, hcJ']
        have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
        have hp := mul_nonneg (sub_nonneg.mpr hnR) hF
        norm_num only [Nat.cast_zero, Nat.cast_one]
        dsimp only [F] at hp
        nlinarith only [hp]
      · have hnoJ : ∀ i, S.ρ (v i) ≠ p.val := fun i h => hj ⟨i, h⟩
        have hcJ' : PhysicalPrimal.tupleCount J v = 0 := by
          simpa only [J, mem_ofPred_eq, hj, ite_false] using hcJ
        rw [show {x | S.ρ x = p.val} = J from rfl, hcJ']
        have hnp : v ∉ S.emptySatPartnerEvent r p n := fun h => hj h.2
        rw [ite_eq_right hnp]
        by_cases hh : ∃ i, v i ∈ S.universalPartnerHoleRegion r p
        · have hH : v ∈ S.emptySatHoleEvent r p n := ⟨fun i => ⟨hnoI i, hnoJ i⟩, hh⟩
          have hnotU : v ∉ S.emptySatCommonEvent r p n := fun hu =>
            let ⟨i, hi⟩ := hh; hu i (Or.inr hi)
          rw [ite_eq_left hH, ite_eq_right hnotU]
          obtain ⟨i, hi⟩ := hh
          have hload : eta ≤ F := (hthreshold i hi).trans
            (negative_sum_ge_coordinate _ hsum i)
          have hnR : 2 ≤ (n : ℝ) - 1 := by exact_mod_cast (show 2 ≤ (n : ℤ) - 1 by omega)
          have hp := mul_nonneg (show 0 ≤ (n : ℝ) - 1 - 2 by linarith only [hnR]) hF
          norm_num only [Nat.cast_zero]
          dsimp only [F, eta] at hp hload
          nlinarith only [hp, hload]
        · have hU : v ∈ S.emptySatCommonEvent r p n := by
            intro i h
            rcases h with (hr | hp) | hH
            · exact hnoI i hr
            · exact hnoJ i hp
            · exact hh ⟨i, hH⟩
          have hnotH : v ∉ S.emptySatHoleEvent r p n := fun h => hh h.2
          rw [ite_eq_right hnotH, ite_eq_left hU]
          have hc := hcommon hU
          have hnR : 4 ≤ (n : ℝ) - 1 := by exact_mod_cast (show 4 ≤ (n : ℤ) - 1 by omega)
          have hp := mul_nonneg (show 0 ≤ (n : ℝ) - 1 - 4 by linarith only [hnR]) hF
          norm_num only [Nat.cast_zero]
          dsimp only [F] at hp
          nlinarith only [hp, hc.2]
  · have hn2 : n ≤ 2 := by omega
    interval_cases n
    · simp [P.feasible.1]
    · simp [P.feasible.2.1]
    · have hz := P.emptySat_noRootLaw_two_eq_zero p hpair hW hd hgap hell.2
      have hfalse : ∀ᵐ v ∂P.laws 2, ¬(∀ i, S.ρ (v i) ≠ r.val) := by
        have he : ∀ᵐ v ∂PhysicalRootReplacement.noRootLaw (P.laws 2) I, False := by
          rw [hz]
          simp
        have he' := (ae_restrict_iff' (hno 2)).mp he
        filter_upwards [he'] with v hv h
        exact hv h
      filter_upwards [P.ae_two_negativeLoad_zero p hpair hW hd hgap hell.2, hfalse]
        with v hv hn
      have hnp : v ∉ S.emptySatPartnerEvent r p 2 := fun h => hn h.1
      have hnh : v ∉ S.emptySatHoleEvent r p 2 := fun h => hn (fun i => (h.1 i).1)
      have hnu : v ∉ S.emptySatCommonEvent r p 2 := fun h =>
        hn (fun i hi => h i (Or.inl (Or.inl hi)))
      simp only [hv, ite_eq_right hnp, ite_eq_right hnh, ite_eq_right hnu,
        mul_zero, sub_zero, add_zero, le_refl]

private theorem eta_bounds {A delta gamma : ℝ} (hA : 0 < A) (hAupper : A < 3 / 8)
    (hdelta : 21 / 100 < delta) (hgamma : 23 / 100 * delta + 37 / 2500 < gamma) :
    let eta := 3 * gamma / A - delta
    29 / 100 < eta ∧ 1 - delta < 3 * eta ∧ (1 - delta) - eta < 1 / 2 := by
  dsimp only
  have hgammapos : 0 < gamma := by linarith only [hdelta, hgamma]
  have hprod := mul_lt_mul_of_pos_left hAupper (show 0 < 8 * gamma by positivity)
  have hratio : 8 * gamma < 3 * gamma / A := (lt_div_iff₀ hA).mpr (by
    nlinarith only [hprod])
  constructor
  · linarith only [hratio, hgamma, hdelta]
  · constructor <;> linarith only [hratio, hgamma, hdelta]

private theorem sigma_payment {n : ℕ} (beta sigma : Fin n → ℝ) (j : Fin n)
    {ell eta : ℝ} (heta : 0 < eta) (hbeta : beta j = 1) (hsigma : sigma j = 0)
    (hsigmaBox : ∀ i, i ≠ j → 0 ≤ sigma i ∧
      sigma i ≤ if eta ≤ beta i then max (ell - eta) 0 else 0)
    (hsum : (∑ i, beta i) ≤ 0) :
    eta * (∑ i, sigma i) ≤
      max (ell - eta) 0 * ((∑ i, max (-beta i) 0) - 1) := by
  classical
  let t := max (ell - eta) 0
  have ht : 0 ≤ t := le_max_right _ _
  have hpoint (i : Fin n) : eta * sigma i ≤
      t * (max (beta i) 0 - if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst i
      simp only [hbeta, hsigma, mul_zero, ite_true]
      norm_num
    · have hi := hsigmaBox i hij
      by_cases hb : eta ≤ beta i
      · have hs : sigma i ≤ t := by simpa only [hb, ite_true] using hi.2
        have hp := mul_le_mul_of_nonneg_left hs heta.le
        have hq := mul_le_mul_of_nonneg_left hb ht
        rw [ite_eq_right hij, sub_zero, max_eq_left (heta.le.trans hb)]
        nlinarith only [hp, hq]
      · have hs : sigma i = 0 := le_antisymm
          (by simpa only [hb, ite_false] using hi.2) hi.1
        rw [hs, mul_zero, ite_eq_right hij, sub_zero]
        exact mul_nonneg ht (le_max_right _ _)
  have hparts : (∑ i, max (beta i) 0) - (∑ i, max (-beta i) 0) = ∑ i, beta i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hb : 0 ≤ beta i
    · rw [max_eq_left hb, max_eq_right (neg_nonpos.mpr hb), sub_zero]
    · have hb' : beta i ≤ 0 := le_of_not_ge hb
      rw [max_eq_right hb', max_eq_left (neg_nonneg.mpr hb')]
      ring
  have hpositive : (∑ i, max (beta i) 0) ≤ ∑ i, max (-beta i) 0 := by
    linarith only [hparts, hsum]
  calc
    _ = ∑ i, eta * sigma i := Finset.mul_sum _ _ _
    _ ≤ ∑ i, t * (max (beta i) 0 - if i = j then 1 else 0) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = t * ((∑ i, max (beta i) 0) - 1) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_right hpositive 1) ht

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem load_integrable (S : SelectedHighLowStructure W m) (r : S.I)
    {n : ℕ} (rho : Measure (Fin n → Ω)) [IsFiniteMeasure rho] :
    Integrable (S.emptySatNegativeLoad r n) rho := by
  apply integrable_finsetSum
  intro i _
  apply Integrable.of_bound
    (((S.measurable_rootChargeRow r).comp (measurable_pi_apply i)).neg.max
      measurable_const).aestronglyMeasurable 3
  exact Eventually.of_forall (fun v => by
    dsimp only [Function.comp_apply, Pi.neg_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(S.rootChargeRow_mem_Icc r (v i)).1]) (by norm_num))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem sigma_integrable (S : SelectedHighLowStructure W m) (r p : S.I)
    {n : ℕ} (rho : Measure (Fin n → Ω)) [IsFiniteMeasure rho] :
    Integrable (S.emptySatSigmaLoad r p n) rho := by
  apply integrable_finsetSum
  intro i _
  have hm : Measurable (fun x => -(S.rootChargeRow r x + S.rootChargeRow p x)) :=
    ((S.measurable_rootChargeRow r).add (S.measurable_rootChargeRow p)).neg
  have hi : Integrable
      (fun v : Fin n → Ω => -(S.rootChargeRow r (v i) + S.rootChargeRow p (v i))) rho := by
    apply Integrable.of_bound (hm.comp (measurable_pi_apply i)).aestronglyMeasurable 6
    filter_upwards [] with v
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(S.rootChargeRow_mem_Icc r (v i)).1,
      (S.rootChargeRow_mem_Icc r (v i)).2, (S.rootChargeRow_mem_Icc p (v i)).1,
      (S.rootChargeRow_mem_Icc p (v i)).2]
  convert hi.indicator
    ((S.measurableSet_universalPartnerCommonRegion r p).preimage (measurable_pi_apply i)) using 1
  funext v
  simp only [Set.indicator, mem_preimage]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem count_load_integrable (S : SelectedHighLowStructure W m) (r : S.I)
    {n : ℕ} (rho : Measure (Fin n → Ω)) [IsFiniteMeasure rho]
    (I : Set Ω) (hI : MeasurableSet I) :
    Integrable
      (fun v => (PhysicalPrimal.tupleCount I v : ℝ) * S.emptySatNegativeLoad r n v) rho := by
  apply (load_integrable S r rho).bdd_mul (c := (n : ℝ))
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (PhysicalPrimal.measurable_tupleCount I hI)).aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  dsimp only [Function.comp_apply]
  exact_mod_cast PhysicalPrimal.tupleCount_le I v

omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
private theorem cost_eq_sum_of_cap (N : ℕ) (eta : PhysicalPrimal.Laws Ω)
    (hcap : ∀ n, N < n → eta n = 0) :
    PhysicalPrimal.cost eta = ∑ n ∈ Finset.range (N + 1), (eta n).real univ := by
  rw [PhysicalPrimal.cost, tsum_eq_sum (s := Finset.range (N + 1))]
  intro n hn
  have hn' : N < n := by simp only [Finset.mem_range] at hn; omega
  simp [hcap n hn']

private theorem ae_partner_sigma_payment (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (heta : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (n : ℕ) :
    ∀ᵐ v ∂P.emptySatPartnerLaws p n,
      (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) *
          S.emptySatSigmaLoad r p n v ≤
        max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))) 0 *
          (S.emptySatNegativeLoad r n v - 1) := by
  let U := S.universalPartnerCommonRegion r p
  let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hpoint := P.ae_original_vertices _
    (P.ae_common_sigma_cap p hpair hW hd hgap hN hA hAhalf hell hmargin) n
  have hrP := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp
    (S.ae_rootChargeRow_on_constant_block r p hW hd hgap 1 hpair.2)
  have hhead := P.ae_original_vertices _ hrP n
  have hrow := P.ae_original_pairs _ (S.ae_root_adjacency p hW hd hgap) n
  filter_upwards [P.ae_emptySat_partner_charge_load p hpair hW hd hgap hN n,
    ae_restrict_of_ae hpoint, ae_restrict_of_ae hhead, ae_restrict_of_ae hrow,
    ae_restrict_of_ae (P.feasible.2.2.1 n),
    ae_restrict_of_ae (P.partner_unique_root p hW hd hgap n),
    ae_restrict_mem (S.measurableSet_emptySatPartnerEvent r p n)]
    with v hload hp hh hr hc hu hv
  obtain ⟨j, hj⟩ := hv.2
  have hcommon (i : Fin n) (hij : i ≠ j) : v i ∈ U := by
    have hpi : S.ρ (v i) ≠ p.val := fun hi => hij (hu i j hi hj)
    have hn : v i ∈ S.rootNeighborhood p := (hr j i hij.symm hj).mp (hc j i hij.symm)
    intro hout
    rcases hout with (hI | hP) | hH
    · exact hv.1 i hI
    · exact hpi hP
    · exact hH (Or.inr hn)
  let sigma : Fin n → ℝ := fun i => U.indicator
    (fun x => -(S.rootChargeRow r x + S.rootChargeRow p x)) (v i)
  have hsigma : sigma j = 0 := by
    dsimp only [sigma]
    have hnot : v j ∉ U := fun h => h (Or.inl (Or.inr hj))
    exact indicator_of_notMem hnot _
  have hbox (i : Fin n) (hij : i ≠ j) : 0 ≤ sigma i ∧
      sigma i ≤ if eta ≤ S.rootChargeRow r (v i) then max (-m - eta) 0 else 0 := by
    dsimp only [sigma]
    rw [indicator_of_mem (hcommon i hij)]
    exact (hp i (hcommon i hij)).2
  exact sigma_payment (fun i => S.rootChargeRow r (v i)) sigma j heta (hh j hj)
    hsigma hbox hload.1

private theorem partner_sigma_payment (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (heta : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) :
    let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
    eta * P.emptySatPartnerSigmaLoad p ≤
      max (-m - eta) 0 * (P.emptySatPartnerNegativeLoad p - P.emptySatPartnerCost p) := by
  let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  let t := max (-m - eta) 0
  have hpoint (n : ℕ) :
      eta * (∫ v, S.emptySatSigmaLoad r p n v ∂P.emptySatPartnerLaws p n) ≤
        t * ((∫ v, S.emptySatNegativeLoad r n v ∂P.emptySatPartnerLaws p n) -
          (P.emptySatPartnerLaws p n).real univ) := by
    have hsig := sigma_integrable S r p (P.emptySatPartnerLaws p n)
    have hneg := load_integrable S r (P.emptySatPartnerLaws p n)
    have hb := integral_mono_ae (hsig.const_mul eta)
      ((hneg.sub (integrable_const 1)).const_mul t)
      (P.ae_partner_sigma_payment p hpair hW hd hgap hN hA hAhalf hell hmargin heta n)
    change (∫ v, eta * S.emptySatSigmaLoad r p n v ∂P.emptySatPartnerLaws p n) ≤
      ∫ v, t * (S.emptySatNegativeLoad r n v - 1) ∂P.emptySatPartnerLaws p n at hb
    rw [integral_const_mul, integral_const_mul, integral_sub hneg (integrable_const 1)] at hb
    simpa only [integral_const, smul_eq_mul, mul_one] using hb
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (P.orderCap + 1)) => hpoint n)
  have hcost : P.emptySatPartnerCost p =
      ∑ n ∈ Finset.range (P.orderCap + 1), (P.emptySatPartnerLaws p n).real univ := by
    apply cost_eq_sum_of_cap
    intro n hn
    simp [emptySatPartnerLaws, P.capped n (Or.inr hn)]
  dsimp only [emptySatPartnerSigmaLoad, emptySatPartnerNegativeLoad]
  rw [hcost]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  exact hsum

private theorem negative_inventory (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (heta : 0 < 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m))
    (hthree : -m < 3 * (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)))
    (hstep : -m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)) < 1 / 2) :
    let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
    3 * P.emptySatPartnerNegativeLoad p + 2 * eta * P.emptySatHoleCost p +
        12 * eta * P.emptySatCommonCost p ≤ S.emptySatNegativeDegreeLoad r p := by
  let eta := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = p.val}
  let B := S.universalNegativeRegion r p
  let f := B.indicator (fun x => -S.rootChargeRow r x)
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let N := S.universalNegativeChargeMass r p
  let g : Ω → ℝ := fun x => ∫ y, adjacencyKernel W x y ∂μ
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hJ : MeasurableSet J := (S.hfibers p.val p.property).1
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hf : Measurable f := (S.measurable_rootChargeRow r).neg.indicator hB
  have hfi : Integrable f μ := (S.integrable_universalNegativeCharge r).indicator hB
  have hfN : (∫ x, f x ∂μ) = N := integral_indicator hB
  have hfzeroI (x : Ω) (hx : x ∈ I) : f x = 0 := by
    have hnot : x ∉ B := fun h => h.1 (Or.inl (Or.inl hx))
    exact indicator_of_notMem hnot _
  have hfzeroJ (x : Ω) (hx : x ∈ J) : f x = 0 := by
    have hnot : x ∉ B := fun h => h.1 (Or.inl (Or.inr hx))
    exact indicator_of_notMem hnot _
  have hfsupportI (x : Ω) (hx : x ∉ {x | S.ρ x ≠ r.val}) : f x = 0 :=
    hfzeroI x (Classical.not_not.mp hx)
  have hfsupportJ (x : Ω) (hx : x ∉ S.rootNeighborhood p) : f x = 0 := by
    have hnot : x ∉ B := fun h => hx (S.common_region_mem_rootNeighborhood r p h.1)
    exact indicator_of_notMem hnot _
  have hload (n : ℕ) : ∀ᵐ v ∂P.laws n,
      S.emptySatNegativeLoad r n v = ∑ i, f (v i) := by
    filter_upwards [P.ae_original_vertices _
      (P.negativePart_eq_common_negative p hpair hW hd hgap hN hA hAhalf hell hmargin) n]
      with v hv
    exact Finset.sum_congr rfl (fun i _ => hv i)
  have hRI : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PhysicalPrimal.tupleCount I v : ℝ) * S.emptySatNegativeLoad r n v ∂P.laws n) = A * N := by
    have h := P.weighted_root_stock I {x | S.ρ x ≠ r.val} hI hI.compl f hf hfi hfzeroI
      hfsupportI (μ I) P.leaves
    rw [hfN] at h
    convert h using 1
    · apply Finset.sum_congr rfl
      intro n _
      exact integral_congr_ae ((hload n).mono (fun v hv => by dsimp only; rw [hv]))
    · rfl
  have hRJ : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PhysicalPrimal.tupleCount J v : ℝ) * S.emptySatNegativeLoad r n v ∂P.laws n) = b * N := by
    have h := P.weighted_root_stock J (S.rootNeighborhood p) hJ
      (S.measurableSet_rootNeighborhood p) f hf hfi hfzeroJ hfsupportJ (μ J)
      (P.partner_rootLeaves p hW hd hgap)
    rw [hfN] at h
    convert h using 1
    · apply Finset.sum_congr rfl
      intro n _
      exact integral_congr_ae ((hload n).mono (fun v hv => by dsimp only; rw [hv]))
    · rfl
  have hdegree : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      ((n : ℝ) - 1) * S.emptySatNegativeLoad r n v ∂P.laws n) = ∫ x, f x * g x ∂μ := by
    have h := P.weighted_degree_stock hW hd hgap f hfi
    convert h using 1
    apply Finset.sum_congr rfl
    intro n _
    exact integral_congr_ae ((hload n).mono (fun v hv => by dsimp only; rw [hv]))
  have hfg : Integrable (fun x => f x * g x) μ := by
    have hfs : Integrable (fun z : Ω × Ω => f z.1) (μ.prod μ) := by
      simpa only [mul_one] using hfi.mul_prod (integrable_const (1 : ℝ))
    have hp := hfs.mul_bdd (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
    have hi := hp.integral_prod_left
    convert hi using 1
    funext x
    exact (integral_const_mul (f x) (fun y => adjacencyKernel W x y)).symm
  have hresource : (∫ x, f x * g x ∂μ) - 3 * (A * N) + b * N =
      S.emptySatNegativeDegreeLoad r p := by
    have hfunc : B.indicator (fun x => -S.rootChargeRow r x * (g x - 3 * A + b)) =
        (fun x => f x * g x - (3 * A) * f x + b * f x) := by
      funext x
      by_cases hx : x ∈ B
      · simp only [f, indicator_of_mem hx]
        ring
      · simp only [f, indicator_of_notMem hx, zero_mul, mul_zero, sub_zero, add_zero]
    calc
      _ = ((∫ x, f x * g x ∂μ) - ∫ x, (3 * A) * f x ∂μ) +
          ∫ x, b * f x ∂μ := by rw [integral_const_mul, integral_const_mul, hfN]; ring
      _ = ∫ x, (f x * g x - (3 * A) * f x) + b * f x ∂μ := by
        have he := integral_add (hfg.sub (hfi.const_mul (3 * A))) (hfi.const_mul b)
        have hs := integral_sub hfg (hfi.const_mul (3 * A))
        simp only [Pi.sub_apply] at he hs
        rw [he, hs]
      _ = S.emptySatNegativeDegreeLoad r p := by
        change _ = ∫ x in B, -S.rootChargeRow r x * (g x - 3 * A + b) ∂μ
        rw [← integral_indicator hB]
        exact integral_congr_ae (Eventually.of_forall (fun x => (congrFun hfunc x).symm))
  have hpoint (n : ℕ) :
      3 * (∫ v, S.emptySatNegativeLoad r n v ∂P.emptySatPartnerLaws p n) +
          2 * eta * (P.emptySatHoleLaws p n).real univ +
          12 * eta * (P.emptySatCommonLaws p n).real univ ≤
        (∫ v, ((n : ℝ) - 1) * S.emptySatNegativeLoad r n v ∂P.laws n) -
          3 * (∫ v, (PhysicalPrimal.tupleCount I v : ℝ) *
            S.emptySatNegativeLoad r n v ∂P.laws n) +
          (∫ v, (PhysicalPrimal.tupleCount J v : ℝ) *
            S.emptySatNegativeLoad r n v ∂P.laws n) := by
    have : IsFiniteMeasure (P.laws n) := P.finite n
    have hi := load_integrable S r (P.laws n)
    have hPI := (hi.const_mul 3).indicator (S.measurableSet_emptySatPartnerEvent r p n)
    have hHI := (integrable_const (μ := P.laws n) (2 * eta)).indicator
      (S.measurableSet_emptySatHoleEvent r p n)
    have hUI := (integrable_const (μ := P.laws n) (12 * eta)).indicator
      (S.measurableSet_emptySatCommonEvent r p n)
    have hDI := hi.const_mul ((n : ℝ) - 1)
    have hII := (count_load_integrable S r (P.laws n) I hI).const_mul 3
    have hJI := count_load_integrable S r (P.laws n) J hJ
    have hb := integral_mono_ae ((hPI.add hHI).add hUI) ((hDI.sub hII).add hJI)
      ((P.ae_negative_stock p hpair hW hd hgap hN hA hAhalf hell hmargin
        heta hthree hstep n).mono (fun v hv => by
          convert hv using 1 <;> simp only [Set.indicator, Pi.add_apply, Pi.sub_apply] <;> ring))
    have he1 := integral_add (hPI.add hHI) hUI
    have he2 := integral_add hPI hHI
    have he3 := integral_add (hDI.sub hII) hJI
    have he4 := integral_sub hDI hII
    simp only [Pi.add_apply, Pi.sub_apply] at hb he1 he2 he3 he4
    rw [he1, he2, he3, he4,
      integral_indicator (S.measurableSet_emptySatPartnerEvent r p n),
      integral_indicator (S.measurableSet_emptySatHoleEvent r p n),
      integral_indicator (S.measurableSet_emptySatCommonEvent r p n),
      integral_const_mul, integral_const_mul] at hb
    simpa only [integral_const_mul, integral_const, smul_eq_mul, mul_one,
      emptySatPartnerLaws, emptySatHoleLaws, emptySatCommonLaws,
      mul_assoc, mul_comm, mul_left_comm] using hb
  have hcostH : P.emptySatHoleCost p =
      ∑ n ∈ Finset.range (P.orderCap + 1), (P.emptySatHoleLaws p n).real univ := by
    apply cost_eq_sum_of_cap
    intro n hn
    simp [emptySatHoleLaws, P.capped n (Or.inr hn)]
  have hcostU : P.emptySatCommonCost p =
      ∑ n ∈ Finset.range (P.orderCap + 1), (P.emptySatCommonLaws p n).real univ := by
    apply cost_eq_sum_of_cap
    intro n hn
    simp [emptySatCommonLaws, P.capped n (Or.inr hn)]
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (P.orderCap + 1)) => hpoint n)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hRI, hRJ, hdegree, hresource] at hsum
  change 3 * P.emptySatPartnerNegativeLoad p + 2 * eta *
    (∑ n ∈ Finset.range (P.orderCap + 1), (P.emptySatHoleLaws p n).real univ) +
    12 * eta *
      (∑ n ∈ Finset.range (P.orderCap + 1), (P.emptySatCommonLaws p n).real univ) ≤ _ at hsum
  rw [← hcostH, ← hcostU] at hsum
  exact hsum

private theorem negative_resource_bounds (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    0 ≤ S.emptySatNegativeDegreeLoad r p ∧
      S.emptySatNegativeDegreeLoad r p ≤
        (1 - 3 * S.originalAtomMass r + S.originalAtomMass p) *
          S.universalNegativeChargeMass r p := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let B := S.universalNegativeRegion r p
  let g : Ω → ℝ := fun x => ∫ y, adjacencyKernel W x y ∂μ
  have hB : MeasurableSet B := S.measurableSet_universalNegativeRegion r p
  have hgI : Integrable g μ :=
    (Integrable.of_bound (adjacencyKernel_measurable W) 1
      (adjacencyKernel_bound W)).integral_prod_left
  have hg : ∀ᵐ x ∂μ, g x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [PhysicalRepresentative.ae_graphDegree_eq_original hW hd hgap] with x hx
    dsimp only [g]
    rw [← hx]
    constructor
    · exact ENNReal.toReal_nonneg
    · change μ.real {y | PhysicalRepresentative.adjacency W m x y = true} ≤ 1
      exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hgbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := hg.mono (fun _ hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2)
  have hf := S.integrable_universalNegativeCharge r
  have hprod := hf.mul_bdd hgI.aestronglyMeasurable hgbound
  have hLI : Integrable (fun x => -S.rootChargeRow r x * (g x - 3 * A + b)) μ := by
    convert (hprod.sub (hf.const_mul (3 * A))).add (hf.const_mul b) using 1
    funext x
    dsimp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]
    ring
  have hsub := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (by linarith only [hA]) hmargin (by linarith only [hell.2])
  have hdegree := (ae_restrict_iff' (S.measurableSet_universalUpperE2BadRegion r p d c)).mp
    (P.ae_universalUpperE2Bad_originalDegree_ge S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hpoint : ∀ᵐ x ∂μ.restrict B,
      0 ≤ -S.rootChargeRow r x * (g x - 3 * A + b) ∧
        -S.rootChargeRow r x * (g x - 3 * A + b) ≤
          (1 - 3 * A + b) * (-S.rootChargeRow r x) := by
    filter_upwards [ae_restrict_of_ae hg, ae_restrict_of_ae hdegree,
      ae_restrict_mem hB] with x hg hd hx
    have hneg : 0 ≤ -S.rootChargeRow r x := le_of_lt (neg_pos.mpr hx.2)
    have hlow : 0 ≤ g x - 3 * A + b := by
      have h := hd (hsub hx)
      dsimp only [g, A, b]
      linarith only [h]
    refine ⟨mul_nonneg hneg hlow, ?_⟩
    have hupper : g x - 3 * A + b ≤ 1 - 3 * A + b := by linarith only [hg.2]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hupper hneg
  refine ⟨integral_nonneg_of_ae (hpoint.mono (fun _ h => h.1)), ?_⟩
  have hbound := integral_mono_ae hLI.integrableOn
    ((hf.const_mul (1 - 3 * A + b)).integrableOn) (hpoint.mono (fun _ h => h.2))
  rw [integral_const_mul] at hbound
  exact hbound

end Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The same original rootless columns use one negative inventory, including
its genuine degree cap and the partner-column sigma payment. -/
theorem ReverseRecovery.empty_sat_corner_rootless_quota
    {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery) (r p : S.I)
    (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    {c : ℝ} (P : S.UniversalPhysicalPrimal r c) {d : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) (hstrip : 21 / 100 < 1 + m) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let gamma := 2 * (c - m * d) + m
    let eta := 3 * gamma / A - (1 + m)
    let N := S.universalNegativeChargeMass r p
    let Bc := 1 - 3 * A + b
    let Nmax := (2 * (c - m * d) - (1 - m) * A) / 2
    let Uload := S.emptySatNegativeDegreeLoad r p
    0 < N ∧ 0 ≤ Bc ∧ 0 ≤ Uload ∧ Uload ≤ Bc * Nmax ∧
      (3 * P.emptySatPartnerNegativeLoad p + 2 * eta * P.emptySatHoleCost p +
        12 * eta * P.emptySatCommonCost p ≤ Uload) ∧
      eta * P.emptySatPartnerSigmaLoad p ≤
        max (-m - eta) 0 * (P.emptySatPartnerNegativeLoad p - P.emptySatPartnerCost p) := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let gamma := 2 * (c - m * d) + m
  let eta := 3 * gamma / A - (1 + m)
  let N := S.universalNegativeChargeMass r p
  let Bc := 1 - 3 * A + b
  let Nmax := (2 * (c - m * d) - (1 - m) * A) / 2
  let Uload := S.emptySatNegativeDegreeLoad r p
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨hAlow, hAupper, hmargin, hnegative, _⟩ :=
    R.empty_sat_corner_bad_region r p hr hpair P hW hd hgap he heq hglobal hnull hstrip
  have hA : 1 / 3 < A := by linarith only [hAlow]
  have hApos : 0 < A := by linarith only [hAlow]
  have hAhalf : A ≤ 1 / 2 := by linarith only [hAupper]
  obtain ⟨hclosed, _, _, hfloor⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hell : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hclosed.1, hclosed.2]
  have hcorrelated : (23 / 100 : ℝ) * (1 + m) + 37 / 2500 < gamma := by
    linarith only [hfloor, hclosed.2]
  obtain ⟨heta, hthree, hstep⟩ :=
    UniversalPhysicalPrimal.eta_bounds hApos hAupper hstrip hcorrelated
  have hNpos : 0 < N := S.universalNegativeChargeMass_pos r p hW hd hgap hN hnegative
  have hNmax : N ≤ Nmax := P.negativeChargeMass_le_row p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  obtain ⟨hUpos, hUcap⟩ := P.negative_resource_bounds p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hBc : 0 ≤ Bc := by
    by_contra h
    have hp := mul_neg_of_neg_of_pos (lt_of_not_ge h) hNpos
    linarith only [hUpos, hUcap, hp]
  have hupper : Uload ≤ Bc * Nmax :=
    hUcap.trans (mul_le_mul_of_nonneg_left hNmax hBc)
  have hquota := P.negative_inventory p hpair hW hd hgap hN hA hAhalf hell hmargin
    (by linarith only [heta]) (by linarith only [hthree]) (by linarith only [hstep])
  have hpayment := P.partner_sigma_payment p hpair hW hd hgap hN hA hAhalf hell hmargin
    (by linarith only [heta])
  exact ⟨hNpos, hBc, hUpos, hupper, hquota, hpayment⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

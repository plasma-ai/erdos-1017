module

public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerQuota
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerContext
public import Erdos1017.Exclusions.Common.Physical.PhysicalCountMeasure

/-!
# Parent counts of the empty-source saturated corner

This module partitions the tuple law into two rooted and three rootless classes
with the matching cost partition, transfers source containment to every parent
coordinate, and bounds the rooted no-partner class below by `K = Aj - GJJ/2`
through the first and factorial source moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The actual old parent contains both original heads. -/
def emptySatRootPartnerEvent (S : SelectedHighLowStructure W m) (r p : S.I) (n : ℕ) :
    Set (Fin n → Ω) :=
  {v | (∃ i, S.ρ (v i) = r.val) ∧ ∃ i, S.ρ (v i) = p.val}

/-- The actual old parent contains the universal root and avoids its partner. -/
def emptySatRootNoPartnerEvent (S : SelectedHighLowStructure W m) (r p : S.I) (n : ℕ) :
    Set (Fin n → Ω) :=
  {v | (∃ i, S.ρ (v i) = r.val) ∧ ∀ i, S.ρ (v i) ≠ p.val}

theorem measurableSet_emptySatRootPartnerEvent (S : SelectedHighLowStructure W m)
    (r p : S.I) (n : ℕ) : MeasurableSet (S.emptySatRootPartnerEvent r p n) := by
  have hr := MeasurableSet.iUnion (fun i : Fin n =>
    (S.hfibers r.val r.property).1.preimage (measurable_pi_apply i))
  have hp := MeasurableSet.iUnion (fun i : Fin n =>
    (S.hfibers p.val p.property).1.preimage (measurable_pi_apply i))
  convert hr.inter hp using 1
  ext v
  simp [emptySatRootPartnerEvent]

theorem measurableSet_emptySatRootNoPartnerEvent (S : SelectedHighLowStructure W m)
    (r p : S.I) (n : ℕ) : MeasurableSet (S.emptySatRootNoPartnerEvent r p n) := by
  have hr := MeasurableSet.iUnion (fun i : Fin n =>
    (S.hfibers r.val r.property).1.preimage (measurable_pi_apply i))
  have hp := MeasurableSet.iInter (fun i : Fin n =>
    ((S.hfibers p.val p.property).1.preimage (measurable_pi_apply i)).compl)
  convert hr.inter hp using 1
  ext v
  simp [emptySatRootNoPartnerEvent]

namespace UniversalPhysicalPrimal

variable {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- Restrict the same attained laws to the columns containing both heads. -/
def emptySatRootPartnerLaws (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    PhysicalPrimal.Laws Ω :=
  fun n => (P.laws n).restrict (S.emptySatRootPartnerEvent r p n)

/-- Restrict the same attained laws to root columns without the partner. -/
def emptySatRootNoPartnerLaws (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    PhysicalPrimal.Laws Ω :=
  fun n => (P.laws n).restrict (S.emptySatRootNoPartnerEvent r p n)

instance (P : S.UniversalPhysicalPrimal r c) (p : S.I) (n : ℕ) :
    IsFiniteMeasure (P.emptySatRootPartnerLaws p n) := by
  have := P.finite n
  dsimp [emptySatRootPartnerLaws]
  infer_instance

instance (P : S.UniversalPhysicalPrimal r c) (p : S.I) (n : ℕ) :
    IsFiniteMeasure (P.emptySatRootNoPartnerLaws p n) := by
  have := P.finite n
  dsimp [emptySatRootNoPartnerLaws]
  infer_instance

/-- Original I-P column cost, without a probability normalization. -/
def emptySatRootPartnerCost (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  PhysicalPrimal.cost (P.emptySatRootPartnerLaws p)

/-- Original I-without-P column cost, retaining its old joint law. -/
def emptySatRootNoPartnerCost (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  PhysicalPrimal.cost (P.emptySatRootNoPartnerLaws p)

/-- The original common-region first occupation in those same I-P columns. -/
def emptySatRootPartnerCommonOccupation (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    Measure Ω :=
  (PhysicalPrimal.firstOccupation (P.emptySatRootPartnerLaws p)).restrict
    (S.universalPartnerCommonRegion r p)

theorem emptySatRootPartnerLaws_capped (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (n : ℕ) (hn : n < 2 ∨ P.orderCap < n) : P.emptySatRootPartnerLaws p n = 0 := by
  simp [emptySatRootPartnerLaws, P.capped n hn]

theorem emptySatRootNoPartnerLaws_capped (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (n : ℕ) (hn : n < 2 ∨ P.orderCap < n) : P.emptySatRootNoPartnerLaws p n = 0 := by
  simp [emptySatRootNoPartnerLaws, P.capped n hn]

private theorem firstOccupation_mono (η ν : PhysicalPrimal.Laws Ω)
    (h : ∀ n, η n ≤ ν n) : PhysicalPrimal.firstOccupation η ≤
      PhysicalPrimal.firstOccupation ν := by
  intro B
  simp only [PhysicalPrimal.firstOccupation, Measure.sum_apply_of_countable]
  apply ENNReal.tsum_le_tsum
  intro n
  simp only [PhysicalPrimal.orderFirstOccupation, Measure.finsetSum_apply]
  apply Finset.sum_le_sum
  intro i _
  exact Measure.map_mono (h n) (measurable_pi_apply i) B

theorem emptySatRootPartnerCommonOccupation_le (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) : P.emptySatRootPartnerCommonOccupation p ≤ μ := by
  apply le_trans Measure.restrict_le_self
  apply le_trans (firstOccupation_mono _ P.laws (fun _ => Measure.restrict_le_self))
  exact (PhysicalPrimal.firstOccupation_le_fst_of_balance P.laws _ P.feasible.1
    P.feasible.2.1 P.feasible.2.2.2).trans (PhysicalPrimal.graphDemand_fst_le μ _)

instance (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    IsFiniteMeasure (P.emptySatRootPartnerCommonOccupation p) :=
  isFiniteMeasure_of_le μ (P.emptySatRootPartnerCommonOccupation_le p)

private theorem cost_eq_sum_of_cap (N : ℕ) (η : PhysicalPrimal.Laws Ω)
    (hcap : ∀ n, N < n → η n = 0) :
    PhysicalPrimal.cost η = ∑ n ∈ Finset.range (N + 1), (η n).real univ := by
  rw [PhysicalPrimal.cost, tsum_eq_sum (s := Finset.range (N + 1))]
  intro n hn
  have hn' : N < n := by simp only [Finset.mem_range] at hn; omega
  simp [hcap n hn']

omit [MeasurableSpace Ω] in
private theorem tupleCount_zero {n : ℕ} (I : Set Ω) (v : Fin n → Ω)
    (h : ∀ i, v i ∉ I) : PhysicalPrimal.tupleCount I v = 0 := by
  simp [PhysicalPrimal.tupleCount, h]

omit [MeasurableSpace Ω] in
private theorem root_counts_indicator {n : ℕ} (I B : Set Ω) (v : Fin n → Ω)
    (hI : ∀ i j, v i ∈ I → v j ∈ I → i = j)
    (hB : ∀ i j, v i ∈ B → v j ∈ B → i = j) :
    (PhysicalPrimal.tupleCount I v : ℝ) * PhysicalPrimal.tupleCount B v =
      {v : Fin n → Ω | (∃ i, v i ∈ I) ∧ ∃ i, v i ∈ B}.indicator
        (fun _ => (1 : ℝ)) v := by
  by_cases hi : ∃ i, v i ∈ I
  · have hi1 : PhysicalPrimal.tupleCount I v = 1 :=
      PhysicalPrimal.tupleCount_eq_one_of_unique I v
        (by obtain ⟨i, hi⟩ := hi; exact ⟨i, hi, fun j hj => hI j i hj hi⟩)
    by_cases hb : ∃ i, v i ∈ B
    · have hb1 : PhysicalPrimal.tupleCount B v = 1 :=
        PhysicalPrimal.tupleCount_eq_one_of_unique B v
          (by obtain ⟨i, hi⟩ := hb; exact ⟨i, hi, fun j hj => hB j i hj hi⟩)
      simp [hi1, hb1, hi, hb]
    · have hb0 := tupleCount_zero B v (by simpa only [not_exists] using hb)
      simp [hb0, hb]
  · have hi0 := tupleCount_zero I v (by simpa only [not_exists] using hi)
    simp [hi0, hi]

end UniversalPhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- Both independent heads occur at most once, so their exact pair demand
is precisely the original I-P parent mass. -/
theorem emptySatRootPartnerCost_eq (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpr : p ≠ r) {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    P.emptySatRootPartnerCost p = S.originalAtomMass r * S.originalAtomMass p := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let I := {x | S.ρ x = r.val}
  let B := {x | S.ρ x = p.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hB : MeasurableSet B := (S.hfibers p.val p.property).1
  have hdis : Disjoint I B := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hpr (Subtype.ext (hy.symm.trans hx))
  have hcap : ∀ n, P.orderCap < n → P.laws n = 0 := fun n hn => P.capped n (Or.inr hn)
  have hcross := PhysicalPrimal.countMeasure_cross_moment P.orderCap P.laws I B hI hB
    hdis hcap _ P.feasible.2.2.2
  have hdemand : (PhysicalPrimal.graphDemand μ
      {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true}).real (I ×ˢ B) =
      S.originalAtomMass r * S.originalAtomMass p := by
    have h := congrArg (fun ν : Measure Ω => ν B) P.leaves
    rw [PhysicalPrimal.rootLeaves_apply_of_balance P.laws _ P.feasible.2.2.2 I B hI hB,
      Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul] at h
    have hsub : B ⊆ {x | S.ρ x ≠ r.val} := by
      intro x hx hr
      exact hpr (Subtype.ext (hx.symm.trans hr))
    simpa only [measureReal_def, originalAtomMass, B,
      inter_eq_left.mpr hsub, ENNReal.toReal_mul] using congrArg ENNReal.toReal h
  rw [PhysicalPrimal.integral_countMeasure P.orderCap P.laws I B hI hB] at hcross
  rw [← hdemand, ← hcross, emptySatRootPartnerCost, cost_eq_sum_of_cap P.orderCap _
    (fun n hn => P.emptySatRootPartnerLaws_capped p n (Or.inr hn))]
  apply Finset.sum_congr rfl
  intro n _
  have heq : ∀ᵐ v ∂P.laws n,
      (PhysicalPrimal.tupleCount I v : ℝ) * PhysicalPrimal.tupleCount B v =
        (S.emptySatRootPartnerEvent r p n).indicator (fun _ => (1 : ℝ)) v := by
    filter_upwards [P.unique_root n, P.partner_unique_root p hW hd hgap n] with v hr hp
    exact root_counts_indicator I B v hr hp
  rw [integral_congr_ae heq, integral_indicator (S.measurableSet_emptySatRootPartnerEvent r p n)]
  simp [emptySatRootPartnerLaws]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem restrict_split {V : Type*} [MeasurableSpace V]
    (ρ : Measure V) (A B : Set V) (hB : MeasurableSet B) :
    ρ.restrict A = ρ.restrict (A ∩ B) + ρ.restrict (A ∩ Bᶜ) := by
  simpa only [Measure.restrict_restrict hB, Measure.restrict_restrict hB.compl,
    inter_comm] using (Measure.restrict_add_restrict_compl (μ := ρ.restrict A) hB).symm

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- These five restrictions partition the original tuple law itself,
before any moment, optimality or conditional sampling argument. -/
theorem emptySat_laws_partition (P : S.UniversalPhysicalPrimal r c) (p : S.I) (n : ℕ) :
    P.emptySatRootPartnerLaws p n + P.emptySatRootNoPartnerLaws p n +
      P.emptySatPartnerLaws p n + P.emptySatHoleLaws p n + P.emptySatCommonLaws p n =
        P.laws n := by
  let A : Set (Fin n → Ω) := {v | ∃ i, S.ρ (v i) = r.val}
  let B : Set (Fin n → Ω) := {v | ∃ i, S.ρ (v i) = p.val}
  let C : Set (Fin n → Ω) := {v | ∃ i, v i ∈ S.universalPartnerHoleRegion r p}
  have hA : MeasurableSet A := by
    convert MeasurableSet.iUnion (fun i : Fin n =>
      (S.hfibers r.val r.property).1.preimage (measurable_pi_apply i)) using 1
    ext v
    simp [A]
  have hB : MeasurableSet B := by
    convert MeasurableSet.iUnion (fun i : Fin n =>
      (S.hfibers p.val p.property).1.preimage (measurable_pi_apply i)) using 1
    ext v
    simp [B]
  have hC : MeasurableSet C := by
    convert MeasurableSet.iUnion (fun i : Fin n =>
      (S.measurableSet_universalPartnerHoleRegion r p).preimage (measurable_pi_apply i)) using 1
    ext v
    simp [C]
  have hIP : S.emptySatRootPartnerEvent r p n = A ∩ B := rfl
  have hI : S.emptySatRootNoPartnerEvent r p n = A ∩ Bᶜ := by
    ext v
    simp [A, B, emptySatRootNoPartnerEvent]
  have hP : S.emptySatPartnerEvent r p n = Aᶜ ∩ B := by
    ext v
    simp [A, B, emptySatPartnerEvent]
  have hH : S.emptySatHoleEvent r p n = (Aᶜ ∩ Bᶜ) ∩ C := by
    ext v
    simp only [A, B, C, emptySatHoleEvent, mem_ofPred_eq, mem_inter_iff,
      mem_compl_iff, not_exists]
    aesop
  have hU : S.emptySatCommonEvent r p n = (Aᶜ ∩ Bᶜ) ∩ Cᶜ := by
    ext v
    simp only [A, B, C, emptySatCommonEvent, universalPartnerCommonRegion,
      mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_union, not_exists]
    aesop
  simp only [emptySatRootPartnerLaws, emptySatRootNoPartnerLaws, emptySatPartnerLaws,
    emptySatHoleLaws, emptySatCommonLaws, hIP, hI, hP, hH, hU]
  have h1 := restrict_split (P.laws n) A B hB
  have h2 := restrict_split (P.laws n) Aᶜ B hB
  have h3 := restrict_split (P.laws n) (Aᶜ ∩ Bᶜ) C hC
  calc
    _ = ((P.laws n).restrict (A ∩ B) + (P.laws n).restrict (A ∩ Bᶜ)) +
        ((P.laws n).restrict (Aᶜ ∩ B) +
          ((P.laws n).restrict ((Aᶜ ∩ Bᶜ) ∩ C) +
            (P.laws n).restrict ((Aᶜ ∩ Bᶜ) ∩ Cᶜ))) := by ac_rfl
    _ = (P.laws n).restrict A + (P.laws n).restrict Aᶜ := by rw [← h1, ← h3, ← h2]
    _ = P.laws n := Measure.restrict_add_restrict_compl hA

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Total old cost is the exact sum of the two rooted and three rootless
classes. Every cost uses the same original physical primal. -/
theorem emptySat_cost_partition (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    c = P.emptySatRootPartnerCost p + P.emptySatRootNoPartnerCost p +
      P.emptySatPartnerCost p + P.emptySatHoleCost p + P.emptySatCommonCost p := by
  have hcap (η : PhysicalPrimal.Laws Ω) (hη : ∀ n, P.orderCap < n → η n = 0) :=
    cost_eq_sum_of_cap P.orderCap η hη
  calc
    c = PhysicalPrimal.cost P.laws := P.cost.symm
    _ = _ := by
      rw [emptySatRootPartnerCost, emptySatRootNoPartnerCost, emptySatPartnerCost,
        emptySatHoleCost, emptySatCommonCost,
        hcap P.laws (fun n hn => P.capped n (Or.inr hn)),
        hcap (P.emptySatRootPartnerLaws p)
          (fun n hn => P.emptySatRootPartnerLaws_capped p n (Or.inr hn)),
        hcap (P.emptySatRootNoPartnerLaws p)
          (fun n hn => P.emptySatRootNoPartnerLaws_capped p n (Or.inr hn)),
        hcap (P.emptySatPartnerLaws p)
          (fun n hn => by simp [emptySatPartnerLaws, P.capped n (Or.inr hn)]),
        hcap (P.emptySatHoleLaws p)
          (fun n hn => by simp [emptySatHoleLaws, P.capped n (Or.inr hn)]),
        hcap (P.emptySatCommonLaws p)
          (fun n hn => by simp [emptySatCommonLaws, P.capped n (Or.inr hn)]),
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      have := P.finite n
      have h := congrArg (fun ν : Measure (Fin n → Ω) => ν.real univ)
        (P.emptySat_laws_partition p n)
      simpa only [measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)] using h.symm

/-- Original source containment and P-adjacency transfer to every actual
parent coordinate; no joint absolute continuity is assumed. -/
theorem emptySat_source_parent_facts (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (n : ℕ) :
    ∀ᵐ v ∂P.laws n,
      (∀ i, v i ∈ S.reverseCompulsorySource {p} →
        v i ∈ S.universalPartnerHoleRegion r p) ∧
      (∀ i, v i ∈ S.reverseCompulsorySource {p} →
        S.ρ (v i) ≠ r.val ∧ S.ρ (v i) ≠ p.val) ∧
      ((∃ i, S.ρ (v i) = p.val) → ∀ j, v j ∉ S.reverseCompulsorySource {p}) := by
  have hsource := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  filter_upwards [P.ae_original_vertices _ hsource n,
    P.ae_original_pairs _ (S.ae_root_adjacency p hW hd hgap) n,
    P.feasible.2.2.1 n] with v hv hrow hcl
  have hheads (i : Fin n) (hi : v i ∈ S.reverseCompulsorySource {p}) :
      S.ρ (v i) ≠ r.val ∧ S.ρ (v i) ≠ p.val := by
    have h := hv i hi
    exact ⟨fun he => h (Or.inl (Or.inl he)), fun he => h (Or.inl (Or.inr he))⟩
  refine ⟨hv, hheads, ?_⟩
  rintro ⟨i, hi⟩ j hj
  have hij : i ≠ j := fun he => (hheads j hj).2 (he ▸ hi)
  exact (hv j hj) (Or.inr ((hrow i j hij hi).mp (hcl i j hij)))

/-- Exact original I-J demand is all carried by I-without-P columns:
I-P columns cannot meet the entire private source. -/
theorem emptySatRootNoPartner_source_first_moment (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PhysicalPrimal.tupleCount (S.reverseCompulsorySource {p}) v : ℝ)
        ∂P.emptySatRootNoPartnerLaws p n) =
      S.originalAtomMass r * μ.real (S.reverseCompulsorySource {p}) := by
  classical
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let I := {x | S.ρ x = r.val}
  let J := S.reverseCompulsorySource {p}
  let f := J.indicator (fun _ => (1 : ℝ))
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hf : Measurable f := measurable_const.indicator hJ
  have hK : Integrable (fun z : Ω × Ω => if z.1 ∈ I then f z.2 else 0)
      (PhysicalPrimal.occupation P.laws) := by
    rw [P.feasible.2.2.2]
    have hi : Integrable ((I ×ˢ J).indicator (fun _ => (1 : ℝ)))
        (PhysicalPrimal.graphDemand μ
          {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true}) :=
      (integrable_const (1 : ℝ)).indicator (hI.prod hJ)
    convert hi using 1
    funext z
    by_cases hx : z.1 ∈ I <;> by_cases hy : z.2 ∈ J <;> simp [f, hx, hy]
  have hweighted := PhysicalPrimal.integral_rootLeaves_eq_sum_of_cap P.orderCap P.laws
    (fun n hn => P.capped n (Or.inr hn)) I hI f hf (by
      convert hK using 1
      funext z
      split_ifs <;> rfl)
  have hmass : (μ.restrict {x | S.ρ x ≠ r.val}).real J = μ.real J := by
    have hsets : J ∩ {x | S.ρ x ≠ r.val} =ᵐ[μ] J := by
      filter_upwards [S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell]
        with x hx
      exact propext ⟨fun h => h.1, fun h =>
        ⟨h, fun he => hx h (Or.inl (Or.inl he))⟩⟩
    simp only [measureReal_def, Measure.restrict_apply hJ, measure_congr hsets]
  have hleft : (∫ x, f x ∂PhysicalPrimal.rootLeaves P.laws I) =
      S.originalAtomMass r * μ.real J := by
    rw [P.leaves, integral_smul_measure, show (∫ x, f x
      ∂μ.restrict {x | S.ρ x ≠ r.val}) = (μ.restrict {x | S.ρ x ≠ r.val}).real J by
        simp [f, integral_indicator hJ], hmass]
    rfl
  rw [hleft] at hweighted
  change _ = S.originalAtomMass r * μ.real J
  rw [hweighted]
  apply Finset.sum_congr rfl
  intro n _
  rw [emptySatRootNoPartnerLaws, ← integral_indicator
    (S.measurableSet_emptySatRootNoPartnerEvent r p n)]
  apply integral_congr_ae
  filter_upwards [P.emptySat_source_parent_facts p hpair hW hd hgap hell n, P.unique_root n]
    with v hv hroot
  have hsum : ∑ i, f (v i) = (PhysicalPrimal.tupleCount J v : ℝ) := by
    simp [f, Set.indicator, PhysicalPrimal.tupleCount]
  have hdiag : (∑ i, @ite ℝ (v i ∈ I) (Classical.propDecidable _) (f (v i)) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : v i ∈ I
    · have hn : v i ∉ J := fun hj => (hv.2.1 i hj).1 hi
      simp [hi, f, hn]
    · simp [hi]
  rw [hsum, hdiag, sub_zero]
  by_cases hr : ∃ i, S.ρ (v i) = r.val
  · have hcount : PhysicalPrimal.tupleCount I v = 1 :=
      PhysicalPrimal.tupleCount_eq_one_of_unique I v (by
        obtain ⟨i, hi⟩ := hr
        exact ⟨i, hi, fun j hj => hroot j i hj hi⟩)
    by_cases hp : ∃ i, S.ρ (v i) = p.val
    · have hz := tupleCount_zero J v (hv.2.2 hp)
      simp [hz, emptySatRootNoPartnerEvent, hp]
    · simp [hcount, emptySatRootNoPartnerEvent, hr, not_exists.mp hp, J]
  · have hz := tupleCount_zero I v (by simpa only [I, mem_ofPred_eq, not_exists] using hr)
    simp [hz, emptySatRootNoPartnerEvent, hr]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem graphDemand_source_square (p : S.I) :
    (PhysicalPrimal.graphDemand μ
      {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true}).real
        (S.reverseCompulsorySource {p} ×ˢ S.reverseCompulsorySource {p}) =
      ∫ q, PhysicalCliqueRepresentative.edgeIndicator
        (Function.uncurry (PhysicalRepresentative.adjacency W m)) q
          ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
            (μ.restrict (S.reverseCompulsorySource {p})) := by
  let J := S.reverseCompulsorySource {p}
  let E : Set (Ω × Ω) := {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true}
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  change (PhysicalPrimal.graphDemand μ E).real (J ×ˢ J) = _
  have heq : PhysicalCliqueRepresentative.edgeIndicator
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) =
        E.indicator (fun _ => (1 : ℝ)) := by
    funext q
    by_cases h : PhysicalRepresentative.adjacency W m q.1 q.2 = true <;>
      simp [PhysicalCliqueRepresentative.edgeIndicator, E, Set.indicator, Function.uncurry, h]
  rw [heq, integral_indicator hE]
  simp only [PhysicalPrimal.graphDemand, measureReal_def, Measure.restrict_apply (hJ.prod hJ),
    setIntegral_const, smul_eq_mul, mul_one, Measure.prod_restrict,
    Measure.restrict_apply hE]
  simp only [J, inter_comm]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The factorial source moment in the rooted restriction spends at most
the original global J-J ordered pair demand, with its exact factor two. -/
theorem emptySatRootNoPartner_source_factorial_bound (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PhysicalPrimal.tupleCount (S.reverseCompulsorySource {p}) v : ℝ) *
        ((PhysicalPrimal.tupleCount (S.reverseCompulsorySource {p}) v : ℝ) - 1)
          ∂P.emptySatRootNoPartnerLaws p n) ≤
      ∫ q, PhysicalCliqueRepresentative.edgeIndicator
        (Function.uncurry (PhysicalRepresentative.adjacency W m)) q
          ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
            (μ.restrict (S.reverseCompulsorySource {p})) := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let J := S.reverseCompulsorySource {p}
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hfull := PhysicalPrimal.countMeasure_factorial_moment P.orderCap P.laws J J hJ hJ
    (fun n hn => P.capped n (Or.inr hn)) _ P.feasible.2.2.2
  rw [PhysicalPrimal.integral_countMeasure P.orderCap P.laws J J hJ hJ] at hfull
  rw [← graphDemand_source_square p, ← hfull]
  apply Finset.sum_le_sum
  intro n _
  apply integral_mono_measure Measure.restrict_le_self
  · exact Eventually.of_forall (fun v => by
      change 0 ≤ (PhysicalPrimal.tupleCount J v : ℝ) *
        ((PhysicalPrimal.tupleCount J v : ℝ) - 1)
      by_cases hz : PhysicalPrimal.tupleCount J v = 0
      · simp [hz]
      · apply mul_nonneg (Nat.cast_nonneg _)
        exact sub_nonneg.mpr (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)))
  · exact PhysicalPrimal.integrable_count_function (P.laws n) J J hJ hJ
      (fun z => (z.1 : ℝ) * ((z.1 : ℝ) - 1))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [StandardBorelSpace Ω] [MeasurableEq Ω]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem count_minus_pairs_le_one (n : ℕ) :
    (n : ℝ) - (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ 1 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith)
      (show 0 ≤ (n : ℝ) - 2 by linarith)]

/-- The elementary source-count inequality and the same actual pair
inventory give the lower cost K=Aj-GJJ/2. -/
theorem emptySatRootNoPartnerCost_ge (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    S.originalAtomMass r * μ.real (S.reverseCompulsorySource {p}) -
      (∫ q, PhysicalCliqueRepresentative.edgeIndicator
        (Function.uncurry (PhysicalRepresentative.adjacency W m)) q
          ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
            (μ.restrict (S.reverseCompulsorySource {p}))) / 2 ≤
      P.emptySatRootNoPartnerCost p := by
  let J := S.reverseCompulsorySource {p}
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  let ν := PhysicalPrimal.countMeasure P.orderCap (P.emptySatRootNoPartnerLaws p) J J
  have hcount : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ)) ν :=
    PhysicalPrimal.integrable_countMeasure _ _ J J hJ hJ _
  have hpairs : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) * ((z.1 : ℝ) - 1)) ν :=
    PhysicalPrimal.integrable_countMeasure _ _ J J hJ hJ _
  have hbound := integral_mono_ae (hcount.sub (hpairs.div_const 2))
    (integrable_const (1 : ℝ)) (Eventually.of_forall (fun z : ℕ × ℕ =>
      count_minus_pairs_le_one z.1))
  change (∫ z : ℕ × ℕ, (z.1 : ℝ) - (z.1 : ℝ) * ((z.1 : ℝ) - 1) / 2 ∂ν) ≤
    ∫ _ : ℕ × ℕ, (1 : ℝ) ∂ν at hbound
  rw [integral_sub hcount (hpairs.div_const 2), integral_div, integral_const,
    smul_eq_mul, mul_one, PhysicalPrimal.countMeasure_mass P.orderCap _ J J hJ hJ
      (fun n hn => P.emptySatRootNoPartnerLaws_capped p n (Or.inr hn)),
    PhysicalPrimal.integral_countMeasure P.orderCap _ J J hJ hJ,
    PhysicalPrimal.integral_countMeasure P.orderCap _ J J hJ hJ,
    P.emptySatRootNoPartner_source_first_moment p hpair hW hd hgap hell] at hbound
  have hfactor := P.emptySatRootNoPartner_source_factorial_bound p
  dsimp only [J, Prod.fst] at hbound
  change _ ≤ PhysicalPrimal.cost (P.emptySatRootNoPartnerLaws p)
  linarith only [hbound, hfactor]

end UniversalPhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure

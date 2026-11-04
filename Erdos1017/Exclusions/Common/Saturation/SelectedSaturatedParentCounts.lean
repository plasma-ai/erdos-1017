module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPhysicalCounts
public import Erdos1017.Exclusions.Common.Physical.PhysicalCountMeasure
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredCopyBonuses
public import Erdos1017.Exclusions.Common.Saturation.SaturatedPhysicalParentShape

/-!
# Count shape of parents containing the saturated head

In the universal physical primal, the zero-body copy bonus makes every present
outside-root edge strictly negative, so a parent containing the saturated head
has at most one coordinate outside the saturated pair and count shape one `A`,
no `E`, at most one `R`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual zero-body copy bonus makes every present outside-root
edge strictly negative in the original bounded physical representative. -/
theorem ae_body_charge_strictly_negative_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      PhysicalRepresentative.charge W m p.1 p.2 < 0 := by
  have hs := hW.strict_gap_structure hd hgap
  have hb : 0 ≤ μ.real {x | S.ρ x = r.val} := ENNReal.toReal_nonneg
  filter_upwards [S.ae_body_penalty_mass_lower_of_zero_body r hW hd hgap hzero,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
    PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hp hG hY hx hy hA
  have hG' : adjacencyKernel W p.1 p.2 = 1 := by simpa only [adjacencyKernel, hA, ↓reduceIte] using hG
  have hlo := hp hx hy hG'
  rw [← hY] at hlo
  by_contra hn
  have hmul := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (le_of_not_gt hn)
  exact (not_lt_of_ge hmul) (hs.gamma_pos.trans_le hlo)

/-- In the unchanged original physical primal, a parent containing the
saturated head has at most one coordinate outside the saturated pair.
Every parent premise is licensed by actual pair balance and tightness. -/
theorem UniversalPhysicalPrimal.ae_saturated_parent_outside_pair_eq
    {S : SelectedHighLowStructure W m} {r a : S.I} {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ j, S.ρ (v j) = a.val →
      ∃ i, S.ρ (v i) = r.val ∧ i ≠ j ∧
        ∀ k l, k ≠ i → k ≠ j → l ≠ i → l ≠ j → k = l := by
  let Y := PhysicalRepresentative.charge W m
  let E := {p : Ω × Ω | PhysicalRepresentative.adjacency W m p.1 p.2 = true}
  let good (p : Ω × Ω) : Prop :=
    (S.ρ p.1 = r.val → Y p.1 p.2 = S.rootChargeRow r p.2) ∧
    (S.ρ p.1 = r.val → S.ρ p.2 = a.val → Y p.1 p.2 = 1) ∧
    (S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true → Y p.1 p.2 < 0)
  have hgood : ∀ᵐ p ∂μ.prod μ, good p := by
    filter_upwards [S.ae_root_charge r hW hd hgap, hpair.2,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support,
      S.ae_body_charge_strictly_negative_of_zero_body r hW hd hgap hzero] with p hr hp he hn
    exact ⟨hr, fun hx hy => he.trans (hp hx hy), hn⟩
  have hparents := PhysicalPrimal.ae_all_pairs_of_balance P.laws
    (PhysicalPrimal.graphDemand μ E) P.feasible.2.2.2 good
    (ae_mono Measure.restrict_le_self hgood) n
  have hN := S.root_neutral_of_zero_body r hW hd hgap hzero
  filter_upwards [hparents, P.ae_parent_meets_of_zero_body hzero n, P.unique_root n,
    P.tight_physical n, P.feasible.2.2.1 n,
    P.ae_saturated_head_cancellation hW hd hgap hN hpair hzero n]
    with v hv hroot huniq ht hc hcancel j hj
  obtain ⟨i, hi⟩ := hroot
  have hij : i ≠ j := by
    intro he
    exact hpair.1 (Subtype.ext (hi.symm.trans (he ▸ hj)))
  have hnotroot (k : Fin n) (hki : k ≠ i) : S.ρ (v k) ≠ r.val :=
    fun hk => hki (huniq k i hk hi)
  have hbody (k l : Fin n) (hkl : k ≠ l) (hki : k ≠ i) (hli : l ≠ i) :
      Y (v k) (v l) < 0 := (hv k l hkl).2.2 (hnotroot k hki) (hnotroot l hli) (hc k l hkl)
  have htriangle (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
      Y (v i) (v k) + Y (v j) (v k) ≤ 0 := by
    have he := hcancel j k hkj.symm hj (hnotroot k hki)
    rw [(hv i k hki.symm).1 hi]
    linarith
  have hsum : (∑ ab : PhysicalPrimal.PairIndex n, Y (v ab.val.1) (v ab.val.2)) = 2 := by
    change (∑ ab : PhysicalPrimal.PairIndex n, Y (v ab.val.1) (v ab.val.2)) / 2 = 1 at ht
    linarith
  exact ⟨i, hi, hij, PhysicalPrimal.SaturatedParent.outside_pair_eq
    (fun k l => Y (v k) (v l)) (fun k l => PhysicalRepresentative.charge_symm W m _ _)
    i j hij ((hv i j hij).2.1 hi hj) hbody htriangle hsum⟩

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual label graph holds on every distinct pair of each original
singular physical parent, by its ordered pair occupation. -/
theorem UniversalPhysicalPrimal.ae_covered_label_clique
    {S : SelectedHighLowStructure W m} {r : S.I} {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (a : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i j, i ≠ j →
      S.coveredGraph r a (S.coveredLabel a (v i)) (S.coveredLabel a (v j)) = true := by
  let E := {p : Ω × Ω | PhysicalRepresentative.adjacency W m p.1 p.2 = true}
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hg : ∀ᵐ p ∂PhysicalPrimal.graphDemand μ E,
      S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) = true := by
    filter_upwards [ae_restrict_of_ae (S.ae_covered_graph r a hW hd hgap hpair hzero),
      ae_restrict_of_ae (PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support), ae_restrict_mem hE] with p hg hp he
    change PhysicalRepresentative.adjacency W m p.1 p.2 = true at he
    rw [he, ite_eq_left rfl] at hp
    have heq := hp.symm.trans hg
    by_contra hn
    simp only [hn, ↓reduceIte] at heq
    norm_num at heq
  exact PhysicalPrimal.ae_all_pairs_of_balance P.laws
    (PhysicalPrimal.graphDemand μ E) P.feasible.2.2.2 _ hg n

/-- Parents containing the saturated head have one A, no E, and at most
one R. This is the actual AB/ABR count contribution used in subtraction. -/
theorem UniversalPhysicalPrimal.ae_saturated_parent_count_shape
    {S : SelectedHighLowStructure W m} {r : S.I} {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (a : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, (∃ j, S.ρ (v j) = a.val) →
      PhysicalPrimal.tupleCount {x | S.ρ x = a.val} v = 1 ∧
      PhysicalPrimal.tupleCount (S.D \ S.rootNeighborhood a) v = 0 ∧
      PhysicalPrimal.tupleCount (S.D ∩ S.rootNeighborhood a) v ≤ 1 := by
  filter_upwards [P.ae_saturated_parent_outside_pair_eq hW hd hgap hpair hzero n,
    P.ae_covered_label_clique a hW hd hgap hpair hzero n] with v hout hc hA
  obtain ⟨j, hj⟩ := hA
  obtain ⟨i, hi, hij, hpairs⟩ := hout j hj
  have hjlabel := (S.coveredLabel_eq_inl_iff a a (v j)).mpr hj
  have hAuniq (k : Fin n) (hk : S.ρ (v k) = a.val) : k = j := by
    by_contra hkj
    have he := hc k j hkj
    rw [(S.coveredLabel_eq_inl_iff a a (v k)).mpr hk, hjlabel] at he
    simp [coveredGraph] at he
  have hnoE (k : Fin n) : v k ∉ S.D \ S.rootNeighborhood a := by
    intro hk
    have hkj : k ≠ j := fun he => S.row_ne_atom_of_mem_diffuse (v k) hk.1 a (he ▸ hj)
    have hklabel := (S.coveredLabel_eq_inr_iff a (v k) false).mpr ⟨hk.1, by simp [hk.2]⟩
    have he := hc j k hkj.symm
    rw [hjlabel, hklabel] at he
    simp [coveredGraph] at he
  refine ⟨PhysicalPrimal.tupleCount_eq_one_of_unique _ v ⟨j, hj, hAuniq⟩, ?_, ?_⟩
  · simp [PhysicalPrimal.tupleCount, hnoE]
  · by_cases hR : ∃ k, v k ∈ S.D ∩ S.rootNeighborhood a
    · obtain ⟨k, hk⟩ := hR
      have hu : ∃! l, v l ∈ S.D ∩ S.rootNeighborhood a := by
        refine ⟨k, hk, ?_⟩
        intro l hl
        exact hpairs l k
          (fun he => S.row_ne_atom_of_mem_diffuse (v l) hl.1 r (he ▸ hi))
          (fun he => S.row_ne_atom_of_mem_diffuse (v l) hl.1 a (he ▸ hj))
          (fun he => S.row_ne_atom_of_mem_diffuse (v k) hk.1 r (he ▸ hi))
          (fun he => S.row_ne_atom_of_mem_diffuse (v k) hk.1 a (he ▸ hj))
      exact (PhysicalPrimal.tupleCount_eq_one_of_unique _ v hu).le
    · simp only [not_exists] at hR
      simp [PhysicalPrimal.tupleCount, hR]

end Erdos1017.CappedModel.SelectedHighLowStructure

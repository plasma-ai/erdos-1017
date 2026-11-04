module

public import Erdos1017.Exclusions.Common.Physical.PhysicalCoverCancellation
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyPrimal
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTriangle
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy

/-!
# Charge cancellation along saturated heads in the zero-body branch

Zero-body tight parents force cancellation along every saturated-root head edge,
lifted from the pair events, so in the selected zero-body branch a saturated
root neighbor's present exterior charge is exactly the negative of the universal
root charge.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Actual zero-body tight parents force cancellation along every
saturated-root head edge. All parent facts are lifted from original
pair events; the root triangle event was derived by original Fubini. -/
theorem UniversalPhysicalPrimal.ae_saturated_head_cancellation
    {S : SelectedHighLowStructure W m} {r u : S.I} {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r u)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ a b, a ≠ b → S.ρ (v a) = u.val → S.ρ (v b) ≠ r.val →
      PhysicalRepresentative.charge W m (v a) (v b) + S.rootChargeRow r (v b) = 0 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let E : Set (Ω × Ω) := {p | A p.1 p.2 = true}
  let pairGood (p : Ω × Ω) : Prop :=
    (S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → Y p.1 p.2 ≤ 0) ∧
    (S.ρ p.1 = r.val → Y p.1 p.2 = S.rootChargeRow r p.2) ∧
    (S.ρ p.1 = r.val → S.ρ p.2 = u.val → Y p.1 p.2 = 1) ∧
    (S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → A p.1 p.2 = true →
      S.rootChargeRow r p.1 + S.rootChargeRow r p.2 + Y p.1 p.2 ≤ 1)
  have hgood : ∀ᵐ p ∂μ.prod μ, pairGood p := by
    filter_upwards [S.zero_body_ae_charge_nonpositive r hzero,
      S.ae_root_charge r hW hd hgap, hpair.2,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support,
      S.ae_universal_root_triangle r hW hd hgap hN] with p hb hr hs he ht
    refine ⟨?_, hr, ?_, ht⟩
    · intro hx hy
      exact he.trans_le (hb hx hy)
    · intro hx hy
      exact he.trans (hs hx hy)
  have hparent := PhysicalPrimal.ae_all_pairs_of_balance P.laws
    (PhysicalPrimal.graphDemand μ E) P.feasible.2.2.2 pairGood
    (ae_mono Measure.restrict_le_self hgood) n
  filter_upwards [hparent, P.ae_parent_meets_of_zero_body hzero n,
    P.unique_root n, P.tight_physical n, P.feasible.2.2.1 n]
    with v hv hroot hu ht hc a b hab ha hb
  obtain ⟨i, hi⟩ := hroot
  have hnotroot (k : Fin n) (hki : k ≠ i) : S.ρ (v k) ≠ r.val :=
    fun hk => hki (hu k i hk hi)
  have hai : a ≠ i := by
    intro he
    have hur : u.val = r.val := ha.symm.trans (he ▸ hi)
    exact hpair.1 (Subtype.ext hur.symm)
  have hbi : b ≠ i := fun he => hb (he ▸ hi)
  have hia := hv i a hai.symm
  have hsat : Y (v i) (v a) = 1 := hia.2.2.1 hi ha
  have hsa : S.rootChargeRow r (v a) = 1 := (hia.2.1 hi).symm.trans hsat
  have hbody (j k : Fin n) (hjk : j ≠ k) (hji : j ≠ i) (hki : k ≠ i) :
      Y (v j) (v k) ≤ 0 := (hv j k hjk).1 (hnotroot j hji) (hnotroot k hki)
  have htriangle (k : Fin n) (hki : k ≠ i) (hka : k ≠ a) :
      Y (v i) (v k) + Y (v a) (v k) ≤ 0 := by
    have htri := (hv a k hka.symm).2.2.2 (hnotroot a hai) (hnotroot k hki) (hc a k hka.symm)
    rw [hsa, ← (hv i k hki.symm).2.1 hi] at htri
    linarith
  have hsum : (∑ ij : PhysicalPrimal.PairIndex n, Y (v ij.val.1) (v ij.val.2)) = 2 := by
    change (∑ ij : PhysicalPrimal.PairIndex n, Y (v ij.val.1) (v ij.val.2)) / 2 = 1 at ht
    linarith
  have he := PhysicalPrimal.saturated_root_cancellation (fun j k => Y (v j) (v k))
    (fun j k => PhysicalRepresentative.charge_symm W m (v j) (v k)) i a hai.symm
    hsat hbody htriangle hsum b hbi hab.symm
  rw [(hv i b hbi.symm).2.1 hi] at he
  linarith

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- In the actual selected zero-body branch, a saturated root neighbor's
present exterior charge is exactly the negative universal-root charge.
The proof constructs the original physical primal and derives the
cancellation, rather than assuming a clipping or optimality certificate. -/
theorem ae_saturated_head_charge_cancel_of_zero_body
    (S : SelectedHighLowStructure W m) (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r u)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 ≠ r.val →
      adjacencyKernel W p.1 p.2 = 1 →
      chargeKernel W p.1 p.2 + S.rootChargeRow r p.2 = 0 := by
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let E : Set (Ω × Ω) := {p | A p.1 p.2 = true}
  let good (p : Ω × Ω) : Prop := S.ρ p.1 = u.val → S.ρ p.2 ≠ r.val →
    Y p.1 p.2 + S.rootChargeRow r p.2 = 0
  have hgood : MeasurableSet {p | good p} := by
    have hsum := (PhysicalRepresentative.measurable_charge W m).add
      ((S.measurable_rootChargeRow r).comp measurable_snd)
    have heq := measurableSet_eq_fun hsum (measurable_const (a := (0 : ℝ)))
    have hm := ((S.hfibers u.val u.property).1.preimage measurable_fst).compl.union
      (((S.hfibers r.val r.property).1.preimage measurable_snd).union heq)
    convert hm using 1
    ext p
    simp only [good, Y, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
    tauto
  have hparents : ∀ n, ∀ᵐ v ∂P.laws n, ∀ a b, a ≠ b → good (v a, v b) :=
    P.ae_saturated_head_cancellation hW hd hgap hN hpair hzero
  have hae := PhysicalPrimal.ae_pair_of_all_parents P.laws
    (PhysicalPrimal.graphDemand μ E) P.feasible.2.2.2 good hgood hparents
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hraw := (ae_restrict_iff' hE).mp hae
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [hraw, PhysicalRepresentative.charge_ae_eq W m hs,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs] with p hp hY hA hu hr hG
  have hpresent : A p.1 p.2 = true := by
    change adjacencyKernel W p.1 p.2 = (if A p.1 p.2 = true then 1 else 0) at hA
    rw [hG] at hA
    split_ifs at hA with h
    · exact h
    · norm_num at hA
  have he := hp hpresent hu hr
  change PhysicalRepresentative.charge W m p.1 p.2 + S.rootChargeRow r p.2 = 0 at he
  rwa [hY] at he

end Erdos1017.CappedModel.SelectedHighLowStructure

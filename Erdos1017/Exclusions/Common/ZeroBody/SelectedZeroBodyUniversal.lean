module

public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyRows

/-!
# Universality and neutrality from zero body energy

Zero positive body energy forces the positive whole cover to be universal, its
derived charge row ruling out every exterior nonedge, and neutral in the
original classification; the bounded-order primal with full root coverage then
follows from zero body energy alone.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Zero positive body energy already forces the original positive whole
cover to be universal. Positivity of its derived charge row rules out
every exterior nonedge on the same original product-law event. -/
theorem ae_root_universal_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ r.val) := by
  filter_upwards [S.ae_root_charge r hW hd hgap, S.ae_root_adjacency r hW hd hgap,
    Measure.quasiMeasurePreserving_snd.ae
      (S.ae_rootChargeRow_pos_of_zero_body r hW hd hgap hzero)] with p hy ha hs hx
  constructor
  · exact fun he => ((ha hx).mp he).1
  · intro hne
    by_contra hn
    have hz := PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2
      (Bool.eq_false_iff.mpr hn)
    have hp := hs hne
    rw [← hy hx, hz] at hp
    exact (lt_irrefl 0) hp

/-- The same whole cover is NEUTRAL in the actual original classification.
Both directed relation-section masses vanish; no class reassignment or
neutrality assumption is used. -/
theorem root_neutral_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N := by
  have hnone : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p ∉ actualZeroRelation W m S.ρ := by
    filter_upwards [S.ae_root_universal_of_zero_body r hW hd hgap hzero,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support,
      (hW.strict_gap_structure hd hgap).strict_support] with p hu hg hs hx hz
    have hne : S.ρ p.2 ≠ r.val := fun he => hz.2 (hx.trans he.symm)
    have ha := (hu hx).mpr hne
    have hG : W.moment CappedColor.adjacency p = 1 := by simpa [ha] using hg
    have hM : shiftedMoment W m p = 0 := hz.1
    rw [hM] at hs
    norm_num [hG] at hs
  have hboth : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      p ∉ actualZeroRelation W m S.ρ ∧ p.swap ∉ actualZeroRelation W m S.ρ := by
    filter_upwards [hnone, actualZeroRelation_symm W m S.ρ] with p hn hs hx
    exact ⟨hn hx, fun he => hn hx (hs.mpr he)⟩
  filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hboth),
    ae_restrict_mem (S.hfibers r.val r.property).1] with x hx hr
  let Z := actualZeroRelation W m S.ρ
  let g := fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x
  have hright : OrderedZeroRelation.rightNeighborMass μ Z g x = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hx] with y hy
    exact fun he => (hy hr).1 he.1
  have hleft : OrderedZeroRelation.leftNeighborMass μ Z g x = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hx] with y hy
    exact fun he => (hy hr).2 he.1
  rw [S.hN]
  change x ∉ OrderedZeroRelation.highClass μ Z g ∪ OrderedZeroRelation.lowClass μ Z g
  simp only [OrderedZeroRelation.highClass, OrderedZeroRelation.lowClass,
    OrderedZeroRelation.leftSide, OrderedZeroRelation.rightSide, mem_union,
    Set.mem_sdiff, mem_ofPred_eq, hright, hleft, lt_irrefl, false_and, or_self, not_false_eq_true]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual bounded-order primal and full root coverage follow from
zero body energy alone, with universality and neutrality derived internally. -/
theorem exists_rooted_primal_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∃ P : S.UniversalPhysicalPrimal r c,
      (∀ n, ∀ᵐ v ∂P.laws n, ∃! i, S.ρ (v i) = r.val) ∧
      ∀ n, PhysicalRootReplacement.noRootLaw (P.laws n) {x | S.ρ x = r.val} = 0 := by
  exact S.exists_zero_body_rooted_primal r hW hd hgap
    (S.root_neutral_of_zero_body r hW hd hgap hzero) hzero

end Erdos1017.CappedModel.SelectedHighLowStructure

module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy
public import Erdos1017.SelectedModel.Saturation.SelectedSaturationAtomic
public import Erdos1017.SelectedModel.Structure.WholeRowCrossBlocks

/-!
# Constant charge on whole-fiber blocks

Every original whole-fiber charge block is constant, charge one on a distinct
pair is equivalent to saturation of the whole block, and almost every charge-one
pair determines a saturated block of distinct original atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Every original whole-fiber charge block is constant. Charge one on a
distinct pair is equivalent to actual saturation of that entire block. -/
theorem exists_charge_cross_constant (S : SelectedHighLowStructure W m) (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∃ b : ℝ,
      (∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
        chargeKernel W p.1 p.2 = b) ∧
      (S.IsSaturatedAtomPair r u ↔ r ≠ u ∧ b = 1) := by
  have hIr := S.hfibers r.val r.property
  have hIu := S.hfibers u.val u.property
  obtain ⟨q, _, _, _, hblock⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ
    r.val u.val hIr.2.1 hIu.2.1 hIr.2.2.2 hIu.2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
    (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm)) hW.moment_mem
  let b := q + m * (if 0 < q then 1 else 0)
  have hb : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
      chargeKernel W p.1 p.2 = b := by
    rw [Measure.prod_restrict] at hblock
    have hraw := (ae_restrict_iff' (hIr.1.prod hIu.1)).mp hblock
    filter_upwards [hraw] with p hp hr hu
    exact (hp ⟨hr, hu⟩).2.2
  refine ⟨b, hb, ?_⟩
  constructor
  · intro hpair
    refine ⟨hpair.1, ?_⟩
    have hconst : ∀ᵐ p ∂(μ.restrict {x | S.ρ x = r.val}).prod
        (μ.restrict {x | S.ρ x = u.val}), b = 1 := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) hb,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hpair.2,
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hIr.1),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hIu.1)] with p hp hs hr hu
      exact (hp hr hu).symm.trans (hs hr hu)
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIr.2.1.ne'
      (Measure.ae_ae_of_ae_prod hconst)
    obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIu.2.1.ne' hx
    exact hy
  · rintro ⟨hru, hb1⟩
    refine ⟨hru, ?_⟩
    filter_upwards [hb] with p hp hr hu
    exact (hp hr hu).trans hb1

/-- On one common conull set, an actual charge-one pair determines an
entire saturated block of distinct original atoms. -/
theorem ae_saturated_pair_has_saturated_atom_block
    [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ p ∂μ.prod μ, chargeKernel W p.1 p.2 = 1 →
      ∃ r u : S.I, S.IsSaturatedAtomPair r u ∧ S.ρ p.1 = r.val ∧ S.ρ p.2 = u.val := by
  let : Countable S.I := S.hI.to_subtype
  have hblocks : ∀ᵐ p ∂μ.prod μ, ∀ r u : S.I,
      r ≠ u → S.ρ p.1 = r.val → S.ρ p.2 = u.val →
        chargeKernel W p.1 p.2 = 1 → S.IsSaturatedAtomPair r u := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro u
    obtain ⟨b, hb, hsat⟩ := S.exists_charge_cross_constant r u hW
    filter_upwards [hb] with p hp hru hr hu hy
    exact hsat.mpr ⟨hru, (hp hr hu).symm.trans hy⟩
  filter_upwards [S.ae_saturated_pair_between_distinct_original_atoms hW hd hgap hell,
    hblocks] with p ha hb hy
  obtain ⟨r, u, hru, hr, hu⟩ := ha hy
  exact ⟨r, u, hb r u hru hr hu hy, hr, hu⟩

end Erdos1017.CappedModel.SelectedHighLowStructure

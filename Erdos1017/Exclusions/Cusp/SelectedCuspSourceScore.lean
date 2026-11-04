module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceRows

/-!
# Signed cusp score of the whole-source child

The whole-source child has the signed cusp score and its own cost bound, with
every current row and the hole identity derived internally
(`exists_cusp_source_child_score`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open WholeSourceChild KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual whole-source child has the signed cusp score and its own
cost bound. Every current row and the hole identity are derived internally. -/
theorem exists_cusp_source_child_score (R : S.ReverseRecovery) (r i : S.I)
    {d c a e : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hr : R.plateau = {r}) (hmissing : 1 - 2 * d = a ^ 2)
    (hvalue : c = (1 - a) * a ^ 2 + e)
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hsourceEdge : 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) :
    ∃ child : Model Ω (law R.cuspPartialLaw {x | S.ρ x = r.val}
        (R.cuspSourcePeak i) (R.cuspSourceRemainder i)),
      FullFeasible child ∧
      objective child ≤ max (R.height ^ 2 / 4) (R.cuspOutsideSquares r i) ∧
      objective child - R.height ^ 2 / 4 =
        e + (2 - 2 * a - (-m)) * a ^ 2 / 2 + (-m) * R.cuspOutsideSquares r i / 2 +
          kernelEnergy (μ := μ) (shiftedKernel W m)
            (MissingFlow.direction μ R.cuspPartialFlow) / 2 +
          (-m - 1) * R.height ^ 2 / 4 -
          (R.height / 2 - S.originalAtomMass i) * R.cuspPeakCredit r i -
          ((R.height / 2 - μ.real (R.cuspSourceRemainder i)) /
            μ.real (R.cuspSourceRemainder i)) * R.cuspRemainderCredit r i +
          ((R.height / 2 - S.originalAtomMass i) *
            (R.height / 2 - μ.real (R.cuspSourceRemainder i)) /
            μ.real (R.cuspSourceRemainder i)) * R.cuspCrossEnergy i -
          (S.originalAtomMass i + S.originalAtomMass r) * R.cuspRemainderEnergy i /
            (2 * μ.real (R.cuspSourceRemainder i)) := by
  let : IsProbabilityMeasure R.cuspPartialLaw := R.cuspPartialLaw_probability
  let : NullSingletonClass R.cuspPartialLaw := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hkernel : chargeKernel R.cuspPartialModel = chargeKernel W := by
    funext x y
    exact R.cuspPartialModel_moment CappedColor.charge (x, y)
  have hg := R.cuspPartialLaw_child_graph r i hW hd hgap hr
  have hPS : Disjoint {x | S.ρ x = r.val} R.cuspSource := by
    rw [cuspSource, hr]
    exact S.disjoint_singleton_fiber_source r
  have hPI : Disjoint {x | S.ρ x = r.val} (R.cuspSourcePeak i) :=
    hPS.mono_right inter_subset_left
  have hPJ : Disjoint {x | S.ρ x = r.val} (R.cuspSourceRemainder i) :=
    hPS.mono_right sdiff_subset
  have ha : 0 < R.cuspPartialLaw.real (R.cuspSourcePeak i) := by
    rw [R.cuspPartialLaw_mass_peak i hinside, originalAtomMass]
    exact ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top _ _)
  have hz : 0 < R.cuspPartialLaw.real (R.cuspSourceRemainder i) := by
    rw [R.cuspPartialLaw_mass_remainder i]
    exact R.cuspSourceRemainder_mass_pos i hsourceEdge
  have hsum : S.originalAtomMass i + μ.real (R.cuspSourceRemainder i) =
      μ.real R.cuspSource := by
    simpa only [R.cuspSourcePeak_mass_original i hinside] using
      R.cuspSource_mass_decomposition i
  have hheight : S.originalAtomMass r + S.originalAtomMass i +
      μ.real (R.cuspSourceRemainder i) = R.height := by
    have h := R.singleton_height_eq_mass_add_source r hr
    change R.height = S.originalAtomMass r + μ.real (S.reverseCompulsorySource {r}) at h
    have hs : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
    rw [← hs] at h
    linarith
  have hcurrent : objective R.cuspPartialModel = (1 - a) * a ^ 2 + e +
      (-m) * R.cuspDensityDrop d + kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ R.cuspPartialFlow) / 2 := by
    have h := hW.missing_flow_endpoint_budget R.cuspPartialFlow
      (MissingFlow.integrable_sourceSlice R.isFullReverseFlow.integrable
        R.measurableSet_source.compl)
      (MissingFlow.nonnegative_sourceSlice R.isFullReverseFlow.nonnegative R.cuspSourceᶜ)
      (R.isFullReverseFlow.retained_supply_le_one R.cuspSource)
    change (2 * (c - m * d) + m) + kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ R.cuspPartialFlow) =
      2 * objective R.cuspPartialModel + m * (1 - 2 * density R.cuspPartialModel) at h
    unfold cuspDensityDrop
    nlinarith [hvalue]
  have hrowP : rowIntegral R.cuspPartialLaw (chargeKernel R.cuspPartialModel)
      {x | S.ρ x = r.val} = R.cuspPartialLaw.real {x | S.ρ x = r.val} *
      (2 * (c - m * d) + m + (-m) *
        (R.cuspPartialLaw.real {x | S.ρ x = r.val} +
          R.cuspPartialLaw.real (R.cuspSourcePeak i) +
          R.cuspPartialLaw.real (R.cuspSourceRemainder i)) + R.cuspFlowPeakMean r) := by
    simpa only [hkernel, R.cuspPartialLaw_mass_head r hW hr, R.cuspPartialLaw_mass_peak i hinside,
      R.cuspPartialLaw_mass_remainder i, ← hsum, add_assoc] using
      R.cuspPartial_charge_row_head r hW hd hgap hr
  have hrowI := R.cuspPartial_charge_row_peak r i hW hd hgap hr hinside
  have hrowJ := R.cuspPartial_charge_row_remainder r i hW hd hgap hr
  have hcross := R.cuspPartial_charge_cross_remainder_peak r i hW hd hgap hr hinside
  have hinternal := R.cuspPartial_charge_cross_remainder_remainder i
  have hhole := R.cusp_source_hole_identity r i hW hd hgap hr hinside
  rw [hmissing, ← hsum] at hhole
  obtain ⟨child, hchild, hcost, hscore⟩ := exists_child_with_cusp_score
    R.cuspPartialModel (R.cuspPartialModel_fullFeasible hW.full)
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.measurable_adjacency W m)
    (PhysicalRepresentative.adjacency_symm W m) hg.1 S.collapsedPartLabel
    S.measurable_collapsedPartLabel {x | S.ρ x = r.val} (R.cuspSourcePeak i)
    (R.cuspSourceRemainder i) (S.hfibers r.val r.property).1
    (R.measurableSet_cuspSourcePeak i) (R.measurableSet_cuspSourceRemainder i)
    hPI hPJ (R.cuspSource_disjoint_peak_remainder i) ha hz hg.2.1 hg.2.2.1
    (hg.2.2.2.mono (fun _ hx => hx.1)) (hg.2.2.2.mono (fun _ hx => hx.2))
    a e (-m) (2 * (c - m * d) + m)
    (R.cuspFlowPeakMean r) (R.cuspPeakCredit r i) (R.cuspRemainderCredit r i)
    (R.cuspCrossEnergy i) (R.cuspRemainderEnergy i) (R.cuspRemainderMissing i)
    (kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.cuspPartialFlow))
    (R.cuspDensityDrop d) hcurrent hrowP
    (by simpa only [hkernel, R.cuspPartialLaw_mass_head r hW hr,
      R.cuspPartialLaw_mass_peak i hinside] using hrowI)
    (by simpa only [hkernel, R.cuspPartialLaw_mass_head r hW hr,
      R.cuspPartialLaw_mass_remainder i] using hrowJ)
    (by simpa only [hkernel, R.cuspPartialLaw_mass_peak i hinside,
      R.cuspPartialLaw_mass_remainder i] using hcross)
    (by simpa only [hkernel, R.cuspPartialLaw_mass_remainder i] using hinternal)
    (by simpa only [R.cuspPartialLaw_mass_head r hW hr, R.cuspPartialLaw_mass_peak i hinside,
      R.cuspPartialLaw_mass_remainder i, cuspOutsideSquares] using hhole)
  rw [R.cuspPartialLaw_halfMass r i hW hr hinside] at hcost hscore
  rw [R.cuspPartialLaw_mass_head r hW hr, R.cuspPartialLaw_mass_peak i hinside,
    R.cuspPartialLaw_mass_remainder i, hheight] at hscore
  have hpow : (R.height / 2) ^ 2 = R.height ^ 2 / 4 := by ring
  exact ⟨child, hchild, by simpa only [hpow, cuspOutsideSquares] using hcost,
    by simpa only [hpow, cuspOutsideSquares] using hscore⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

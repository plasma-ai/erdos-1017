module

public import Erdos1017.Exclusions.Common.ControlledDiffuseAtomization
public import Erdos1017.Exclusions.Common.Flows.FullForwardSharpSelector
public import Erdos1017.SelectedModel.SelectedHeadPeak

/-!
# Diffuse high-section cap on the sharp middle cell

Small diffuse rerouting and atomization retain the sharp middle-cell square
price at every admissible target mass, with the shifted energy paid by the same
flow (`middle_diffuse_high_excess_sharp_sq_bound`); a strict scalar margin gives
an almost-everywhere cap on the diffuse high section
(`ae_middle_diffuse_high_outside_le`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

private theorem diffuse_middle_sharp_budget (S : SelectedHighLowStructure W m)
    {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hret : S.forwardClassMass q i = S.originalAtomMass i)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (C : Set Ω) (hC : MeasurableSet C) (hCD : C ⊆ S.D)
    (b : ℝ) (hb : 0 < b) (hmass : (missingFlowEndpointLaw μ q).real C = b)
    (hbA : b ≤ S.originalAtomMass i) :
    2 * (c - m * d) + m +
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) +
      (-m - 2 / 3) * (1 - 2 * density hq.endpoint - (S.originalAtomMass i) ^ 2 + b ^ 2) ≤
      (-1 + 8 * S.originalAtomMass i - (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 +
        ∫ p : Ω × Ω in C ×ˢ C, shiftedKernel W m p.1 p.2
          ∂(missingFlowEndpointLaw μ q).prod (missingFlowEndpointLaw μ q) := by
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  let A := S.originalAtomMass i
  have hApos : 0 < A := by dsimp only [A]; linarith only [hA.1]
  have hCdust := hCD.trans S.diffuse_subset_collapsed_dust
  have hCpos : 0 < (missingFlowEndpointLaw μ q) C := by
    have hp : 0 < (missingFlowEndpointLaw μ q).real C := by rw [hmass]; exact hb
    exact ENNReal.toReal_pos_iff.mp hp |>.1
  obtain ⟨V, hV, hAdj, _, hDen, hObj⟩ := DustAtomization.exists_model
    hq.endpoint (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel
    S.measurable_collapsedPartLabel (by
      filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp)
    C hC hCpos hCdust
  let labels := MultipartiteDustAtomization.atomizedLabels S.collapsedPartLabel C
  have hlabels := MultipartiteDustAtomization.measurable_atomizedLabels
    S.collapsedPartLabel S.measurable_collapsedPartLabel C hC
  have hmassOld (j : S.I) :
      MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q) labels (.inl j) =
        S.forwardClassMass q j := by
    simp only [MultipartiteClassMasses.classMass, labels,
      MultipartiteDustAtomization.atomized_old_fiber S.collapsedPartLabel C hCdust,
      forwardClassMass]
  have hmassNew (u : Unit) :
      MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q) labels (.inr u) = b := by
    cases u
    simpa only [MultipartiteClassMasses.classMass, labels,
      MultipartiteDustAtomization.atomized_new_fiber] using hmass
  have hp := hq.classMass_properties
  have hbdd : BddAbove (insert (0 : ℝ) (range (S.forwardClassMass q))) := by
    refine ⟨1, ?_⟩
    rintro y (rfl | ⟨j, rfl⟩)
    · norm_num
    · exact (hp.1 j).2
  have hmax (j : S.I) : S.forwardClassMass q j ≤ S.forwardClassMass q i := by
    rw [← (hpeak q hq).2.1]
    exact le_csSup hbdd (Or.inr (mem_range_self j))
  have hnewMax (j : S.I ⊕ Unit) :
      MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q) labels j ≤
        MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q) labels (.inl i) := by
    cases j with
    | inl j => simpa only [hmassOld] using hmax j
    | inr u => simpa only [hmassNew, hmassOld, hret] using hbA
  have hnewPos : 0 <
      MultipartiteClassMasses.classMass (missingFlowEndpointLaw μ q) labels (.inl i) := by
    simpa only [hmassOld, hret] using hApos
  obtain ⟨_, hmiddle, _⟩ := MultipartiteClassMasses.objective_sharp_countCells
    V hV labels hlabels (by
      filter_upwards [] with p
      have hp := hAdj p
      split_ifs at hp ⊢ <;> exact hp) (.inl i) hnewPos hnewMax
  rw [hmassOld, hret] at hmiddle
  have hT : (1 - A) / A ∈ Icc (2 : ℝ) 3 := by
    constructor
    · apply (le_div_iff₀ hApos).mpr
      linarith only [hA.2]
    · apply (div_le_iff₀ hApos).mpr
      linarith only [hA.1]
  have hcost := hmiddle hT
  have hid : 2 * (A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12) -
      (-m) * A ^ 2 = (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 := by
    field_simp
    ring
  have hcharge := hq.endpoint_diffuse_internal_charge hW hd hgap C hC hCD
  rw [hmass] at hDen hcharge
  have hbudget := hq.endpoint_budget hW
  change 2 * (c - m * d) + m + _ +
    (-m - 2 / 3) * (1 - 2 * density hq.endpoint - A ^ 2 + b ^ 2) ≤ _
  nlinarith only [hcost, hid, hObj, hDen, hcharge, hbudget]

/-- Actual small diffuse rerouting and atomization retain the sharp
middle-cell square price at every legal target mass. The internal shifted
energy is paid by the same flow energy before its error tends to zero. -/
theorem middle_diffuse_high_excess_sharp_sq_bound (S : SelectedHighLowStructure W m)
    (i : S.I) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3)) (hell : 2 / 3 ≤ -m)
    (b : ℝ) (hb : 0 < b) (hbA : b ≤ S.originalAtomMass i)
    (hpositive : 0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x})) :
    2 * (c - m * d) + m + (-m - 2 / 3) * b ^ 2 ≤
      (-1 + 8 * S.originalAtomMass i - (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  apply le_of_forall_pos_le_add
  intro ε hε
  have hscale : 0 < 8 * b := mul_pos (by norm_num) hb
  obtain ⟨C, J, θ, hC, hJ, hCp, hCD, hCH, hJL, hJI, hzero, hsmall, hθ, hu, hCb, hkeep⟩ :=
    hq.exists_selected_small_diffuse_rerouting hW hd hgap b (ε / (8 * b)) hb
      (div_pos hε hscale) hpositive
  let u := fun p => (1 - θ) * q p + θ * MissingFlow.redirect μ q C J p
  have hstill : ∀ᵐ p ∂μ.prod μ, u p ≠ 0 → S.ρ p.1 ≠ i := hkeep i havoid
  have hret := hu.classMass_eq_original_of_avoids_nonlow i hnonlow hstill
  have hbudget := S.diffuse_middle_sharp_budget hu i hW hd hgap hpeak hret hA
    C hC hCD b hb hCb hbA
  have hp := hu.classMass_properties
  have hsq : Summable (fun j => (S.forwardClassMass u j) ^ 2) :=
    hp.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      nlinarith only [(hp.1 j).1, (hp.1 j).2])
  have hsingle := (hsq.le_tsum i (fun _ _ => sq_nonneg _)).trans_eq
    (hu.missing_density_eq_classMass_sq hW hd hgap).symm
  rw [hret] at hsingle
  change (S.originalAtomMass i) ^ 2 ≤ 1 - 2 * density hu.endpoint at hsingle
  have htail := mul_nonneg (sub_nonneg.mpr hell) (sub_nonneg.mpr hsingle)
  have herror := hq.diffuse_endpoint_energy_le_flow_energy_add_error hW hd hgap
    C J hC hJ hCp hCD hCH hJL hJI hzero θ ⟨hθ.1.le, hθ.2.le⟩ b hCb
  rw [hu.endpoint_internal_kernel_integral (shiftedKernel W m) C hC] at hbudget
  have hsmall' : 8 * b * (μ.real C + ∫ x in C, MissingFlow.receipt μ q x ∂μ) < ε := by
    have h := mul_lt_mul_of_pos_left hsmall hscale
    exact h.trans_eq (mul_div_cancel₀ ε hscale.ne')
  nlinarith only [hbudget, htail, herror, hsmall']

/-- A strict scalar margin turns the actual controlled comparison into
an AE diffuse HIGH section cap, without an additional original gamma guard. -/
theorem ae_middle_diffuse_high_outside_le (S : SelectedHighLowStructure W m)
    (i : S.I) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3)) (hell : 2 / 3 ≤ -m)
    {R : ℝ} (hR : 0 < R) (hRA : R ≤ S.originalAtomMass i)
    (hmargin : (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 <
      2 * (c - m * d) + m + (-m - 2 / 3) * R ^ 2) :
    ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → S.outsideSectionMass x ≤ R := by
  have hnull : μ (S.D ∩ S.H ∩ {x | R < S.outsideSectionMass x}) = 0 := by
    by_contra hn
    have hbudget := S.middle_diffuse_high_excess_sharp_sq_bound i hW hd hgap hpeak
      hnonlow hA hell R hR hRA (pos_iff_ne_zero.mpr hn)
    exact (not_lt_of_ge hbudget) hmargin
  have hnot : ∀ᵐ x ∂μ, x ∉ S.D ∩ S.H ∩ {x | R < S.outsideSectionMass x} :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hnot] with x hx hxD hxH
  exact le_of_not_gt (fun h => hx ⟨⟨hxD, hxH⟩, h⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure

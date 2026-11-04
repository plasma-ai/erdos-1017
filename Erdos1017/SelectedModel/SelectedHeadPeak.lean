module

public import Erdos1017.SelectedModel.Flows.FullForwardPeakAtom
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterHeadPrice
public import Erdos1017.Exclusions.Common.SelectedRootRows

/-!
# Common forward peaks as recovered heads

This module defines `IsCommonForwardPeak` and shows that a common peak surviving
as a reverse head is neutral, hence a universal atom with vanishing reverse
marginals, retaining its original mass and satisfying the two-head square
budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual common-forward-peak property uses the same original label
at every genuine full forward endpoint. -/
def IsCommonForwardPeak (S : SelectedHighLowStructure W m) (d c : ℝ) (r : S.I) : Prop :=
  ∀ q, S.IsFullForwardFlow q → 0 < S.forwardClassMass q r ∧
    ForwardPeak.massPeak (S.forwardClassMass q) = S.forwardClassMass q r ∧
    ForwardPeak.IsSeparatedPeak (S.forwardClassMass q) (forwardPeakGap d c m) r

/-- A neutral original whole atom has no outside zero pairs. This is a
product-AE statement, obtained from the actual neutral section masses. -/
theorem ae_neutral_not_zeroRelation (S : SelectedHighLowStructure W m) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.N → p ∉ actualZeroRelation W m S.ρ := by
  have hmeas : MeasurableSet {p : Ω × Ω |
      p.1 ∈ S.N → p ∉ actualZeroRelation W m S.ρ} := by
    convert (S.hpartition.2.2.1.preimage measurable_fst).compl.union
      (measurableSet_actualZeroRelation W m S.ρ S.hρ).compl using 1
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
    tauto
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [S.hneutral] with x hx
  by_cases hN : x ∈ S.N
  · have hn : ∀ᵐ y ∂μ, (x, y) ∉ actualZeroRelation W m S.ρ := by
      exact (ae_iff.mpr (by simpa only [not_not] using hx hN))
    exact hn.mono (fun _ hy _ => hy)
  · exact Eventually.of_forall (fun _ hi => False.elim (hN hi))

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- A neutral whole atom is universal outside its own independent fiber.
No values at exceptional representatives are selected. -/
theorem neutral_atom_adjacency (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val then 0 else 1 := by
  have hf := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hN
  have hz := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp
    (S.root_row_zero_on_fiber r)
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [S.ae_neutral_not_zeroRelation,
    Measure.quasiMeasurePreserving_fst.ae hf,
    Measure.quasiMeasurePreserving_snd.ae hz,
    S.ae_kernel_eq_fiber_row r.val r.property, hW.moment_mem, hs]
    with p hn hf hz hr hk hg hpr
  change adjacencyKernel W p.1 p.2 = if 0 < shiftedKernel W m p.1 p.2 then 1 else 0 at hg
  by_cases hsame : S.ρ p.2 = r.val
  · have hzero : shiftedKernel W m p.1 p.2 = 0 := (hr hpr).trans (hz hsame)
    rw [hg, hzero]
    simp only [lt_irrefl, ite_false, hsame, ite_true]
  · have hpos : 0 < shiftedKernel W m p.1 p.2 := by
      apply lt_of_le_of_ne hk.1
      intro he
      exact hn (hf hpr) ⟨he.symm, fun h => hsame (h.symm.trans hpr)⟩
    rw [hg]
    simp only [hpos, ite_true, hsame, ite_false]

namespace ReverseRecovery

variable {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- An actual common peak that survives as a reverse head must be neutral:
reverse eligibility excludes HIGH, and positive forward mass excludes LOW. -/
theorem common_peak_head_neutral (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hpeak : S.IsCommonForwardPeak d c r) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N := by
  rcases S.eligibleReverseAtom_low_or_neutral r (R.plateau_eligible r hr) with hL | hN
  · have hp := (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).1
    rw [S.forwardFlow_isFullForwardFlow.classMass_eq_zero_of_low r hL] at hp
    exact False.elim (lt_irrefl _ hp)
  · exact hN

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- Both actual reverse marginals vanish on a neutral original fiber. -/
theorem reverse_marginals_zero_on_neutral (r : S.I)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ, S.ρ x = r.val →
      MissingFlow.receipt μ R.flow x = 0 ∧ MissingFlow.supply μ R.flow x = 0 := by
  have hf := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hN
  filter_upwards [hf, R.isFullReverseFlow.receipt_zero_off_low, R.isFullReverseFlow.supply]
    with x hf hr hs hx
  have hn := hf hx
  have hL : x ∉ S.L := fun h => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 h hn
  have hH : x ∉ S.H := fun h => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 h hn
  exact ⟨hr hL, hs.trans (indicator_of_notMem hH _)⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- A recovered common head peak retains exactly its original mass. -/
theorem common_peak_head_mass (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hpeak : S.IsCommonForwardPeak d c r) :
    μ.real {x | S.ρ x = r.val} = R.height := by
  have hm := R.reverse_marginals_zero_on_neutral r (R.common_peak_head_neutral r hr hpeak)
  have he := MissingFlow.endpoint_real_set_eq_original R.flow R.isFullReverseFlow.integrable
    R.isFullReverseFlow.nonnegative R.isFullReverseFlow.supply_le_one
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
    (hm.mono (fun _ h hx => (h hx).1)) (hm.mono (fun _ h hx => (h hx).2))
  have ht := (R.classMass_eq_iff hW r).mpr hr
  rw [reverseClassMass, S.collapsedPartLabel_fiber r, he] at ht
  exact ht

/-- The actual two-head reverse budget gives the original head-peak
square bound. Its energy and physical mass cap are derived internally. -/
theorem common_peak_head_square_budget (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c r)
    (hcard : R.plateau.card = 2) :
    2 * (c - m * d) + m ≤ 2 * (1 + m) * (μ.real {x | S.ρ x = r.val}) ^ 2 := by
  have hb := R.isFullReverseFlow.plateau_budget hW hd hgap R.plateau R.height
    (R.classMass_le hW) (fun i hi => (R.classMass_eq_iff hW i).mpr hi)
  rw [hcard] at hb
  norm_num only [Nat.cast_ofNat] at hb
  rw [R.common_peak_head_mass r hr hW hpeak]
  nlinarith [R.isFullReverseFlow.energy_nonnegative hW hd hgap]

/-- A common peak that is a recovered head is an original universal atom. -/
theorem common_peak_head_adjacency (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c r) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val then 0 else 1 :=
  S.neutral_atom_adjacency r hW hd hgap (R.common_peak_head_neutral r hr hpeak)

/-- The two-center head-peak mass bound has its positive denominator
derived from the actual recovered two-center budget. -/
theorem common_peak_head_mass_sq_lower (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c r)
    (hcard : R.plateau.card = 2)
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    (2 * (c - m * d) + m) / (2 * (1 + m)) ≤
      (μ.real {x | S.ρ x = r.val}) ^ 2 := by
  have hp := R.two_center_parameters hW hd hgap hcard hintercept
  apply (div_le_iff₀ (show 0 < 2 * (1 + m) by linarith [hp.2.1])).mpr
  nlinarith only [R.common_peak_head_square_budget r hr hW hd hgap hpeak hcard]

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure

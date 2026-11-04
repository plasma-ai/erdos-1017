module

public import Erdos1017.Exclusions.Common.Flows.FullForwardSharpSelector
public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence
public import Erdos1017.SelectedModel.SelectedHeadPeak

/-!
# Closed missing-mass cap on the sharp middle cell

A peak-avoiding endpoint on the sharp middle count cell bounds the original
gamma, dropping only its nonnegative tail-square term
(`middle_common_peak_sharp_gap_bound`), and redirecting such a flow to a
distinct high atom keeps its entire closed missing mass as a paid endpoint
square (`middle_high_atom_closed_missing_sq_bound`).
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

private theorem middle_peak_sharp_tail_budget (S : SelectedHighLowStructure W m)
    {q : Ω × Ω → ℝ} (hq : S.IsFullForwardFlow q) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hret : S.forwardClassMass q i = S.originalAtomMass i)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3)) :
    0 ≤ 1 - 2 * density hq.endpoint - (S.originalAtomMass i) ^ 2 ∧
      2 * (c - m * d) + m + (-m - 2 / 3) *
        (1 - 2 * density hq.endpoint - (S.originalAtomMass i) ^ 2) ≤
        (-1 + 8 * S.originalAtomMass i - (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  let A := S.originalAtomMass i
  have hApos : 0 < A := by dsimp only [A]; linarith only [hA.1]
  have hp := hq.classMass_properties
  have hbdd : BddAbove (insert (0 : ℝ) (range (S.forwardClassMass q))) := by
    refine ⟨1, ?_⟩
    rintro y (rfl | ⟨j, rfl⟩)
    · norm_num
    · exact (hp.1 j).2
  have hmax (j : S.I) : S.forwardClassMass q j ≤ S.forwardClassMass q i := by
    rw [← (hpeak q hq).2.1]
    exact le_csSup hbdd (Or.inr (mem_range_self j))
  obtain ⟨_, hσ, _, _, hmiddle, _⟩ :=
    hq.endpoint_sharp_selector_bounds hW hd hgap i (hpeak q hq).1 hmax
  rw [hret] at hσ hmiddle
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
  have henergy := hq.energy_nonnegative hW hd hgap
  have hbudget := hq.endpoint_budget hW
  refine ⟨hσ, ?_⟩
  change 2 * (c - m * d) + m + (-m - 2 / 3) *
    (1 - 2 * density hq.endpoint - A ^ 2) ≤ _
  nlinarith only [hcost, hid, henergy, hbudget]

/-- An actual peak-avoiding endpoint on the sharp middle count cell
bounds the original gamma. Only its nonnegative tail-square term is dropped. -/
theorem middle_common_peak_sharp_gap_bound (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3)) (hell : 2 / 3 ≤ -m) :
    2 * (c - m * d) + m ≤
      (-1 + 8 * S.originalAtomMass i - (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hret := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  obtain ⟨hσ, hbudget⟩ := S.middle_peak_sharp_tail_budget hq i hW hd hgap hpeak hret hA
  have htail := mul_nonneg (sub_nonneg.mpr hell) hσ
  linarith only [hbudget, htail]

/-- Redirecting an actual peak-avoiding flow to a distinct HIGH atom
retains its entire original closed missing mass as a paid endpoint square.
The sharp count cell gives coefficient ell-2/3 without a supplied resource cap. -/
theorem middle_high_atom_closed_missing_sq_bound (S : SelectedHighLowStructure W m)
    (i j : S.I) (hji : j ≠ i)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3)) (hell : 2 / 3 ≤ -m) :
    2 * (c - m * d) + m + (-m - 2 / 3) *
      (S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)) ^ 2 ≤
      (-1 + 8 * S.originalAtomMass i - (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hredirect := hq.atomRedirect_of_stationary hW j j.property hhigh
  have hne : (j : Lp ℝ 2 μ) ≠ i := fun he => hji (Subtype.ext he)
  have hstill := S.atomRedirect_avoids j i hne q havoid
  have hret := hredirect.classMass_eq_original_of_avoids_nonlow i hnonlow hstill
  have hmassJ : S.forwardClassMass (S.atomRedirect j q) j =
      S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
    rw [S.forwardClassMass_eq_fiber]
    exact hq.atomRedirect_endpoint_mass hW j j.property hhigh
  have hp := hredirect.classMass_properties
  have hsq : Summable (fun k => (S.forwardClassMass (S.atomRedirect j q) k) ^ 2) :=
    hp.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => by
      nlinarith only [(hp.1 k).1, (hp.1 k).2])
  have htwo := (hsq.sum_le_tsum {i, j} (fun _ _ => sq_nonneg _)).trans_eq
    (hredirect.missing_density_eq_classMass_sq hW hd hgap).symm
  rw [Finset.sum_pair hji.symm, hret, hmassJ] at htwo
  change (S.originalAtomMass i) ^ 2 +
    (S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)) ^ 2 ≤
      1 - 2 * density hredirect.endpoint at htwo
  obtain ⟨_, hbudget⟩ := S.middle_peak_sharp_tail_budget
    hredirect i hW hd hgap hpeak hret hA
  have htail := mul_le_mul_of_nonneg_left htwo (sub_nonneg.mpr hell)
  nlinarith only [hbudget, htail]

end Erdos1017.CappedModel.SelectedHighLowStructure

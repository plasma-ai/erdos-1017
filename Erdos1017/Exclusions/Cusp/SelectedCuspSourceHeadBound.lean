module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourcePeakGuards

/-!
# Sharpened reverse-head bound from two squares

Keeping both distinct original squares in the same reserve sharpens the
reverse-head bound; at the fifth cusp this gives `b < A/2`
(`cusp_source_head_sq_bound`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- Retaining both distinct original squares in the same reserve sharpens
the reverse-head bound. At the fifth cusp this gives b<A/2. -/
theorem cusp_source_head_sq_bound (R : S.ReverseRecovery) (r i : S.I)
    (k : ℕ) (hk : 4 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) :
    ((k : ℝ) - 1) * (S.originalAtomMass r) ^ 2 < (S.originalAtomMass i) ^ 2 := by
  obtain ⟨hd, hslope, hell, _, hmargin⟩ :=
    hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  obtain ⟨hhead, hsquare, _⟩ :=
    R.cusp_source_peak_guards r i k hk hdk hW hgap hglobal hr hinside hpeak
  have hri : r ≠ i := by intro heq; subst i; exact lt_irrefl _ hhead
  obtain ⟨hDelta, j, _, _, hj, _, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have htwo : (S.originalAtomMass r) ^ 2 + (S.originalAtomMass i) ^ 2 ≤
      ∑' j, (S.originalAtomMass j) ^ 2 := by
    simpa only [Finset.sum_pair hri] using Summable.sum_le_tsum (s := {r, i})
      (fun j _ => sq_nonneg (S.originalAtomMass j)) S.originalAtomMass_sq_summable
  have hweighted := mul_le_mul_of_nonneg_left htwo (show 0 ≤ -m by linarith [hell.1])
  have hdelta : 0 < 2 - 2 / (k : ℝ) + m := by linarith [hslope.2]
  have hblock := mul_le_mul_of_nonneg_left hsquare hdelta.le
  rw [mul_one_div] at hblock
  have hcombined : (2 - 2 / (k : ℝ) + m) *
      (S.originalAtomMass r + S.originalAtomMass i) ^ 2 +
      (-m) * ((S.originalAtomMass r) ^ 2 + (S.originalAtomMass i) ^ 2) <
      2 * (S.originalAtomMass i) ^ 2 := by
    linarith only [hblock, hweighted, hmargin, hreserve]
  have hcross := mul_nonneg hdelta.le
    (mul_nonneg (measureReal_nonneg : 0 ≤ S.originalAtomMass r)
      (measureReal_nonneg : 0 ≤ S.originalAtomMass i))
  change 0 ≤ (2 - 2 / (k : ℝ) + m) *
    (S.originalAtomMass r * S.originalAtomMass i) at hcross
  have hscalar : (2 - 2 / (k : ℝ)) * (S.originalAtomMass r) ^ 2 <
      (2 / (k : ℝ)) * (S.originalAtomMass i) ^ 2 := by
    nlinarith only [hcombined, hcross]
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hscaled := mul_lt_mul_of_pos_left hscalar (by positivity : 0 < (k : ℝ) / 2)
  have hleft : (k : ℝ) / 2 * (2 - 2 / (k : ℝ)) = (k : ℝ) - 1 := by
    field_simp
  have hright : (k : ℝ) / 2 * (2 / (k : ℝ)) = 1 := by field_simp
  simpa only [← mul_assoc, hleft, hright, one_mul] using hscaled

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

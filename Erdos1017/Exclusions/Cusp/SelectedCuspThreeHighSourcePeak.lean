module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeHighSourceAccounting
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeHighTailCap
public import Erdos1017.Exclusions.Cusp.CuspThreeHighSourcePayment
public import Erdos1017.Exclusions.Cusp.CorrelatedSourceLoss

/-!
# No high-slope source peak at the third cusp

At the third cusp with own penalty at least one, the original common peak cannot
lie in the entire source of the singleton recovery; every resource, trace, child
score and price premise is derived (`no_cusp_three_high_source_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- At the third cusp with own penalty at least one, the original common
peak cannot lie in the singleton recovery's entire source. Every resource,
trace, child score and price premise comes from the same original model. -/
theorem no_cusp_three_high_source_peak (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : 1 ≤ -m)
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) : False := by
  let T := R.height
  let X := S.originalAtomMass i / T
  let t := μ.real (R.cuspSourceRemainder i) / T
  let y := (1 / 9 : ℝ) / T ^ 2
  let q := R.cuspOutsideSquares r i / T ^ 2
  let e := (c - 2 / 27) / T ^ 2
  let V := kernelEnergy (μ := μ) (shiftedKernel W m)
    (MissingFlow.direction μ R.cuspPartialFlow) / T ^ 2
  let cI := R.cuspPeakCredit r i / T
  let CJ := R.cuspRemainderCredit r i / T ^ 2
  let Phi := R.cuspCrossEnergy i / T
  let FJ := R.cuspRemainderEnergy i / T ^ 2
  let root := Real.sqrt (t ^ 2 + 2 * X * t)
  let L := max (max (1 / 2 - X) 0 / X) (max (max (1 / 2 - t) 0 / t)
    ((max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t) * (root - t) + 1 - t) / root))
  obtain ⟨hX, ht, hsum, _, hy, hpenalty, hq, _, hreserve, hhole⟩ :=
    R.cusp_three_high_source_normalized_guards r i hdk hW hgap hglobal hell hr hinside hpeak
  change 0 < X at hX
  change 0 < t at ht
  change X + t < 1 at hsum
  change y ∈ Ioo (16 / 25 : ℝ) 1 at hy
  change 0 ≤ q at hq
  change (4 / 3 + m) * y < (2 + m) * X ^ 2 at hreserve
  change 1 - t ^ 2 - 2 * X * t ≤ y at hhole
  obtain ⟨he, hV, hcI, hCJ, hPhi, hFJ, htrace, hbudget, C, hcost, hscore⟩ :=
    R.exists_cusp_three_high_normalized_child r i hdk hW hgap hglobal hell hr hinside hpeak
  change 0 < e at he
  change 0 ≤ V at hV
  change 0 ≤ cI at hcI
  change 0 ≤ CJ at hCJ
  change 0 ≤ Phi at hPhi
  change 0 ≤ FJ at hFJ
  change FJ / 2 ≤ (t + root) / 2 * Phi at htrace
  change e + V / 2 + (X * cI + CJ + X * Phi + FJ / 2) ≤
    ((4 / 3 + m) * (1 - y) - (-m - 1) * q) / 2 at hbudget
  change C ≤ max (1 / 4) q at hcost
  change C - 1 / 4 = e + V / 2 + (4 / 3 + m) * y / 2 + (-m - 1) / 4 +
    (-m) * q / 2 - ((1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
      ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t)) at hscore
  have hqhalf := R.cusp_three_high_outsideSquares_lt_half r hdk hW hgap hglobal hell hr
  rw [← R.cuspOutsideSquares_eq_whole r i] at hqhalf
  change q < 1 / 2 at hqhalf
  have hpayment := CuspThreeHighSourcePayment.source_payment_sqrt hX ht hsum hy.1 hy.2
    hell hpenalty.2 hq hqhalf (by simpa only [sub_neg_eq_add] using hreserve) hhole
  simp only [sub_neg_eq_add] at hpayment
  change L * ((4 / 3 + m) * (1 - y) - (-m - 1) * q) / 2 ≤
    (4 / 3 + m) * y / 2 + (-m - 1) / 4 + (-m) * q / 2 - max (q - 1 / 4) 0 at hpayment
  have hloss := CorrelatedSourceLoss.source_loss_le_sqrt hX ht hcI hCJ hPhi hFJ htrace
  change (1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
      ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t) ≤
    L * (X * cI + CJ + X * Phi + FJ / 2) at hloss
  have hL : 0 ≤ L :=
    (div_nonneg (le_max_right _ _) hX.le).trans (le_max_left _ _)
  have hpaid := mul_le_mul_of_nonneg_left hbudget hL
  have hstrict : 0 < (1 + L) * (e + V / 2) :=
    mul_pos (by linarith only [hL]) (by linarith only [he, hV])
  have hmax : max (q - 1 / 4) 0 = max (1 / 4) q - 1 / 4 := by
    by_cases hqsmall : q ≤ 1 / 4
    · rw [max_eq_right (by linarith), max_eq_left hqsmall]
      ring
    · rw [max_eq_left (by linarith), max_eq_right (le_of_not_ge hqsmall)]
  nlinarith only [hpaid, hpayment, hloss, hscore, hcost, hstrict, hmax]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

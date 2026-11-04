module

public import Erdos1017.Exclusions.Cusp.SelectedCuspFourSourceAccounting
public import Erdos1017.Exclusions.Cusp.CuspFourSourcePeakPayment
public import Erdos1017.Exclusions.Cusp.CorrelatedSourceLoss

/-!
# No source peak at the fourth cusp

At the fourth reciprocal cusp, the original common peak cannot lie in the entire
source of the singleton recovery; every resource, trace, child score and price
premise is derived (`no_cusp_four_source_peak`).
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

/-- At the fourth reciprocal cusp, the original common peak cannot lie in the
singleton recovery's entire source. Every resource, trace, child score and price
premise comes from the same original model, and the reciprocal slope identity
`(-m - 1) / 2 * (4 * (1 + ρ)) = 1` is derived from the actual multiplier. -/
theorem no_cusp_four_source_peak (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 15 / 32) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) : False := by
  let T := R.height
  let X := S.originalAtomMass i / T
  let t := μ.real (R.cuspSourceRemainder i) / T
  let y := (1 / 16 : ℝ) / T ^ 2
  let ρ := (3 / 2 + m) / (-m - 1)
  let q := R.cuspOutsideSquares r i / T ^ 2
  let e := (c - 3 / 64) / T ^ 2
  let V := kernelEnergy (μ := μ) (shiftedKernel W m)
    (MissingFlow.direction μ R.cuspPartialFlow) / T ^ 2
  let cI := R.cuspPeakCredit r i / T
  let CJ := R.cuspRemainderCredit r i / T ^ 2
  let Phi := R.cuspCrossEnergy i / T
  let FJ := R.cuspRemainderEnergy i / T ^ 2
  let root := Real.sqrt (t ^ 2 + 2 * X * t)
  let L := max (max (1 / 2 - X) 0 / X) (max (max (1 / 2 - t) 0 / t)
    ((max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t) * (root - t) + 1 - t) / root))
  have hdk' : d = (1 - 1 / (4 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  have hell : -m ∈ Ioo (11 / 10 : ℝ) (3 / 2) := by
    have h := (hW.cusp_contact_parameters 4 (by norm_num) hdk' hgap hglobal).2.1
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hden : 0 < -m - 1 := by linarith only [hell.1]
  obtain ⟨hX, ht, hsum, hhead, hy, hρ, hq, hqmax, hqH, hreserve, hhole⟩ :=
    R.cusp_four_source_normalized_guards r i hdk hW hgap hglobal hr hinside hpeak
  change 0 < X at hX
  change 0 < t at ht
  change X + t < 1 at hsum
  change (1 - t) / 2 < X at hhead
  change y ∈ Ioo (2 / 5 : ℝ) 1 at hy
  change ρ ∈ Ioo (0 : ℝ) 4 at hρ
  change 0 ≤ q at hq
  change q < ρ * (1 - y) at hqmax
  change q < 5 / 2 * y - 1 at hqH
  change ρ * y < (1 + 2 * ρ) * X ^ 2 at hreserve
  change 1 - t ^ 2 - 2 * X * t ≤ y at hhole
  obtain ⟨he, hV, hcI, hCJ, hPhi, hFJ, htrace, hbudget, C, hcost, hscore⟩ :=
    R.exists_cusp_four_normalized_child r i hdk hW hgap hglobal hr hinside hpeak
  change 0 < e at he
  change 0 ≤ V at hV
  change 0 ≤ cI at hcI
  change 0 ≤ CJ at hCJ
  change 0 ≤ Phi at hPhi
  change 0 ≤ FJ at hFJ
  change FJ / 2 ≤ (t + root) / 2 * Phi at htrace
  change e + V / 2 + (X * cI + CJ + X * Phi + FJ / 2) ≤
    (-m - 1) / 2 * (ρ * (1 - y) - q) at hbudget
  change C ≤ max (1 / 4) q at hcost
  change C - 1 / 4 = e + V / 2 + (-m - 1) / 2 * (ρ * y + 1 / 2 + (3 + 2 * ρ) * q) -
    ((1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
      ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t)) at hscore
  have hpayment := CuspFourSourcePeakPayment.payment_nonneg_sqrt hX ht hsum hhead hy.1 hy.2
    hρ.1 hρ.2 hq hqmax.le hqH.le hreserve hhole
  change 0 ≤ ρ * y + 1 / 2 + (3 + 2 * ρ) * q - 4 * (1 + ρ) * max (q - 1 / 4) 0 -
    L * (ρ * (1 - y) - q) at hpayment
  have hloss := CorrelatedSourceLoss.source_loss_le_sqrt hX ht hcI hCJ hPhi hFJ htrace
  change (1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
      ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t) ≤
    L * (X * cI + CJ + X * Phi + FJ / 2) at hloss
  have hL : 0 ≤ L :=
    (div_nonneg (le_max_right _ _) hX.le).trans (le_max_left _ _)
  have hslope : (-m - 1) / 2 * (4 * (1 + ρ)) = 1 := by
    dsimp only [ρ]
    field_simp
    ring
  have hpaid := mul_le_mul_of_nonneg_left hbudget hL
  have hprice := mul_nonneg (by linarith only [hden] : (0 : ℝ) ≤ (-m - 1) / 2) hpayment
  have hstrict : 0 < (1 + L) * (e + V / 2) :=
    mul_pos (by linarith only [hL]) (by linarith only [he, hV])
  have hmax : max (q - 1 / 4) 0 = max (1 / 4) q - 1 / 4 := by
    by_cases hqsmall : q ≤ 1 / 4
    · rw [max_eq_right (by linarith), max_eq_left hqsmall]
      ring
    · rw [max_eq_left (by linarith), max_eq_right (le_of_not_ge hqsmall)]
  have hoverflow : (-m - 1) / 2 * (4 * (1 + ρ)) * max (q - 1 / 4) 0 =
      max (q - 1 / 4) 0 := by
    rw [hslope, one_mul]
  nlinarith only [hpaid, hprice, hloss, hscore, hcost, hstrict, hmax, hoverflow]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

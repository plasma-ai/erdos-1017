module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeDominantInventory
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopeUniversal
public import Erdos1017.Exclusions.Cusp.CuspThreeDominantPayment

/-!
# No dominant missing atom at the low-slope third cusp

A designated original atom cannot dominate the entire missing region of a
selected low-slope third-cusp peak; the remainder is paid by one marked edit
(`no_cusp_three_dominant_missing_atom`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

/-- A designated original atom cannot dominate the entire missing region
of a selected low-slope third-cusp peak. The literal remainder is paid by
one actual marked edit, and every copy moment uses its original body. -/
theorem no_cusp_three_dominant_missing_atom (S : SelectedHighLowStructure W m) (i j : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hdom : μ.real (S.cuspThreeMissingRegion i \ S.cuspThreeDominantAtom i j) ≤
      μ.real (S.cuspThreeDominantAtom i j) / 20) : False := by
  let P := S.cuspThreeDominantAtom i j
  let J := S.cuspThreeMissingRegion i
  let D := S.rootNeighborhood i
  let U := S.cuspThreeDominantSource i j
  let N := D ∩ S.rootNeighborhood j
  let A := S.originalAtomMass i
  let b := μ.real P
  let r := μ.real (J \ P)
  let t := μ.real J
  let tau := μ.real U
  let n := μ.real N
  let ell := -m
  let gamma := 2 * (c - m * d) + m
  let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) Dᶜ
  let Z := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) Dᶜ
  let H := ∫ p : Ω × Ω, (Z p.1 p.2) ^ 2 ∂μ.prod μ
  let X := ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ
  let L := ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ
  let C := ∫ p in U ×ˢ N, max (PhysicalRepresentative.charge W m p.1 p.2) 0 ∂μ.prod μ
  let R := ∫ p in U ×ˢ D, max (PhysicalRepresentative.charge W m p.1 p.2) 0 ∂μ.prod μ
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1) :=
    fun huniv => S.no_cusp_three_low_slope_universal_peak i hdk hW hgap hglobal hell hpeak huniv
  obtain ⟨hells, hA, _⟩ := S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
  change ell ∈ Ioo (5 / 6 : ℝ) 1 at hells
  change 11 / 39 < A at hA
  obtain ⟨ht, _, hAt, _, _⟩ :=
    S.cusp_three_low_slope_missing_region i hdk hW hgap hglobal hell hpeak hnonuniv
  change 0 < t at ht
  change A + t < 1 / 3 at hAt
  have hmass := S.cusp_three_dominant_masses i j
  change b + r = t ∧ n ≤ 1 - A - b at hmass
  have hr : 0 ≤ r := measureReal_nonneg
  change r ≤ b / 20 at hdom
  have hb : 0 < b := by linarith only [ht, hmass.1, hdom]
  have hAb : A + b ≤ 1 / 3 := by linarith only [hAt, hmass.1, hr]
  have hgamma : (4 / 3 - ell) / 9 ≤ gamma := by
    have hmargin := (hW.split_cusp_gamma_margin 3 (by norm_num) (by norm_num [hdk]) hgap hglobal).2
    norm_num at hmargin
    change (4 / 3 - -m) / 9 ≤ 2 * (c - m * d) + m
    linarith only [hmargin]
  have htau := S.cusp_three_dominant_source_pos i j hdk hW hgap hglobal hell hpeak hnonuniv hb
  change 0 < tau at htau
  have hn : 0 ≤ n := measureReal_nonneg
  have hH0 : 0 ≤ H := integral_nonneg (fun _ => sq_nonneg _)
  have hH := S.cusp_three_dominant_missing_body_square_le i j hW hd hgap
  change H ≤ 1 - 2 * d - (A + b) ^ 2 at hH
  rw [hdk] at hH
  norm_num at hH
  have hbody := S.cusp_three_dominant_body_moments i j
  change 0 ≤ X ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ R ∧ R + C ≤ L ∧ 2 * C ≤ L ∧
    L ^ 2 ≤ X ∧ 2 * C ^ 2 ≤ tau * n * X at hbody
  obtain ⟨_, hL, hC, _, hRC, htwoC, hLsq, hCauchy⟩ := hbody
  have hpay := S.cusp_three_dominant_atom_payment i j hW hd hgap
  change (ell * b - r) * tau ≤ R at hpay
  have hcoef : 0 < ell * b - r := by
    have hmul := mul_lt_mul_of_pos_right hells.1 hb
    nlinarith only [hmul, hdom, hb]
  have hRpos : 0 < R := (mul_pos hcoef htau).trans_le hpay
  have hLpos : 0 < L := by linarith only [hRpos, hRC, hC]
  have hXpos : 0 < X := (sq_pos_of_pos hLpos).trans_le hLsq
  have htrace := S.cusp_three_dominant_positive_body_trace i j hW hd hgap hXpos
  change (A - Real.sqrt (2 * H)) * X + (gamma - r) * L ≤ 2 * b * C at htrace
  exact CuspThreeDominantPayment.dominant_payment_contradiction hA.le hb hr hdom hAb hells hgamma
    htau hn hmass.2 hH0 hH hC hL hXpos (by linarith only [hRC]) htwoC hpay htrace hCauchy

end Erdos1017.CappedModel.SelectedHighLowStructure

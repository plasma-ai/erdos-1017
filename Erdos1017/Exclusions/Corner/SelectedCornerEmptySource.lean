module

public import Erdos1017.Certificates.EmptySatCorner.EmptySatCornerScalar
public import Erdos1017.Certificates.EmptySatCorner.EmptySatCornerMoments
public import Erdos1017.Certificates.EmptySatCorner.EmptySatCornerCertificates
public import Erdos1017.Certificates.EmptySatCorner.EmptySatCornerHardCertificates
public import Erdos1017.Exclusions.Common.E2.EmptySatE2Scalar
public import Erdos1017.Exclusions.Corner.SelectedCornerZeroBody
public import Erdos1017.Exclusions.Common.SelectedEmptySourceExit
public import Erdos1017.SelectedModel.SelectedBodyEnergy
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairBlocks
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic
public import Erdos1017.Exclusions.Common.E2.SelectedEmptySatE2Inventory
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerBadRegion
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerSourceGeometry
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitTangents
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateRootStar
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerContextPrice
public import Erdos1017.SelectedModel.Structure.L1KernelTangent
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Exclusion of the corner recovery with empty source

A singleton corner recovery with null source is impossible: the saturated
sectors are excluded, the hard nonexceptional sector spending the one negative
quota and the private-source moments through the coupled moment certificates,
and both saturation alternatives are excluded.
-/

@[expose] public section

noncomputable section

set_option Elab.async false

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.EmptySatCorner

private theorem exceptional_excess_le_six {δ A E L r u h di : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A))
    (hr : r ∈ Icc (0 : ℝ) E) (hEL : E < L)
    (hu : u ≤ cornerBadCap δ A E) (hh : 23 / 100 ≤ h)
    (hden : 0 < 1 - u - 2 * h)
    (htangent : δ * (A + E) * (A + E - u - r) ≤ di * (1 - u - 2 * h))
    (hrow : (L - E + 2 * r) * di ≤ δ * r) : L - E ≤ 6 * r := by
  let D := A + E
  let Ubad := cornerBadCap δ A E
  let Rbad := 1 - Ubad - 23 / 50
  let g0 := D - Ubad - r
  obtain ⟨_, hgap, hR, hstock, _⟩ := exceptional_guards hδ hA hE
  have hδ0 : 0 < δ := by linarith only [hδ.1]
  have hD0 : 0 ≤ D := by dsimp only [D]; linarith only [hA.1, hE.1]
  have hR0 : 0 < Rbad := by dsimp only [Rbad, Ubad]; linarith only [hR]
  have hgap0 : 0 < A - Ubad := by dsimp only [Ubad]; linarith only [hgap]
  have hg0 : A - Ubad ≤ g0 := by dsimp only [g0, D]; linarith only [hr.2]
  have hDhi : D < 27 / 50 := by
    have hcap : D ≤ cornerDeficitCap δ := by dsimp only [D]; linarith only [hE.2]
    have hfrac : 0 < 37 / (1250 * δ) := by positivity
    unfold cornerDeficitCap at hcap
    linarith only [hcap, hfrac]
  have hcompare : g0 * (1 - u - 2 * h) ≤ Rbad * (D - u - r) := by
    have hid : Rbad * (D - u - r) - g0 * (1 - u - 2 * h) =
        (Ubad - u) * (1 - D + r - 23 / 50) + 2 * (h - 23 / 100) * g0 := by
      dsimp only [Rbad, g0]
      ring
    have hp := mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ 1 - D + r - 23 / 50 by linarith only [hDhi, hr.1])
    have hq := mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ g0 by linarith only [hg0, hgap0])
    nlinarith only [hid, hp, hq]
  have htanR := mul_le_mul_of_nonneg_left htangent hR0.le
  have hcomparison := mul_le_mul_of_nonneg_left hcompare (mul_nonneg hδ0.le hD0)
  have hlower : δ * D * g0 ≤ di * Rbad := by
    apply (mul_le_mul_iff_right₀ hden).mp
    dsimp only [D] at *
    nlinarith only [htanR, hcomparison]
  have hstock' : Rbad < 8 * D * g0 := by
    have hp := mul_le_mul_of_nonneg_left hg0 (show 0 ≤ 8 * D by positivity)
    dsimp only [D, Ubad, Rbad] at *
    linarith only [hstock, hp]
  have hdi : δ / 8 < di := by
    by_contra hn
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hR0.le
    have hscaled := mul_lt_mul_of_pos_left hstock' hδ0
    nlinarith only [hp, hscaled, hlower]
  have hcoef : 0 < L - E + 2 * r := by linarith only [hEL, hr.1]
  have hp := mul_lt_mul_of_pos_right hdi hcoef
  have hsmall : δ * (L - E - 6 * r) < 0 := by nlinarith only [hp, hrow]
  by_contra hn
  have hnonneg := mul_nonneg hδ0.le (show 0 ≤ L - E - 6 * r by linarith only [hn])
  linarith only [hsmall, hnonneg]

private theorem exceptional_raw_price_pos {δ A E L r Z b s u h : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A))
    (hr : r ∈ Icc (0 : ℝ) E) (hEL : E ≤ L)
    (hLmax : L ≤ 2 - 5 * A - E) (hLr : L ≤ E + 6 * r)
    (hb : b = 1 - A - (A + E) - L) (hb0 : 0 ≤ b)
    (hs : s - L = A + E - u) (hu : u ≤ cornerBadCap δ A E)
    (hZ : Z ≤ δ * (E + r) / 2)
    (hcorr : 37 / 1250 < δ * (1 - (A + E) - 2 * h)) :
    0 < EmptySatE2.rawExceptionalScore δ h A (A + E) r Z +
      4 * δ * b * (s - L - r) := by
  have hδ0 : 0 ≤ δ := by linarith only [hδ.1]
  have hδpos : 0 < δ := by linarith only [hδ.1]
  have hD0 : 0 ≤ A + E := by linarith only [hA.1, hE.1]
  have hDhi : A + E < 27 / 50 := by
    have hfrac : 0 < 37 / (1250 * δ) := by positivity
    unfold cornerDeficitCap at hE
    linarith only [hE.2, hfrac]
  have hv0 : 0 ≤ EmptySatE2.baseDifference A (A + E) := by
    unfold EmptySatE2.baseDifference
    linarith only [hA.1, hE.1]
  have hvhi : EmptySatE2.baseDifference A (A + E) ≤ 29 / 100 := by
    unfold EmptySatE2.baseDifference
    linarith only [hA.2, hDhi]
  have hmv : (2 - δ) * EmptySatE2.baseDifference A (A + E) ≤ 29 / 50 := by
    have hp := mul_le_mul_of_nonneg_right (show 2 - δ ≤ 2 by linarith only [hδ.1]) hv0
    linarith only [hp, hvhi]
  have hEhi : E ≤ 19 / 100 := by linarith only [hDhi, hA.1]
  have hδE : δ * E ≤ (2 / 5 : ℝ) * (19 / 100) :=
    mul_le_mul hδ.2 hEhi hE.1 (by norm_num)
  have hrex : (δ - 23 / 12) * r ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hδ.2]) hr.1
  have hargbase : EmptySatE2.baseCredit δ A (A + E) - 23 * r / 12 +
      δ * (E + r) ≤ 2 * A := by
    unfold EmptySatE2.baseCredit
    nlinarith only [hmv, hδE, hrex, hD0, hA.1]
  let Zmax := δ * (E + r) / 2
  have harg : EmptySatE2.baseCredit δ A (A + E) - 23 * r / 12 + Z + Zmax ≤ 2 * A := by
    dsimp only [Zmax]
    linarith only [hargbase, hZ]
  have hcoef : 0 ≤ 4 * A - (48 / 25) *
      (EmptySatE2.baseCredit δ A (A + E) - 23 * r / 12 + Z + Zmax) := by
    linarith only [harg, hA.1]
  have hdiff : EmptySatE2.rawExceptionalScore δ h A (A + E) r Z -
      EmptySatE2.rawExceptionalScore δ h A (A + E) r Zmax =
        (Zmax - Z) * (4 * A - (48 / 25) *
          (EmptySatE2.baseCredit δ A (A + E) - 23 * r / 12 + Z + Zmax)) := by
    unfold EmptySatE2.rawExceptionalScore
    ring
  have hnonneg := mul_nonneg (show 0 ≤ Zmax - Z from sub_nonneg.mpr hZ) hcoef
  have hraw : EmptySatE2.exceptionalScore δ h A (A + E) r ≤
      EmptySatE2.rawExceptionalScore δ h A (A + E) r Z := by
    change EmptySatE2.rawExceptionalScore δ h A (A + E) r
      (δ * (A + E - A + r) / 2) ≤ _
    have he : A + E - A = E := by ring
    rw [he]
    linarith only [hdiff, hnonneg]
  have hprice := exceptional_price_pos hδ hA hE hr hEL hLmax hLr
  have hidentity : EmptySatE2.rawExceptionalScore δ h A (A + E) r Z +
      4 * δ * b * (s - L - r) - cornerExceptionalPrice δ A E L r =
        (EmptySatE2.rawExceptionalScore δ h A (A + E) r Z -
          EmptySatE2.exceptionalScore δ h A (A + E) r) +
          (δ * (1 - (A + E) - 2 * h) - 37 / 1250) +
            4 * δ * b * (cornerBadCap δ A E - u) := by
    rw [cornerExceptionalPrice_eq_score δ h A E L r, hb]
    linear_combination 4 * δ * (1 - A - (A + E) - L) * hs
  have hdebit : 0 ≤ 4 * δ * b * (cornerBadCap δ A E - u) :=
    mul_nonneg (mul_nonneg (by linarith only [hδ0]) hb0) (sub_nonneg.mpr hu)
  linarith only [hprice, hidentity, hdebit, hcorr, hraw]

end Erdos1017.EmptySatCorner

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem wholeRowDegree_eq_rootNeighborhood
    (S : SelectedHighLowStructure W m) (r : S.I) :
    wholeRowDegree r.val = μ.real (S.rootNeighborhood r) := by
  have hN := S.measurableSet_rootNeighborhood r
  have heq : (fun x => if 0 < (r.val : Ω → ℝ) x then (1 : ℝ) else 0) =ᵐ[μ]
      (S.rootNeighborhood r).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [S.ae_rootNeighborhood_iff r] with x hx
    by_cases hr : 0 < (r.val : Ω → ℝ) x
    · simp [hr, (hx.mpr hr)]
    · simp [hr, (not_iff_not.mpr hx).mpr hr]
  rw [wholeRowDegree, integral_congr_ae heq]
  exact integral_indicator_one hN

private theorem exceptional_atomic_tangent_data
    (S : SelectedHighLowStructure W m) (r p i : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (hip : i ≠ p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hwhole : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.universalPartnerHoleRegion r p)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val → adjacencyKernel W q.1 q.2 =
      if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    {di : ℝ} (hdef : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      S.universalRootDeficit r x = di) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let s := μ.real (S.universalPartnerHoleRegion r p)
    let a := S.originalAtomMass i
    0 < 4 * d - 2 + A + b + s ∧
      (1 - m - 4 * (c - m * d)) * (s - a) ≤ di * (4 * d - 2 + A + b + s) := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hdis : Disjoint I P := disjoint_left.mpr (fun _ hi hp =>
    hip (Subtype.ext (hi.symm.trans hp)))
  have hNeq : S.rootNeighborhood i =ᵐ[μ] (I ∪ P)ᶜ :=
    (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate).mono
      (fun _ hx => propext (by simpa only [I, P, mem_compl_iff, mem_union,
        mem_ofPred_eq, not_or] using hx))
  have hdegI : wholeRowDegree i.val = 1 - S.originalAtomMass i - S.originalAtomMass p := by
    rw [wholeRowDegree_eq_rootNeighborhood S i, measureReal_congr hNeq,
      measureReal_compl (hI.union hP), probReal_univ, measureReal_union hdis hP]
    change 1 - (S.originalAtomMass i + S.originalAtomMass p) =
      1 - S.originalAtomMass i - S.originalAtomMass p
    ring
  have hdegR : wholeRowDegree r.val = 1 - S.originalAtomMass r := by
    rw [wholeRowDegree_eq_rootNeighborhood S r]
    exact S.neutral_rootNeighborhood_mass r hW hd hgap hN
  have hdegP : wholeRowDegree p.val = 1 - S.originalAtomMass p -
      μ.real (S.universalPartnerHoleRegion r p) := by
    rw [wholeRowDegree_eq_rootNeighborhood S p]
    exact S.universal_partner_neighborhood_mass r p hpair hW hd hgap
  obtain ⟨_, hden, htan⟩ :=
    hpair.universal_atomic_deficit_tangent i hW hd hgap hell hN hwhole
  have hdi : (μ.real I)⁻¹ * ∫ x in I, S.universalRootDeficit r x ∂μ = di := by
    rw [integral_congr_ae hdef, setIntegral_const, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (show μ.real I ≠ 0 from
        (ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ I)).ne'), one_mul]
  rw [hdegI, hdegR, hdegP, hdi] at htan
  rw [hdegR, hdegP] at hden
  have hden' : 0 < 4 * d - 2 + S.originalAtomMass r + S.originalAtomMass p +
      μ.real (S.universalPartnerHoleRegion r p) := by linarith only [hden]
  refine ⟨hden', ?_⟩
  have htan' := (div_le_iff₀ hden).mp htan
  nlinarith only [htan']

private theorem exceptional_support_with_debit (S : SelectedHighLowStructure W m)
    (r p i : S.I) (hpair : S.IsSaturatedAtomPair r p) (hir : i ≠ r) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (_hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (_hwhole : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.universalPartnerHoleRegion r p)
    (di : ℝ) (hdef : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      S.universalRootDeficit r x = di)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val → adjacencyKernel W q.1 q.2 =
      if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let a := S.originalAtomMass i
    let s := μ.real (S.universalPartnerHoleRegion r p)
    let U := A + a + b
    let v := A - a - b
    let T := (1 + m) * U - 2 * (2 * (c - m * d) + m)
    let Z := a * di
    (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T -
      (1 - U) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - U) / 12 + 2 * Z) 0 ^ 2 -
        4 * A * Z + 4 * (1 + m) * b * (s - a) ≤ 0 := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let C := {x | S.ρ x = i.val}
  let K := (I ∪ P ∪ C)ᶜ
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let a := S.originalAtomMass i
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let U := A + a + b
  let v := A - a - b
  let T := (1 + m) * U - 2 * (2 * (c - m * d) + m)
  let Z := a * di
  let HI := (∫ q, PhysicalRepresentative.charge W m q.1 q.2
    ∂(μ.restrict I).prod (μ.restrict K)) / A
  let CK := FiniteCappedSamplingCost.physicalObjective (μ.restrict K)
    (PhysicalRepresentative.charge W m)
  let Q := ∫ q, (1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true
    then (1 : ℝ) else 0) ∂(μ.restrict K).prod (μ.restrict K)
  obtain ⟨hHI, hCK, hQ, hmass⟩ :=
    S.empty_sat_exceptional_inventory r p i hpair hir hip hW hd hgap hN di hdef hprivate
  change HI = 2 * (c - m * d) + m - a - b - m * A + a * di at hHI
  change CK = c - (A + b + a) * (2 * (c - m * d)) -
    m * (A + b + a - A ^ 2 - b ^ 2 - b * s - a * (a + b)) +
      A * b + A * a * (1 - di) at hCK
  change Q = 1 - 2 * d - A ^ 2 - b ^ 2 - a ^ 2 - 2 * b * s at hQ
  change μ.real K = 1 - A - b - a at hmass
  have hK : MeasurableSet K :=
    (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).union
      (S.hfibers i.val i.property).1).compl
  have hdis : Disjoint I K := disjoint_left.mpr (fun _ hx hy => hy (Or.inl (Or.inl hx)))
  have hsupport := S.universal_restriction_support_price r hW hd hgap hN K hK hdis
  change CK ≤ (μ.real K) ^ 2 / 48 + Q / 2 - (12 / 25) *
    max (HI - μ.real K / 24) 0 ^ 2 at hsupport
  have hmass' : μ.real K = 1 - U := by dsimp only [U]; linarith only [hmass]
  rw [hmass'] at hsupport
  have henergy : 4 * (CK - Q / 2) =
      (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T +
        4 * (1 + m) * b * (s - a) - 4 * A * Z := by
    rw [hCK, hQ]
    dsimp only [U, v, T, Z]
    ring
  have harg : (1 - m) * v - T - (1 - U) / 12 + 2 * Z =
      2 * (HI - (1 - U) / 24) := by
    rw [hHI]
    dsimp only [U, v, T, Z]
    ring
  have hmax : max ((1 - m) * v - T - (1 - U) / 12 + 2 * Z) 0 =
      2 * max (HI - (1 - U) / 24) 0 := by
    rw [harg]
    by_cases hx : 0 ≤ HI - (1 - U) / 24
    · rw [max_eq_left hx, max_eq_left (mul_nonneg (by norm_num) hx)]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_right (by linarith only [le_of_not_ge hx])]
      ring
  change (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T -
    (1 - U) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - U) / 12 + 2 * Z) 0 ^ 2 -
      4 * A * Z + 4 * (1 + m) * b * (s - a) ≤ 0
  rw [hmax]
  nlinarith only [hsupport, henergy]

private theorem bad_region_stock_nonneg
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m))
    (hnegative : 0 < μ (S.universalNegativeRegion r p)) :
    0 ≤ 1 - 3 * S.originalAtomMass r + S.originalAtomMass p := by
  let B := S.universalUpperE2BadRegion r p d c
  have hBpos : 0 < μ B := hnegative.trans_le (measure_mono
    (S.universalNegativeRegion_subset_upperE2Bad r p d c
      (by linarith only [hA]) hmargin (by linarith only [hell.2])))
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hBpos.ne'
    (P.ae_universalUpperE2Bad_originalDegree_ge S r p hpair hW hd hgap
      hN hA hAhalf hell hmargin)
  have hxint : Integrable (adjacencyKernel W x) μ := by
    have hm := (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
      (measurable_const.prodMk measurable_id : Measurable (fun y : Ω => (x, y)))
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall (fun y => by
      have hy := adjacency_moment_mem W (x, y)
      change adjacencyKernel W x y ∈ Icc (0 : ℝ) 1 at hy
      change ‖adjacencyKernel W x y‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg hy.1]
      exact hy.2)
  have hbound := integral_mono_ae hxint (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun y => (adjacency_moment_mem W (x, y)).2))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hbound
  linarith only [hx, hbound]

private theorem exceptional_deficit_row
    (S : SelectedHighLowStructure W m) (r p i : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hwhole : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.universalPartnerHoleRegion r p)
    {di : ℝ} (hdef : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      S.universalRootDeficit r x = di)
    (hkzero : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      S.universalPartnerCommonMissingMass r p x = 0) :
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real (S.universalPartnerHoleRegion r p) +
      μ.real (S.universalPartnerCommonRegion r p) - D
    let E := D - S.originalAtomMass r
    let e := S.originalAtomMass i - L
    (L - E + 2 * e) * di ≤ (1 + m) * e := by
  let H := S.universalPartnerHoleRegion r p
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  have hdelta : 0 < 1 + m := by linarith only [hell]
  have hratio : (1 + m) * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hdelta.ne'
  have hrow := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
    (S.ae_universalPartnerHole_deficit_row r p hpair hW hd hgap hell hN)
  have hmass := S.ae_hole_missing_mass_eq_originalAtomMass_on_whole_fiber
    r p i hpair hW hd hgap hell hwhole
  obtain ⟨x, _, hxH, hxd, hxk, hxrow, hxa⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae (S.hfibers i.val i.property).2.1.ne'
      (hwhole.and (hdef.and (hkzero.and ((ae_restrict_of_ae hrow).and hmass))))
  have hr := hxrow hxH
  have hB := S.universalPartnerCommonMissingDeficit_ge_floor r p hpair hW hd hgap hell hN x
  rw [hxa, hxd, hxk] at hr
  rw [hxk] at hB
  dsimp only
  dsimp only [D] at hratio
  nlinarith only [hr, hB, hratio]

end Erdos1017.CappedModel.SelectedHighLowStructure

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- An actual corner singleton with null entire source cannot have an
unsaturated original head. Its own slope, universal row, positive body,
triangle margin and actual physical quota are all derived internally. -/
theorem no_corner_unsaturated_empty_source (R : S.ReverseRecovery)
    (r : S.I) (hr : R.plateau = {r})
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hnosat : ∀ p : S.I, p ≠ r → ¬S.IsSaturatedAtomPair r p) : False := by
  let A := μ.real {x | S.ρ x = r.val}
  let gamma := 2 * (c - m * d) + m
  obtain ⟨hell, hc, hh, hfloor⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hsq := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  change c ≤ A ^ 2 at hsq
  have hA : 1 / 3 < A := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hA0
      (sub_nonpos.mpr (le_of_not_gt hn))
    nlinarith only [hc, hsq, hp]
  have hmargin := EmptySatCorner.contact_margin hell hA hfloor
  have hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1 := by
    filter_upwards [S.ae_saturated_pair_has_saturated_atom_block hW hd hgap
      (show -m < 1 by linarith only [hell.2])] with p hp hr _
    have hne : chargeKernel W p.1 p.2 ≠ 1 := by
      intro he
      obtain ⟨a, u, hau, ha, _⟩ := hp he
      have har : a = r := Subtype.ext (ha.symm.trans hr)
      subst a
      exact hnosat u hau.1.symm hau
    exact lt_of_le_of_ne
      ((charge_moment_le_adjacency W p).trans (adjacency_moment_mem W p).2) hne
  have hquota := R.empty_source_unsaturated_objective_le_half_root_quota r hr hW hd hgap
    hnull hstar hA
    (show -m ∈ Ioo (1 / 2 : ℝ) 1 by constructor <;> linarith [hell.1, hell.2])
    (by simpa only [sub_neg_eq_add] using hmargin)
  have hnonnegative := bodyPositiveEnergy_nonnegative W {x | S.ρ x = r.val}
  have hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} := by
    apply lt_of_le_of_ne hnonnegative
    intro hzero
    exact S.no_corner_zero_body r hW hd hgap he heq hglobal hzero.symm
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap {x | S.ρ x = r.val}
    (S.hfibers r.val r.property).1] at hpositive
  have htrace := S.universal_positive_body_trace r hW hd hgap
    (R.empty_source_head_neutral r hr hW hd hgap hnull) hpositive
  exact EmptySatCorner.unsaturated_false hA0
    (hW.strict_gap_structure hd hgap).gamma_pos.le
    (by linarith only [hc]) (by linarith only [hh]) htrace hquota

/-- A null entire source at the corner leaves a strictly positive
saturated-partner hole and positive correlated excess. The nonpositive
excess sector is excluded by its actual signed restriction price. -/
theorem corner_saturated_empty_source_excess_pos (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    0 < 1 - S.originalAtomMass r - S.originalAtomMass p -
        (1 - m - 4 * (c - m * d)) / (1 + m) ∧
      0 < μ (S.universalPartnerHoleRegion r p) := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let delta := 1 + m
  let gamma := 2 * (c - m * d) + m
  let D := (1 - m - 4 * (c - m * d)) / delta
  let w := 2 * gamma / delta
  let X := A + b
  let V := A - b
  obtain ⟨hell, hc, hh, hfloor⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hdelta : delta ∈ Icc (2 / 11 : ℝ) (2 / 5) := by
    dsimp only [delta]
    constructor <;> linarith only [hell.1, hell.2]
  have hdelta0 : 0 < delta := by linarith only [hdelta.1]
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  have hnonnegative := bodyPositiveEnergy_nonnegative W {x | S.ρ x = r.val}
  have hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} := by
    apply lt_of_le_of_ne hnonnegative
    intro hzero
    exact S.no_corner_zero_body r hW hd hgap he heq hglobal hzero.symm
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap {x | S.ρ x = r.val}
    (S.hfibers r.val r.property).1] at hpositive
  have htrace := S.universal_positive_body_trace r hW hd hgap hN hpositive
  change 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 2 * (1 - 2 * d) at htrace
  have hgamma : 7 / 125 < gamma := by
    dsimp only [gamma]
    linarith only [hfloor, hell.2]
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hAhi : A < 3 / 8 := by
    by_contra hn
    have hge : 3 / 8 ≤ A := le_of_not_gt hn
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 8) hge 2
    have hp : (3 / 8 : ℝ) * (7 / 125) < A * gamma := by
      calc
        _ ≤ A * (7 / 125) := mul_le_mul_of_nonneg_right hge (by norm_num)
        _ < A * gamma := mul_lt_mul_of_pos_left hgamma (by linarith only [hge])
    have hgsq : (7 / 125 : ℝ) ^ 2 < gamma ^ 2 := by
      have hp := mul_pos (sub_pos.mpr hgamma)
        (show 0 < gamma + 7 / 125 by linarith only [hgamma])
      nlinarith only [hp]
    nlinarith only [htrace, hh, hsq, hp, hgsq]
  have hmass : A + b + s + u = 1 := S.universalPartner_regions_mass r p hpair.1
  have hratio : delta * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hdelta0.ne'
  have hsum : delta * (1 - D) = 2 * gamma := by
    dsimp only [delta, gamma] at *
    nlinarith only [hratio]
  have hwD : w = 1 - D := by
    dsimp only [w]
    apply (div_eq_iff hdelta0.ne').mpr
    nlinarith only [hsum]
  have hhole := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
  have hint : 0 ≤ ∫ x in S.universalPartnerHoleRegion r p,
      S.universalRootDeficit r x ∂μ :=
    integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  have hule : u ≤ D := by
    change (∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ) ≤
      1 - m - 4 * (c - m * d) - delta * u at hhole
    nlinarith only [hhole, hint, hratio, hdelta0]
  have hL : 0 < 1 - A - b - D := by
    by_contra hn
    have hLX : w ≤ X := by dsimp only [X]; rw [hwD]; linarith only [hn]
    have hhbox : 1 - 2 * d ∈ Icc (23 / 100 : ℝ) (467 / 2000) := by
      have hbox := (Benchmark.crossing_contact_location he heq).1
      constructor <;> linarith only [hbox.1, hbox.2]
    have hcorr : delta * (1 - 2 * d) + 37 / 2500 < gamma := by
      dsimp only [delta, gamma]
      linarith only [hc, hh]
    have hw : 2 * (1 - 2 * d) + 37 / (1250 * delta) < w := by
      dsimp only [w]
      apply (lt_div_iff₀ hdelta0).mpr
      have hid : (2 * (1 - 2 * d) + 37 / (1250 * delta)) * delta =
          2 * (1 - 2 * d) * delta + 37 / 1250 := by
        field_simp
      rw [hid]
      nlinarith only [hcorr]
    have hcircle := S.two_originalAtomMass_sq_le_missing_density r p hpair.1
    rw [hW.density_eq] at hcircle
    change A ^ 2 + b ^ 2 ≤ 1 - 2 * d at hcircle
    have hXhi : X < 137 / 200 := by
      have hX0 : 0 ≤ X := add_nonneg hA0 hb0
      have hcircle' : X ^ 2 ≤ 2 * (1 - 2 * d) := by
        dsimp only [X]
        nlinarith only [hcircle, sq_nonneg (A - b)]
      nlinarith only [hX0, hcircle', hhbox.2]
    have hpeak := R.empty_source_is_original_peak r hr hW hd hgap hnull
    have horder : b ≤ A := (hpeak.2 p hpair.1.symm).le
    have hV0 : 0 ≤ V := sub_nonneg.mpr horder
    have hVhi : V ≤ 3 / 4 - X := by dsimp only [V, X]; linarith only [hAhi]
    have hpos := EmptySatCorner.supportPolynomial_pos_of_nonpositive_excess hdelta
      hhbox hw hLX hXhi hV0 hVhi
    have hbudget := S.empty_sat_deleted_partner_support r p hpair hW hd hgap hN
    change delta * (X - 2 * (1 - 2 * d)) + 2 * m * V ^ 2 +
      (2 * X - 1) * (delta * X - 2 * gamma) - (1 - X) ^ 2 / 12 +
      (12 / 25) * max ((1 - m) * V - (delta * X - 2 * gamma) -
        (1 - X) / 12) 0 ^ 2 + 4 * delta * b * s ≤ 0 at hbudget
    have hwdelta : delta * w = 2 * gamma := by
      dsimp only [w]
      exact mul_div_cancel₀ _ hdelta0.ne'
    have hprice : EmptySatCorner.supportPolynomial delta (1 - 2 * d) X V
        (delta * (X - w)) + 4 * delta * b * s ≤ 0 := by
      unfold EmptySatCorner.supportPolynomial
      have hT : delta * (X - w) = delta * X - 2 * gamma := by
        nlinarith only [hwdelta]
      rw [hT]
      have hm : 1 - delta = -m := by dsimp only [delta]; ring
      have hm' : 2 - delta = 1 - m := by dsimp only [delta]; ring
      rw [hm, hm']
      nlinarith only [hbudget]
    have hdebit : 0 ≤ 4 * delta * b * s := by positivity
    linarith only [hpos, hprice, hdebit]
  refine ⟨hL, ?_⟩
  have hs : 0 < s := by linarith only [hL, hmass, hule]
  by_contra hn
  have hz : μ (S.universalPartnerHoleRegion r p) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  simp only [s, measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hs

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

namespace Erdos1017.EmptySatCorner

open EmptySatE2

private theorem small_delta_D_lt {delta D : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hD : D ≤ 27 / 50 - 37 / (1250 * delta)) : D < 2 / 5 := by
  have hdelta0 : 0 < delta := by linarith only [hdelta.1]
  have hscaled := mul_le_mul_of_nonneg_left hD hdelta0.le
  have hid : delta * (37 / (1250 * delta)) = 37 / 1250 := by field_simp
  nlinarith only [hscaled, hid, hdelta0, hdelta.2]

private theorem small_delta_baseCredit_pos {delta A D : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 2 / 5) :
    0 < baseCredit delta A D := by
  have hv : 1 / 20 ≤ baseDifference A D := by unfold baseDifference; linarith only [hA, hAD]
  have hm : 179 / 100 ≤ 2 - delta := by linarith only [hdelta.2]
  have hp := mul_le_mul_of_nonneg_right hm (show 0 ≤ baseDifference A D by linarith only [hv])
  unfold baseCredit
  nlinarith only [hv, hp, hD]

private theorem score_missing_mono (delta h h' A D L : ℝ)
    (hdelta : 0 ≤ delta) (hh : h ≤ h') :
    supportScore delta h' A D L ≤ supportScore delta h A D L := by
  have hid : supportScore delta h A D L - supportScore delta h' A D L =
      2 * delta * (h' - h) := by unfold supportScore baseScore; ring
  have hp := mul_nonneg hdelta (sub_nonneg.mpr hh)
  nlinarith only [hid, hp]

private theorem small_delta_score_excess_pos {delta A D : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * delta)))
    (hA : 7 / 20 ≤ A) (_hAD : A ≤ D) :
    0 < supportScore delta (467 / 2000) A D (D - A) := by
  have hbase := small_delta_support_endpoint_pos hdelta hD
  have hfactor : 0 ≤ 12 * delta * (A + 7 / 20 - 1 + D) + 4 * D - 1 := by
    have hp := mul_nonneg (show 0 ≤ 12 * delta by linarith only [hdelta.1])
      (show 0 ≤ A + 7 / 20 - 1 + D by linarith only [hA, hD.1])
    linarith only [hp, hD.1]
  have hid : supportScore delta (467 / 2000) A D (D - A) -
      supportScore delta (467 / 2000) (7 / 20) D (D - 7 / 20) =
        (4 * delta / 25) * (A - 7 / 20) *
          (12 * delta * (A + 7 / 20 - 1 + D) + 4 * D - 1) := by
    unfold supportScore baseScore baseCredit baseDifference
    ring
  have hp : 0 ≤ (4 * delta / 25) * (A - 7 / 20) *
      (12 * delta * (A + 7 / 20 - 1 + D) + 4 * D - 1) :=
    mul_nonneg (mul_nonneg (by linarith only [hdelta.1]) (sub_nonneg.mpr hA)) hfactor
  linarith only [hid, hp, hbase]

private theorem small_delta_supportScore_pos {delta h A D L : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * delta)))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hh : h ≤ 467 / 2000)
    (hL : 0 ≤ L) (hLE : L ≤ D - A) : 0 < supportScore delta h A D L := by
  have hbase := small_delta_score_excess_pos hdelta hD hA hAD
  have hv : 0 ≤ baseDifference A D := by unfold baseDifference; linarith only [hA, hAD]
  have hcoef : 0 ≤ 4 * (2 - delta) * baseDifference A D + 8 * D := by
    have hm : 0 ≤ 2 - delta := by linarith only [hdelta.2]
    have hD0 : 0 ≤ D := by linarith only [hD.1]
    positivity
  have hp := mul_nonneg hcoef (sub_nonneg.mpr hLE)
  have hsquare : L ^ 2 ≤ (D - A) ^ 2 := pow_le_pow_left₀ hL hLE 2
  have hmono := score_missing_mono delta h (467 / 2000) A D L
    (by linarith only [hdelta.1]) hh
  unfold supportScore at hbase hmono ⊢
  nlinarith only [hbase, hp, hsquare, hmono]

private theorem integrated_cubic_identity (delta h A D t : ℝ) :
    integratedScore delta h A D t =
      -(4 * delta) * t ^ 3 +
        (4 * delta * (1 - A - D) - 8 * (D - A) / 25) * t ^ 2 -
        (D - A) * ((4 * (2 - delta) * baseDifference A D + 8 * D) / 25) * t +
        (D - A) * baseScore delta h A D := by
  unfold integratedScore supportScore
  ring

private theorem small_delta_integratedScore_pos {delta h A D L : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * delta)))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hh : h ≤ 467 / 2000)
    (hEL : D - A < L) (hsquare : L ^ 2 ≤ (D - A) * D) :
    0 < integratedScore delta h A D L := by
  let E := D - A
  let B := 1 - A - D
  let p := (4 * (2 - delta) * baseDifference A D + 8 * D) / 25
  let M := Real.sqrt (E * D)
  have hDhi : D < 2 / 5 := small_delta_D_lt hdelta hD.2
  have hdelta0 : 0 < delta := by linarith only [hdelta.1]
  have hE0 : 0 ≤ E := sub_nonneg.mpr hAD
  have hL0 : 0 < L := lt_of_le_of_lt hE0 hEL
  have hE : 0 < E := by
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (show 0 ≤ D by linarith only [hD.1])
    nlinarith only [hp, hsquare, hL0]
  have hEhi : E ≤ 1 / 20 := by dsimp only [E]; linarith only [hA, hDhi]
  have hED : 0 ≤ E * D := mul_nonneg hE0 (by linarith only [hD.1])
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM2 : M ^ 2 = E * D := Real.sq_sqrt hED
  have hLM : L ≤ M := by nlinarith only [hsquare, hM2, hM0, hL0]
  have hEM : E ≤ M := hEL.le.trans hLM
  have hbase := small_delta_score_excess_pos hdelta hD hA hAD
  have hleft : 0 < integratedScore delta (467 / 2000) A D E := by
    have hnonneg : 0 ≤ 4 * delta * (1 - 2 * D) * E ^ 2 := by
      have hD' : 0 ≤ 1 - 2 * D := by linarith only [hDhi]
      positivity
    have hid : integratedScore delta (467 / 2000) A D E =
        E * supportScore delta (467 / 2000) A D E + 4 * delta * (1 - 2 * D) * E ^ 2 := by
      unfold integratedScore
      dsimp only [E]
      ring
    change 0 < supportScore delta (467 / 2000) A D E at hbase
    have hp := mul_pos hE hbase
    linarith only [hid, hp, hnonneg]
  have hsep := small_delta_radical_separation hdelta ⟨hD.1, hDhi.le⟩
    (show E ∈ Icc (0 : ℝ) (D - 7 / 20) by
      constructor
      · exact hE0
      · dsimp only [E]; linarith only [hA])
  let X0 := baseScore delta (467 / 2000) A D + 4 * delta * D * B - (8 / 25) * D * E
  let Y0 := p + 4 * delta * D
  have hAE : D - E = A := by dsimp only [E]; ring
  dsimp only at hsep
  rw [hAE] at hsep
  change 0 < X0 ∧ Y0 ^ 2 * D * E < X0 ^ 2 at hsep
  have hX : Y0 * M < X0 := by
    by_contra hn
    have hs := pow_le_pow_left₀ hsep.1.le (le_of_not_gt hn) 2
    have hmul := congrArg (fun z => Y0 ^ 2 * z) hM2
    nlinarith only [hs, hmul, hsep.2]
  have hrightId : integratedScore delta (467 / 2000) A D M = E * (X0 - Y0 * M) := by
    rw [integrated_cubic_identity]
    have hM3 : M ^ 3 = M * (E * D) := by rw [pow_succ, hM2]; ring
    rw [hM3, hM2]
    dsimp only [X0, Y0, p, B, E]
    ring
  have hright : 0 < integratedScore delta (467 / 2000) A D M := by
    rw [hrightId]
    exact mul_pos hE (sub_pos.mpr hX)
  have hv0 : 0 ≤ baseDifference A D := by unfold baseDifference; linarith only [hA, hAD]
  have hvhi : baseDifference A D ≤ 1 / 5 := by unfold baseDifference; linarith only [hAD, hDhi]
  have hmv : (2 - delta) * baseDifference A D ≤ 2 / 5 := by
    have hp := mul_le_mul_of_nonneg_right (show 2 - delta ≤ 2 by linarith only [hdelta.1]) hv0
    linarith only [hp, hvhi]
  have hp : p ≤ 24 / 125 := by dsimp only [p]; linarith only [hmv, hDhi]
  have hBE : 7 / 20 ≤ 2 * B - 3 * E := by dsimp only [B, E]; linarith only [hA, hDhi]
  have hprod : (2 / 11 : ℝ) * (7 / 20) ≤ delta * (2 * B - 3 * E) :=
    mul_le_mul hdelta.1 hBE (by norm_num) hdelta0.le
  have hslope : 0 ≤ -3 * (4 * delta) * E ^ 2 +
      2 * (4 * delta * B - 8 * E / 25) * E - E * p := by
    have hinner : 0 ≤ 4 * delta * (2 * B - 3 * E) - 16 * E / 25 - p := by
      linarith only [hprod, hp, hEhi]
    have hnonneg := mul_nonneg hE0 hinner
    nlinarith only [hnonneg]
  rw [integrated_cubic_identity] at hleft hright
  have hcubic := cubic_pos_between (E := E) (L := L) (M := M) (a := 4 * delta)
    (b := 4 * delta * B - 8 * E / 25) (c := -E * p)
    (d := E * baseScore delta (467 / 2000) A D)
    (show 0 ≤ 4 * delta by positivity) hEL.le hLM (by nlinarith only [hslope])
    (by dsimp only [E, B, p]; nlinarith only [hleft])
    (by dsimp only [E, B, p]; nlinarith only [hright])
  have hpoly : 0 < integratedScore delta (467 / 2000) A D L := by
    rw [integrated_cubic_identity]
    dsimp only [E, B, p] at hcubic
    nlinarith only [hcubic]
  have hmono := mul_le_mul_of_nonneg_left
    (score_missing_mono delta h (467 / 2000) A D L hdelta0.le hh) hE0
  unfold integratedScore
  unfold integratedScore at hpoly
  change E * supportScore delta (467 / 2000) A D L ≤ E * supportScore delta h A D L at hmono
  linarith only [hpoly, hmono]

private theorem exceptionalBaseScore_chord (δ h A a D : ℝ) :
    (D - a) * exceptionalBaseScore δ h A D =
      (D - A) * exceptionalBaseScore δ h a D +
        (A - a) * exceptionalBaseScore δ h D D -
        ((108 * δ ^ 2 - 38 * δ - 8) / 25) * (D - a) * (A - a) * (D - A) := by
  unfold exceptionalBaseScore baseScore baseCredit baseDifference
  ring

/-- Concavity and both certified endpoints pay the entire exceptional-atom head interval. -/
private theorem small_delta_exceptionalBaseScore_pos {δ A D : ℝ}
    (hdelta : δ ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D)
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ))) :
    0 < exceptionalBaseScore δ (467 / 2000) A D := by
  obtain ⟨hlo, hhi⟩ := small_delta_exceptional_endpoints_pos hdelta hD
  by_cases heq : D = 7 / 20
  · have hAe : A = 7 / 20 := by linarith
    simpa only [hAe] using hlo
  have hDa : 0 < D - 7 / 20 :=
    sub_pos.mpr (lt_of_le_of_ne (hA.trans hAD) (Ne.symm heq))
  have hδ := hdelta
  have hδ0 : 0 ≤ δ := by linarith [hδ.1]
  have hδsq := mul_self_le_mul_self hδ0 hδ.2
  have hcoef : (108 * δ ^ 2 - 38 * δ - 8) / 25 ≤ 0 := by
    nlinarith only [hδsq, hδ0]
  have hpos : 0 < (D - A) * exceptionalBaseScore δ
      (467 / 2000) (7 / 20) D +
        (A - 7 / 20) * exceptionalBaseScore δ
          (467 / 2000) D D := by
    by_cases hlt : A < D
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hlo)
        (mul_nonneg (sub_nonneg.mpr hA) hhi.le)
    · have hAe : A = D := le_antisymm hAD (le_of_not_gt hlt)
      rw [hAe]
      nlinarith only [mul_pos hDa hhi]
  have hnonpos : ((108 * δ ^ 2 - 38 * δ - 8) / 25) *
      (D - 7 / 20) * (A - 7 / 20) * (D - A) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hcoef hDa.le) (sub_nonneg.mpr hA))
      (sub_nonneg.mpr hAD)
  have he := exceptionalBaseScore_chord δ (467 / 2000)
    A (7 / 20) D
  exact (mul_pos_iff_of_pos_left hDa).mp (by linarith only [he, hpos, hnonpos])

private theorem exceptionalScore_difference (δ h A D e : ℝ) :
    exceptionalScore δ h A D e - exceptionalBaseScore δ h A D =
      e * (δ * (2 * (1 - 2 * D) + (4 + 24 * δ) * (D - A) / 25) + 2 * δ * e +
        (8 - 6 * δ - 24 * δ ^ 2) * (baseDifference A D - e / 2) / 25 +
        (8 - 2 * δ) * (D - e / 2) / 25) := by
  unfold exceptionalScore rawExceptionalScore exceptionalBaseScore baseScore baseCredit
    baseDifference
  ring

/-- The exceptional score increases from the certified zero-deficit endpoint. -/
private theorem small_delta_exceptionalScore_pos {δ A D e : ℝ}
    (hdelta : δ ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D)
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ)))
    (he : 0 ≤ e) (heE : e ≤ D - A) :
    0 < exceptionalScore δ (467 / 2000) A D e := by
  have hbase := small_delta_exceptionalBaseScore_pos hdelta hA hAD hD
  have hδ := hdelta
  have hDhi := (small_delta_D_lt hdelta hD.2).le
  have hδ0 : 0 ≤ δ := by linarith [hδ.1]
  have hδsq := mul_self_le_mul_self hδ0 hδ.2
  have hc₁ : 0 ≤ 8 - 6 * δ - 24 * δ ^ 2 := by
    nlinarith only [hδ.2, hδsq]
  have hc₂ : 0 ≤ 8 - 2 * δ := by linarith [hδ.2]
  have hv : 0 ≤ baseDifference A D - e / 2 := by unfold baseDifference; linarith
  have hDe : 0 ≤ D - e / 2 := by linarith
  have hinner : 0 ≤ 2 * (1 - 2 * D) + (4 + 24 * δ) * (D - A) / 25 := by
    have hp : 0 ≤ (4 + 24 * δ) * (D - A) / 25 :=
      div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hAD)) (by norm_num)
    linarith
  have hnonneg : 0 ≤ e * (δ *
      (2 * (1 - 2 * D) + (4 + 24 * δ) * (D - A) / 25) + 2 * δ * e +
      (8 - 6 * δ - 24 * δ ^ 2) * (baseDifference A D - e / 2) / 25 +
      (8 - 2 * δ) * (D - e / 2) / 25) := by positivity
  have hdiff := exceptionalScore_difference δ (467 / 2000)
    A D e
  linarith only [hbase, hnonneg, hdiff]

private theorem rawExceptionalScore_difference (δ h A D e Z Z' : ℝ) :
    rawExceptionalScore δ h A D e Z - rawExceptionalScore δ h A D e Z' =
      (Z' - Z) * (4 * A - (48 / 25) * (baseCredit δ A D - 23 * e / 12 + Z + Z')) := by
  unfold rawExceptionalScore
  ring

/-- Every allowed original exceptional deficit has a strictly positive restriction price. -/
private theorem small_delta_rawExceptionalScore_pos {δ A D e Z : ℝ}
    (hdelta : δ ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D)
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ)))
    (he : 0 ≤ e) (heE : e ≤ D - A) (hZ : Z ≤ δ * (D - A + e) / 2) :
    0 < rawExceptionalScore δ (467 / 2000) A D e Z := by
  have hbase := small_delta_exceptionalScore_pos hdelta hA hAD hD he heE
  have hδ := hdelta
  have hDhi := (small_delta_D_lt hdelta hD.2).le
  have hδ0 : 0 ≤ δ := by linarith [hδ.1]
  have hm : 0 ≤ 2 - δ := by linarith [hδ.2]
  have hv : 0 ≤ baseDifference A D := by unfold baseDifference; linarith
  have hvhi : baseDifference A D ≤ 1 / 5 := by unfold baseDifference; linarith
  have hmv : (2 - δ) * baseDifference A D ≤ 2 / 5 := by
    have hp := mul_le_mul_of_nonneg_right (show 2 - δ ≤ 2 by linarith) hv
    linarith
  have hE : D - A ≤ 1 / 20 := by linarith
  have hδE : δ * (D - A) ≤ (21 / 100 : ℝ) * (1 / 20) :=
    mul_le_mul hδ.2 hE (sub_nonneg.mpr hAD) (by norm_num)
  have hδe : δ * e ≤ (21 / 100 : ℝ) * (1 / 20) :=
    mul_le_mul hδ.2 (heE.trans hE) he (by norm_num)
  have hbound : baseCredit δ A D - 23 * e / 12 +
      δ * (D - A + e) ≤ 2 * A := by
    unfold baseCredit
    nlinarith only [hmv, hδE, hδe, he, hA, hAD]
  let Z' := δ * (D - A + e) / 2
  have harg : baseCredit δ A D - 23 * e / 12 + Z + Z' ≤ 2 * A := by
    dsimp only [Z']
    linarith only [hbound, hZ]
  have hcoef : 0 ≤ 4 * A - (48 / 25) *
      (baseCredit δ A D - 23 * e / 12 + Z + Z') := by
    linarith only [harg, hA]
  have hnonneg := mul_nonneg (show 0 ≤ Z' - Z by exact sub_nonneg.mpr hZ) hcoef
  have hdiff := rawExceptionalScore_difference δ
    (467 / 2000) A D e Z Z'
  change 0 < rawExceptionalScore δ (467 / 2000) A D e Z'
    at hbase
  linarith only [hbase, hnonneg, hdiff]

private theorem deleted_price_eq (δ h A D L s : ℝ) :
    let b := 1 - A - D - L
    let U := A + b
    let v := A - b
    let T := -δ * L
    δ * (U - 2 * h) - 2 * (1 - δ) * v ^ 2 + (2 * U - 1) * T -
      (1 - U) ^ 2 / 12 + (12 / 25) *
        (baseCredit δ A D + 23 * L / 12) ^ 2 + 4 * δ * b * s =
      supportScore δ h A D L + 4 * δ * b * (s - L) := by
  dsimp only
  unfold supportScore baseScore baseCredit baseDifference
  ring

private theorem exceptional_price_eq (δ h A D e Z : ℝ) :
    let U := 1 - D + e
    let v := baseDifference A D - e
    let T := δ * e
    δ * (U - 2 * h) - 2 * (1 - δ) * v ^ 2 + (2 * U - 1) * T -
      (1 - U) ^ 2 / 12 + (12 / 25) *
        (baseCredit δ A D - 23 * e / 12 + 2 * Z) ^ 2 - 4 * A * Z =
      rawExceptionalScore δ h A D e Z := by
  dsimp only
  unfold rawExceptionalScore baseCredit baseDifference
  ring

private theorem exceptional_square_pos {δ A D e Z : ℝ}
    (hδ : δ ∈ Icc (2 / 11 : ℝ) (21 / 100)) (hA : 7 / 20 ≤ A)
    (_hAD : A ≤ D) (hD : D ≤ 2 / 5) (he : 0 ≤ e) (heE : e ≤ D - A)
    (hZ : 0 ≤ Z) : 0 < baseCredit δ A D - 23 * e / 12 + 2 * Z := by
  have hv : 1 / 20 ≤ baseDifference A D - e := by unfold baseDifference; linarith
  have hm : 179 / 100 ≤ 2 - δ := by linarith only [hδ.2]
  have he3 : e ≤ 1 / 20 := by linarith
  have hde : δ * e ≤ (21 / 100) * (1 / 20) :=
    (mul_le_mul_of_nonneg_right hδ.2 he).trans
      (mul_le_mul_of_nonneg_left he3 (by norm_num))
  have hp := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ baseDifference A D - e by linarith)
  have hid : baseCredit δ A D - 23 * e / 12 =
      (2 - δ) * (baseDifference A D - e) - δ * e - (D - e) / 12 := by
    unfold baseCredit
    ring
  rw [hid]
  nlinarith only [hp, hv, hde, hD, he, hZ]

private theorem small_delta_rawExceptionalScore_pos_of_missing {δ h A D e Z : ℝ}
    (hdelta : δ ∈ Icc (2 / 11 : ℝ) (21 / 100))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D)
    (hD : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ)))
    (he : 0 ≤ e) (heE : e ≤ D - A) (hZ : Z ≤ δ * (D - A + e) / 2)
    (hh : h ≤ 467 / 2000) : 0 < rawExceptionalScore δ h A D e Z := by
  have hbase := small_delta_rawExceptionalScore_pos hdelta hA hAD hD he heE hZ
  have hid : rawExceptionalScore δ h A D e Z -
      rawExceptionalScore δ (467 / 2000) A D e Z = 2 * δ * (467 / 2000 - h) := by
    unfold rawExceptionalScore
    ring
  have hp := mul_nonneg (show 0 ≤ δ by linarith only [hdelta.1]) (sub_nonneg.mpr hh)
  nlinarith only [hid, hp, hbase]

end Erdos1017.EmptySatCorner

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- The upper own-slope strip at the actual corner is excluded for a null
entire source. Every original small-part and exceptional-atom restriction
is charged in the same model. -/
theorem no_corner_saturated_empty_source_small_delta (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hstrip : 1 + m ≤ 21 / 100) : False := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let δ := 1 + m
  let γ := 2 * (c - m * d) + m
  let D := (1 - m - 4 * (c - m * d)) / δ
  let L := s + u - D
  let E := D - A
  obtain ⟨hellbox, hc, hh, hfloor⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hell : -m < 1 := by linarith only [hellbox.2]
  have hδbox : δ ∈ Icc (2 / 11 : ℝ) (21 / 100) := by
    dsimp only [δ]
    exact ⟨by linarith only [hellbox.2], hstrip⟩
  have hδ : 0 < δ := by linarith only [hδbox.1]
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hcA := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  change c ≤ A ^ 2 at hcA
  have hA : 7 / 20 ≤ A := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hA0
      (show A - 7 / 20 ≤ 0 by linarith only [hn])
    nlinarith only [hc, hcA, hp]
  have hratio : δ * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hδ.ne'
  have hDγ : δ * (1 - D) = 2 * γ := by
    dsimp only [δ, γ] at *
    nlinarith only [hratio]
  have hmass : A + b + s + u = 1 := S.universalPartner_regions_mass r p hpair.1
  have hL : L = 1 - A - b - D := by dsimp only [L]; linarith only [hmass]
  have hb : b = 1 - A - D - L := by linarith only [hL]
  have hexcess := R.corner_saturated_empty_source_excess_pos r p hr hpair hW hd hgap
    he heq hglobal hnull
  have hLpos : 0 < L := by rw [hL]; exact hexcess.1
  have hholes := hexcess.2
  have hAD : A ≤ D := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap hell hN hholes
  have hmissing : 23 / 100 < 1 - 2 * d := by
    have hbox := (Benchmark.crossing_contact_location he heq).1
    linarith only [hbox.1]
  have hcorr : δ * (23 / 100) + 37 / 2500 < γ := by
    have hprod := mul_pos hδ (sub_pos.mpr hmissing)
    dsimp only [δ, γ] at *
    nlinarith only [hc, hh, hprod]
  have hhweak : 1 - 2 * d ≤ 467 / 2000 := by linarith only [hh]
  have hDref : D < 27 / 50 - 37 / (1250 * δ) := by
    apply (mul_lt_mul_iff_left₀ hδ).mp
    have hid : δ * (37 / (1250 * δ)) = 37 / 1250 := by field_simp
    nlinarith only [hDγ, hcorr, hid]
  have hDbox : D ∈ Icc (7 / 20 : ℝ) (27 / 50 - 37 / (1250 * δ)) :=
    ⟨hA.trans hAD, hDref.le⟩
  have hDhi := EmptySatCorner.small_delta_D_lt hδbox hDref.le
  have hbudget := S.empty_sat_deleted_partner_support r p hpair hW hd hgap hN
  change δ * (A + b - 2 * (1 - 2 * d)) + 2 * m * (A - b) ^ 2 +
    (2 * (A + b) - 1) * (δ * (A + b) - 2 * γ) - (1 - (A + b)) ^ 2 / 12 +
      (12 / 25) * max ((1 - m) * (A - b) - (δ * (A + b) - 2 * γ) -
        (1 - (A + b)) / 12) 0 ^ 2 + 4 * δ * b * s ≤ 0 at hbudget
  have hT : δ * (A + b) - 2 * γ = -δ * L := by rw [hL]; nlinarith only [hDγ]
  have hcap := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
  have hint : 0 ≤ ∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ :=
    integral_nonneg (fun x => (S.universalRootDeficit_mem_Icc r x).1)
  have hLs : L ≤ s := by
    change (∫ x in S.universalPartnerHoleRegion r p, S.universalRootDeficit r x ∂μ) ≤
      1 - m - 4 * (c - m * d) - δ * u at hcap
    have hdu : u ≤ D := by nlinarith only [hcap, hint, hratio, hδ]
    dsimp only [L]
    linarith only [hdu]
  have hbase := EmptySatCorner.small_delta_baseCredit_pos hδbox hA hAD hDhi.le
  have harg : (1 - m) * (A - b) - (δ * (A + b) - 2 * γ) - (1 - (A + b)) / 12 =
      EmptySatE2.baseCredit δ A D + 23 * L / 12 := by
    rw [hT, hb]
    dsimp only [δ]
    unfold EmptySatE2.baseCredit EmptySatE2.baseDifference
    ring
  rw [harg, max_eq_left (by linarith only [hbase, hLpos]), hT] at hbudget
  have hnorm := EmptySatCorner.deleted_price_eq δ (1 - 2 * d) A D L s
  rw [← hb] at hnorm
  have hmδ : m = δ - 1 := by dsimp only [δ]; ring
  have hprice : EmptySatE2.supportScore δ (1 - 2 * d) A D L +
      4 * δ * b * (s - L) ≤ 0 := by
    rw [hmδ] at hbudget
    nlinarith only [hbudget, hnorm]
  have hE0 : 0 ≤ E := sub_nonneg.mpr hAD
  by_cases hLE : L ≤ E
  · have hpos := EmptySatCorner.small_delta_supportScore_pos hδbox hDbox hA hAD hhweak hLpos.le hLE
    have hdebit : 0 ≤ 4 * δ * b * (s - L) := by positivity
    linarith only [hprice, hpos, hdebit]
  have hEL : E < L := lt_of_not_ge hLE
  by_cases hsmall : ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x < L
  · obtain ⟨_, hstrong, hsquare⟩ :=
      S.empty_sat_small_parts_integrated_bounds r p hpair hW hd hgap hell hN hholes
        hLpos hEL hsmall
    change E * L + L ^ 2 ≤ E * s at hstrong
    change L ^ 2 ≤ E * D at hsquare
    have hpos := EmptySatCorner.small_delta_integratedScore_pos
      hδbox hDbox hA hAD hhweak hEL hsquare
    have hmul := mul_le_mul_of_nonneg_left hprice hE0
    have hstrong' := mul_le_mul_of_nonneg_left hstrong
      (show 0 ≤ 4 * δ * b by positivity)
    unfold EmptySatE2.integratedScore at hpos
    rw [← hb] at hpos
    dsimp only [E] at hmul hstrong'
    nlinarith only [hmul, hstrong', hpos]
  obtain ⟨i, di, hir, hip, hwhole, haL, haE, hdi, _, hdef, hkzero, hZcap⟩ :=
    S.empty_sat_exceptional_atom r p hpair hW hd hgap hell hN hholes hEL hsmall
  have hprivate := S.empty_sat_exceptional_private_row
    r p i hpair hir hW hd hgap hell hN hwhole hkzero
  have hex := S.empty_sat_exceptional_support
    r p i hpair hir hip hW hd hgap hell hN hwhole di hdef hprivate
  let a := S.originalAtomMass i
  let e := a - L
  let Z := a * di
  have ha0 : 0 ≤ a := measureReal_nonneg
  have he0 : 0 ≤ e := sub_nonneg.mpr haL
  have heE : e ≤ D - A := by change a ≤ L + E at haE; dsimp only [e, E]; linarith
  have hZ0 : 0 ≤ Z := mul_nonneg ha0 hdi
  have hargpos := EmptySatCorner.exceptional_square_pos hδbox hA hAD hDhi.le he0 heE hZ0
  have hUex : A + a + b = 1 - D + e := by dsimp only [e]; linarith only [hb]
  have hvex : A - a - b = EmptySatE2.baseDifference A D - e := by
    dsimp only [e]
    unfold EmptySatE2.baseDifference
    linarith only [hb]
  have hTex : δ * (A + a + b) - 2 * γ = δ * e := by
    rw [hUex]
    nlinarith only [hDγ]
  change δ * (A + a + b - 2 * (1 - 2 * d)) + 2 * m * (A - a - b) ^ 2 +
    (2 * (A + a + b) - 1) * (δ * (A + a + b) - 2 * γ) -
      (1 - (A + a + b)) ^ 2 / 12 + (12 / 25) *
        max ((1 - m) * (A - a - b) - (δ * (A + a + b) - 2 * γ) -
          (1 - (A + a + b)) / 12 + 2 * Z) 0 ^ 2 - 4 * A * Z ≤ 0 at hex
  rw [hTex, hUex, hvex, hmδ] at hex
  have hargex : (1 - (δ - 1)) * (EmptySatE2.baseDifference A D - e) - δ * e -
      (1 - (1 - D + e)) / 12 + 2 * Z =
        EmptySatE2.baseCredit δ A D - 23 * e / 12 + 2 * Z := by
    unfold EmptySatE2.baseCredit
    ring
  rw [hargex, max_eq_left hargpos.le] at hex
  have hnormex := EmptySatCorner.exceptional_price_eq δ (1 - 2 * d) A D e Z
  dsimp only at hnormex
  have hnonpos : EmptySatE2.rawExceptionalScore δ (1 - 2 * d) A D e Z ≤ 0 := by
    nlinarith only [hex, hnormex]
  have hpos := EmptySatCorner.small_delta_rawExceptionalScore_pos_of_missing
    hδbox hA hAD hDbox he0 heE hZcap hhweak
  exact (not_lt_of_ge hnonpos) hpos

private theorem saturated_corner_joint_price (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) (hstrip : 21 / 100 < 1 + m) :
    let δ := 1 + m
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let D := (1 - m - 4 * (c - m * d)) / δ
    let E := D - A
    let L := 1 - A - b - D
    δ ∈ Icc (21 / 100 : ℝ) (2 / 5) ∧
      A ∈ Icc (3507 / 10000 : ℝ) (3 / 8) ∧
      E ∈ Icc (0 : ℝ) (EmptySatCorner.cornerDeficitCap δ - A) ∧ 0 < L ∧
      0 < EmptySatCorner.cornerTraceSlack δ A ∧
      EmptySatCorner.cornerPrice δ A E L < 0 := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let δ := 1 + m
  let γ := 2 * (c - m * d) + m
  let D := (1 - m - 4 * (c - m * d)) / δ
  let E := D - A
  let L := 1 - A - b - D
  obtain ⟨hell, hc, hh, hfloor⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hδbox : δ ∈ Icc (21 / 100 : ℝ) (2 / 5) := by
    dsimp only [δ]
    exact ⟨hstrip.le, by linarith only [hell.1]⟩
  have hδ : 0 < δ := by linarith only [hδbox.1]
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨hAlo, hAhi, _, _, hu⟩ :=
    R.empty_sat_corner_bad_region r p hr hpair P hW hd hgap he heq hglobal hnull hstrip
  have hcA := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  change c ≤ A ^ 2 at hcA
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hAstrong : 3507 / 10000 ≤ A := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hA0
      (show A - 3507 / 10000 ≤ 0 by linarith only [hn])
    nlinarith only [hc, hcA, hp]
  obtain ⟨hL, hholes⟩ :=
    R.corner_saturated_empty_source_excess_pos r p hr hpair hW hd hgap he heq hglobal hnull
  have hAD : A ≤ D := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap (by linarith only [hell.2]) hN hholes
  have hratio : δ * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hδ.ne'
  have hDγ : δ * (1 - D) = 2 * γ := by
    dsimp only [δ, γ] at *
    nlinarith only [hratio]
  have hmissing : 289 / 1250 < 1 - 2 * d := by
    have hbox := (Benchmark.crossing_contact_location he heq).1
    linarith only [hbox.1]
  have hcorr : δ * (1 - 2 * d) + 37 / 2500 < γ := by
    dsimp only [δ, γ]
    nlinarith only [hc, hh]
  have hDcap : D < EmptySatCorner.cornerDeficitCap δ := by
    apply (mul_lt_mul_iff_left₀ hδ).mp
    have hid : δ * (37 / (1250 * δ)) = 37 / 1250 := by field_simp
    have hp := mul_pos hδ (sub_pos.mpr hmissing)
    unfold EmptySatCorner.cornerDeficitCap
    nlinarith only [hDγ, hcorr, hid, hp]
  have hgammaLo : (23 / 100) * δ + 37 / 2500 < γ := by
    have hp := mul_pos hδ (show 0 < 1 - 2 * d - 23 / 100 by
      linarith only [hmissing])
    nlinarith only [hcorr, hp]
  have hnonnegative := bodyPositiveEnergy_nonnegative W {x | S.ρ x = r.val}
  have hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val} := by
    apply lt_of_le_of_ne hnonnegative
    intro hz
    exact S.no_corner_zero_body r hW hd hgap he heq hglobal hz.symm
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap {x | S.ρ x = r.val}
    (S.hfibers r.val r.property).1] at hpositive
  have htrace := S.universal_positive_body_trace r hW hd hgap hN hpositive
  change 3 * A ^ 2 + 2 * A * γ + γ ^ 2 ≤ 2 * (1 - 2 * d) at htrace
  have htraceSlack : 0 < EmptySatCorner.cornerTraceSlack δ A := by
    have hprod := mul_nonneg hA0 (sub_nonneg.mpr hgammaLo.le)
    have hsq := mul_pos (sub_pos.mpr hgammaLo)
      (show 0 < γ + ((23 / 100) * δ + 37 / 2500) by
        linarith only [hgammaLo, hδ])
    unfold EmptySatCorner.cornerTraceSlack
    nlinarith only [htrace, hprod, hsq, hh]
  have hmass : A + b + s + u = 1 := S.universalPartner_regions_mass r p hpair.1
  have hbudget := S.empty_sat_deleted_partner_support r p hpair hW hd hgap hN
  have harg : (1 - m) * (A - b) - (δ * (A + b) - 2 * γ) -
      (1 - (A + b)) / 12 = EmptySatE2.baseCredit δ A D + 23 * L / 12 := by
    dsimp only [L, δ]
    unfold EmptySatE2.baseCredit EmptySatE2.baseDifference
    nlinarith only [hDγ]
  have hv : 1 / 20 ≤ EmptySatE2.baseDifference A D := by
    unfold EmptySatE2.baseDifference
    linarith only [hAlo, hAD]
  have hDhi : D < 3 / 5 := by
    have hterm : 0 < 37 / (1250 * δ) := by positivity
    unfold EmptySatCorner.cornerDeficitCap at hDcap
    linarith only [hterm, hDcap]
  have hK : 0 < EmptySatE2.baseCredit δ A D := by
    have hp := mul_le_mul_of_nonneg_right
      (show 8 / 5 ≤ 2 - δ by linarith only [hδbox.2])
      (show 0 ≤ EmptySatE2.baseDifference A D by linarith only [hv])
    unfold EmptySatE2.baseCredit
    nlinarith only [hp, hv, hDhi]
  change δ * (A + b - 2 * (1 - 2 * d)) + 2 * m * (A - b) ^ 2 +
    (2 * (A + b) - 1) * (δ * (A + b) - 2 * γ) - (1 - (A + b)) ^ 2 / 12 +
      (12 / 25) * max ((1 - m) * (A - b) - (δ * (A + b) - 2 * γ) -
        (1 - (A + b)) / 12) 0 ^ 2 + 4 * δ * b * s ≤ 0 at hbudget
  rw [harg, max_eq_left (by linarith only [hK, hL])] at hbudget
  have hbad : u < EmptySatCorner.cornerBadCap δ A E := by
    change u < 1 + 2 * m * A - 3 * γ at hu
    unfold EmptySatCorner.cornerBadCap
    dsimp only [E, δ]
    nlinarith only [hu, hDγ]
  have hidentity : EmptySatCorner.cornerPrice δ A E L =
      (δ * (A + b - 2 * (1 - 2 * d)) + 2 * m * (A - b) ^ 2 +
        (2 * (A + b) - 1) * (δ * (A + b) - 2 * γ) - (1 - (A + b)) ^ 2 / 12 +
        (12 / 25) * (EmptySatE2.baseCredit δ A D + 23 * L / 12) ^ 2 +
          4 * δ * b * s) - (2 * γ - 2 * δ * (1 - 2 * d) - 37 / 1250) -
            4 * δ * b * (EmptySatCorner.cornerBadCap δ A E - u) := by
    have hγ : γ = δ * (1 - D) / 2 := by nlinarith only [hDγ]
    have hs : s = 1 - A - b - u := by linarith only [hmass]
    rw [hγ, hs]
    unfold EmptySatCorner.cornerPrice EmptySatCorner.cornerBadCap
      EmptySatE2.baseCredit EmptySatE2.baseDifference
    dsimp only [E, L, δ]
    ring
  have hdebit : 0 ≤ 4 * δ * b * (EmptySatCorner.cornerBadCap δ A E - u) := by
    exact mul_nonneg (mul_nonneg (by linarith only [hδ]) hb0)
      (sub_nonneg.mpr hbad.le)
  have hprice : EmptySatCorner.cornerPrice δ A E L < 0 := by
    nlinarith only [hidentity, hbudget, hcorr, hdebit]
  exact ⟨hδbox, ⟨hAstrong, hAhi.le⟩, ⟨sub_nonneg.mpr hAD, by
    linarith only [hDcap]⟩, hL, htraceSlack, hprice⟩

/-- The original saturated corner with null entire source has no excess
at or below its own deficit difference. No signed price is supplied. -/
theorem no_corner_saturated_empty_source_small_excess (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hsmall : let A := S.originalAtomMass r
      let b := S.originalAtomMass p
      let D := (1 - m - 4 * (c - m * d)) / (1 + m)
      1 - A - b - D ≤ D - A) : False := by
  by_cases hstrip : 1 + m ≤ 21 / 100
  · exact R.no_corner_saturated_empty_source_small_delta
      r p hr hpair hW hd hgap he heq hglobal hnull hstrip
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  obtain ⟨hδ, hA, hE, hL, _, hprice⟩ := saturated_corner_joint_price
    R r p hr hpair P hW hd hgap he heq hglobal hnull (lt_of_not_ge hstrip)
  have hpos := EmptySatCorner.small_excess_price_pos hδ hA hE ⟨hL.le, hsmall⟩
  exact (not_lt_of_ge hpos.le) hprice

/-- The original nonexceptional null-source corner is excluded in both
easy moment sectors. The private-source mean and its strict original
endpoint cap are integrated from the same model. -/
theorem no_corner_saturated_empty_source_nonexceptional_easy (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hsmall : let H := S.universalPartnerHoleRegion r p
      let D := (1 - m - 4 * (c - m * d)) / (1 + m)
      let L := μ.real H + μ.real (S.universalPartnerCommonRegion r p) - D
      ∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L)
    (heasy : (1 - m - 4 * (c - m * d)) / (1 + m) - S.originalAtomMass r ≤ 1 / 20 ∨
      1 + m ≤ 1 / 4) : False := by
  by_cases hstrip : 1 + m ≤ 21 / 100
  · exact R.no_corner_saturated_empty_source_small_delta
      r p hr hpair hW hd hgap he heq hglobal hnull hstrip
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let J := S.reverseCompulsorySource {p}
  let δ := 1 + m
  let D := (1 - m - 4 * (c - m * d)) / δ
  let E := D - A
  let L := μ.real H + μ.real U - D
  have hmass : A + b + μ.real H + μ.real U = 1 :=
    S.universalPartner_regions_mass r p hpair.1
  have hLid : L = 1 - A - b - D := by dsimp only [L]; linarith only [hmass]
  by_cases hEL : E < L
  swap
  · exact R.no_corner_saturated_empty_source_small_excess
      r p hr hpair hW hd hgap he heq hglobal hnull
      (by change 1 - A - b - D ≤ E; rw [← hLid]; exact le_of_not_gt hEL)
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  obtain ⟨hδ, hA, hE, hL0, htrace, hprice⟩ := saturated_corner_joint_price
    R r p hr hpair P hW hd hgap he heq hglobal hnull (lt_of_not_ge hstrip)
  have hL : 0 < L := by rw [hLid]; exact hL0
  have hellbox := (hW.corner_contact_parameters hd hgap he heq hglobal).1
  have hell : -m < 1 := by linarith only [hellbox.2]
  obtain ⟨_, hj, hjcap, hSigma, hameas, ha, hdef, had, hrow, hbudget, _, _⟩ :=
    R.empty_sat_corner_source_geometry r p hr hpair hW hd hgap hell hnull hL hEL hsmall
  have hμj : (μ.restrict J).real univ = μ.real J := measureReal_restrict_apply_univ J
  obtain ⟨hq, hqcap, hlower, _⟩ := EmptySatCorner.deficit_moment_bounds
    (μ.restrict J) S.ownIndependentMass (S.universalRootDeficit r)
    (by rw [hμj]; exact hj) ha hameas hdef had
    (hrow.mono (fun _ hx => hx.1)) (hrow.mono (fun _ hx => hx.2.1))
    hEL (show 0 < 1 + m by linarith only [hell]) (hrow.mono (fun _ hx => hx.2.2))
  simp only [hμj] at hq hqcap hlower
  have hbudget' : (∫ x in J, S.universalRootDeficit r x ∂μ) ≤ δ * (μ.real J - L) := by
    linarith only [hbudget, hSigma]
  obtain ⟨_, hEpos, _, hmean, _⟩ := EmptySatCorner.mean_mass_bounds_of_deficit_budget
    hj hq hqcap hEL (show 0 < δ by linarith only [hell]) hlower hbudget'
  have hj' : μ.real J < 3 * A - 1 + E + L := by
    change b + μ.real J < A at hjcap
    dsimp only [E]
    nlinarith only [hjcap, hLid]
  have hcap : A + E ≤ EmptySatCorner.cornerDeficitCap δ := by
    dsimp only [E]
    linarith only [hE.2]
  have hpos := EmptySatCorner.nonexceptional_easy_price_pos hδ
    (show A ∈ Icc (7 / 20 : ℝ) (3 / 8) from ⟨by linarith only [hA.1], hA.2⟩)
    hEpos hEL hcap htrace.le hmean hj' heasy
  have hprice' : EmptySatCorner.cornerPrice δ A E L < 0 := by rw [hLid]; exact hprice
  exact (not_lt_of_ge hpos.le) hprice'

/-- Every exceptional whole atom at the null-source corner is excluded
by its original degree tangent, stock cap and retained signed restriction
price. The scalar certificate is applied only after those facts are derived. -/
theorem no_corner_saturated_empty_source_exceptional (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hlarge : let H := S.universalPartnerHoleRegion r p
      let D := (1 - m - 4 * (c - m * d)) / (1 + m)
      let L := μ.real H + μ.real (S.universalPartnerCommonRegion r p) - D
      ¬∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L) : False := by
  by_cases hstrip : 1 + m ≤ 21 / 100
  · exact R.no_corner_saturated_empty_source_small_delta
      r p hr hpair hW hd hgap he heq hglobal hnull hstrip
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let δ := 1 + m
  let γ := 2 * (c - m * d) + m
  let D := (1 - m - 4 * (c - m * d)) / δ
  let E := D - A
  let L := s + u - D
  have hmass : A + b + s + u = 1 := S.universalPartner_regions_mass r p hpair.1
  have hLid : L = 1 - A - b - D := by dsimp only [L]; linarith only [hmass]
  have hb : b = 1 - A - (A + E) - L := by dsimp only [E]; linarith only [hLid]
  by_cases hEL : E < L
  swap
  · exact R.no_corner_saturated_empty_source_small_excess
      r p hr hpair hW hd hgap he heq hglobal hnull
      (by change 1 - A - b - D ≤ E; rw [← hLid]; exact le_of_not_gt hEL)
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  obtain ⟨hδ, hA, hE, _, _, _⟩ := saturated_corner_joint_price
    R r p hr hpair P hW hd hgap he heq hglobal hnull (lt_of_not_ge hstrip)
  obtain ⟨hellbox, hc, hh, _⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hell : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hellbox.1, hellbox.2]
  obtain ⟨_, _, hmargin, hnegative, hu⟩ := R.empty_sat_corner_bad_region
    r p hr hpair P hW hd hgap he heq hglobal hnull (lt_of_not_ge hstrip)
  have hstock := bad_region_stock_nonneg S r p hpair P hW hd hgap hN
    (by linarith only [hA.1]) (by linarith only [hA.2]) hell hmargin hnegative
  have hLmax : L ≤ 2 - 5 * A - E := by
    change 0 ≤ 1 - 3 * A + b at hstock
    linarith only [hb, hstock]
  have hratio : δ * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ (show δ ≠ 0 by dsimp only [δ]; linarith only [hell.2])
  have hDγ : δ * (1 - D) = 2 * γ := by
    dsimp only [δ, γ] at *
    nlinarith only [hratio]
  have hbad : u ≤ EmptySatCorner.cornerBadCap δ A E := by
    unfold EmptySatCorner.cornerBadCap
    dsimp only [E, δ]
    change u < 1 + 2 * m * A - 3 * γ at hu
    nlinarith only [hu, hDγ]
  have hhlo : 23 / 100 ≤ 1 - 2 * d := by
    have hbox := (Benchmark.crossing_contact_location he heq).1
    linarith only [hbox.1]
  have hholes := (R.corner_saturated_empty_source_excess_pos
    r p hr hpair hW hd hgap he heq hglobal hnull).2
  obtain ⟨i, di, hir, hip, hwhole, haL, haE, hdi, _, hdef, hkzero, hZcap⟩ :=
    S.empty_sat_exceptional_atom r p hpair hW hd hgap hell.2 hN hholes hEL hlarge
  have hprivate := S.empty_sat_exceptional_private_row
    r p i hpair hir hW hd hgap hell.2 hN hwhole hkzero
  have hrow := exceptional_deficit_row S r p i hpair hW hd hgap hell.2 hN hwhole hdef hkzero
  obtain ⟨hden, htangent⟩ := exceptional_atomic_tangent_data
    S r p i hpair hip hW hd hgap hell.2 hN hwhole hprivate hdef
  let a := S.originalAtomMass i
  let e := a - L
  let Z := a * di
  have he0 : 0 ≤ e := sub_nonneg.mpr haL
  have heE : e ≤ E := by change a ≤ L + E at haE; dsimp only [e]; linarith only [haE]
  have hden' : 0 < 1 - u - 2 * (1 - 2 * d) := by
    change 0 < 4 * d - 2 + A + b + s at hden
    linarith only [hden, hmass]
  have htan : δ * (A + E) * (A + E - u - e) ≤ di * (1 - u - 2 * (1 - 2 * d)) := by
    change (1 - m - 4 * (c - m * d)) * (s - a) ≤ di * (4 * d - 2 + A + b + s)
      at htangent
    rw [← hratio] at htangent
    have hdenid : 4 * d - 2 + A + b + s = 1 - u - 2 * (1 - 2 * d) := by
      linarith only [hmass]
    rw [hdenid] at htangent
    convert htangent using 1
    dsimp only [E, e, L]
    ring
  have hrow' : (L - E + 2 * e) * di ≤ δ * e := hrow
  have hLr := EmptySatCorner.exceptional_excess_le_six
    hδ hA hE ⟨he0, heE⟩ hEL hbad hhlo hden' htan hrow'
  have hZ0 : 0 ≤ Z := mul_nonneg (show 0 ≤ a from measureReal_nonneg) hdi
  have hguard := (EmptySatCorner.exceptional_guards hδ hA hE).2.2.2.2
  have hargpos : 0 < EmptySatE2.baseCredit δ A (A + E) - 23 * e / 12 + 2 * Z := by
    have hid : EmptySatE2.baseCredit δ A (A + E) - 23 * e / 12 + 2 * Z =
        ((2 - δ) * (3 * A - 1) - δ * E - A / 12) + 23 * (E - e) / 12 + 2 * Z := by
      unfold EmptySatE2.baseCredit EmptySatE2.baseDifference
      ring
    linarith only [hid, hguard, heE, hZ0]
  have hex := exceptional_support_with_debit S r p i hpair hir hip hW hd hgap hell.2
    hN hwhole di hdef hprivate
  have hUex : A + a + b = 1 - (A + E) + e := by dsimp only [E, e]; linarith only [hLid]
  have hvex : A - a - b = EmptySatE2.baseDifference A (A + E) - e := by
    dsimp only [E, e]
    unfold EmptySatE2.baseDifference
    linarith only [hLid]
  have hTex : δ * (A + a + b) - 2 * γ = δ * e := by
    rw [hUex]
    dsimp only [E]
    nlinarith only [hDγ]
  change δ * (A + a + b - 2 * (1 - 2 * d)) + 2 * m * (A - a - b) ^ 2 +
    (2 * (A + a + b) - 1) * (δ * (A + a + b) - 2 * γ) - (1 - (A + a + b)) ^ 2 / 12 +
      (12 / 25) * max ((1 - m) * (A - a - b) - (δ * (A + a + b) - 2 * γ) -
        (1 - (A + a + b)) / 12 + 2 * Z) 0 ^ 2 - 4 * A * Z +
          4 * δ * b * (s - a) ≤ 0 at hex
  rw [hTex, hUex, hvex] at hex
  have harg : (1 - m) * (EmptySatE2.baseDifference A (A + E) - e) - δ * e -
      (1 - (1 - (A + E) + e)) / 12 + 2 * Z =
        EmptySatE2.baseCredit δ A (A + E) - 23 * e / 12 + 2 * Z := by
    unfold EmptySatE2.baseCredit
    dsimp only [δ]
    ring
  rw [harg, max_eq_left hargpos.le] at hex
  have hraw : EmptySatE2.rawExceptionalScore δ (1 - 2 * d) A (A + E) e Z +
      4 * δ * b * (s - L - e) ≤ 0 := by
    unfold EmptySatE2.rawExceptionalScore
    dsimp only [δ, e] at *
    nlinarith only [hex]
  have hcorr : 37 / 1250 < δ * (1 - (A + E) - 2 * (1 - 2 * d)) := by
    have hg : δ * (1 - 2 * d) + 37 / 2500 < γ := by
      dsimp only [δ, γ]
      nlinarith only [hc, hh]
    dsimp only [E]
    nlinarith only [hg, hDγ]
  have hpos := EmptySatCorner.exceptional_raw_price_pos hδ hA hE ⟨he0, heE⟩ hEL.le
    hLmax (by linarith only [hLr]) hb (show 0 ≤ b from measureReal_nonneg)
    (by dsimp only [E, L]; ring) hbad hZcap hcorr
  exact (not_lt_of_ge hraw) hpos

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

namespace Erdos1017.EmptySatCorner

private def hardScore (δ A b gamma P0 W e F dJ j : ℝ) : ℝ :=
  let ell := 1 - δ
  let K := A * j - e
  let C0 := F / 2 - ell * e + A * j - A * dJ
  let RJ := j * (gamma + ell * (b + j) - A) + A * dJ - F
  C0 * (W - K) - K * b * (gamma + ell * b) + (A ^ 2 - K) * RJ +
    K * ell * P0 / (4 * δ)

private theorem hard_score_lower {δ A b gamma P0 W Wlo e F dJ j L E r : ℝ}
    (hA : 0 < A) (hj : 0 ≤ j) (he : 0 ≤ e) (hjA : j < A) (hjE : 2 * E < j)
    (hW : W ≤ A ^ 2) (hWlo : Wlo ≤ W) (hWlower : A ^ 2 - 2 * A * E < W)
    (hF : F ≤ 2 * j * dJ - δ * j ^ 2 - r) (hD : dJ ≤ δ * (j - L))
    (hC : 0 ≤ (δ * j * (j - 2 * L) - r) / 2 - (1 - δ) * e +
      A * j - A * δ * (j - L)) :
    hardScore δ A b gamma P0 Wlo e (δ * j * (j - 2 * L) - r) (δ * (j - L)) j ≤
      hardScore δ A b gamma P0 W e F dJ j := by
  let K := A * j - e
  let Fbound := fun t : ℝ => 2 * j * t - δ * j ^ 2 - r
  have hK : K ≤ A ^ 2 := by
    have hp := mul_nonneg hA.le (sub_nonneg.mpr hjA.le)
    dsimp only [K]
    nlinarith only [hp, he]
  have hFcoef : (W + K - 2 * A ^ 2) / 2 ≤ 0 := by linarith only [hW, hK]
  have hFdiff : hardScore δ A b gamma P0 W e F dJ j -
      hardScore δ A b gamma P0 W e (Fbound dJ) dJ j =
        (F - Fbound dJ) * ((W + K - 2 * A ^ 2) / 2) := by
    unfold hardScore
    dsimp only [K]
    ring
  have hFpositive := mul_nonneg_of_nonpos_of_nonpos
    (show F - Fbound dJ ≤ 0 from sub_nonpos.mpr hF) hFcoef
  have hstepF : hardScore δ A b gamma P0 W e (Fbound dJ) dJ j ≤
      hardScore δ A b gamma P0 W e F dJ j := by
    linarith only [hFdiff, hFpositive]
  have hinner : A * (A - j) - W < 0 := by
    have hp := mul_pos hA (sub_pos.mpr hjE)
    nlinarith only [hp, hWlower]
  have hDcoef : (A - j) * (A * (A - j) - W) - j * e < 0 := by
    have hp := mul_neg_of_pos_of_neg (sub_pos.mpr hjA) hinner
    have hq := mul_nonneg hj he
    linarith only [hp, hq]
  have hDdiff : hardScore δ A b gamma P0 W e (Fbound dJ) dJ j -
      hardScore δ A b gamma P0 W e (Fbound (δ * (j - L))) (δ * (j - L)) j =
        (dJ - δ * (j - L)) * ((A - j) * (A * (A - j) - W) - j * e) := by
    unfold hardScore
    dsimp only [Fbound]
    ring
  have hDpositive := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hD) hDcoef.le
  have hstepD : hardScore δ A b gamma P0 W e (Fbound (δ * (j - L))) (δ * (j - L)) j ≤
      hardScore δ A b gamma P0 W e (Fbound dJ) dJ j := by
    linarith only [hDdiff, hDpositive]
  have hFeq : Fbound (δ * (j - L)) = δ * j * (j - 2 * L) - r := by
    dsimp only [Fbound]
    ring
  rw [hFeq] at hstepD
  have hWdiff : hardScore δ A b gamma P0 W e (δ * j * (j - 2 * L) - r)
      (δ * (j - L)) j - hardScore δ A b gamma P0 Wlo e (δ * j * (j - 2 * L) - r)
        (δ * (j - L)) j = (W - Wlo) *
          ((δ * j * (j - 2 * L) - r) / 2 - (1 - δ) * e + A * j - A * δ * (j - L)) := by
    unfold hardScore
    ring
  have hWpositive := mul_nonneg (sub_nonneg.mpr hWlo) hC
  linarith only [hWdiff, hWpositive, hstepD, hstepF]

private theorem hard_source_coefficient_pos {δ A E L q e j : ℝ}
    (hδ : δ ∈ Icc (1 / 4 : ℝ) (2 / 5)) (hA : 0 < A) (hj : 0 < j)
    (hjA : j < A) (hE : 0 < E) (hEL : E < L) (hq : q ∈ Icc (0 : ℝ) E)
    (hsquare : 2 * e = j ^ 2 - j * q) :
    0 < (δ * j * (j - 2 * L) - δ * j * (L - E) * q / (L + E)) / 2 -
      (1 - δ) * e + A * j - A * δ * (j - L) := by
  have hδ0 : 0 ≤ δ := by linarith only [hδ.1]
  have hell : 0 < 1 - δ := by linarith only [hδ.2]
  have hbeta : 0 ≤ 1 - 2 * δ := by linarith only [hδ.2]
  have hC : 0 < L + E := by linarith only [hE, hEL]
  have hratio : δ * (L - E) / (L + E) ≤ δ := by
    apply (div_le_iff₀ hC).mpr
    have hp := mul_nonneg hδ0 hE.le
    nlinarith only [hp]
  have hmiddle : 0 ≤ (1 - δ) * A - (1 - 2 * δ) * j := by
    have hp := mul_nonneg hbeta (sub_nonneg.mpr hjA.le)
    have hq := mul_nonneg hδ0 hA.le
    nlinarith only [hp, hq]
  have hbracket : 0 ≤ (1 - δ) - δ * (L - E) / (L + E) := by
    linarith only [hratio, hδ.2]
  have heq : e = (j ^ 2 - j * q) / 2 := by linarith only [hsquare]
  have hid : (δ * j * (j - 2 * L) - δ * j * (L - E) * q / (L + E)) / 2 -
      (1 - δ) * e + A * j - A * δ * (j - L) =
        (1 - δ) * A * j / 2 + j * ((1 - δ) * A - (1 - 2 * δ) * j) / 2 +
          δ * L * (A - j) + j * q / 2 * ((1 - δ) - δ * (L - E) / (L + E)) := by
    rw [heq]
    ring
  have hfirst : 0 < (1 - δ) * A * j / 2 := by positivity
  have hsecond : 0 ≤ j * ((1 - δ) * A - (1 - 2 * δ) * j) / 2 := by positivity
  have hthird : 0 ≤ δ * L * (A - j) := by
    exact mul_nonneg (mul_nonneg hδ0 (by linarith only [hE, hEL]))
      (sub_nonneg.mpr hjA.le)
  have hfourth : 0 ≤ j * q / 2 * ((1 - δ) - δ * (L - E) / (L + E)) := by
    exact mul_nonneg (div_nonneg (mul_nonneg hj.le hq.1) (by norm_num)) hbracket
  linarith only [hid, hfirst, hsecond, hthird, hfourth]

private def hardEndpointScore (δ A b gamma P0 W E L q j : ℝ) : ℝ :=
  hardScore δ A b gamma P0 W (j * (j - q) / 2)
    (δ * j * (j - 2 * L) - δ * j * (L - E) * q / (L + E)) (δ * (j - L)) j

private theorem hard_score_pos_of_endpoints {δ A b gamma P0 W E L q j : ℝ}
    (hδ : δ ∈ Icc (0 : ℝ) 1) (hE : 0 < E) (hEL : E ≤ L)
    (hq : q ∈ Icc (0 : ℝ) E)
    (hzero : 0 < hardEndpointScore δ A b gamma P0 W E L 0 j)
    (hupper : 0 < hardEndpointScore δ A b gamma P0 W E L E j) :
    0 < hardEndpointScore δ A b gamma P0 W E L q j := by
  by_cases hq0 : q = 0
  · simpa only [hq0] using hzero
  by_cases hqE : q = E
  · simpa only [hqE] using hupper
  have hC : 0 < L + E := by linarith only [hE, hEL]
  have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hq0)
  have hqhi : q < E := lt_of_le_of_ne hq.2 hqE
  have hid : E * hardEndpointScore δ A b gamma P0 W E L q j -
      (E - q) * hardEndpointScore δ A b gamma P0 W E L 0 j -
      q * hardEndpointScore δ A b gamma P0 W E L E j =
        E * j ^ 2 / 4 * ((1 - δ) + δ * (L - E) / (L + E)) * q * (E - q) := by
    unfold hardEndpointScore hardScore
    ring
  have hbracket : 0 ≤ (1 - δ) + δ * (L - E) / (L + E) :=
    add_nonneg (sub_nonneg.mpr hδ.2)
      (div_nonneg (mul_nonneg hδ.1 (sub_nonneg.mpr hEL)) hC.le)
  have hremainder : 0 ≤ E * j ^ 2 / 4 *
      ((1 - δ) + δ * (L - E) / (L + E)) * q * (E - q) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hbracket) hq.1)
      (sub_nonneg.mpr hq.2)
  have hfirst := mul_pos (sub_pos.mpr hqhi) hzero
  have hsecond := mul_nonneg hqpos.le hupper.le
  have hproduct : 0 < E * hardEndpointScore δ A b gamma P0 W E L q j := by
    linarith only [hid, hremainder, hfirst, hsecond]
  exact (mul_pos_iff_of_pos_left hE).mp hproduct

private theorem hard_lower_cost_gt {A E en Bc Bcap N : ℝ}
    (hA : 0 ≤ A) (hen : 0 < en) (hN : 0 ≤ N) (hBc : Bc ≤ Bcap)
    (hcert : 0 < 2 * en * (2 * A * E - A ^ 2 + 123 / 1000) - A * Bcap * N) :
    A ^ 2 - 2 * A * E < 123 / 1000 - A * Bc * N / (2 * en) := by
  have hden : 0 < 2 * en := by positivity
  have hproduct := mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hBc)) hN
  have hbound : (A ^ 2 - 2 * A * E) * (2 * en) <
      (123 / 1000) * (2 * en) - A * Bc * N := by
    nlinarith only [hcert, hproduct]
  have hid : (123 / 1000 - A * Bc * N / (2 * en)) * (2 * en) =
      (123 / 1000) * (2 * en) - A * Bc * N := by
    rw [sub_mul, div_mul_cancel₀ _ hden.ne']
  exact (mul_lt_mul_iff_right₀ hden).mp (by nlinarith only [hid, hbound])

private theorem hard_score_nonpos_of_cost {δ A b gamma P0 c U eta e F dJ j s : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hK : 0 ≤ A * j - e)
    (hC : 0 < F / 2 - (1 - δ) * e + A * j - A * dJ)
    (hcost : c ≤ A * b + (A * j - e) +
      ((A * j - e) * b * (gamma + (1 - δ) * (b + s)) -
        A * b * (F / 2 - (1 - δ) * e + A * j - A * dJ) -
          (A ^ 2 - (A * j - e)) *
            (j * (gamma + (1 - δ) * (b + j) - A) + A * dJ - F)) /
        (F / 2 - (1 - δ) * e + A * j - A * dJ) + U / (2 * eta))
    (hsupport : P0 + 4 * δ * b * s ≤ 0) :
    hardScore δ A b gamma P0 (c - U / (2 * eta)) e F dJ j ≤ 0 := by
  let K := A * j - e
  let C0 := F / 2 - (1 - δ) * e + A * j - A * dJ
  let RJ := j * (gamma + (1 - δ) * (b + j) - A) + A * dJ - F
  let ZP := gamma + (1 - δ) * (b + s)
  let Rctx := K * b * ZP - A * b * C0 - (A ^ 2 - K) * RJ
  let W := c - U / (2 * eta)
  change 0 < C0 at hC
  have hcost' : c ≤ A * b + K + Rctx / C0 + U / (2 * eta) := hcost
  have hscaled := mul_le_mul_of_nonneg_right hcost' hC.le
  have hcancel : (Rctx / C0) * C0 = Rctx := div_mul_cancel₀ _ hC.ne'
  have hnecessary : C0 * (W - K) - K * b * ZP + (A ^ 2 - K) * RJ ≤ 0 := by
    dsimp only [Rctx, W] at *
    nlinarith only [hscaled, hcancel]
  have hfactor : 0 ≤ K * (1 - δ) / (4 * δ) :=
    div_nonneg (mul_nonneg hK (sub_nonneg.mpr hδone)) (by positivity)
  have hsupport' := mul_le_mul_of_nonneg_left hsupport hfactor
  have hid : (K * (1 - δ) / (4 * δ)) * (P0 + 4 * δ * b * s) =
      K * (1 - δ) * P0 / (4 * δ) + K * b * (1 - δ) * s := by
    field_simp [hδ.ne']
  rw [mul_zero, hid] at hsupport'
  have hscore : hardScore δ A b gamma P0 W e F dJ j -
      (C0 * (W - K) - K * b * ZP + (A ^ 2 - K) * RJ) =
        K * (1 - δ) * P0 / (4 * δ) + K * b * (1 - δ) * s := by
    unfold hardScore
    dsimp only [K, C0, RJ, ZP]
    ring
  nlinarith only [hsupport', hscore, hnecessary]

end Erdos1017.EmptySatCorner

namespace Erdos1017.EmptySatCorner

private def supportIntercept (δ A D L : ℝ) : ℝ :=
  let v := EmptySatE2.baseDifference A D
  let K := EmptySatE2.baseCredit δ A D
  let p := (4 * (2 - δ) * v + 8 * D) / 25
  37 / 1250 - 2 * (1 - δ) * v ^ 2 - D ^ 2 / 12 + (12 / 25) * K ^ 2 -
    p * L - (8 / 25) * L ^ 2 - 4 * δ * (1 - A - D - L) * L

end Erdos1017.EmptySatCorner

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

private theorem actual_corner_support_intercept
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let δ := 1 + m
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let D := (1 - m - 4 * (c - m * d)) / δ
    let L := 1 - A - b - D
    0 < δ → δ ≤ 2 / 5 → 7 / 20 ≤ A → A ≤ D → D ≤ 3 / 5 → 0 < L →
      37 / 1250 < δ * (1 - D - 2 * (1 - 2 * d)) →
      EmptySatCorner.supportIntercept δ A D L +
        4 * δ * b * μ.real (S.universalPartnerHoleRegion r p) < 0 := by
  dsimp only
  intro hδ hδhi hA hAD hDhi hL hcorr
  let δ := 1 + m
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let D := (1 - m - 4 * (c - m * d)) / δ
  let L := 1 - A - b - D
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let γ := 2 * (c - m * d) + m
  have hratio : δ * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hδ.ne'
  have hDγ : δ * (1 - D) = 2 * γ := by
    dsimp only [δ, γ] at *
    nlinarith only [hratio]
  have hv : 1 / 20 ≤ EmptySatE2.baseDifference A D := by
    unfold EmptySatE2.baseDifference
    linarith only [hA, hAD]
  have hK : 0 < EmptySatE2.baseCredit δ A D := by
    have hp := mul_le_mul_of_nonneg_right
      (show 8 / 5 ≤ 2 - δ by linarith only [hδhi])
      (show 0 ≤ EmptySatE2.baseDifference A D by linarith only [hv])
    unfold EmptySatE2.baseCredit
    nlinarith only [hp, hv, hDhi]
  have hbudget := S.empty_sat_deleted_partner_support r p hpair hW hd hgap hN
  change δ * (A + b - 2 * (1 - 2 * d)) + 2 * m * (A - b) ^ 2 +
    (2 * (A + b) - 1) * (δ * (A + b) - 2 * γ) - (1 - (A + b)) ^ 2 / 12 +
      (12 / 25) * max ((1 - m) * (A - b) - (δ * (A + b) - 2 * γ) -
        (1 - (A + b)) / 12) 0 ^ 2 + 4 * δ * b * s ≤ 0 at hbudget
  have harg : (1 - m) * (A - b) - (δ * (A + b) - 2 * γ) -
      (1 - (A + b)) / 12 = EmptySatE2.baseCredit δ A D + 23 * L / 12 := by
    dsimp only [L, δ]
    unfold EmptySatE2.baseCredit EmptySatE2.baseDifference
    nlinarith only [hDγ]
  rw [harg, max_eq_left (by linarith only [hK, hL])] at hbudget
  have hid : EmptySatCorner.supportIntercept δ A D L + 4 * δ * b * s =
      (δ * (A + b - 2 * (1 - 2 * d)) + 2 * m * (A - b) ^ 2 +
        (2 * (A + b) - 1) * (δ * (A + b) - 2 * γ) - (1 - (A + b)) ^ 2 / 12 +
        (12 / 25) * (EmptySatE2.baseCredit δ A D + 23 * L / 12) ^ 2 + 4 * δ * b * s) -
          (δ * (1 - D - 2 * (1 - 2 * d)) - 37 / 1250) := by
    have hγ : γ = δ * (1 - D) / 2 := by nlinarith only [hDγ]
    rw [hγ]
    unfold EmptySatCorner.supportIntercept EmptySatE2.baseCredit EmptySatE2.baseDifference
    dsimp only [L, δ]
    ring
  nlinarith only [hid, hbudget, hcorr]

private theorem actual_negative_degree_load_nonneg
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r) (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m)) :
    0 ≤ ∫ x in S.universalNegativeRegion r p, -S.rootChargeRow r x *
      ((∫ y, adjacencyKernel W x y ∂μ) - 3 * S.originalAtomMass r +
        S.originalAtomMass p) ∂μ := by
  have hB := S.measurableSet_universalUpperE2BadRegion r p d c
  have hNeg := S.measurableSet_universalNegativeRegion r p
  have hsubset := S.universalNegativeRegion_subset_upperE2Bad r p d c
    (by linarith only [hA]) hmargin (by linarith only [hell.2])
  have hdegree := (ae_restrict_iff' hB).mp
    (P.ae_universalUpperE2Bad_originalDegree_ge S r p hpair hW hd hgap
      hN hA hAhalf hell hmargin)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hNeg, ae_restrict_of_ae hdegree] with x hx hdeg
  have hd := hdeg (hsubset hx)
  exact mul_nonneg (neg_nonneg.mpr hx.2.le) (by linarith only [hd])

end Erdos1017.CappedModel.SelectedHighLowStructure

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

private theorem actual_private_source_moments (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    let J := S.reverseCompulsorySource {p}
    let j := μ.real J
    let δ := 1 + m
    let D := (1 - m - 4 * (c - m * d)) / δ
    let L := μ.real (S.universalPartnerHoleRegion r p) +
      μ.real (S.universalPartnerCommonRegion r p) - D
    let E := D - S.originalAtomMass r
    let q := (∫ x in J, S.ownIndependentMass x ∂μ) / j
    let F := ∫ z, shiftedKernel W m z.1 z.2 ∂(μ.restrict J).prod (μ.restrict J)
    let e := (∫ z, PhysicalCliqueRepresentative.edgeIndicator
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) z
      ∂(μ.restrict J).prod (μ.restrict J)) / 2
    let dJ := ∫ x in J, S.universalRootDeficit r x ∂μ
    0 < L → E < L →
      (∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
        S.universalPartnerHoleMissingMass r p x < L) →
      0 ≤ q ∧ q < E ∧ 2 * L < j ∧ 0 < E ∧ (L + E) * L ≤ E * j ∧
        (j - 2 * L) * q ≤ E * j - (L + E) * L ∧
        2 * e = j ^ 2 - j * q ∧
        F ≤ 2 * j * dJ - δ * j ^ 2 - δ * j * (L - E) * q / (L + E) := by
  dsimp only
  intro hL hEL hsmall
  let J := S.reverseCompulsorySource {p}
  let j := μ.real J
  let ν := μ.restrict J
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  let δ := 1 + m
  let D := (1 - m - 4 * (c - m * d)) / δ
  let L := μ.real (S.universalPartnerHoleRegion r p) +
    μ.real (S.universalPartnerCommonRegion r p) - D
  let E := D - S.originalAtomMass r
  let q := (∫ x in J, S.ownIndependentMass x ∂μ) / j
  let F := ∫ z : Ω × Ω, shiftedKernel W m z.1 z.2 ∂ν.prod ν
  let e := (∫ z, G z ∂ν.prod ν) / 2
  let dJ := ∫ x in J, S.universalRootDeficit r x ∂μ
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hell]
  obtain ⟨_, hj, _, hSigma, hameas, ha, hdef, had, hrow, hbudget, hmarginal, htriangle⟩ :=
    R.empty_sat_corner_source_geometry r p hr hpair hW hd hgap hell hnull hL hEL hsmall
  have hνj : ν.real univ = j := measureReal_restrict_apply_univ J
  obtain ⟨hq, hqcap, hlower, hweighted⟩ := EmptySatCorner.deficit_moment_bounds
    ν S.ownIndependentMass (S.universalRootDeficit r)
    (by rw [hνj]; exact hj) ha hameas hdef had
    (hrow.mono (fun _ hx => hx.1)) (hrow.mono (fun _ hx => hx.2.1))
    hEL hδ (hrow.mono (fun _ hx => hx.2.2))
  simp only [hνj] at hq hqcap hlower hweighted
  have hbudget' : dJ ≤ δ * (j - L) := by linarith only [hbudget, hSigma]
  obtain ⟨hjL, hE, hqE, hmean, hmeanstrong⟩ :=
    EmptySatCorner.mean_mass_bounds_of_deficit_budget hj hq hqcap hEL hδ hlower hbudget'
  have hGmeas : Measurable G := PhysicalCliqueRepresentative.measurable_edgeIndicator
    (PhysicalRepresentative.measurable_adjacency W m)
  have hGi : Integrable G (ν.prod ν) := Integrable.of_bound hGmeas.aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      have hz := PhysicalCliqueRepresentative.edgeIndicator_bounds
        (Function.uncurry (PhysicalRepresentative.adjacency W m)) z
      rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
      exact hz.2))
  have hGeq : (∫ z, G z ∂ν.prod ν) = j ^ 2 - ∫ x in J, S.ownIndependentMass x ∂μ := by
    rw [integral_prod G hGi]
    have heq : (fun x => ∫ y, G (x, y) ∂ν) =ᵐ[ν] fun x => j - S.ownIndependentMass x :=
      hmarginal
    rw [integral_congr_ae heq, integral_sub (integrable_const j) ha,
      integral_const, smul_eq_mul, hνj]
    ring
  have hqmean : j * q = ∫ x in J, S.ownIndependentMass x ∂μ := by
    dsimp only [q]
    exact mul_div_cancel₀ _ (show j ≠ 0 from hj.ne')
  have heq : 2 * e = j ^ 2 - j * q := by
    dsimp only [e]
    nlinarith only [hGeq, hqmean]
  have hprod : ν.prod ν ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hMi : Integrable (fun z : Ω × Ω => shiftedKernel W m z.1 z.2) (ν.prod ν) := by
    have hi : Integrable (fun z : Ω × Ω => shiftedKernel W m z.1 z.2) (μ.prod μ) := by
      simpa only [mul_one] using KernelOperator.integrable_kernel_bilinear (shiftedKernel_measurable W m)
        (shiftedKernel_bound W m) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
    exact hi.mono_measure hprod
  have hGsym : ∀ᵐ z : Ω × Ω ∂ν.prod ν, G z = G z.swap := by
    apply Eventually.of_forall
    intro z
    have hb : Function.uncurry (PhysicalRepresentative.adjacency W m) z =
        Function.uncurry (PhysicalRepresentative.adjacency W m) z.swap :=
      PhysicalRepresentative.adjacency_symm W m z.1 z.2
    simpa only [G, PhysicalCliqueRepresentative.edgeIndicator] using
      congrArg (fun b : Bool => if b then (1 : ℝ) else 0) hb
  have htriangleIntegral := EmptySatCorner.triangle_deficit_moment_bound ν
    S.ownIndependentMass (S.universalRootDeficit r) (fun x y => G (x, y))
    (fun z => shiftedKernel W m z.1 z.2) hdef had hMi hGmeas
    (fun x y => PhysicalCliqueRepresentative.edgeIndicator_bounds
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) (x, y)) hGsym (by rw [hνj]; exact hmarginal) htriangle
  rw [hνj] at htriangleIntegral
  have htriangleIntegral' : F / 2 + δ * e +
      (∫ x in J, S.ownIndependentMass x * S.universalRootDeficit r x ∂μ) ≤ j * dJ := by
    dsimp only [F, e, δ, dJ]
    have hfunction : (fun q : Ω × Ω => G (q.1, q.2)) = G := rfl
    rw [hfunction] at htriangleIntegral
    nlinarith only [htriangleIntegral]
  have hF := (EmptySatCorner.square_moment_triangle_bound hj.le hq hqcap hEL.le hδ.le
    heq htriangleIntegral' hweighted).2
  exact ⟨hq, hqE, hjL, hE, hmean, hmeanstrong, heq, hF⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

private theorem actual_context_score_nonpos (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) (hstrip : 21 / 100 < 1 + m) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let J := S.reverseCompulsorySource {p}
    let j := μ.real J
    let delta := 1 + m
    let gamma := 2 * (c - m * d) + m
    let D := (1 - m - 4 * (c - m * d)) / delta
    let L := μ.real (S.universalPartnerHoleRegion r p) +
      μ.real (S.universalPartnerCommonRegion r p) - D
    let E := D - A
    let F := ∫ z, shiftedKernel W m z.1 z.2 ∂(μ.restrict J).prod (μ.restrict J)
    let e := S.emptySatPrivateEdgeMass p
    let dJ := ∫ x in J, S.universalRootDeficit r x ∂μ
    let eta := 3 * gamma / A - delta
    let cost := c - S.emptySatNegativeDegreeLoad r p / (2 * eta)
    0 < L → E < L →
      (∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
        S.universalPartnerHoleMissingMass r p x < L) →
      EmptySatCorner.hardScore delta A b gamma
        (EmptySatCorner.supportIntercept delta A D L) cost e F dJ j ≤ 0 := by
  dsimp only
  intro hL hEL hsmall
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let J := S.reverseCompulsorySource {p}
  let j := μ.real J
  let delta := 1 + m
  let gamma := 2 * (c - m * d) + m
  let D := (1 - m - 4 * (c - m * d)) / delta
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let L := s + u - D
  let F := ∫ z, shiftedKernel W m z.1 z.2 ∂(μ.restrict J).prod (μ.restrict J)
  let e := S.emptySatPrivateEdgeMass p
  let dJ := ∫ x in J, S.universalRootDeficit r x ∂μ
  let eta := 3 * gamma / A - delta
  let K := A * j - e
  let C0 := F / 2 + m * e + A * (j - dJ)
  let RJ := j * (gamma - m * (b + j) - A) + A * dJ - F
  let ZP := gamma - m * (b + s)
  let Uload := S.emptySatNegativeDegreeLoad r p
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨hell, hc, hh, _⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hdelta : 0 < delta := by linarith only [hstrip]
  have hdeltaHi : delta ≤ 2 / 5 := by dsimp only [delta]; linarith only [hell.1]
  have hcA := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  change c ≤ A ^ 2 at hcA
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hA : 7 / 20 ≤ A := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hA0
      (show A - 7 / 20 ≤ 0 by linarith only [hn])
    nlinarith only [hp, hc, hcA]
  have hholes := (R.corner_saturated_empty_source_excess_pos
    r p hr hpair hW hd hgap he heq hglobal hnull).2
  have hAD : A ≤ D := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap (by linarith only [hell.2]) hN hholes
  have hratio : delta * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hdelta.ne'
  have hDgamma : delta * (1 - D) = 2 * gamma := by
    dsimp only [delta, gamma] at *
    nlinarith only [hratio]
  have hcorr : 37 / 1250 < delta * (1 - D - 2 * (1 - 2 * d)) := by
    have hg : delta * (1 - 2 * d) + 37 / 2500 < gamma := by
      dsimp only [delta, gamma]
      nlinarith only [hc, hh]
    nlinarith only [hg, hDgamma]
  have hDhi : D ≤ 3 / 5 := by
    have hmissing : 23 / 100 ≤ 1 - 2 * d := by
      have hbox := (Benchmark.crossing_contact_location he heq).1
      linarith only [hbox.1]
    have hδmissing := mul_le_mul_of_nonneg_left hmissing hdelta.le
    nlinarith only [hcorr, hδmissing, hdelta]
  have hmass : A + b + s + u = 1 := S.universalPartner_regions_mass r p hpair.1
  have hLid : L = 1 - A - b - D := by dsimp only [L]; linarith only [hmass]
  have hsupport := actual_corner_support_intercept S r p hpair hW hd hgap hN
    hdelta hdeltaHi hA hAD hDhi (by rw [← hLid]; exact hL) hcorr
  change EmptySatCorner.supportIntercept delta A D (1 - A - b - D) +
    4 * delta * b * s < 0 at hsupport
  rw [← hLid] at hsupport
  obtain ⟨hK, hC, _, _, hcost⟩ := R.empty_sat_corner_context_price
    r p hr hpair P hW hd hgap he heq hglobal hnull hstrip hL hEL hsmall
  change 0 < K at hK
  change 0 < C0 at hC
  change c ≤ A * b + K + (K * b * ZP - A * b * C0 - (A ^ 2 - K) * RJ) / C0 +
    Uload / (2 * eta) at hcost
  have hCeq : C0 = F / 2 - (1 - delta) * e + A * j - A * dJ := by
    dsimp only [C0, delta]
    ring
  have hRJeq : RJ = j * (gamma + (1 - delta) * (b + j) - A) + A * dJ - F := by
    dsimp only [RJ, delta]
    ring
  have hZPeq : ZP = gamma + (1 - delta) * (b + s) := by dsimp only [ZP, delta]; ring
  exact EmptySatCorner.hard_score_nonpos_of_cost hdelta
    (show delta ≤ 1 by linarith only [hdeltaHi]) hK.le (by rw [← hCeq]; exact hC)
    (by rw [← hCeq, ← hRJeq, ← hZPeq]; exact hcost) hsupport.le

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

namespace Erdos1017.EmptySatCorner

private theorem hard_score_eq_Phi (δ A E L q j : ℝ) :
    hardEndpointScore δ A (EmptySatCornerHard.b A E L) (EmptySatCornerHard.gamma δ A E)
      (EmptySatCornerHard.P0 δ A E L) (EmptySatCornerHard.Wlo δ A E L) E L q j =
        EmptySatCornerHard.Phi δ A E L q j := by
  unfold hardEndpointScore hardScore EmptySatCornerHard.Phi
    EmptySatCornerHard.Kq EmptySatCornerHard.Cq EmptySatCornerHard.Rq
    EmptySatCornerHard.Fq EmptySatCornerHard.edgeMoment
  ring_nf

private theorem hard_Phi_pos {δ A E L q j : ℝ}
    (hδ : δ ∈ Icc (1 / 4 : ℝ) (2 / 5))
    (hA : A ∈ Icc (7 / 20 : ℝ) (3 / 8))
    (hE : E ∈ Icc (1 / 20 : ℝ) (29 / 250))
    (hL : L ∈ Icc E (E + (3 * A - 1) / 2))
    (hq : q ∈ Icc (0 : ℝ) E)
    (hjlo : (L + E) * L / E ≤ j)
    (hjhi : j ≤ EmptySatE2.baseDifference A (A + E) + L) :
    0 < EmptySatCornerHard.Phi δ A E L q j := by
  let jlo := (L + E) * L / E
  let jhi := EmptySatE2.baseDifference A (A + E) + L
  have hE0 : 0 < E := by linarith only [hE.1]
  have hL0 : 0 < L := hE0.trans_le hL.1
  have hjlo0 : 2 * L ≤ jlo := by
    apply (le_div_iff₀ hE0).mpr
    have hp := mul_nonneg hL0.le (sub_nonneg.mpr hL.1)
    nlinarith only [hp]
  have hj : j ∈ Icc (2 * L) jhi := ⟨hjlo0.trans hjlo, hjhi⟩
  have hjlo' : jlo ∈ Icc (2 * L) jhi := ⟨hjlo0, hjlo.trans hjhi⟩
  have hmono : StrictMonoOn (fun t => EmptySatCornerHard.Phi δ A E L 0 t)
      (Icc (2 * L) jhi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t _
      exact (EmptySatCornerHard.PhiZero_hasDerivAt δ A E L t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(EmptySatCornerHard.PhiZero_hasDerivAt δ A E L t).deriv]
      exact EmptySatCornerHard.zero_derivative_pos hδ hA hE hL (interior_subset ht)
  have hzero : 0 < EmptySatCornerHard.Phi δ A E L 0 j :=
    (EmptySatCornerHard.zero_lower_endpoint_pos hδ hA hE hL).trans_le
      (hmono.monotoneOn hjlo' hj hjlo)
  have hupper := EmptySatCornerHard.moment_endpoint_pos hδ hA hE hL hj
  rw [← hard_score_eq_Phi] at hzero hupper ⊢
  exact hard_score_pos_of_endpoints ⟨by linarith only [hδ.1], by linarith only [hδ.2]⟩
    hE0 hL.1 hq hzero hupper


end Erdos1017.EmptySatCorner

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual hard nonexceptional sector spends the one original negative
quota and the same private-source moments, then applies the exact coupled
moment certificates. No scalar cost or moment bound is supplied. -/
theorem no_corner_saturated_empty_source_hard (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (hsmall : let H := S.universalPartnerHoleRegion r p
      let D := (1 - m - 4 * (c - m * d)) / (1 + m)
      let L := μ.real H + μ.real (S.universalPartnerCommonRegion r p) - D
      ∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L)
    (hhardδ : 1 / 4 < 1 + m)
    (hhardE : 1 / 20 < (1 - m - 4 * (c - m * d)) / (1 + m) - S.originalAtomMass r) :
    False := by
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let J := S.reverseCompulsorySource {p}
  let j := μ.real J
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let u := μ.real (S.universalPartnerCommonRegion r p)
  let δ := 1 + m
  let gamma := 2 * (c - m * d) + m
  let D := (1 - m - 4 * (c - m * d)) / δ
  let E := D - A
  let L := s + u - D
  let q := (∫ x in J, S.ownIndependentMass x ∂μ) / j
  let e := S.emptySatPrivateEdgeMass p
  let F := ∫ z, shiftedKernel W m z.1 z.2 ∂(μ.restrict J).prod (μ.restrict J)
  let dJ := ∫ x in J, S.universalRootDeficit r x ∂μ
  let eta := 3 * gamma / A - δ
  let K := A * j - e
  let C0 := F / 2 + m * e + A * (j - dJ)
  let RJ := j * (gamma - m * (b + j) - A) + A * dJ - F
  let ZP := gamma - m * (b + s)
  let Bc := 1 - 3 * A + b
  let Nmax := (2 * (c - m * d) - (1 - m) * A) / 2
  let Uload := S.emptySatNegativeDegreeLoad r p
  let Wcost := c - Uload / (2 * eta)
  have hmass : A + b + s + u = 1 := S.universalPartner_regions_mass r p hpair.1
  have hLid : L = 1 - A - b - D := by dsimp only [L]; linarith only [hmass]
  by_cases hEL : E < L
  swap
  · exact R.no_corner_saturated_empty_source_small_excess
      r p hr hpair hW hd hgap he heq hglobal hnull
      (by change 1 - A - b - D ≤ E; rw [← hLid]; exact le_of_not_gt hEL)
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  have hstrip : 21 / 100 < 1 + m := by linarith only [hhardδ]
  obtain ⟨hδbox, hA, hEcap, hL0, _, _⟩ := saturated_corner_joint_price
    R r p hr hpair P hW hd hgap he heq hglobal hnull hstrip
  have hL : 0 < L := by rw [hLid]; exact hL0
  have hApos : 0 < A := by linarith only [hA.1]
  have hδpos : 0 < δ := by linarith only [hδbox.1]
  have hδ : δ ∈ Icc (1 / 4 : ℝ) (2 / 5) := ⟨hhardδ.le, hδbox.2⟩
  have hA' : A ∈ Icc (7 / 20 : ℝ) (3 / 8) := ⟨by linarith only [hA.1], hA.2⟩
  have hfrac : 37 / 500 ≤ 37 / (1250 * δ) := by
    apply (le_div_iff₀ (show 0 < 1250 * δ by positivity)).mpr
    linarith only [hδ.2]
  have hE : E ∈ Icc (1 / 20 : ℝ) (29 / 250) := by
    refine ⟨hhardE.le, ?_⟩
    have hcap := hEcap.2
    unfold EmptySatCorner.cornerDeficitCap at hcap
    linarith only [hcap, hfrac, hA.1]
  obtain ⟨hellbox, hc, hh, _⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hell : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith only [hellbox.1, hellbox.2]
  obtain ⟨_, _, hmargin, _, _⟩ := R.empty_sat_corner_bad_region
    r p hr hpair P hW hd hgap he heq hglobal hnull hstrip
  obtain ⟨_, hj, hjcap, hSigma, _, _, _, _, _, hbudget, _, _⟩ :=
    R.empty_sat_corner_source_geometry r p hr hpair hW hd hgap hell.2 hnull hL hEL hsmall
  obtain ⟨hq0, hqE, hjL, hEpos, hmean, _, hEdge, hFbound⟩ :=
    actual_private_source_moments R r p hr hpair hW hd hgap hell.2 hnull hL hEL hsmall
  change 0 ≤ q at hq0
  change q < E at hqE
  change 2 * L < j at hjL
  change 0 < E at hEpos
  change (L + E) * L ≤ E * j at hmean
  change 2 * e = j ^ 2 - j * q at hEdge
  change F ≤ 2 * j * dJ - δ * j ^ 2 - δ * j * (L - E) * q / (L + E) at hFbound
  have hjupper : j < 3 * A - 1 + E + L := by
    change b + j < A at hjcap
    dsimp only [E]
    nlinarith only [hjcap, hLid]
  have hEJ := mul_lt_mul_of_pos_left hjupper hEpos
  have hsquare : L ^ 2 < E * (3 * A - 1 + E) := by nlinarith only [hmean, hEJ]
  have hwidth : L - E < (3 * A - 1) / 2 := by
    by_contra hn
    have hp := mul_nonneg
      (show 0 ≤ L - (E + (3 * A - 1) / 2) by linarith only [hn])
      (show 0 ≤ L + (E + (3 * A - 1) / 2) by linarith only [hL, hEpos, hA.1])
    nlinarith only [hsquare, hp, sq_nonneg (3 * A - 1)]
  have hLbox : L ∈ Icc E (E + (3 * A - 1) / 2) := ⟨hEL.le, by linarith only [hwidth]⟩
  have hjlo : (L + E) * L / E ≤ j := by
    apply (div_le_iff₀ hEpos).mpr
    nlinarith only [hmean]
  have hjhi : j ≤ EmptySatE2.baseDifference A (A + E) + L := by
    unfold EmptySatE2.baseDifference
    linarith only [hjupper]
  have hPhi := EmptySatCorner.hard_Phi_pos hδ hA' hE hLbox ⟨hq0, hqE.le⟩ hjlo hjhi
  have hratio : δ * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hδpos.ne'
  have hDgamma : δ * (1 - D) = 2 * gamma := by
    dsimp only [δ, gamma] at *
    nlinarith only [hratio]
  have hgammaEq : gamma = EmptySatCornerHard.gamma δ A E := by
    unfold EmptySatCornerHard.gamma
    dsimp only [E]
    nlinarith only [hDgamma]
  have hbEq : b = EmptySatCornerHard.b A E L := by
    unfold EmptySatCornerHard.b
    dsimp only [E]
    linarith only [hLid]
  have hNmaxEq : Nmax = EmptySatCornerHard.Nmax δ A E := by
    unfold EmptySatCornerHard.Nmax
    rw [← hgammaEq]
    dsimp only [Nmax, δ, gamma]
    ring
  have heta : 0 < eta := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hApos).mpr
    have hp := mul_pos hApos hδpos
    nlinarith only [hmargin, hp]
  have henEq : EmptySatCornerHard.en δ A E = A * eta := by
    unfold EmptySatCornerHard.en
    rw [← hgammaEq]
    dsimp only [eta]
    field_simp [hApos.ne']
  have hEn := (EmptySatCornerHard.enclosure_positive_factors hδ hA' hE hLbox).2.2.1
  have hNmax0 : 0 ≤ Nmax := by
    have hgamma0 : 0 ≤ gamma := (hW.strict_gap_structure hd hgap).gamma_pos.le
    have hp : (3 / 5 : ℝ) * (5 / 8) ≤ (1 - δ) * (1 - A) :=
      mul_le_mul (by linarith only [hδ.2]) (by linarith only [hA.2])
        (by norm_num) (by linarith only [hδ.2])
    have hid : Nmax = (1 - δ + gamma - (2 - δ) * A) / 2 := by
      dsimp only [Nmax, δ, gamma]
      ring
    nlinarith only [hp, hid, hgamma0, hA.2]
  obtain ⟨hK, hC, hBc, hUcap, hcost⟩ := R.empty_sat_corner_context_price
    r p hr hpair P hW hd hgap he heq hglobal hnull hstrip hL hEL hsmall
  change 0 < K at hK
  change 0 < C0 at hC
  change 0 ≤ Bc at hBc
  change Uload ≤ Bc * Nmax at hUcap
  change c ≤ A * b + K + (K * b * ZP - A * b * C0 - (A ^ 2 - K) * RJ) / C0 +
    Uload / (2 * eta) at hcost
  have hU0 := actual_negative_degree_load_nonneg S r p hpair P hW hd hgap hN
    (by linarith only [hA.1]) (by linarith only [hA.2]) hell hmargin
  change 0 ≤ Uload at hU0
  have hWloEq : EmptySatCornerHard.Wlo δ A E L =
      123 / 1000 - Bc * Nmax / (2 * eta) := by
    unfold EmptySatCornerHard.Wlo EmptySatCornerHard.Bc
    rw [← hbEq, ← hNmaxEq, henEq]
    dsimp only [Bc]
    field_simp [hApos.ne', heta.ne']
  have hdiv : Uload / (2 * eta) ≤ Bc * Nmax / (2 * eta) := by
    have hden : 0 < 2 * eta := by positivity
    have hleft := div_mul_cancel₀ Uload hden.ne'
    have hright := div_mul_cancel₀ (Bc * Nmax) hden.ne'
    apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith only [hleft, hright, hUcap]
  have hWlo : EmptySatCornerHard.Wlo δ A E L ≤ Wcost := by
    rw [hWloEq]
    dsimp only [Wcost]
    linarith only [hdiv, hc]
  have hCeq : C0 = F / 2 - (1 - δ) * e + A * j - A * dJ := by
    dsimp only [C0, δ]
    ring
  have hRJeq : RJ = j * (gamma + (1 - δ) * (b + j) - A) + A * dJ - F := by
    dsimp only [RJ, δ]
    ring
  have hZPeq : ZP = gamma + (1 - δ) * (b + s) := by dsimp only [ZP, δ]; ring
  have hcorr : 37 / 1250 < δ * (1 - D - 2 * (1 - 2 * d)) := by
    have hg : δ * (1 - 2 * d) + 37 / 2500 < gamma := by
      dsimp only [δ, gamma]
      nlinarith only [hc, hh]
    nlinarith only [hg, hDgamma]
  have hDhi : D ≤ 3 / 5 := by
    have hcap := hEcap.2
    have hterm : 0 < 37 / (1250 * δ) := by positivity
    unfold EmptySatCorner.cornerDeficitCap at hcap
    change D - A ≤ 336 / 625 - 37 / (1250 * δ) - A at hcap
    linarith only [hcap, hterm]
  have hsupport := actual_corner_support_intercept S r p hpair hW hd hgap hN
    hδpos hδ.2 (by linarith only [hA.1])
    (by
      have hnonneg := hEcap.1
      change 0 ≤ D - A at hnonneg
      linarith only [hnonneg])
    hDhi (by rw [← hLid]; exact hL) hcorr
  have hP0eq : EmptySatCorner.supportIntercept δ A D L =
      EmptySatCornerHard.P0 δ A E L := by
    unfold EmptySatCorner.supportIntercept EmptySatCornerHard.P0 EmptySatCornerHard.b
    dsimp only [E]
    ring
  change EmptySatCorner.supportIntercept δ A D (1 - A - b - D) + 4 * δ * b * s < 0
    at hsupport
  rw [← hLid, hP0eq] at hsupport
  have hnonpos := EmptySatCorner.hard_score_nonpos_of_cost
    (δ := δ) (A := A) (b := b) (gamma := gamma) (P0 := EmptySatCornerHard.P0 δ A E L)
    (c := c) (U := Uload) (eta := eta) (e := e) (F := F) (dJ := dJ) (j := j) (s := s)
    hδpos (show δ ≤ 1 by linarith only [hδ.2]) hK.le (hCeq ▸ hC)
    (by simpa only [← hCeq, ← hRJeq, ← hZPeq] using hcost) hsupport.le
  have hcA := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  have hWmax : Wcost ≤ A ^ 2 := by
    have hquot : 0 ≤ Uload / (2 * eta) := div_nonneg hU0 (by positivity)
    dsimp only [Wcost]
    change c ≤ A ^ 2 at hcA
    linarith only [hcA, hquot]
  have hBcCap : Bc ≤ 2 - 5 * A - 2 * E := by
    have hbform : b = 1 - 2 * A - E - L := by dsimp only [E]; linarith only [hLid]
    dsimp only [Bc]
    linarith only [hbform, hEL]
  have hWloForm : EmptySatCornerHard.Wlo δ A E L =
      123 / 1000 - A * Bc * Nmax / (2 * EmptySatCornerHard.en δ A E) := by
    unfold EmptySatCornerHard.Wlo EmptySatCornerHard.Bc
    rw [← hbEq, ← hNmaxEq]
  have hWlower := EmptySatCorner.hard_lower_cost_gt hApos.le hEn hNmax0 hBcCap
    (by rw [hNmaxEq]; exact EmptySatCornerHard.selector_guard_pos hδ hA' hE)
  rw [← hWloForm] at hWlower
  have hjA : j < A := by
    change b + j < A at hjcap
    have hb0 : 0 ≤ b := measureReal_nonneg
    linarith only [hjcap, hb0]
  have he0 : 0 ≤ e := by
    have hprod := mul_nonneg (show 0 ≤ j from hj.le)
      (show 0 ≤ j - q by linarith only [hjL, hEL, hqE, hEpos])
    nlinarith only [hEdge, hprod]
  have hCq := EmptySatCorner.hard_source_coefficient_pos hδ hApos hj hjA hEpos hEL
    ⟨hq0, hqE.le⟩ hEdge
  have hbudget' : dJ ≤ δ * (j - L) := by linarith only [hbudget, hSigma]
  have hlower := EmptySatCorner.hard_score_lower (b := b) (gamma := gamma)
    (P0 := EmptySatCornerHard.P0 δ A E L) hApos hj.le he0 hjA
    (show 2 * E < j by linarith only [hjL, hEL]) hWmax hWlo
    (hWlower.trans_le hWlo) hFbound hbudget' hCq.le
  have heq' : e = j * (j - q) / 2 := by nlinarith only [hEdge]
  rw [heq'] at hlower hnonpos
  change EmptySatCorner.hardEndpointScore δ A b gamma
    (EmptySatCornerHard.P0 δ A E L) (EmptySatCornerHard.Wlo δ A E L) E L q j ≤ _ at hlower
  rw [hbEq, hgammaEq, EmptySatCorner.hard_score_eq_Phi] at hlower
  rw [hbEq, hgammaEq] at hnonpos
  exact (not_lt_of_ge (hlower.trans hnonpos)) hPhi


/-- All original saturated corner sectors with a null entire source
are excluded. Every scalar and physical sector premise is derived. -/
theorem no_corner_saturated_empty_source (R : S.ReverseRecovery)
    (r p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) : False := by
  let H := S.universalPartnerHoleRegion r p
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  let L := μ.real H + μ.real (S.universalPartnerCommonRegion r p) - D
  let E := D - S.originalAtomMass r
  by_cases hsmall : ∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L
  · by_cases hdelta : 1 + m ≤ 1 / 4
    · exact R.no_corner_saturated_empty_source_nonexceptional_easy
        r p hr hpair hW hd hgap he heq hglobal hnull hsmall (Or.inr hdelta)
    · by_cases hE : E ≤ 1 / 20
      · exact R.no_corner_saturated_empty_source_nonexceptional_easy
          r p hr hpair hW hd hgap he heq hglobal hnull hsmall (Or.inl hE)
      · exact R.no_corner_saturated_empty_source_hard
          r p hr hpair hW hd hgap he heq hglobal hnull hsmall
          (lt_of_not_ge hdelta) (lt_of_not_ge hE)
  · exact R.no_corner_saturated_empty_source_exceptional
      r p hr hpair hW hd hgap he heq hglobal hnull hsmall

/-- An actual singleton corner recovery with null entire source is
impossible. Both saturation alternatives are handled in the original model. -/
theorem no_corner_one_center_empty_source (R : S.ReverseRecovery)
    (r : S.I) (hr : R.plateau = {r})
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) : False := by
  by_cases hsat : ∃ p : S.I, S.IsSaturatedAtomPair r p
  · obtain ⟨p, hpair⟩ := hsat
    exact R.no_corner_saturated_empty_source r p hr hpair hW hd hgap he heq hglobal hnull
  · exact R.no_corner_unsaturated_empty_source r hr hW hd hgap he heq hglobal hnull
      (fun p _ hpair => hsat ⟨p, hpair⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

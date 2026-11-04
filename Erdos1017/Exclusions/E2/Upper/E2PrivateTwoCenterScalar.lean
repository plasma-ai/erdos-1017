module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Scalar contradiction for the private two-center case

The private two-center `E₂` scalar capacity and entire-source budget are
incompatible throughout the closed upper range `q ≤ 1/5`
(`private_two_center_scalar_contradiction`).
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators unitInterval

namespace Erdos1017.LowerE2Scalar

private def privateD (z : ℝ) : ℝ := z ^ 2 + z - 1

private def privateY (z : ℝ) : ℝ := z * (2 * z - 1) / (8 * privateD z)

private def privateCap (z : ℝ) : ℝ := (3 * z - 2) / (2 * privateD z)

private def privateN (z : ℝ) : ℝ :=
  40 * z - 182 * z ^ 2 + 267 * z ^ 3 - 126 * z ^ 4

private def privateP (z : ℝ) : ℝ :=
  16 - 64 * z + 59 * z ^ 2 + 21 * z ^ 3 - 27 * z ^ 4

private def privateV (z : ℝ) : ℝ := privateN z / (8 * privateP z)

private def privateVderivNumerator (z : ℝ) : ℝ :=
  640 - 5824 * z + 22104 * z ^ 2 - 43920 * z ^ 3 +
    47007 * z ^ 4 - 24696 * z ^ 5 + 4563 * z ^ 6

private theorem privateD_pos {z : ℝ} (hz : z ∈ Icc (2 / 3 : ℝ) (369 / 500)) :
    0 < privateD z := by
  have hzsq : (2 / 3 : ℝ) ^ 2 ≤ z ^ 2 := by
    gcongr
    exact hz.1
  unfold privateD
  nlinarith [hz.1, hzsq]

private theorem privateP_eq (z : ℝ) :
    privateP z = privateD z * (4 - 3 * z) * (9 * z - 4) := by
  unfold privateP privateD
  ring

private theorem privateP_pos {z : ℝ} (hz : z ∈ Icc (2 / 3 : ℝ) (369 / 500)) :
    0 < privateP z := by
  rw [privateP_eq]
  exact mul_pos (mul_pos (privateD_pos hz) (by linarith [hz.2])) (by linarith [hz.1])

private theorem private_bernstein_sum_pos (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : ∀ i, (1 / 100 : ℝ) ≤ c i) (x : I) :
    0 < ∑ i, c i * bernstein n i x := by
  have hsum : (∑ i : Fin (n + 1), (1 / 100 : ℝ) * bernstein n i x) ≤
      ∑ i : Fin (n + 1), c i * bernstein n i x :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i) bernstein_nonneg)
  rw [← Finset.mul_sum, bernstein.probability, mul_one] at hsum
  exact (by norm_num : (0 : ℝ) < 1 / 100).trans_le hsum

private theorem privateVderivNumerator_pos {z : ℝ}
    (hz : z ∈ Icc (2 / 3 : ℝ) (369 / 500)) :
    0 < privateVderivNumerator z := by
  let x : I := ⟨(z - 2 / 3) / (369 / 500 - 2 / 3), by
    constructor <;> norm_num at * <;> linarith [hz.1, hz.2]⟩
  have hpos := private_bernstein_sum_pos 6
    (fun i => ![16 / 9, 19712 / 10125, 1478873 / 703125,
      694896151 / 312500000, 6401777121641 / 2812500000000,
      311989760066033 / 140625000000000,
      31200365108363203 / 15625000000000000] i)
    (by intro i; fin_cases i <;> norm_num) x
  convert hpos using 1
  norm_num [privateVderivNumerator, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

private theorem privateV_hasDerivAt {z : ℝ}
    (hz : z ∈ Icc (2 / 3 : ℝ) (369 / 500)) :
    HasDerivAt privateV (privateVderivNumerator z / (8 * privateP z ^ 2)) z := by
  have hi := hasDerivAt_id z
  have hN : HasDerivAt privateN
      (40 - 364 * z + 801 * z ^ 2 - 504 * z ^ 3) z := by
    have hN0 := (hi.const_mul 40).sub ((hi.pow 2).const_mul 182)
    have hN1 := hN0.add ((hi.pow 3).const_mul 267)
    have hN2 := hN1.sub ((hi.pow 4).const_mul 126)
    convert hN2 using 1
    · funext x
      dsimp [privateN]
    · simp only [id_eq]
      ring
  have hP : HasDerivAt privateP
      (-64 + 118 * z + 63 * z ^ 2 - 108 * z ^ 3) z := by
    have hP0 := (hasDerivAt_const z (16 : ℝ)).sub (hi.const_mul 64)
    have hP1 := hP0.add ((hi.pow 2).const_mul 59)
    have hP2 := hP1.add ((hi.pow 3).const_mul 21)
    have hP3 := hP2.sub ((hi.pow 4).const_mul 27)
    convert hP3 using 1
    · funext x
      dsimp [privateP]
    · simp only [id_eq]
      ring
  have hPne : 8 * privateP z ≠ 0 :=
    mul_ne_zero (by norm_num) (privateP_pos hz).ne'
  convert hN.div (hP.const_mul 8) hPne using 1
  · rfl
  · dsimp [privateN, privateP, privateVderivNumerator]
    field_simp
    ring

private theorem privateV_strictMonoOn :
    StrictMonoOn privateV (Icc (2 / 3 : ℝ) (369 / 500)) := by
  have hc : ContinuousOn privateV (Icc (2 / 3 : ℝ) (369 / 500)) := by
    intro z hz
    have hPne := (privateP_pos hz).ne'
    apply ContinuousAt.continuousWithinAt
    unfold privateV privateN privateP at *
    fun_prop (disch := positivity)
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
  intro z hz
  rw [(privateV_hasDerivAt (interior_subset hz)).deriv]
  exact div_pos (privateVderivNumerator_pos (interior_subset hz))
    (by have hP := privateP_pos (interior_subset hz); positivity : 0 < 8 * privateP z ^ 2)

private theorem privateY_hasDerivAt {z : ℝ}
    (hz : z ∈ Icc (2 / 3 : ℝ) (369 / 500)) :
    HasDerivAt privateY ((z - 1) * (3 * z - 1) / (8 * privateD z ^ 2)) z := by
  have hi := hasDerivAt_id z
  have hD := ((hi.pow 2).add hi).sub (hasDerivAt_const z (1 : ℝ))
  have hN := hi.mul ((hi.const_mul 2).sub (hasDerivAt_const z (1 : ℝ)))
  have hDne : 8 * privateD z ≠ 0 :=
    mul_ne_zero (by norm_num) (privateD_pos hz).ne'
  convert hN.div (hD.const_mul 8) hDne using 1
  · rfl
  · dsimp [privateD, privateY]
    field_simp
    ring

private theorem privateCap_hasDerivAt {z : ℝ}
    (hz : z ∈ Icc (2 / 3 : ℝ) (369 / 500)) :
    HasDerivAt privateCap (-(z - 1) * (3 * z - 1) / (2 * privateD z ^ 2)) z := by
  have hi := hasDerivAt_id z
  have hD := ((hi.pow 2).add hi).sub (hasDerivAt_const z (1 : ℝ))
  have hN := (hi.const_mul 3).sub (hasDerivAt_const z (2 : ℝ))
  have hDne : 2 * privateD z ≠ 0 :=
    mul_ne_zero (by norm_num) (privateD_pos hz).ne'
  convert hN.div (hD.const_mul 2) hDne using 1
  · rfl
  · dsimp [privateD, privateCap]
    field_simp
    ring

private theorem privateY_strictAntiOn :
    StrictAntiOn privateY (Icc (2 / 3 : ℝ) (369 / 500)) := by
  have hc : ContinuousOn privateY (Icc (2 / 3 : ℝ) (369 / 500)) := by
    intro z hz
    have hDne := (privateD_pos hz).ne'
    apply ContinuousAt.continuousWithinAt
    unfold privateY privateD at *
    fun_prop (disch := positivity)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
  intro z hz
  rw [(privateY_hasDerivAt (interior_subset hz)).deriv]
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (by linarith [(interior_subset hz).2])
      (by linarith [(interior_subset hz).1])
  · have hD := privateD_pos (interior_subset hz)
    positivity

private theorem privateCap_strictMonoOn :
    StrictMonoOn privateCap (Icc (2 / 3 : ℝ) (369 / 500)) := by
  have hc : ContinuousOn privateCap (Icc (2 / 3 : ℝ) (369 / 500)) := by
    intro z hz
    have hDne := (privateD_pos hz).ne'
    apply ContinuousAt.continuousWithinAt
    unfold privateCap privateD at *
    fun_prop (disch := positivity)
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
  intro z hz
  rw [(privateCap_hasDerivAt (interior_subset hz)).deriv]
  apply div_pos
  · have hz1 : z - 1 < 0 := by linarith [(interior_subset hz).2]
    have hz2 : 0 < 3 * z - 1 := by linarith [(interior_subset hz).1]
    exact mul_pos (neg_pos.mpr hz1) hz2
  · have hD := privateD_pos (interior_subset hz)
    positivity

private theorem private_radical_gap_of_interval {z l r p v : ℝ}
    (hglobal : z ∈ Icc (2 / 3 : ℝ) (369 / 500))
    (hl : l ∈ Icc (2 / 3 : ℝ) (369 / 500))
    (hr : r ∈ Icc (2 / 3 : ℝ) (369 / 500))
    (hz : z ∈ Icc l r) (hp : 0 ≤ p)
    (hY : p ^ 2 < privateY r / 4)
    (hV : v ^ 2 ≤ privateV l)
    (hcap : privateCap r < p + v) :
    privateCap z < Real.sqrt (privateY z) / 2 + Real.sqrt (privateV z) := by
  have hYle : privateY r ≤ privateY z := by
    rcases hz.2.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (privateY_strictAntiOn hglobal hr hlt).le
  have hVle : privateV l ≤ privateV z := by
    rcases hz.1.eq_or_lt with heq | hlt
    · rw [← heq]
    · exact (privateV_strictMonoOn hl hglobal hlt).le
  have hcaple : privateCap z ≤ privateCap r := by
    rcases hz.2.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (privateCap_strictMonoOn hglobal hr hlt).le
  have hYpos : 0 ≤ privateY z := by nlinarith [sq_nonneg p]
  have hVpos : 0 ≤ privateV z := by nlinarith [sq_nonneg v]
  have hpS : p < Real.sqrt (privateY z) / 2 := by
    have hs := Real.sq_sqrt hYpos
    have hn := Real.sqrt_nonneg (privateY z)
    nlinarith
  have hvS : v ≤ Real.sqrt (privateV z) := by
    have hs := Real.sq_sqrt hVpos
    have hn := Real.sqrt_nonneg (privateV z)
    nlinarith
  linarith

private theorem private_radical_gap {z : ℝ}
    (hz : z ∈ Icc (2 / 3 : ℝ) (147 / 200)) :
    privateCap z < Real.sqrt (privateY z) / 2 + Real.sqrt (privateV z) := by
  have hglobal : z ∈ Icc (2 / 3 : ℝ) (369 / 500) :=
    ⟨hz.1, by linarith [hz.2]⟩
  by_cases hz1 : z ≤ 69 / 100
  · apply private_radical_gap_of_interval hglobal
      (show (2 / 3 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show (69 / 100 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show z ∈ Icc (2 / 3 : ℝ) (69 / 100) from ⟨hz.1, hz1⟩)
      (show (0 : ℝ) ≤ 11 / 50 by norm_num)
      (show (11 / 50 : ℝ) ^ 2 < privateY (69 / 100) / 4 by
        norm_num [privateY, privateD])
      (show (0 : ℝ) ^ 2 ≤ privateV (2 / 3) by
        norm_num [privateV, privateN, privateP])
      (show privateCap (69 / 100) < (11 / 50 : ℝ) + 0 by
        norm_num [privateCap, privateD])
  by_cases hz2 : z ≤ 18 / 25
  · apply private_radical_gap_of_interval hglobal
      (show (69 / 100 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show (18 / 25 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show z ∈ Icc (69 / 100 : ℝ) (18 / 25) from
        ⟨(lt_of_not_ge hz1).le, hz2⟩)
      (show (0 : ℝ) ≤ 2037 / 10000 by norm_num)
      (show (2037 / 10000 : ℝ) ^ 2 < privateY (18 / 25) / 4 by
        norm_num [privateY, privateD])
      (show (267 / 2000 : ℝ) ^ 2 ≤ privateV (69 / 100) by
        norm_num [privateV, privateN, privateP])
      (show privateCap (18 / 25) < (2037 / 10000 : ℝ) + 267 / 2000 by
        norm_num [privateCap, privateD])
  by_cases hz3 : z ≤ 73 / 100
  · apply private_radical_gap_of_interval hglobal
      (show (18 / 25 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show (73 / 100 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show z ∈ Icc (18 / 25 : ℝ) (73 / 100) from
        ⟨(lt_of_not_ge hz2).le, hz3⟩)
      (show (0 : ℝ) ≤ 1997 / 10000 by norm_num)
      (show (1997 / 10000 : ℝ) ^ 2 < privateY (73 / 100) / 4 by
        norm_num [privateY, privateD])
      (show (337 / 2000 : ℝ) ^ 2 ≤ privateV (18 / 25) by
        norm_num [privateV, privateN, privateP])
      (show privateCap (73 / 100) < (1997 / 10000 : ℝ) + 337 / 2000 by
        norm_num [privateCap, privateD])
  · apply private_radical_gap_of_interval hglobal
      (show (73 / 100 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show (147 / 200 : ℝ) ∈ Icc (2 / 3) (369 / 500) by norm_num)
      (show z ∈ Icc (73 / 100 : ℝ) (147 / 200) from
        ⟨(lt_of_not_ge hz3).le, hz.2⟩)
      (show (0 : ℝ) ≤ 4951 / 25000 by norm_num)
      (show (4951 / 25000 : ℝ) ^ 2 < privateY (147 / 200) / 4 by
        norm_num [privateY, privateD])
      (show (349 / 2000 : ℝ) ^ 2 ≤ privateV (73 / 100) by
        norm_num [privateV, privateN, privateP])
      (show privateCap (147 / 200) < (4951 / 25000 : ℝ) + 349 / 2000 by
        norm_num [privateCap, privateD])

private theorem private_parameter_identities {q : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    let z := (q + 2) / 3
    privateY z = gapFloor q / (2 * (1 - multiplier q)) ∧
      privateCap z = 1 - 2 * gapFloor q / (1 - multiplier q) ∧
      privateV z = gapFloor q * (5 * multiplier q - 2) /
        (4 * multiplier q * (2 - multiplier q)) := by
  let z := (q + 2) / 3
  have hz : z ∈ Icc (2 / 3 : ℝ) (369 / 500) := by
    dsimp [z]
    constructor <;> linarith [hq.1, hq.2]
  have hDexpr : privateD z = denominator q / 9 := by
    dsimp [privateD, denominator, z]
    ring
  have hPexpr : privateP z = denominator q / 9 * (2 - q) * (2 + 3 * q) := by
    rw [privateP_eq, hDexpr]
    dsimp [z]
    ring
  have hNexpr : privateN z = q * (1 + 2 * q) * (6 - 7 * q) * (q + 2) / 9 := by
    dsimp [privateN, z]
    ring
  have hR : denominator q ≠ 0 := (denominator_pos hq.1.le).ne'
  have hq2 : q + 2 ≠ 0 := by linarith [hq.1]
  have hq2' : 2 + q ≠ 0 := by linarith [hq.1]
  have hq0 : q ≠ 0 := hq.1.ne'
  have h2q : 2 - q ≠ 0 := by linarith [hq.2]
  have h3q : 2 + 3 * q ≠ 0 := by linarith [hq.1]
  have hδ : 1 - multiplier q ≠ 0 := by
    unfold multiplier
    apply sub_ne_zero.mpr
    intro heq
    have h := (div_eq_iff hq2').mp heq.symm
    linarith [hq.1]
  have hell : multiplier q ≠ 0 := by
    unfold multiplier
    exact div_ne_zero h2q hq2'
  have htwo : 2 - multiplier q ≠ 0 := by
    unfold multiplier
    apply sub_ne_zero.mpr
    intro heq
    have h := (div_eq_iff hq2').mp heq.symm
    linarith [hq.1]
  dsimp
  constructor
  · rw [show privateY z = z * (2 * z - 1) / (8 * privateD z) from rfl, hDexpr]
    dsimp [gapFloor, multiplier, z]
    field_simp [hq0]
    ring
  constructor
  · rw [show privateCap z = (3 * z - 2) / (2 * privateD z) from rfl, hDexpr]
    dsimp [gapFloor, multiplier, z]
    field_simp [hq0]
    unfold denominator
    ring
  · rw [show privateV z = privateN z / (8 * privateP z) from rfl, hNexpr, hPexpr]
    dsimp [gapFloor, multiplier]
    field_simp
    ring

private theorem private_quadratic_minimum {ell γ A R : ℝ}
    (hell : 0 < ell) (hell2 : ell < 2) (hell5 : 2 < 5 * ell)
    (hγ : 0 < γ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hidentity : ell * R ^ 2 = (2 - ell) * A ^ 2 - γ) :
    Real.sqrt (γ * (5 * ell - 2) / (4 * ell * (2 - ell))) ≤ A - R / 2 := by
  have hC : 0 < 4 * ell * (2 - ell) := by positivity
  have hrad : 0 ≤ γ * (5 * ell - 2) / (4 * ell * (2 - ell)) := by positivity
  have hAminus : 0 ≤ A - R / 2 := by
    by_contra hn
    have hlt : A < R / 2 := by linarith
    have hsq : A ^ 2 ≤ (R / 2) ^ 2 := by
      nlinarith [hA, hR, sq_nonneg (A + R / 2)]
    have hmul := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hell2.le)
    have hrest : 0 ≤ (5 * ell - 2) * R ^ 2 := by positivity
    nlinarith [hmul, hrest]
  have hsqidentity :
      4 * ell * (2 - ell) * (A - R / 2) ^ 2 - γ * (5 * ell - 2) =
        ((2 - ell) * A - 2 * ell * R) ^ 2 := by
    have hγeq : γ = (2 - ell) * A ^ 2 - ell * R ^ 2 := by linarith [hidentity]
    rw [hγeq]
    ring
  have hsq : γ * (5 * ell - 2) / (4 * ell * (2 - ell)) ≤ (A - R / 2) ^ 2 := by
    apply (div_le_iff₀ hC).mpr
    nlinarith [sq_nonneg ((2 - ell) * A - 2 * ell * R), hsqidentity]
  have hsqrt := Real.sq_sqrt hrad
  have hsqrtnonneg := Real.sqrt_nonneg (γ * (5 * ell - 2) / (4 * ell * (2 - ell)))
  nlinarith

/-- The private two-center E2 scalar capacity and entire-source budget are
incompatible throughout the closed upper range `q ≤ 1/5`. The displayed
capacity identity, energy bound, and budget are explicit premises; the
original-model geometry that produces them is not part of this statement. -/
theorem private_two_center_scalar_contradiction {q γ t A R : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hγ : gapFloor q < γ)
    (ht : 0 ≤ t) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hRidentity : multiplier q * R ^ 2 = (2 - multiplier q) * A ^ 2 - γ)
    (henergy : γ ≤ 2 * (1 - multiplier q) * t ^ 2)
    (hbudget : 1 - 2 * γ / (1 - multiplier q) ≥ t / 2 + A - R / 2) : False := by
  have hq0 : 0 ≤ q := hq.1.le
  have hq2 : 0 < 2 + q := by linarith [hq.1]
  have hell : 0 < multiplier q := by
    unfold multiplier
    exact div_pos (by linarith [hq.2]) hq2
  have helllt : multiplier q < 1 := by
    unfold multiplier
    apply (div_lt_iff₀ hq2).mpr
    linarith [hq.1]
  have hell2 : multiplier q < 2 := by linarith [helllt]
  have helllower : (9 / 11 : ℝ) ≤ multiplier q := by
    unfold multiplier
    apply (le_div_iff₀ hq2).mpr
    linarith [hq.2]
  have hell5 : 2 < 5 * multiplier q := by linarith [helllower]
  have hδ : 0 < 1 - multiplier q := sub_pos.mpr helllt
  have hγpos : 0 < γ := by
    have hgpos : 0 < gapFloor q := by
      unfold gapFloor
      exact div_pos (mul_pos hq.1 (by linarith [hq.1]))
        (mul_pos (by norm_num) (denominator_pos hq0))
    exact hgpos.trans hγ
  have hD2 : 0 < 2 * (1 - multiplier q) := by positivity
  have hD4 : 0 < 4 * multiplier q * (2 - multiplier q) := by positivity
  have htbound : Real.sqrt (γ / (2 * (1 - multiplier q))) ≤ t := by
    have hrad : 0 ≤ γ / (2 * (1 - multiplier q)) := by positivity
    have hsquare : γ / (2 * (1 - multiplier q)) ≤ t ^ 2 := by
      apply (div_le_iff₀ hD2).mpr
      nlinarith [henergy]
    have hs := Real.sq_sqrt hrad
    have hsnonneg := Real.sqrt_nonneg (γ / (2 * (1 - multiplier q)))
    nlinarith
  have hAbound := private_quadratic_minimum hell hell2 hell5 hγpos hA hR hRidentity
  have hXorder : gapFloor q / (2 * (1 - multiplier q)) ≤
      γ / (2 * (1 - multiplier q)) :=
    div_le_div_of_nonneg_right hγ.le hD2.le
  have hVorder : gapFloor q * (5 * multiplier q - 2) /
      (4 * multiplier q * (2 - multiplier q)) ≤
      γ * (5 * multiplier q - 2) /
        (4 * multiplier q * (2 - multiplier q)) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγ.le (by linarith [hell5])) hD4.le
  have hCapOrder : 1 - 2 * γ / (1 - multiplier q) <
      1 - 2 * gapFloor q / (1 - multiplier q) := by
    have hh := div_lt_div_of_pos_right hγ hδ
    have hγeq : 2 * γ / (1 - multiplier q) =
        2 * (γ / (1 - multiplier q)) := by ring
    have hgeq : 2 * gapFloor q / (1 - multiplier q) =
        2 * (gapFloor q / (1 - multiplier q)) := by ring
    rw [hγeq, hgeq]
    linarith
  let z := (q + 2) / 3
  have hz : z ∈ Icc (2 / 3 : ℝ) (147 / 200) := by
    dsimp [z]
    constructor <;> linarith [hq.1, hq.2]
  obtain ⟨hYid, hCid, hVid⟩ := private_parameter_identities hq
  have hgapz := private_radical_gap hz
  change privateCap z < Real.sqrt (privateY z) / 2 + Real.sqrt (privateV z) at hgapz
  rw [hYid, hCid, hVid] at hgapz
  have hXsqrt := Real.sqrt_le_sqrt hXorder
  have hVsqrt := Real.sqrt_le_sqrt hVorder
  linarith [hgapz, hCapOrder, hXsqrt, hVsqrt, htbound, hAbound, hbudget]

end Erdos1017.LowerE2Scalar

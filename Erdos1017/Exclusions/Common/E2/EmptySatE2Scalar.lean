module

public import Erdos1017.Exclusions.Common.E2.EmptySatE2Certificates

/-!
# Scalar bounds for the empty-source saturated `E₂` case

The integrated support score and the exceptional-restriction score are defined
and shown strictly positive, a common small-atom pointwise deficit floor is
derived, and the lower contact strip is excluded by the universal mass cap.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.EmptySatE2

/-- The exact weighted support score after integrating the original deficit floor. -/
def integratedScore (δ h A D L : ℝ) : ℝ :=
  (D - A) * supportScore δ h A D L + 4 * δ * (1 - A - D - L) * L ^ 2

/-- The actual exceptional-restriction score before its deficit is maximized. -/
def rawExceptionalScore (δ h A D e Z : ℝ) : ℝ :=
  δ * (1 - D + e - 2 * h) - 2 * (1 - δ) * (baseDifference A D - e) ^ 2 +
    (1 - 2 * D + 2 * e) * δ * e - (D - e) ^ 2 / 12 +
    (12 / 25) * (baseCredit δ A D - 23 * e / 12 + 2 * Z) ^ 2 - 4 * A * Z

/-- The exceptional score at its maximal allowed original deficit. -/
def exceptionalScore (δ h A D e : ℝ) : ℝ :=
  rawExceptionalScore δ h A D e (δ * (D - A + e) / 2)

private theorem delta_mem {q : ℝ} (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000)) :
    delta q ∈ Icc (18 / 109 : ℝ) (1 / 5) := by
  have hq2 : 0 < 2 + q := by linarith [hq.1]
  have heq : delta q = 2 * q / (2 + q) := by
    unfold delta LowerE2Scalar.multiplier
    field_simp
    ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ hq2).mpr
    linarith [hq.1]
  · apply (div_le_iff₀ hq2).mpr
    linarith [hq.2]

private theorem supportScore_excess_difference (δ h A a D : ℝ) :
    supportScore δ h A D (D - A) - supportScore δ h a D (D - a) =
      (4 * δ / 25) * (A - a) * (12 * δ * (A + a - 1 + D) + 4 * D - 1) := by
  unfold supportScore baseScore baseCredit baseDifference
  ring

/-- The first certificate controls every actual original head mass in the enclosure. -/
theorem supportScore_excess_pos {q A D : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 19 / 50) :
    0 < supportScore (delta q) (LowerE2Scalar.missingMass q) A D (D - A) := by
  have hδ := delta_mem hq
  have hbase := supportScore_lower_pos hq ⟨hA.trans hAD, hD⟩
  have hfactor : 0 ≤ 12 * delta q * (A + 7 / 20 - 1 + D) + 4 * D - 1 := by
    have hp : 0 ≤ 12 * delta q * (A + 7 / 20 - 1 + D) :=
      mul_nonneg (by linarith [hδ.1]) (by linarith)
    linarith
  have hdiff := supportScore_excess_difference (delta q)
    (LowerE2Scalar.missingMass q) A (7 / 20) D
  have hp : 0 ≤ (4 * delta q / 25) * (A - 7 / 20) *
      (12 * delta q * (A + 7 / 20 - 1 + D) + 4 * D - 1) :=
    mul_nonneg (mul_nonneg (by linarith [hδ.1]) (sub_nonneg.mpr hA)) hfactor
  linarith only [hbase, hdiff, hp]

/-- A nonnegative excess no larger than `D-A` already contradicts the support price. -/
theorem supportScore_pos_of_le_excess {q A D L : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 19 / 50)
    (hL : 0 ≤ L) (hLE : L ≤ D - A) :
    0 < supportScore (delta q) (LowerE2Scalar.missingMass q) A D L := by
  have hbase := supportScore_excess_pos hq hA hAD hD
  have hδ := delta_mem hq
  have hv : 0 ≤ baseDifference A D := by unfold baseDifference; linarith
  have hm : 0 ≤ 2 - delta q := by linarith [hδ.2]
  have hD0 : 0 ≤ D := by linarith
  have hcoef : 0 ≤ 4 * (2 - delta q) * baseDifference A D + 8 * D := by positivity
  have hp := mul_nonneg hcoef (sub_nonneg.mpr hLE)
  have hsq : L ^ 2 ≤ (D - A) ^ 2 := pow_le_pow_left₀ hL hLE 2
  unfold supportScore at hbase ⊢
  nlinarith only [hbase, hp, hsq]

private theorem exceptionalBaseScore_chord (δ h A a D : ℝ) :
    (D - a) * exceptionalBaseScore δ h A D =
      (D - A) * exceptionalBaseScore δ h a D +
        (A - a) * exceptionalBaseScore δ h D D -
        ((108 * δ ^ 2 - 38 * δ - 8) / 25) * (D - a) * (A - a) * (D - A) := by
  unfold exceptionalBaseScore baseScore baseCredit baseDifference
  ring

/-- Concavity and both certified endpoints pay the entire exceptional-atom head interval. -/
theorem exceptionalBaseScore_pos {q A D : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 19 / 50) :
    0 < exceptionalBaseScore (delta q) (LowerE2Scalar.missingMass q) A D := by
  obtain ⟨hlo, hhi⟩ := exceptionalBaseScore_endpoints_pos hq ⟨hA.trans hAD, hD⟩
  by_cases heq : D = 7 / 20
  · have hAe : A = 7 / 20 := by linarith
    simpa only [hAe] using hlo
  have hDa : 0 < D - 7 / 20 :=
    sub_pos.mpr (lt_of_le_of_ne (hA.trans hAD) (Ne.symm heq))
  have hδ := delta_mem hq
  have hδ0 : 0 ≤ delta q := by linarith [hδ.1]
  have hδsq := mul_self_le_mul_self hδ0 hδ.2
  have hcoef : (108 * delta q ^ 2 - 38 * delta q - 8) / 25 ≤ 0 := by
    nlinarith only [hδsq, hδ0]
  have hpos : 0 < (D - A) * exceptionalBaseScore (delta q)
      (LowerE2Scalar.missingMass q) (7 / 20) D +
        (A - 7 / 20) * exceptionalBaseScore (delta q)
          (LowerE2Scalar.missingMass q) D D := by
    by_cases hlt : A < D
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hlo)
        (mul_nonneg (sub_nonneg.mpr hA) hhi.le)
    · have hAe : A = D := le_antisymm hAD (le_of_not_gt hlt)
      rw [hAe]
      nlinarith only [mul_pos hDa hhi]
  have hnonpos : ((108 * delta q ^ 2 - 38 * delta q - 8) / 25) *
      (D - 7 / 20) * (A - 7 / 20) * (D - A) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hcoef hDa.le) (sub_nonneg.mpr hA))
      (sub_nonneg.mpr hAD)
  have he := exceptionalBaseScore_chord (delta q) (LowerE2Scalar.missingMass q)
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
theorem exceptionalScore_pos {q A D e : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 19 / 50)
    (he : 0 ≤ e) (heE : e ≤ D - A) :
    0 < exceptionalScore (delta q) (LowerE2Scalar.missingMass q) A D e := by
  have hbase := exceptionalBaseScore_pos hq hA hAD hD
  have hδ := delta_mem hq
  have hδ0 : 0 ≤ delta q := by linarith [hδ.1]
  have hδsq := mul_self_le_mul_self hδ0 hδ.2
  have hc₁ : 0 ≤ 8 - 6 * delta q - 24 * delta q ^ 2 := by
    nlinarith only [hδ.2, hδsq]
  have hc₂ : 0 ≤ 8 - 2 * delta q := by linarith [hδ.2]
  have hv : 0 ≤ baseDifference A D - e / 2 := by unfold baseDifference; linarith
  have hDe : 0 ≤ D - e / 2 := by linarith
  have hinner : 0 ≤ 2 * (1 - 2 * D) + (4 + 24 * delta q) * (D - A) / 25 := by
    have hp : 0 ≤ (4 + 24 * delta q) * (D - A) / 25 :=
      div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hAD)) (by norm_num)
    linarith
  have hnonneg : 0 ≤ e * (delta q *
      (2 * (1 - 2 * D) + (4 + 24 * delta q) * (D - A) / 25) + 2 * delta q * e +
      (8 - 6 * delta q - 24 * delta q ^ 2) * (baseDifference A D - e / 2) / 25 +
      (8 - 2 * delta q) * (D - e / 2) / 25) := by positivity
  have hdiff := exceptionalScore_difference (delta q) (LowerE2Scalar.missingMass q)
    A D e
  linarith only [hbase, hnonneg, hdiff]

private theorem rawExceptionalScore_difference (δ h A D e Z Z' : ℝ) :
    rawExceptionalScore δ h A D e Z - rawExceptionalScore δ h A D e Z' =
      (Z' - Z) * (4 * A - (48 / 25) * (baseCredit δ A D - 23 * e / 12 + Z + Z')) := by
  unfold rawExceptionalScore
  ring

/-- Every allowed original exceptional deficit has a strictly positive restriction price. -/
theorem rawExceptionalScore_pos {q A D e Z : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 19 / 50)
    (he : 0 ≤ e) (heE : e ≤ D - A) (hZ : Z ≤ delta q * (D - A + e) / 2) :
    0 < rawExceptionalScore (delta q) (LowerE2Scalar.missingMass q) A D e Z := by
  have hbase := exceptionalScore_pos hq hA hAD hD he heE
  have hδ := delta_mem hq
  have hδ0 : 0 ≤ delta q := by linarith [hδ.1]
  have hm : 0 ≤ 2 - delta q := by linarith [hδ.2]
  have hv : 0 ≤ baseDifference A D := by unfold baseDifference; linarith
  have hvhi : baseDifference A D ≤ 7 / 50 := by unfold baseDifference; linarith
  have hmv : (2 - delta q) * baseDifference A D ≤ 7 / 25 := by
    have hp := mul_le_mul_of_nonneg_right (show 2 - delta q ≤ 2 by linarith) hv
    linarith
  have hE : D - A ≤ 3 / 100 := by linarith
  have hδE : delta q * (D - A) ≤ (1 / 5 : ℝ) * (3 / 100) :=
    mul_le_mul hδ.2 hE (sub_nonneg.mpr hAD) (by norm_num)
  have hδe : delta q * e ≤ (1 / 5 : ℝ) * (3 / 100) :=
    mul_le_mul hδ.2 (heE.trans hE) he (by norm_num)
  have hbound : baseCredit (delta q) A D - 23 * e / 12 +
      delta q * (D - A + e) ≤ 2 * A := by
    unfold baseCredit
    nlinarith only [hmv, hδE, hδe, he, hA, hAD]
  let Z' := delta q * (D - A + e) / 2
  have harg : baseCredit (delta q) A D - 23 * e / 12 + Z + Z' ≤ 2 * A := by
    dsimp only [Z']
    linarith only [hbound, hZ]
  have hcoef : 0 ≤ 4 * A - (48 / 25) *
      (baseCredit (delta q) A D - 23 * e / 12 + Z + Z') := by
    linarith only [harg, hA]
  have hnonneg := mul_nonneg (show 0 ≤ Z' - Z by exact sub_nonneg.mpr hZ) hcoef
  have hdiff := rawExceptionalScore_difference (delta q)
    (LowerE2Scalar.missingMass q) A D e Z Z'
  change 0 < rawExceptionalScore (delta q) (LowerE2Scalar.missingMass q) A D e Z'
    at hbase
  linarith only [hbase, hnonneg, hdiff]

/-- The actual pointwise old-row inequality pays the exceptional deficit cap,
including zero excess or zero deficit. -/
theorem exceptional_deficit_credit_le {δ L E e d : ℝ}
    (hδ : 0 ≤ δ) (hLE : E < L) (he : 0 ≤ e) (heE : e ≤ E)
    (hrow : (L - E + 2 * e) * d ≤ δ * e) :
    (L + e) * d ≤ δ * (E + e) / 2 := by
  have hden : 0 < L - E + 2 * e := by linarith
  have hLe : 0 ≤ L + e := by linarith
  have hp := mul_le_mul_of_nonneg_left hrow hLe
  have hcross : 0 ≤ δ * (L - E) * (E - e) := by positivity
  have haux : (L - E + 2 * e) * ((L + e) * d - δ * (E + e) / 2) ≤ 0 := by
    nlinarith only [hp, hcross]
  nlinarith only [haux, hden]

private theorem integratedScore_difference (δ h A D L : ℝ) :
    let E := D - A
    let B := 1 - A - D
    let v := baseDifference A D
    integratedScore δ h A D L - integratedScore δ h A D E =
      (L - E) * (E * (-(4 * (2 - δ) * v + 8 * D) / 25 - 16 * E / 25 +
        4 * δ * (2 * B - 3 * E)) + (L - E) *
          (-8 * E / 25 + 4 * δ * (B - L - 2 * E))) := by
  dsimp only
  unfold integratedScore supportScore
  ring

/-- The original integrated small-atom deficit bound makes its weighted
support price strictly positive; no finite atom-count premise is used. -/
theorem integratedScore_pos {q A D L : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hA : 7 / 20 ≤ A) (hAD : A ≤ D) (hD : D ≤ 19 / 50)
    (hEL : D - A < L) (hsquare : L ^ 2 ≤ (D - A) * D) :
    0 < integratedScore (delta q) (LowerE2Scalar.missingMass q) A D L := by
  let E := D - A
  let B := 1 - A - D
  have hE0 : 0 ≤ E := sub_nonneg.mpr hAD
  have hL0 : 0 < L := lt_of_le_of_lt hE0 hEL
  have hE : 0 < E := by
    by_contra h
    have hEn : E ≤ 0 := le_of_not_gt h
    have hp : E * D ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hEn (by linarith)
    nlinarith only [hsquare, hp, hL0]
  have hEhi : E ≤ 3 / 100 := by dsimp only [E]; linarith
  have hED := mul_le_mul hEhi hD (show 0 ≤ D by linarith) (by norm_num : (0 : ℝ) ≤ 3 / 100)
  have hLhi : L ≤ 11 / 100 := by nlinarith only [hsquare, hED, hL0]
  have hB : 6 / 25 ≤ B := by dsimp only [B]; linarith
  have hδ := delta_mem hq
  have hδ0 : 0 ≤ delta q := by linarith [hδ.1]
  have hv : 0 ≤ baseDifference A D := by unfold baseDifference; linarith
  have hvhi : baseDifference A D ≤ 7 / 50 := by unfold baseDifference; linarith
  have hmv : (2 - delta q) * baseDifference A D ≤ 7 / 25 := by
    have hp := mul_le_mul_of_nonneg_right (show 2 - delta q ≤ 2 by linarith) hv
    linarith
  have hprod₁ : (18 / 109 : ℝ) * (39 / 100) ≤ delta q * (2 * B - 3 * E) :=
    mul_le_mul hδ.1 (by linarith) (by norm_num) hδ0
  have hprod₂ : (18 / 109 : ℝ) * (7 / 100) ≤ delta q * (B - L - 2 * E) :=
    mul_le_mul hδ.1 (by linarith) (by norm_num) hδ0
  have hc₁ : 0 ≤ -(4 * (2 - delta q) * baseDifference A D + 8 * D) / 25 -
      16 * E / 25 + 4 * delta q * (2 * B - 3 * E) := by
    linarith only [hmv, hD, hEhi, hprod₁]
  have hc₂ : 0 ≤ -8 * E / 25 + 4 * delta q * (B - L - 2 * E) := by
    linarith only [hEhi, hprod₂]
  have hdiff := integratedScore_difference (delta q) (LowerE2Scalar.missingMass q) A D L
  have hnonneg : 0 ≤ (L - E) *
      (E * (-(4 * (2 - delta q) * baseDifference A D + 8 * D) / 25 - 16 * E / 25 +
        4 * delta q * (2 * B - 3 * E)) + (L - E) *
          (-8 * E / 25 + 4 * delta q * (B - L - 2 * E))) := by
    have hLE : 0 ≤ L - E := sub_nonneg.mpr hEL.le
    positivity
  have hsupport := supportScore_excess_pos hq hA hAD hD
  have hnonneg' : 0 ≤ 4 * delta q * (1 - 2 * D) * E ^ 2 := by
    have h1D : 0 ≤ 1 - 2 * D := by linarith
    positivity
  have hbase : 0 < integratedScore (delta q) (LowerE2Scalar.missingMass q) A D E := by
    have heq : integratedScore (delta q) (LowerE2Scalar.missingMass q) A D E =
        E * supportScore (delta q) (LowerE2Scalar.missingMass q) A D E +
          4 * delta q * (1 - 2 * D) * E ^ 2 := by
      unfold integratedScore
      dsimp only [E]
      ring
    rw [heq]
    exact add_pos_of_pos_of_nonneg (mul_pos hE hsupport) hnonneg'
  change integratedScore (delta q) (LowerE2Scalar.missingMass q) A D L -
    integratedScore (delta q) (LowerE2Scalar.missingMass q) A D E = _ at hdiff
  linarith only [hbase, hdiff, hnonneg]

/-- The true whole-part row inequality supplies the common small-atom
pointwise floor, without dividing by an unchecked coefficient. -/
theorem small_atom_deficit_floor {δ L E a k d : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hE : 0 ≤ E) (hEL : E < L)
    (ha : 0 ≤ a) (haL : a < L) (hk : 0 ≤ k) (hd : 0 ≤ d)
    (hrow : δ * (L - a) ≤ (L + E - 2 * a - k) * d) :
    δ * L ≤ (L + E) * d := by
  have hcoef : 0 < L + E - 2 * a - k := by
    by_contra h
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hd
    have hpos := mul_pos hδ (sub_pos.mpr haL)
    linarith only [hrow, hp, hpos]
  have hcross : 0 ≤ δ * (a * (L - E) + L * k) := by
    have hLE : 0 ≤ L - E := sub_nonneg.mpr hEL.le
    positivity
  have hmul := mul_le_mul_of_nonneg_left hrow (show 0 ≤ L + E by linarith)
  have hfinal : 0 ≤ (L + E - 2 * a - k) * ((L + E) * d - δ * L) := by
    nlinarith only [hmul, hcross]
  have hnonneg := nonneg_of_mul_nonneg_right hfinal hcoef
  linarith only [hnonneg]

/-- The exceptional whole atom has deficit below half the score floor,
and the actual extra-hole floor consequently removes all its common-region holes. -/
theorem exceptional_deficit_bounds {δ L E e k d : ℝ}
    (hδ : 0 < δ) (hLE : E < L) (he : 0 ≤ e) (heE : e ≤ E)
    (hk : 0 ≤ k) (hd : 0 ≤ d)
    (hrow : δ * (L - (L + e)) ≤ (L + E - 2 * (L + e) - k) * d)
    (hfloor : 0 < k → δ < d) :
    d < δ / 2 ∧ k = 0 ∧ (L + e) * d ≤ δ * (E + e) / 2 := by
  have hkd : 0 ≤ k * d := mul_nonneg hk hd
  have hrow' : (L - E + 2 * e) * d ≤ δ * e := by nlinarith only [hrow, hkd]
  have hden : 0 < L - E + 2 * e := by linarith
  have hstrict : d < δ / 2 := by
    have hgap := mul_pos hδ (sub_pos.mpr hLE)
    nlinarith only [hrow', hgap, hden]
  have hk0 : k = 0 := by
    by_contra h
    have hpos := lt_of_le_of_ne hk (Ne.symm h)
    linarith only [hfloor hpos, hstrict, hδ]
  exact ⟨hstrict, hk0, exceptional_deficit_credit_le hδ.le hLE he heE hrow'⟩

/-- The explicit original E2 value in the contact parameter. -/
theorem contact_value_eq {q : ℝ} (hq : 0 ≤ q) :
    Benchmark.twoHeadValue ((q + 2) / 3) =
      (4 + 20 * q + 87 * q ^ 2 + 56 * q ^ 3 - 5 * q ^ 4) /
        (16 * LowerE2Scalar.denominator q ^ 2) := by
  have hR := (LowerE2Scalar.denominator_pos hq).ne'
  have hq2 : q + 2 ≠ 0 := by linarith
  have hvalue := LowerE2Scalar.gapFloor_eq_twoHeadValue hq
  have he : Benchmark.twoHeadValue ((q + 2) / 3) =
      (LowerE2Scalar.gapFloor q +
        LowerE2Scalar.multiplier q * LowerE2Scalar.missingMass q) / 2 := by linarith
  rw [he]
  unfold LowerE2Scalar.gapFloor LowerE2Scalar.multiplier LowerE2Scalar.missingMass
  field_simp [hR, hq2]
  simp only [LowerE2Scalar.denominator]
  ring

/-- The lower contact strip is excluded directly by the universal mass cap. -/
theorem contact_value_gt_reference_sq {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (9 / 50)) :
    (9 * q / (2 * LowerE2Scalar.denominator q)) ^ 2 <
      Benchmark.twoHeadValue ((q + 2) / 3) := by
  have hR := LowerE2Scalar.denominator_pos hq.1
  have hid : 16 * LowerE2Scalar.denominator q ^ 2 *
      (Benchmark.twoHeadValue ((q + 2) / 3) -
        (9 * q / (2 * LowerE2Scalar.denominator q)) ^ 2) =
      4 + 20 * q - 237 * q ^ 2 + 56 * q ^ 3 - 5 * q ^ 4 := by
    rw [contact_value_eq hq.1]
    field_simp
    ring
  have hrem : 0 ≤ q * (9 / 50 - q) *
      (5 * q ^ 2 - (551 / 10) * q + 113541 / 500) := by
    have hpoly : 0 ≤ 5 * q ^ 2 - (551 / 10) * q + 113541 / 500 := by
      nlinarith only [sq_nonneg q, hq.2]
    exact mul_nonneg (mul_nonneg hq.1 (sub_nonneg.mpr hq.2)) hpoly
  have hidentity : 4 + 20 * q - 237 * q ^ 2 + 56 * q ^ 3 - 5 * q ^ 4 =
      4 + ((303179 / 1250000 : ℝ) - 4) * q / (9 / 50) +
        q * (9 / 50 - q) * (5 * q ^ 2 - (551 / 10) * q + 113541 / 500) := by ring
  have hpos : 0 < 4 + 20 * q - 237 * q ^ 2 + 56 * q ^ 3 - 5 * q ^ 4 := by
    rw [hidentity]
    linarith only [hq.2, hrem]
  rw [← hid] at hpos
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity)).mp hpos)

/-- Exact original enclosing bounds used by all three tensor certificates. -/
theorem contact_enclosure {q A D c : ℝ}
    (hq : q ∈ Icc (9 / 50 : ℝ) (213 / 1000))
    (hA : 0 ≤ A) (hc : Benchmark.twoHeadValue ((q + 2) / 3) < c)
    (hcA : c ≤ A ^ 2) (hD : D < 9 * q / (2 * LowerE2Scalar.denominator q)) :
    7 / 20 < A ∧ D < 19 / 50 ∧ delta q ∈ Icc (18 / 109 : ℝ) (1 / 5) := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := LowerE2Scalar.denominator_pos hq0
  have hq₂ := pow_le_pow_left₀ hq0 hq.2 2
  have hq₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 50) hq.1 3
  have hq₄ := pow_le_pow_left₀ hq0 hq.2 4
  have hid : (Benchmark.twoHeadValue ((q + 2) / 3) - 49 / 400) *
      (400 * LowerE2Scalar.denominator q ^ 2) =
      51 - 186 * q - 324 * q ^ 2 + 714 * q ^ 3 - 174 * q ^ 4 := by
    rw [contact_value_eq hq0]
    field_simp
    simp only [LowerE2Scalar.denominator]
    ring
  have hpoly : 0 < 51 - 186 * q - 324 * q ^ 2 + 714 * q ^ 3 - 174 * q ^ 4 := by
    norm_num at hq₂ hq₃ hq₄
    linarith only [hq.2, hq₂, hq₃, hq₄]
  rw [← hid] at hpoly
  have hcost : (49 / 400 : ℝ) < Benchmark.twoHeadValue ((q + 2) / 3) :=
    sub_pos.mp ((mul_pos_iff_of_pos_right (by positivity)).mp hpoly)
  have hAlow : 7 / 20 < A := by nlinarith only [hcost, hc, hcA, hA]
  have hqdiff : 0 ≤ (213 / 1000 - q) * (184 - 38 * (213 / 1000 + q)) :=
    mul_nonneg (sub_nonneg.mpr hq.2) (by linarith [hq.2])
  have hratio : 9 * q / (2 * LowerE2Scalar.denominator q) < 19 / 50 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * LowerE2Scalar.denominator q)).mpr
    unfold LowerE2Scalar.denominator
    nlinarith only [hqdiff]
  exact ⟨hAlow, hD.trans hratio, delta_mem hq⟩

end Erdos1017.EmptySatE2

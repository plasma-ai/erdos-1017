module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Scalar certificates for the private `E₂` curvature

The `E₂` curvature coefficient `curvature` is strictly positive and below six on
the closed `E₂` interval, the missing mass is below one quarter, the multiplier
is at least `9/11`, and the scalar inequalities required by the `S = I` private
boundary are incompatible (`single_source_contradiction`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.E2PrivateCurvature

open LowerE2Scalar

/-- The scalar factor governing the derivative of the E2 missing mass. -/
def derivativeFactor (q : ℝ) : ℝ := 1 - 3 * q ^ 2 - 7 * q ^ 3

/-- The exact smooth E2 curvature coefficient in the original q parameter. -/
def curvature (q : ℝ) : ℝ :=
  32 * denominator q ^ 3 / (9 * (q + 2) ^ 3 * derivativeFactor q)

/-- The cleared margin between six and the E2 curvature coefficient. -/
def curvatureMargin (q : ℝ) : ℝ :=
  400 - 24 * q - 5772 * q ^ 2 - 17234 * q ^ 3 -
    10308 * q ^ 4 - 3102 * q ^ 5 - 410 * q ^ 6

/-- The effective coefficient after the constant-row Schur elimination.
Its displayed degree offset is computed from the actual E2 missing mass. -/
def effectiveCurvature (q ν z : ℝ) : ℝ :=
  curvature q * ν / (ν + curvature q * (z - missingMass q) ^ 2)

/-- The final one-variable envelope in the single-source private boundary. -/
def singleSourceEnvelope (z : ℝ) : ℝ :=
  12 * z * (z - 7 / 20) / (1 + 6 * (z - 1 / 4) ^ 2)

theorem derivativeFactor_pos {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    0 < derivativeFactor q := by
  have h2 : q ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    gcongr
    · exact hq.1
    · exact hq.2
  have h3 : q ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := by
    gcongr
    · exact hq.1
    · exact hq.2
  unfold derivativeFactor
  norm_num at h2 h3
  linarith

/-- The own-slope derivative is derived from the literal rational formula. -/
theorem multiplier_hasDerivAt {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt multiplier (-4 / (q + 2) ^ 2) q := by
  have hi := hasDerivAt_id q
  have hq2 : 2 + q ≠ 0 := by linarith
  convert ((hasDerivAt_const q (2 : ℝ)).sub hi).div (hi.const_add 2) hq2 using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The actual missing-mass derivative agrees with the displayed source formula. -/
theorem missingMass_hasDerivAt {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt missingMass
      (-9 * (q + 2) * derivativeFactor q / (4 * denominator q ^ 3)) q := by
  have hi := hasDerivAt_id q
  have hN := ((hi.add_const 2).pow 2).mul
    (((hasDerivAt_const q (1 : ℝ)).add (hi.const_mul 4)).add ((hi.pow 2).const_mul 13))
  have hbase := ((hasDerivAt_const q (1 : ℝ)).add (hi.const_mul 7)).add (hi.pow 2)
  have hD := (hbase.pow 2).const_mul 8
  have hR := ne_of_gt (denominator_pos hq)
  convert hN.div hD (mul_ne_zero (by norm_num) (pow_ne_zero 2 hR)) using 1
  · rfl
  · dsimp [denominator, derivativeFactor] at *
    field_simp
    ring

/-- The curvature coefficient is the actual density-parameter slope ratio.
This scalar identity does not assert activity of a benchmark branch. -/
theorem curvature_eq_deriv_ratio {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    curvature q = 2 * deriv multiplier q / deriv missingMass q := by
  rw [(multiplier_hasDerivAt hq.1).deriv, (missingMass_hasDerivAt hq.1).deriv]
  have hR := ne_of_gt (denominator_pos hq.1)
  have hF := ne_of_gt (derivativeFactor_pos hq)
  have hq2 : q + 2 ≠ 0 := by linarith [hq.1]
  unfold curvature
  field_simp
  ring

/-- Clearing the positive curvature denominator gives this exact polynomial. -/
theorem curvature_margin_identity (q : ℝ) :
    6 * (9 * (q + 2) ^ 3 * derivativeFactor q) - 32 * denominator q ^ 3 =
      curvatureMargin q := by
  unfold denominator derivativeFactor curvatureMargin
  ring

/-- The entire closed E2 interval has strictly positive curvature below six. -/
theorem curvature_pos_lt_six {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    0 < curvature q ∧ curvature q < 6 := by
  have hR := denominator_pos hq.1
  have hF := derivativeFactor_pos hq
  have hq2 : 0 < q + 2 := by linarith [hq.1]
  have hD : 0 < 9 * (q + 2) ^ 3 * derivativeFactor q := by positivity
  have hmargin : 0 < curvatureMargin q := by
    have hlo : curvatureMargin (1 / 5) ≤ curvatureMargin q := by
      unfold curvatureMargin
      gcongr <;> first | exact hq.1 | exact hq.2
    have hend : curvatureMargin (1 / 5) = (27926 / 3125 : ℝ) := by
      norm_num [curvatureMargin]
    rw [hend] at hlo
    linarith
  constructor
  · exact div_pos (by positivity) hD
  · apply (div_lt_iff₀ hD).mpr
    rw [← curvature_margin_identity] at hmargin
    linarith

theorem curvature_one_fifth : curvature (1 / 5) = (7263392 / 1233837 : ℝ) := by
  norm_num [curvature, denominator, derivativeFactor]

/-- The no-saturation parameter guard pays the strict quarter missing-mass bound. -/
theorem missingMass_lt_quarter {q : ℝ}
    (hq : q ∈ Set.Icc (187 / 1000 : ℝ) (1 / 5)) : missingMass q < 1 / 4 := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have h2 : (187 / 1000 : ℝ) ^ 2 ≤ q ^ 2 := by
    gcongr
    exact hq.1
  have h3 : q ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := by
    gcongr
    exact hq.2
  have h4 : q ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := by
    gcongr
    exact hq.2
  have hpoly : 0 < -2 + 8 * q + 33 * q ^ 2 - 28 * q ^ 3 - 11 * q ^ 4 := by
    norm_num at h2 h3 h4
    linarith [hq.1]
  apply (div_lt_iff₀ (by positivity : 0 < 8 * denominator q ^ 2)).mpr
  change (q + 2) ^ 2 * (1 + 4 * q + 13 * q ^ 2) < _
  unfold denominator
  nlinarith [hpoly]

theorem multiplier_ge_nine_elevenths {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (1 / 5)) : (9 / 11 : ℝ) ≤ multiplier q := by
  have hq2 : 0 < 2 + q := by linarith [hq.1]
  apply (le_div_iff₀ hq2).mpr
  linarith [hq.2]

/-- The final rational upper bound has an exact nonnegative factored margin. -/
theorem singleSourceEnvelope_gap (z : ℝ) :
    (882 / 1163 - singleSourceEnvelope z) * (1 + 6 * (z - 1 / 4) ^ 2) =
      (21 / 40 - z) * (8664 * z + 2310) / 1163 := by
  have hD : 1 + 6 * (z - 1 / 4) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold singleSourceEnvelope
  field_simp
  ring

theorem singleSourceEnvelope_le {z : ℝ} (hz : z ∈ Set.Icc (7 / 20 : ℝ) (21 / 40)) :
    singleSourceEnvelope z ≤ 882 / 1163 := by
  have hD : 0 < 1 + 6 * (z - 1 / 4) ^ 2 := by positivity
  have hgap : 0 ≤ (21 / 40 - z) * (8664 * z + 2310) / 1163 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (sub_nonneg.mpr hz.2) (by linarith [hz.1])
  rw [← singleSourceEnvelope_gap] at hgap
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hD).mp hgap)

/-- The same actual missing mass, row constant and degree offset determine
the effective coefficient; its denominator and monotone bound are derived. -/
theorem effectiveCurvature_pos_le {q ν z : ℝ}
    (hq : q ∈ Set.Icc (187 / 1000 : ℝ) (1 / 5))
    (hν : ν ∈ Set.Ioc (0 : ℝ) 1) (hz : z ∈ Set.Icc (7 / 20 : ℝ) (21 / 40)) :
    0 < effectiveCurvature q ν z ∧
      effectiveCurvature q ν z ≤ 6 / (1 + 6 * (z - 1 / 4) ^ 2) := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hC := curvature_pos_lt_six (show q ∈ Set.Icc (0 : ℝ) (1 / 5) from ⟨hq0, hq.2⟩)
  have hCpos := hC.1
  have hνpos := hν.1
  have hh := missingMass_lt_quarter hq
  have hD : 0 < ν + curvature q * (z - missingMass q) ^ 2 := by positivity
  have hB : 0 < 1 + 6 * (z - 1 / 4) ^ 2 := by positivity
  have hsq : (z - 1 / 4) ^ 2 ≤ (z - missingMass q) ^ 2 := by
    gcongr
    linarith [hz.1]
  have hνsq : ν * (z - 1 / 4) ^ 2 ≤ (z - missingMass q) ^ 2 :=
    (mul_le_mul_of_nonneg_right hν.2 (sq_nonneg _)).trans (by simpa using hsq)
  constructor
  · exact div_pos (mul_pos hC.1 hν.1) hD
  · apply (div_le_div_iff₀ hD hB).mpr
    have hfirst := mul_le_mul_of_nonneg_right hC.2.le hν.1.le
    have hsecond := mul_le_mul_of_nonneg_left hνsq hC.1.le
    nlinarith

/-- The explicit scalar inequalities required by the S=I private boundary
are incompatible. Physical mass, positive-star and Schur bounds remain
the displayed premises; no model or matrix consequence is assumed implicitly. -/
theorem single_source_contradiction {q ν z A k E D : ℝ}
    (hq : q ∈ Set.Icc (187 / 1000 : ℝ) (1 / 5))
    (hz : z ∈ Set.Icc (7 / 20 : ℝ) (21 / 40))
    (hA : 0 ≤ A) (hk : 0 < k) (hkz : k ≤ z - 7 / 20) (hAk : A + k ≤ z)
    (hν : ν ∈ Set.Ioc (0 : ℝ) 1)
    (hstar : multiplier q * k < E) (hdegree : D ≤ k * (A + k))
    (hschur : E ≤ 2 * effectiveCurvature q ν z * k * D) : False := by
  have hC := effectiveCurvature_pos_le hq hν hz
  have hCpos := hC.1
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hell := multiplier_ge_nine_elevenths
    (show q ∈ Set.Icc (0 : ℝ) (1 / 5) from ⟨hq0, hq.2⟩)
  have hupper : E ≤ (2 * effectiveCurvature q ν z * k * (A + k)) * k := by
    calc
      E ≤ 2 * effectiveCurvature q ν z * k * D := hschur
      _ ≤ 2 * effectiveCurvature q ν z * k * (k * (A + k)) :=
        mul_le_mul_of_nonneg_left hdegree (by positivity)
      _ = _ := by ring
  have hellupper : multiplier q < 2 * effectiveCurvature q ν z * k * (A + k) :=
    (mul_lt_mul_iff_of_pos_right hk).mp (hstar.trans_le hupper)
  have hprod : k * (A + k) ≤ (z - 7 / 20) * z :=
    mul_le_mul hkz hAk (by positivity) (by linarith [hkz, hk])
  have hbound : 2 * effectiveCurvature q ν z * k * (A + k) ≤ singleSourceEnvelope z := by
    calc
      _ = (2 * effectiveCurvature q ν z) * (k * (A + k)) := by ring
      _ ≤ (2 * (6 / (1 + 6 * (z - 1 / 4) ^ 2))) * ((z - 7 / 20) * z) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hC.2 (by norm_num)
        · exact hprod
        · positivity
        · positivity
      _ = _ := by
        unfold singleSourceEnvelope
        ring
  have hfinal := singleSourceEnvelope_le hz
  have hgap : (882 / 1163 : ℝ) < 9 / 11 := by norm_num
  linarith

end Erdos1017.E2PrivateCurvature

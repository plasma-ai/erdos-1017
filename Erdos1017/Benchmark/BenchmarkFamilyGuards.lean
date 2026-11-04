module

public import Erdos1017.Benchmark.BenchmarkContinuity
public import Erdos1017.Benchmark.BenchmarkContactGeometry

/-!
# Parameter guards for the stationary benchmark families

The supporting tangent and active two-head cutoff below concern the explicit
benchmark only; they do not classify a selected extremal model or prove the full
upper bound.
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- The split junction of `W` satisfies `ε* < 1/10`. -/
theorem epsilonStar_lt_tenth : epsilonStar < 1 / 10 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  unfold epsilonStar
  nlinarith

/-- The split junction of `E₂` satisfies `1/10 < ε_C`. -/
theorem tenth_lt_epsilonC : (1 / 10 : ℝ) < epsilonC := by
  linarith [epsilonC_bounds.1]

/-- The split junction of `E₂` satisfies `ε_C < 9/80`. -/
theorem epsilonC_lt_nine_eightieths : epsilonC < 9 / 80 := by
  have hz : (3 / 4 : ℝ) < zC := by
    have hne : zC ≠ 3 / 4 := by
      intro h
      have hr := zC_spec.2
      rw [h] at hr
      norm_num [twoHeadRootPolynomial] at hr
    exact lt_of_le_of_ne zC_spec.1.1 hne.symm
  have h := twoHeadDensity_strictAntiOn_full
    (show (3 / 4 : ℝ) ∈ Set.Icc (2 / 3) (4 / 5) by norm_num)
    (show zC ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) from
      ⟨by linarith [zC_spec.1.1], zC_spec.1.2⟩) hz
  norm_num [twoHeadDensity, twoHeadDenominator] at h
  exact h

/-- The end of the mixed branch of `W` satisfies `1/8 < ε_D`. -/
theorem eighth_lt_epsilonD : (1 / 8 : ℝ) < epsilonD := by
  have h := mixedDensity_strictAntiOn.antitoneOn
    (show sigmaD ∈ Set.Icc sigmaD sigmaZero from
      ⟨le_rfl, by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1]⟩)
    (show (11 / 10 : ℝ) ∈ Set.Icc sigmaD sigmaZero from
      ⟨sigmaD_spec.1.2, sigmaZero_bounds.1.le⟩) sigmaD_spec.1.2
  norm_num [mixedDensity, mixedDenominator] at h
  change 1 / 8 < mixedDensity sigmaD
  unfold mixedDensity mixedDenominator
  linarith

/-- The upper end of the mixed parameters satisfies `σ₀ < 19/15`. -/
theorem sigmaZero_lt_nineteen_fifteenths : sigmaZero < 19 / 15 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  unfold sigmaZero
  nlinarith

/-- For `s > 1` and `0 < z < 4/5`, the mixed slope `(s + 1)/(3s)` is below
`2/3` and the two-head slope `(4 - 3z)/(3z)` is above `2/3`. -/
theorem stationary_slope_separation {s z : ℝ} (hs : 1 < s)
    (hz : 0 < z) (hzhi : z < 4 / 5) :
    (s + 1) / (3 * s) < 2 / 3 ∧ 2 / 3 < (4 - 3 * z) / (3 * z) := by
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 3 * s)).mpr
    linarith
  · apply (lt_div_iff₀ (by positivity : 0 < 3 * z)).mpr
    linarith

/-- The mixed cutoff root satisfies `1 < σ_D`. -/
theorem sigmaD_gt_one : (1 : ℝ) < sigmaD := by
  have hne : sigmaD ≠ 1 := by
    intro h
    have hr := sigmaD_spec.2
    rw [h] at hr
    norm_num [mixedRootPolynomial] at hr
  exact lt_of_le_of_ne sigmaD_spec.1.1 hne.symm

/-- The two-head cutoff root satisfies `z_C < 4/5`. -/
theorem zC_lt_four_fifths : zC < 4 / 5 := by
  have hne : zC ≠ 4 / 5 := by
    intro h
    have hr := zC_spec.2
    rw [h] at hr
    norm_num [twoHeadRootPolynomial] at hr
  exact lt_of_le_of_ne zC_spec.1.2 hne

/-- `s ↦ mixedValue s - (2/3)·mixedDensity s` is strictly increasing on `[σ_D, σ₀]`. -/
theorem mixedValue_sub_two_thirds_density_strictMonoOn :
    StrictMonoOn (fun s => mixedValue s - 2 / 3 * mixedDensity s)
      (Set.Icc sigmaD sigmaZero) := by
  have hc : ContinuousOn (fun s => mixedValue s - 2 / 3 * mixedDensity s)
      (Set.Icc sigmaD sigmaZero) := by
    intro s hs
    have hd := mixedDenominator_pos (by linarith [sigmaD_spec.1.1, hs.1] : 0 ≤ s)
    unfold mixedDenominator at hd
    unfold mixedValue mixedDensity mixedDenominator
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
  intro s hs
  have hs1 : 1 < s := sigmaD_gt_one.trans_le (interior_subset hs).1
  have hs0 : 0 < s := by linarith
  have hsl : (s + 1) / (3 * s) < 2 / 3 := by
    apply (div_lt_iff₀ (by positivity : 0 < 3 * s)).mpr
    linarith
  have hd : -s * (2 + 24 * s + 93 * s ^ 2 + 120 * s ^ 3) /
      mixedDenominator s ^ 3 < 0 := by
    apply div_neg_of_neg_of_pos
    · have hp : 0 < 2 + 24 * s + 93 * s ^ 2 + 120 * s ^ 3 := by positivity
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs0) hp
    · exact pow_pos (mixedDenominator_pos hs0.le) 3
  change 0 < deriv (mixedValue - fun s => 2 / 3 * mixedDensity s) s
  rw [((mixedValue_hasDerivAt hs0).sub
    ((mixedDensity_hasDerivAt hs0.le).const_mul (2 / 3))).deriv]
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr hsl) hd]

/-- `z ↦ twoHeadValue z - (2/3)·twoHeadDensity z` is strictly decreasing on `[2/3, z_C]`. -/
theorem twoHeadValue_sub_two_thirds_density_strictAntiOn :
    StrictAntiOn (fun z => twoHeadValue z - 2 / 3 * twoHeadDensity z)
      (Set.Icc (2 / 3) zC) := by
  have hc : ContinuousOn (fun z => twoHeadValue z - 2 / 3 * twoHeadDensity z)
      (Set.Icc (2 / 3) zC) := by
    intro z hz
    have hd := twoHeadDenominator_pos hz.1
    unfold twoHeadDenominator at hd
    unfold twoHeadValue twoHeadDensity twoHeadDenominator
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
  intro z hz
  have hzlo := (interior_subset hz).1
  have hzhi : z < 4 / 5 := (interior_subset hz).2.trans_lt zC_lt_four_fifths
  have hz0 : 0 < z := by linarith
  have hsl : 2 / 3 < (4 - 3 * z) / (3 * z) := by
    apply (lt_div_iff₀ (by positivity : 0 < 3 * z)).mpr
    linarith
  have ht : 0 ≤ z - 2 / 3 := sub_nonneg.mpr hzlo
  have ht' : z - 2 / 3 ≤ 2 / 15 := by linarith
  have h2 : (z - 2 / 3) ^ 2 ≤ (2 / 15 : ℝ) ^ 2 := by gcongr
  have h3 : (z - 2 / 3) ^ 3 ≤ (2 / 15 : ℝ) ^ 3 := by gcongr
  have hp : 21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5 < 0 := by nlinarith
  have hd : z * (21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5) /
      (8 * twoHeadDenominator z ^ 3) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hz0 hp)
      (mul_pos (by norm_num) (pow_pos (twoHeadDenominator_pos hzlo) 3))
  change deriv (twoHeadValue - fun z => 2 / 3 * twoHeadDensity z) z < 0
  rw [((twoHeadValue_hasDerivAt hzlo).sub
    ((twoHeadDensity_hasDerivAt hzlo).const_mul (2 / 3))).deriv]
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hsl) hd]

/-- The two stationary family values cross at most once on their overlap. -/
theorem stationary_family_difference_strictMonoOn :
    StrictMonoOn (fun e => twoHeadValue (twoHeadInverse e) - mixedValue (mixedInverse e))
      (Set.Icc epsilonC epsilonD) := by
  intro e he f hf hef
  have hes : e ∈ Set.Icc epsilonStar epsilonD :=
    ⟨by linarith [he.1, epsilonStar_lt_tenth, tenth_lt_epsilonC], he.2⟩
  have hfs : f ∈ Set.Icc epsilonStar epsilonD :=
    ⟨by linarith [hf.1, epsilonStar_lt_tenth, tenth_lt_epsilonC], hf.2⟩
  have hec : e ∈ Set.Icc epsilonC (1 / 4) :=
    ⟨he.1, he.2.trans epsilonD_lt_quarter.le⟩
  have hfc : f ∈ Set.Icc epsilonC (1 / 4) :=
    ⟨hf.1, hf.2.trans epsilonD_lt_quarter.le⟩
  have hse := mixedInverse_spec hes
  have hsf := mixedInverse_spec hfs
  have hze := twoHeadInverse_spec hec
  have hzf := twoHeadInverse_spec hfc
  have hs : mixedInverse f < mixedInverse e := by
    by_contra h
    have h := mixedDensity_strictAntiOn.antitoneOn hse.1 hsf.1 (le_of_not_gt h)
    rw [hse.2, hsf.2] at h
    linarith
  have hz : twoHeadInverse f < twoHeadInverse e := by
    by_contra h
    have h := twoHeadDensity_strictAntiOn.antitoneOn hze.1 hzf.1 (le_of_not_gt h)
    rw [hze.2, hzf.2] at h
    linarith
  have hw := mixedValue_sub_two_thirds_density_strictMonoOn hsf.1 hse.1 hs
  have hc := twoHeadValue_sub_two_thirds_density_strictAntiOn hzf.1 hze.1 hz
  dsimp only at hw hc ⊢
  rw [hse.2, hsf.2] at hw
  rw [hze.2, hzf.2] at hc
  linarith

/-- The line through `(mixedDensity a, mixedValue a)` with slope
`(a + 1)/(3a)`, evaluated at the missing-edge density `e`; for `a > 0` it is
the tangent to the mixed family's curve `s ↦ (mixedDensity s, mixedValue s)`
at `s = a`. -/
noncomputable def mixedTangent (a e : ℝ) : ℝ :=
  mixedValue a + (a + 1) / (3 * a) * (e - mixedDensity a)

/-- An exact remainder proves the stationary mixed supporting tangent globally. -/
theorem mixedValue_sub_tangent {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    mixedValue s - mixedTangent a (mixedDensity s) =
      (s - a) ^ 2 *
        (120 * a * s ^ 2 + 62 * a * s + 8 * a + 31 * s ^ 2 + 16 * s + 2) /
        (6 * a * mixedDenominator a * mixedDenominator s ^ 2) := by
  have ha' := ha.ne'
  have hpa := (mixedDenominator_pos ha.le).ne'
  have hps := (mixedDenominator_pos hs).ne'
  unfold mixedTangent mixedValue mixedDensity
  field_simp
  unfold mixedDenominator
  ring

/-- For `a > 0` and `s ≥ 0`, the mixed family lies on or above its tangent at
`a`: `mixedTangent a (mixedDensity s) ≤ mixedValue s`. -/
theorem mixedTangent_le_mixedValue {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    mixedTangent a (mixedDensity s) ≤ mixedValue s := by
  have h := mixedValue_sub_tangent ha hs
  have hn : 0 ≤ (s - a) ^ 2 *
      (120 * a * s ^ 2 + 62 * a * s + 8 * a + 31 * s ^ 2 + 16 * s + 2) /
      (6 * a * mixedDenominator a * mixedDenominator s ^ 2) := by
    have hpa := mixedDenominator_pos ha.le
    have hps := mixedDenominator_pos hs
    positivity
  linarith

/-- For `a > 0` and `e ∈ [ε*, ε_D]`, `mixedTangent a e ≤ W(e)`. -/
theorem mixedTangent_le_mixedCurve {a e : ℝ} (ha : 0 < a)
    (he : e ∈ Set.Icc epsilonStar epsilonD) : mixedTangent a e ≤ mixedCurve e := by
  have hi := mixedInverse_spec he
  have hs : 0 ≤ mixedInverse e := by linarith [sigmaD_spec.1.1, hi.1.1]
  have ht := mixedTangent_le_mixedValue ha hs
  rw [hi.2] at ht
  have hcurve : mixedCurve e = mixedValue (mixedInverse e) := by
    by_cases heq : e = epsilonStar
    · subst e
      rw [mixed_branch_match]
      exact ite_eq_left le_rfl
    · have hlt := lt_of_le_of_ne he.1 (Ne.symm heq)
      simp only [mixedCurve, not_le.mpr hlt, ite_false, he.2, ite_true]
  rwa [hcurve]

/-- The mixed tangent at `a = 117/100`, evaluated at the left end
`23243416/(2·10⁸)` of the crossing box, equals
`138261458236451/1116960975000000`. -/
theorem mixedTangent_anchor_lower :
    mixedTangent (117 / 100) (23243416 / (2 * 10 ^ 8)) =
      (138261458236451 : ℝ) / 1116960975000000 := by
  norm_num [mixedTangent, mixedValue, mixedDensity, mixedDenominator]

/-- At `z = (213/1000 + 2)/3`,
`mixedTangent (117/100) (twoHeadDensity z) - twoHeadValue z` equals
`151720393970785/21290658581268687754`. -/
theorem mixedTangent_anchor_cutoff_gap :
    mixedTangent (117 / 100) (twoHeadDensity ((213 / 1000 + 2) / 3)) -
      twoHeadValue ((213 / 1000 + 2) / 3) =
        (151720393970785 : ℝ) / 21290658581268687754 := by
  norm_num [mixedTangent, mixedValue, mixedDensity, mixedDenominator,
    twoHeadValue, twoHeadDensity, twoHeadDenominator]

/-- For `q ≥ 0` and `z = (q + 2)/3`,
`mixedTangent (117/100) (twoHeadDensity z) - twoHeadValue z` equals
`P(q)/(19857084(q² + 7q + 1)²)`, where
`P(q) = 17211110q⁴ - 12094992q³ - 2436825q² + 4961734q - 863928`. -/
theorem mixedTangent_anchor_twoHead_gap {q : ℝ} (hq : 0 ≤ q) :
    mixedTangent (117 / 100) (twoHeadDensity ((q + 2) / 3)) -
      twoHeadValue ((q + 2) / 3) =
        (17211110 * q ^ 4 - 12094992 * q ^ 3 - 2436825 * q ^ 2 +
          4961734 * q - 863928) / (19857084 * (q ^ 2 + 7 * q + 1) ^ 2) := by
  have hz : (2 / 3 : ℝ) ≤ (q + 2) / 3 := by linarith
  have hp := (twoHeadDenominator_pos hz).ne'
  have hq' : q ^ 2 + 7 * q + 1 ≠ 0 := by positivity
  unfold mixedTangent mixedValue mixedDensity mixedDenominator twoHeadValue twoHeadDensity
  field_simp
  unfold twoHeadDenominator
  ring

/-- For `213/1000 ≤ q ≤ 2/9`, `17211110q⁴ - 12094992q³ - 2436825q² + 4961734q - 863928 > 0`. -/
theorem twoHead_cutoff_polynomial_pos {q : ℝ} (hlo : 213 / 1000 ≤ q)
    (hhi : q ≤ 2 / 9) :
    0 < 17211110 * q ^ 4 - 12094992 * q ^ 3 - 2436825 * q ^ 2 +
      4961734 * q - 863928 := by
  let t := q - 213 / 1000
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht' : t ≤ 1 / 100 := by dsimp [t]; linarith
  have hl : 0 < 73567959942667 / 25000000 - 274020989523 / 50000 * t := by
    linarith
  have heq : 17211110 * q ^ 4 - 12094992 * q ^ 3 - 2436825 * q ^ 2 +
      4961734 * q - 863928 =
        17211110 * t ^ 4 + 64221843 / 25 * t ^ 3 +
          t * (73567959942667 / 25000000 - 274020989523 / 50000 * t) +
          91032236382471 / 100000000000 := by
    dsimp [t]
    ring
  rw [heq]
  positivity

/-- For `213/1000 ≤ q ≤ 2/9` and `z = (q + 2)/3`,
`twoHeadValue z < mixedTangent (117/100) (twoHeadDensity z)`. -/
theorem mixedTangent_anchor_gt_twoHead {q : ℝ} (hlo : 213 / 1000 ≤ q)
    (hhi : q ≤ 2 / 9) :
    twoHeadValue ((q + 2) / 3) <
      mixedTangent (117 / 100) (twoHeadDensity ((q + 2) / 3)) := by
  have hq : 0 ≤ q := by linarith
  have hgap := mixedTangent_anchor_twoHead_gap hq
  have hp := twoHead_cutoff_polynomial_pos hlo hhi
  have hd : 0 < 19857084 * (q ^ 2 + 7 * q + 1) ^ 2 := by positivity
  have hpos := div_pos hp hd
  linarith

/-- For `213/1000 ≤ q ≤ 2/9`, `9/80 < twoHeadDensity ((q + 2)/3) < 1/8`. -/
theorem twoHead_cutoff_density_bounds {q : ℝ} (hlo : 213 / 1000 ≤ q)
    (hhi : q ≤ 2 / 9) :
    9 / 80 < twoHeadDensity ((q + 2) / 3) ∧
      twoHeadDensity ((q + 2) / 3) < 1 / 8 := by
  have hz : (q + 2) / 3 ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) := by
    constructor <;> linarith
  have hl := twoHeadDensity_strictAntiOn_full.antitoneOn hz
    (show (20 / 27 : ℝ) ∈ Set.Icc (2 / 3) (4 / 5) by norm_num)
    (by linarith : (q + 2) / 3 ≤ (20 / 27 : ℝ))
  have hu := twoHeadDensity_strictAntiOn_full.antitoneOn
    (show (2213 / 3000 : ℝ) ∈ Set.Icc (2 / 3) (4 / 5) by norm_num) hz
    (by linarith : (2213 / 3000 : ℝ) ≤ (q + 2) / 3)
  norm_num [twoHeadDensity, twoHeadDenominator] at hl hu
  unfold twoHeadDensity twoHeadDenominator
  constructor <;> linarith

/-- Throughout this interval the actual mixed family strictly wins. -/
theorem mixedCurve_gt_twoHeadCurve_of_cutoff {q : ℝ} (hlo : 213 / 1000 ≤ q)
    (hhi : q ≤ 2 / 9) :
    twoHeadCurve (twoHeadDensity ((q + 2) / 3)) <
      mixedCurve (twoHeadDensity ((q + 2) / 3)) := by
  have he := twoHead_cutoff_density_bounds hlo hhi
  have heC : epsilonC < twoHeadDensity ((q + 2) / 3) :=
    epsilonC_lt_nine_eightieths.trans he.1
  have he' : twoHeadDensity ((q + 2) / 3) ∈ Set.Icc epsilonStar epsilonD :=
    ⟨by linarith [epsilonStar_lt_tenth], he.2.le.trans eighth_lt_epsilonD.le⟩
  have hz : (q + 2) / 3 ∈ Set.Icc (2 / 3 : ℝ) zC := by
    constructor <;> linarith [zC_spec.1.1]
  have hi := twoHeadInverse_unique
    (show twoHeadDensity ((q + 2) / 3) ∈ Set.Icc epsilonC (1 / 4) from
      ⟨heC.le, by linarith [he.2]⟩) hz rfl
  have hcurve : twoHeadCurve (twoHeadDensity ((q + 2) / 3)) =
      twoHeadValue ((q + 2) / 3) := by
    simp only [twoHeadCurve, show twoHeadDensity ((q + 2) / 3) ≠ 0 by linarith [he.1],
      ite_false, not_le.mpr heC, ← hi]
  rw [hcurve]
  exact (mixedTangent_anchor_gt_twoHead hlo hhi).trans_le
    (mixedTangent_le_mixedCurve (by norm_num) he')

end Erdos1017.Benchmark

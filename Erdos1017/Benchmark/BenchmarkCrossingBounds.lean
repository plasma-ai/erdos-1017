module

public import Erdos1017.Benchmark.BenchmarkContactGeometry
public import Erdos1017.Benchmark.BenchmarkFamilyGuards

/-!
# Exact rational brackets for the stationary benchmark families

The interval arithmetic is checked by Lean against the benchmark's density, value
and inverse definitions, with no external computation. The stationary overlap
has a unique crossing, and family activity implies the parameter guards. The
full split-branch comparison and the contact exclusions of the selected model
are not part of this module.
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- `mixedValue` is strictly decreasing on `[σ_D, σ₀]`. -/
theorem mixedValue_strictAntiOn : StrictAntiOn mixedValue (Set.Icc sigmaD sigmaZero) := by
  have hc : ContinuousOn mixedValue (Set.Icc sigmaD sigmaZero) := by
    intro s hs
    exact (mixedValue_hasDerivAt (by linarith [sigmaD_spec.1.1, hs.1])).continuousAt.continuousWithinAt
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
  intro s hs
  have hs0 : 0 < s := by linarith [sigmaD_spec.1.1, (interior_subset hs).1]
  rw [(mixedValue_hasDerivAt hs0).deriv]
  apply mul_neg_of_pos_of_neg (by positivity)
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs0) (by positivity)
  · exact pow_pos (mixedDenominator_pos hs0.le) 3

/-- `twoHeadValue` is strictly decreasing on `[2/3, z_C]`. -/
theorem twoHeadValue_strictAntiOn : StrictAntiOn twoHeadValue (Set.Icc (2 / 3) zC) := by
  have hc : ContinuousOn twoHeadValue (Set.Icc (2 / 3) zC) := by
    intro z hz
    exact (twoHeadValue_hasDerivAt hz.1).continuousAt.continuousWithinAt
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
  intro z hz
  have hzlo := (interior_subset hz).1
  have hzhi : z ≤ 4 / 5 := (interior_subset hz).2.trans zC_spec.1.2
  have hz0 : 0 < z := by linarith
  have ht : 0 ≤ z - 2 / 3 := sub_nonneg.mpr hzlo
  have ht' : z - 2 / 3 ≤ 2 / 15 := by linarith
  have h2 : (z - 2 / 3) ^ 2 ≤ (2 / 15 : ℝ) ^ 2 := by gcongr
  have h3 : (z - 2 / 3) ^ 3 ≤ (2 / 15 : ℝ) ^ 3 := by gcongr
  have hp : 21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5 < 0 := by nlinarith
  rw [(twoHeadValue_hasDerivAt hzlo).deriv]
  apply mul_neg_of_pos_of_neg
  · apply div_pos (by linarith) (by positivity)
  · exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hz0 hp)
      (mul_pos (by norm_num) (pow_pos (twoHeadDenominator_pos hzlo) 3))

/-- Bracketing `mixedInverse`: if `e ∈ [ε*, ε_D]` and `l, u ∈ [σ_D, σ₀]`
satisfy `mixedDensity u < e < mixedDensity l`, then
`l < mixedInverse e < u`. -/
theorem mixedInverse_mem_Ioo_of_bracket {e l u : ℝ}
    (he : e ∈ Set.Icc epsilonStar epsilonD)
    (hl : l ∈ Set.Icc sigmaD sigmaZero) (hu : u ∈ Set.Icc sigmaD sigmaZero)
    (hlo : e < mixedDensity l) (hhi : mixedDensity u < e) :
    mixedInverse e ∈ Set.Ioo l u := by
  have hi := mixedInverse_spec he
  constructor
  · by_contra h
    have hm := mixedDensity_strictAntiOn.antitoneOn hi.1 hl (le_of_not_gt h)
    rw [hi.2] at hm
    linarith
  · by_contra h
    have hm := mixedDensity_strictAntiOn.antitoneOn hu hi.1 (le_of_not_gt h)
    rw [hi.2] at hm
    linarith

/-- Bracketing `twoHeadInverse`: if `e ∈ [ε_C, 1/4]` and `l, u ∈ [2/3, z_C]`
satisfy `twoHeadDensity u < e < twoHeadDensity l`, then
`l < twoHeadInverse e < u`. -/
theorem twoHeadInverse_mem_Ioo_of_bracket {e l u : ℝ}
    (he : e ∈ Set.Icc epsilonC (1 / 4))
    (hl : l ∈ Set.Icc (2 / 3) zC) (hu : u ∈ Set.Icc (2 / 3) zC)
    (hlo : e < twoHeadDensity l) (hhi : twoHeadDensity u < e) :
    twoHeadInverse e ∈ Set.Ioo l u := by
  have hi := twoHeadInverse_spec he
  constructor
  · by_contra h
    have hm := twoHeadDensity_strictAntiOn.antitoneOn hi.1 hl (le_of_not_gt h)
    rw [hi.2] at hm
    linarith
  · by_contra h
    have hm := twoHeadDensity_strictAntiOn.antitoneOn hu hi.1 (le_of_not_gt h)
    rw [hi.2] at hm
    linarith

/-- Every `s ∈ [11/10, 5/4]` lies in `[σ_D, σ₀]`. -/
private theorem mixed_parameter_mem {s : ℝ} (hlo : 11 / 10 ≤ s) (hhi : s ≤ 5 / 4) :
    s ∈ Set.Icc sigmaD sigmaZero := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  refine ⟨sigmaD_spec.1.2.trans hlo, ?_⟩
  unfold sigmaZero
  nlinarith

/-- Every `z ∈ [2/3, 3/4]` lies in `[2/3, z_C]`. -/
private theorem twoHead_parameter_mem {z : ℝ} (hlo : 2 / 3 ≤ z) (hhi : z ≤ 3 / 4) :
    z ∈ Set.Icc (2 / 3) zC := ⟨hlo, hhi.trans zC_spec.1.1⟩

/-- On the closed crossing box `[23243416, 23243417]/(2·10⁸)`, `e` lies in
both `[ε*, ε_D]` and `[ε_C, 1/4]`, and both curves are on their rational
branches: `W(e) = mixedValue (mixedInverse e)` and
`E₂(e) = twoHeadValue (twoHeadInverse e)`. -/
theorem crossing_box_stationary {e : ℝ}
    (he : e ∈ Set.Icc (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8))) :
    e ∈ Set.Icc epsilonStar epsilonD ∧ e ∈ Set.Icc epsilonC (1 / 4) ∧
      mixedCurve e = mixedValue (mixedInverse e) ∧
      twoHeadCurve e = twoHeadValue (twoHeadInverse e) := by
  have hs : epsilonStar < e := by linarith [epsilonStar_lt_tenth, he.1]
  have hd : e < epsilonD := by linarith [eighth_lt_epsilonD, he.2]
  have hc : epsilonC < e := by linarith [epsilonC_lt_nine_eightieths, he.1]
  have hq : e < 1 / 4 := by linarith [he.2]
  refine ⟨⟨hs.le, hd.le⟩, ⟨hc.le, hq.le⟩, ?_, ?_⟩
  · simp only [mixedCurve, not_le.mpr hs, ite_false, hd.le, ite_true]
  · have he0 : e ≠ 0 := by linarith [he.1]
    simp only [twoHeadCurve, he0, ite_false, not_le.mpr hc]

/-- At the left end `e = 23243416/(2·10⁸)` of the crossing box,
`mixedInverse e` and `twoHeadInverse e` lie in explicit rational open
intervals of width at most `2⁻⁵⁰`, near `1.17195` and `0.73756`. -/
theorem crossing_lower_inverse_brackets :
    mixedInverse (23243416 / (2 * 10 ^ 8)) ∈
        Set.Ioo (164937062659747 / 140737488355328) (1319496501277977 / 1125899906842624) ∧
      twoHeadInverse (23243416 / (2 * 10 ^ 8)) ∈
        Set.Ioo (830421315356311 / 1125899906842624) (1245631973034467 / 1688849860263936) := by
  have hs := crossing_box_stationary (e := 23243416 / (2 * 10 ^ 8)) (by norm_num)
  constructor
  · apply mixedInverse_mem_Ioo_of_bracket hs.1
      (mixed_parameter_mem (by norm_num) (by norm_num))
      (mixed_parameter_mem (by norm_num) (by norm_num))
    · norm_num [mixedDensity, mixedDenominator]
    · norm_num [mixedDensity, mixedDenominator]
  · apply twoHeadInverse_mem_Ioo_of_bracket hs.2.1
      (twoHead_parameter_mem (by norm_num) (by norm_num))
      (twoHead_parameter_mem (by norm_num) (by norm_num))
    · norm_num [twoHeadDensity, twoHeadDenominator]
    · norm_num [twoHeadDensity, twoHeadDenominator]

/-- At the right end `e = 23243417/(2·10⁸)` of the crossing box,
`mixedInverse e` and `twoHeadInverse e` lie in explicit rational open
intervals of width at most `2⁻⁵⁰`, near `1.17195` and `0.73756`. -/
theorem crossing_upper_inverse_brackets :
    mixedInverse (23243417 / (2 * 10 ^ 8)) ∈
        Set.Ioo (1319496472920331 / 1125899906842624) (329874118230083 / 281474976710656) ∧
      twoHeadInverse (23243417 / (2 * 10 ^ 8)) ∈
        Set.Ioo (622815974973377 / 844424930131968) (830421299964503 / 1125899906842624) := by
  have hs := crossing_box_stationary (e := 23243417 / (2 * 10 ^ 8)) (by norm_num)
  constructor
  · apply mixedInverse_mem_Ioo_of_bracket hs.1
      (mixed_parameter_mem (by norm_num) (by norm_num))
      (mixed_parameter_mem (by norm_num) (by norm_num))
    · norm_num [mixedDensity, mixedDenominator]
    · norm_num [mixedDensity, mixedDenominator]
  · apply twoHeadInverse_mem_Ioo_of_bracket hs.2.1
      (twoHead_parameter_mem (by norm_num) (by norm_num))
      (twoHead_parameter_mem (by norm_num) (by norm_num))
    · norm_num [twoHeadDensity, twoHeadDenominator]
    · norm_num [twoHeadDensity, twoHeadDenominator]

/-- At the left end `e = 23243416/(2·10⁸)` of the crossing box, `E₂(e) < W(e)`. -/
theorem crossing_lower_sign :
    twoHeadCurve (23243416 / (2 * 10 ^ 8)) < mixedCurve (23243416 / (2 * 10 ^ 8)) := by
  have hs := crossing_box_stationary (e := 23243416 / (2 * 10 ^ 8)) (by norm_num)
  have hi := crossing_lower_inverse_brackets
  have hw := mixedValue_strictAntiOn (mixedInverse_spec hs.1).1
    (mixed_parameter_mem (by norm_num) (by norm_num)) hi.1.2
  have he := twoHeadValue_strictAntiOn
    (twoHead_parameter_mem (by norm_num) (by norm_num)) (twoHeadInverse_spec hs.2.1).1 hi.2.1
  have hgap : twoHeadValue (830421315356311 / 1125899906842624) <
      mixedValue (1319496501277977 / 1125899906842624) := by
    norm_num [mixedValue, mixedDenominator, twoHeadValue, twoHeadDensity, twoHeadDenominator]
  rw [hs.2.2.1, hs.2.2.2]
  exact he.trans (hgap.trans hw)

/-- At the right end `e = 23243417/(2·10⁸)` of the crossing box, `W(e) < E₂(e)`. -/
theorem crossing_upper_sign :
    mixedCurve (23243417 / (2 * 10 ^ 8)) < twoHeadCurve (23243417 / (2 * 10 ^ 8)) := by
  have hs := crossing_box_stationary (e := 23243417 / (2 * 10 ^ 8)) (by norm_num)
  have hi := crossing_upper_inverse_brackets
  have hw := mixedValue_strictAntiOn
    (mixed_parameter_mem (by norm_num) (by norm_num)) (mixedInverse_spec hs.1).1 hi.1.1
  have he := twoHeadValue_strictAntiOn (twoHeadInverse_spec hs.2.1).1
    (twoHead_parameter_mem (by norm_num) (by norm_num)) hi.2.2
  have hgap : mixedValue (1319496472920331 / 1125899906842624) <
      twoHeadValue (830421299964503 / 1125899906842624) := by
    norm_num [mixedValue, mixedDenominator, twoHeadValue, twoHeadDensity, twoHeadDenominator]
  rw [hs.2.2.1, hs.2.2.2]
  exact hw.trans (hgap.trans he)

/-- Some `e` in the open crossing box `(23243416, 23243417)/(2·10⁸)` has `E₂(e) = W(e)`. -/
theorem exists_crossing_in_exact_interval :
    ∃ e ∈ Set.Ioo (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8)),
      twoHeadCurve e = mixedCurve e := by
  have hc : ContinuousOn (fun e => twoHeadCurve e - mixedCurve e)
      (Set.Icc (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8))) :=
    (twoHeadCurve_continuousOn.sub mixedCurve_continuousOn).mono (by
      intro e he
      constructor <;> linarith [he.1, he.2])
  obtain ⟨e, he, hz⟩ := intermediate_value_Icc (by norm_num) hc
    (show (0 : ℝ) ∈ Set.Icc
      (twoHeadCurve (23243416 / (2 * 10 ^ 8)) - mixedCurve (23243416 / (2 * 10 ^ 8)))
      (twoHeadCurve (23243417 / (2 * 10 ^ 8)) - mixedCurve (23243417 / (2 * 10 ^ 8))) from
        ⟨by linarith [crossing_lower_sign], by linarith [crossing_upper_sign]⟩)
  have heq : twoHeadCurve e = mixedCurve e := sub_eq_zero.mp hz
  refine ⟨e, ⟨?_, ?_⟩, heq⟩
  · exact lt_of_le_of_ne he.1 (by intro h; rw [← h] at heq; exact (ne_of_lt crossing_lower_sign) heq)
  · exact lt_of_le_of_ne he.2 (by intro h; rw [h] at heq; exact (ne_of_lt crossing_upper_sign) heq.symm)

/-- On the closed crossing box `[23243416, 23243417]/(2·10⁸)`,
`7/6 < mixedInverse e < 589/500` and the `E₂` parameter
`q = 3·twoHeadInverse e - 2` satisfies `1/5 < q < 213/1000`. -/
theorem crossing_box_parameter_guards {e : ℝ}
    (he : e ∈ Set.Icc (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8))) :
    mixedInverse e ∈ Set.Ioo (7 / 6) (589 / 500) ∧
      3 * twoHeadInverse e - 2 ∈ Set.Ioo (1 / 5) (213 / 1000) := by
  have hs := crossing_box_stationary he
  constructor
  · apply mixedInverse_mem_Ioo_of_bracket hs.1
      (mixed_parameter_mem (by norm_num) (by norm_num))
      (mixed_parameter_mem (by norm_num) (by norm_num))
    · have h : 23243417 / (2 * 10 ^ 8) < mixedDensity (7 / 6) := by
        norm_num [mixedDensity, mixedDenominator]
      exact he.2.trans_lt h
    · have h : mixedDensity (589 / 500) < 23243416 / (2 * 10 ^ 8) := by
        norm_num [mixedDensity, mixedDenominator]
      exact h.trans_le he.1
  · have hi : twoHeadInverse e ∈ Set.Ioo (11 / 15) (2213 / 3000) := by
      apply twoHeadInverse_mem_Ioo_of_bracket hs.2.1
        (twoHead_parameter_mem (by norm_num) (by norm_num))
        (twoHead_parameter_mem (by norm_num) (by norm_num))
      · have h : 23243417 / (2 * 10 ^ 8) < twoHeadDensity (11 / 15) := by
          norm_num [twoHeadDensity, twoHeadDenominator]
        exact he.2.trans_lt h
      · have h : twoHeadDensity (2213 / 3000) < 23243416 / (2 * 10 ^ 8) := by
          norm_num [twoHeadDensity, twoHeadDenominator]
        exact h.trans_le he.1
    constructor <;> linarith [hi.1, hi.2]

/-- On the closed crossing box `[23243416, 23243417]/(2·10⁸)`, with
`s = mixedInverse e` and `z = twoHeadInverse e`, the slopes satisfy
`363/589 < (s + 1)/(3s) < (4 - 3z)/(3z) < 9/11`. -/
theorem crossing_box_slope_guards {e : ℝ}
    (he : e ∈ Set.Icc (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8))) :
    363 / 589 < (mixedInverse e + 1) / (3 * mixedInverse e) ∧
      (mixedInverse e + 1) / (3 * mixedInverse e) <
        (4 - 3 * twoHeadInverse e) / (3 * twoHeadInverse e) ∧
      (4 - 3 * twoHeadInverse e) / (3 * twoHeadInverse e) < 9 / 11 := by
  have hi := crossing_box_parameter_guards he
  have hs0 : 0 < mixedInverse e := by linarith [hi.1.1]
  have hz0 : 0 < twoHeadInverse e := by linarith [hi.2.1]
  have hsep := stationary_slope_separation
    (s := mixedInverse e) (z := twoHeadInverse e)
    (by linarith [hi.1.1]) hz0 (by linarith [hi.2.2])
  refine ⟨?_, hsep.1.trans hsep.2, ?_⟩
  · apply (lt_div_iff₀ (by positivity : 0 < 3 * mixedInverse e)).mpr
    linarith [hi.1.2]
  · apply (div_lt_iff₀ (by positivity : 0 < 3 * twoHeadInverse e)).mpr
    linarith [hi.2.1]

/-- On the open crossing box `(23243416, 23243417)/(2·10⁸)`,
`W(e) > 138261458236451/1116960975000000`, about `0.12378`. -/
theorem crossing_box_value_lower {e : ℝ}
    (he : e ∈ Set.Ioo (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8))) :
    (138261458236451 : ℝ) / 1116960975000000 < mixedCurve e := by
  have hs := crossing_box_stationary ⟨he.1.le, he.2.le⟩
  have ht := mixedTangent_le_mixedCurve (a := 117 / 100) (by norm_num) hs.1
  have h : mixedTangent (117 / 100) (23243416 / (2 * 10 ^ 8)) <
      mixedTangent (117 / 100) e := by
    unfold mixedTangent
    norm_num
    linarith [he.1]
  rw [mixedTangent_anchor_lower] at h
  exact h.trans_le ht

/-- On `[ε_C, ε_D]` both curves are on their rational branches:
`E₂(e) = twoHeadValue (twoHeadInverse e)` and
`W(e) = mixedValue (mixedInverse e)`. -/
theorem family_curves_eq_stationary_on_overlap {e : ℝ}
    (he : e ∈ Set.Icc epsilonC epsilonD) :
    twoHeadCurve e = twoHeadValue (twoHeadInverse e) ∧
      mixedCurve e = mixedValue (mixedInverse e) := by
  have hs : epsilonStar < e := by
    linarith [he.1, epsilonStar_lt_tenth, tenth_lt_epsilonC]
  have he0 : e ≠ 0 := by linarith [he.1, tenth_lt_epsilonC]
  constructor
  · by_cases heq : e = epsilonC
    · subst e
      simp only [twoHeadCurve, he0, ite_false, le_refl, ite_true]
      exact twoHead_branch_match.symm
    · have hlt : epsilonC < e := lt_of_le_of_ne he.1 (Ne.symm heq)
      simp only [twoHeadCurve, he0, ite_false, not_le.mpr hlt]
  · simp only [mixedCurve, not_le.mpr hs, ite_false, he.2, ite_true]

/-- `E₂ - W` is strictly increasing on `[ε_C, ε_D]`. -/
theorem family_difference_strictMonoOn :
    StrictMonoOn (fun e => twoHeadCurve e - mixedCurve e) (Set.Icc epsilonC epsilonD) := by
  intro e he f hf hef
  have h := stationary_family_difference_strictMonoOn he hf hef
  have heq := family_curves_eq_stationary_on_overlap he
  have hfq := family_curves_eq_stationary_on_overlap hf
  dsimp only at h ⊢
  rwa [heq.1, heq.2, hfq.1, hfq.2]

/-- The stationary overlap has exactly one crossing, in the exact rational box. -/
theorem exists_unique_crossing_on_overlap :
    ∃ e ∈ Set.Ioo (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8)),
      twoHeadCurve e = mixedCurve e ∧
        ∀ f ∈ Set.Icc epsilonC epsilonD, twoHeadCurve f = mixedCurve f → f = e := by
  obtain ⟨e, he, heq⟩ := exists_crossing_in_exact_interval
  have hs := crossing_box_stationary ⟨he.1.le, he.2.le⟩
  refine ⟨e, he, heq, ?_⟩
  intro f hf hfq
  apply family_difference_strictMonoOn.injOn hf ⟨hs.2.1.1, hs.1.2⟩
  simp only [hfq, heq, sub_self]

/-- Every active point on the actual two-head stationary branch has the sharp guard. -/
theorem active_twoHead_parameter_lt_cutoff {e : ℝ}
    (he : e ∈ Set.Icc epsilonC (1 / 4)) (hactive : mixedCurve e ≤ twoHeadCurve e) :
    3 * twoHeadInverse e - 2 < 213 / 1000 := by
  have hl := crossing_box_stationary (e := 23243416 / (2 * 10 ^ 8)) (by norm_num)
  have hegt : 23243416 / (2 * 10 ^ 8) < e := by
    by_contra h
    have hele := le_of_not_gt h
    have hm := family_difference_strictMonoOn.monotoneOn
      (show e ∈ Set.Icc epsilonC epsilonD from ⟨he.1, hele.trans hl.1.2⟩)
      ⟨hl.2.1.1, hl.1.2⟩ hele
    linarith [crossing_lower_sign]
  have hi := twoHeadInverse_spec he
  have hparam : twoHeadInverse e < 2213 / 3000 := by
    by_contra h
    have hm := twoHeadDensity_strictAntiOn.antitoneOn
      (twoHead_parameter_mem (by norm_num) (by norm_num)) hi.1 (le_of_not_gt h)
    rw [hi.2] at hm
    have hd : twoHeadDensity (2213 / 3000) < 23243416 / (2 * 10 ^ 8) := by
      norm_num [twoHeadDensity, twoHeadDenominator]
    linarith
  linarith

/-- The W exclusion's parameter and missing-density guards follow from activity. -/
theorem active_mixed_parameter_guards {e : ℝ}
    (he : e ∈ Set.Icc epsilonStar epsilonD) (hactive : twoHeadCurve e ≤ mixedCurve e) :
    7 / 6 < mixedInverse e ∧ 2 * e < 1163 / 5000 := by
  have hu := crossing_box_stationary (e := 23243417 / (2 * 10 ^ 8)) (by norm_num)
  have helt : e < 23243417 / (2 * 10 ^ 8) := by
    by_contra h
    have hele := le_of_not_gt h
    have hm := family_difference_strictMonoOn.monotoneOn
      ⟨hu.2.1.1, hu.1.2⟩
      (show e ∈ Set.Icc epsilonC epsilonD from ⟨hu.2.1.1.trans hele, he.2⟩) hele
    linarith [crossing_upper_sign]
  have hi := mixedInverse_spec he
  constructor
  · by_contra h
    have hm := mixedDensity_strictAntiOn.antitoneOn hi.1
      (mixed_parameter_mem (by norm_num) (by norm_num)) (le_of_not_gt h)
    rw [hi.2] at hm
    have hd : 23243417 / (2 * 10 ^ 8) < mixedDensity (7 / 6) := by
      norm_num [mixedDensity, mixedDenominator]
    linarith
  · linarith

end Erdos1017.Benchmark

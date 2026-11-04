module

public import Erdos1017.Benchmark
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Basic properties of the benchmark branches

The mixed and two-head denominators are positive, the constants `sigmaZero`,
`epsilonStar` and `epsilonC` have explicit bounds, the branches have explicit
endpoint values, and the split and rational mixed and two-head branches match at
their common endpoints (`mixed_branch_match`, `twoHead_branch_match`).
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- The mixed denominator `s² + 8s + 2` is positive for `s ≥ 0`. -/
theorem mixedDenominator_pos {s : ℝ} (hs : 0 ≤ s) : 0 < mixedDenominator s := by
  unfold mixedDenominator
  positivity

/-- The two-head denominator `z² + z - 1` is positive for `z ≥ 2/3`. -/
theorem twoHeadDenominator_pos {z : ℝ} (hz : 2 / 3 ≤ z) : 0 < twoHeadDenominator z := by
  unfold twoHeadDenominator
  nlinarith [sq_nonneg (z - 2 / 3)]

/-- The upper end `σ₀ = (3 + √21)/6` of the mixed parameters satisfies `11/10 < σ₀ < 2`. -/
theorem sigmaZero_bounds : (11 / 10 : ℝ) < sigmaZero ∧ sigmaZero < 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  unfold sigmaZero
  constructor <;> nlinarith

/-- The mixed family has missing-edge density `ε*` at `σ₀`: `mixedDensity σ₀ = ε*`. -/
theorem mixedDensity_sigmaZero : mixedDensity sigmaZero = epsilonStar := by
  have hs : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 21) ^ 3 = 21 * Real.sqrt 21 := by
    rw [pow_succ, hs]
  have h4 : (Real.sqrt 21) ^ 4 = 441 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]
    norm_num
  have h5 : (Real.sqrt 21) ^ 5 = 441 * Real.sqrt 21 := by
    rw [pow_succ, h4]
  have hd := ne_of_gt (mixedDenominator_pos (by linarith [sigmaZero_bounds.1] : 0 ≤ sigmaZero))
  unfold mixedDensity epsilonStar
  apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd))).mpr
  unfold mixedDenominator sigmaZero
  ring_nf
  rw [hs, h3, h4, h5]
  ring

/-- `mixedDensity` is continuous on `[σ_D, σ₀]`. -/
theorem mixedDensity_continuousOn : ContinuousOn mixedDensity (Set.Icc sigmaD sigmaZero) := by
  intro s hs
  have hd := mixedDenominator_pos (by linarith [sigmaD_spec.1.1, hs.1] : 0 ≤ s)
  unfold mixedDenominator at hd
  unfold mixedDensity mixedDenominator
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

/-- `twoHeadDensity` is continuous on `[2/3, z_C]`. -/
theorem twoHeadDensity_continuousOn : ContinuousOn twoHeadDensity (Set.Icc (2 / 3) zC) := by
  intro z hz
  have hd := twoHeadDenominator_pos hz.1
  unfold twoHeadDenominator at hd
  unfold twoHeadDensity twoHeadDenominator
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

/-- The two-head family has missing-edge density `1/4` at `z = 2/3`. -/
@[simp] theorem twoHeadDensity_two_thirds : twoHeadDensity (2 / 3) = 1 / 4 := by
  norm_num [twoHeadDensity, twoHeadDenominator]

/-- Existence for `mixedInverse`: for every `e ∈ [ε*, ε_D]` some
`s ∈ [σ_D, σ₀]` has `mixedDensity s = e`. -/
theorem mixedInverse_exists {e : ℝ} (he : e ∈ Set.Icc epsilonStar epsilonD) :
    ∃ s ∈ Set.Icc sigmaD sigmaZero, mixedDensity s = e := by
  apply intermediate_value_Icc' (by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1])
    mixedDensity_continuousOn
  simpa only [mixedDensity_sigmaZero, epsilonD] using he

/-- Existence for `twoHeadInverse`: for every `e ∈ [ε_C, 1/4]` some
`z ∈ [2/3, z_C]` has `twoHeadDensity z = e`. -/
theorem twoHeadInverse_exists {e : ℝ} (he : e ∈ Set.Icc epsilonC (1 / 4)) :
    ∃ z ∈ Set.Icc (2 / 3) zC, twoHeadDensity z = e := by
  apply intermediate_value_Icc' (by linarith [zC_spec.1.1]) twoHeadDensity_continuousOn
  simpa only [twoHeadDensity_two_thirds, epsilonC] using he

/-- The selected mixed inverse is an actual solution in the stated parameter interval. -/
theorem mixedInverse_spec {e : ℝ} (he : e ∈ Set.Icc epsilonStar epsilonD) :
    mixedInverse e ∈ Set.Icc sigmaD sigmaZero ∧ mixedDensity (mixedInverse e) = e := by
  apply (mixedDensity_continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_singleton (x := e))).csInf_mem
  · exact mixedInverse_exists he
  · exact ⟨sigmaD, fun s hs => hs.1.1⟩

/-- The selected two-head inverse is an actual solution in its parameter interval. -/
theorem twoHeadInverse_spec {e : ℝ} (he : e ∈ Set.Icc epsilonC (1 / 4)) :
    twoHeadInverse e ∈ Set.Icc (2 / 3) zC ∧ twoHeadDensity (twoHeadInverse e) = e := by
  apply (twoHeadDensity_continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_singleton (x := e))).csInf_mem
  · exact twoHeadInverse_exists he
  · exact ⟨2 / 3, fun z hz => hz.1.1⟩

/-- For `s ≥ 0`, `mixedDensity` has derivative
`-s(2 + 24s + 93s² + 120s³) / (s² + 8s + 2)³` at `s`. -/
theorem mixedDensity_hasDerivAt {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt mixedDensity
      (-s * (2 + 24 * s + 93 * s ^ 2 + 120 * s ^ 3) / mixedDenominator s ^ 3) s := by
  have hi := hasDerivAt_id s
  have hn := (((hasDerivAt_const s (2 : ℝ)).add (hi.const_mul 16)).add
    ((hi.pow 2).const_mul 33)).sub ((hi.pow 4).const_mul 15)
  have hd := (((hi.pow 2).add (hi.const_mul 8)).add_const 2).pow 2 |>.const_mul 2
  have hq := ne_of_gt (mixedDenominator_pos hs)
  convert hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hq)) using 1
  · rfl
  · dsimp [mixedDenominator] at *
    field_simp
    ring

/-- `mixedDensity` is strictly decreasing on `[σ_D, σ₀]`. -/
theorem mixedDensity_strictAntiOn : StrictAntiOn mixedDensity (Set.Icc sigmaD sigmaZero) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) mixedDensity_continuousOn
  intro s hs
  have hs1 := (interior_subset hs).1
  have hs0 : 0 < s := by linarith [sigmaD_spec.1.1]
  rw [(mixedDensity_hasDerivAt hs0.le).deriv]
  apply div_neg_of_neg_of_pos
  · have : 0 < 2 + 24 * s + 93 * s ^ 2 + 120 * s ^ 3 := by positivity
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs0) this
  · exact pow_pos (mixedDenominator_pos hs0.le) 3

/-- For `z ≥ 2/3`, `twoHeadDensity` has derivative
`z(21z³ - 39z² + 24z - 5) / (8(z² + z - 1)³)` at `z`. -/
theorem twoHeadDensity_hasDerivAt {z : ℝ} (hz : 2 / 3 ≤ z) :
    HasDerivAt twoHeadDensity
      (z * (21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5) / (8 * twoHeadDenominator z ^ 3)) z := by
  have hi := hasDerivAt_id z
  have hn := (hi.pow 2).mul ((((hi.pow 2).const_mul 13).sub (hi.const_mul 16)).add_const 5)
  have hd := ((((hi.pow 2).add hi).sub_const 1).pow 2).const_mul 16
  have hq := ne_of_gt (twoHeadDenominator_pos hz)
  convert hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hq)) using 1
  · rfl
  · dsimp [twoHeadDenominator] at *
    field_simp
    ring

/-- `twoHeadDensity` is strictly decreasing on `[2/3, 4/5]`. -/
theorem twoHeadDensity_strictAntiOn_full : StrictAntiOn twoHeadDensity (Set.Icc (2 / 3) (4 / 5)) := by
  have hc : ContinuousOn twoHeadDensity (Set.Icc (2 / 3) (4 / 5)) := by
    intro z hz
    have hd := twoHeadDenominator_pos hz.1
    unfold twoHeadDenominator at hd
    unfold twoHeadDensity twoHeadDenominator
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
  intro z hz
  have hzlo := (interior_subset hz).1
  have hzhi : z ≤ 4 / 5 := (interior_subset hz).2
  have hz0 : 0 < z := by linarith
  have ht : 0 ≤ z - 2 / 3 := sub_nonneg.mpr hzlo
  have ht' : z - 2 / 3 ≤ 2 / 15 := by linarith
  have h2 : (z - 2 / 3) ^ 2 ≤ (2 / 15 : ℝ) ^ 2 := by gcongr
  have h3 : (z - 2 / 3) ^ 3 ≤ (2 / 15 : ℝ) ^ 3 := by gcongr
  have hp : 21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5 < 0 := by nlinarith
  rw [(twoHeadDensity_hasDerivAt hzlo).deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hz0 hp)
    (mul_pos (by norm_num) (pow_pos (twoHeadDenominator_pos hzlo) 3))

/-- `twoHeadDensity` is strictly decreasing on `[2/3, z_C]`. -/
theorem twoHeadDensity_strictAntiOn : StrictAntiOn twoHeadDensity (Set.Icc (2 / 3) zC) :=
  twoHeadDensity_strictAntiOn_full.mono (fun _ hz => ⟨hz.1, hz.2.trans zC_spec.1.2⟩)

/-- Uniqueness for `mixedInverse`: for `e ∈ [ε*, ε_D]`, every `s ∈ [σ_D, σ₀]`
with `mixedDensity s = e` equals `mixedInverse e`. -/
theorem mixedInverse_unique {e s : ℝ} (he : e ∈ Set.Icc epsilonStar epsilonD)
    (hs : s ∈ Set.Icc sigmaD sigmaZero) (hroot : mixedDensity s = e) : s = mixedInverse e := by
  apply mixedDensity_strictAntiOn.injOn hs (mixedInverse_spec he).1
  exact hroot.trans (mixedInverse_spec he).2.symm

/-- Uniqueness for `twoHeadInverse`: for `e ∈ [ε_C, 1/4]`, every
`z ∈ [2/3, z_C]` with `twoHeadDensity z = e` equals `twoHeadInverse e`. -/
theorem twoHeadInverse_unique {e z : ℝ} (he : e ∈ Set.Icc epsilonC (1 / 4))
    (hz : z ∈ Set.Icc (2 / 3) zC) (hroot : twoHeadDensity z = e) : z = twoHeadInverse e := by
  apply twoHeadDensity_strictAntiOn.injOn hz (twoHeadInverse_spec he).1
  exact hroot.trans (twoHeadInverse_spec he).2.symm

/-- The ends of the mixed branch of `W` satisfy `ε* < ε_D`. -/
theorem epsilonStar_lt_epsilonD : epsilonStar < epsilonD := by
  have hlt : sigmaD < sigmaZero := by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1]
  have h := mixedDensity_strictAntiOn ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  simpa only [mixedDensity_sigmaZero, epsilonD] using h

/-- The split junction of `E₂` satisfies `ε_C < 1/4`. -/
theorem epsilonC_lt_quarter : epsilonC < 1 / 4 := by
  have hlt : (2 / 3 : ℝ) < zC := by linarith [zC_spec.1.1]
  have h := twoHeadDensity_strictAntiOn ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  simpa only [twoHeadDensity_two_thirds, epsilonC] using h

/-- At `e = ε*` the mixed inverse is the upper end: `mixedInverse ε* = σ₀`. -/
theorem mixedInverse_epsilonStar : mixedInverse epsilonStar = sigmaZero := by
  symm
  exact mixedInverse_unique ⟨le_rfl, epsilonStar_lt_epsilonD.le⟩
    ⟨by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1], le_rfl⟩ mixedDensity_sigmaZero

/-- At `e = ε_D` the mixed inverse is the lower end: `mixedInverse ε_D = σ_D`. -/
theorem mixedInverse_epsilonD : mixedInverse epsilonD = sigmaD := by
  symm
  exact mixedInverse_unique ⟨epsilonStar_lt_epsilonD.le, le_rfl⟩
    ⟨le_rfl, by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1]⟩ rfl

/-- At `e = ε_C` the two-head inverse is the upper end: `twoHeadInverse ε_C = z_C`. -/
theorem twoHeadInverse_epsilonC : twoHeadInverse epsilonC = zC := by
  symm
  exact twoHeadInverse_unique ⟨le_rfl, epsilonC_lt_quarter.le⟩
    ⟨by linarith [zC_spec.1.1], le_rfl⟩ rfl

/-- At `e = 1/4` the two-head inverse is the lower end: `twoHeadInverse (1/4) = 2/3`. -/
theorem twoHeadInverse_quarter : twoHeadInverse (1 / 4) = 2 / 3 := by
  symm
  exact twoHeadInverse_unique ⟨epsilonC_lt_quarter.le, le_rfl⟩
    ⟨le_rfl, by linarith [zC_spec.1.1]⟩ twoHeadDensity_two_thirds

/-- At `σ_D` the mixed dual-certificate value equals the missing-edge density:
`mixedValue σ_D = ε_D`. -/
theorem mixedValue_sigmaD : mixedValue sigmaD = epsilonD := by
  have hq := ne_of_gt (mixedDenominator_pos (by linarith [sigmaD_spec.1.1] : 0 ≤ sigmaD))
  have hid (s : ℝ) (hq : mixedDenominator s ≠ 0) :
      mixedValue s - mixedDensity s = s * mixedRootPolynomial s / (6 * mixedDenominator s ^ 2) := by
    unfold mixedValue mixedDensity mixedRootPolynomial
    field_simp
    ring
  have h := hid sigmaD hq
  rw [sigmaD_spec.2, mul_zero, zero_div] at h
  exact sub_eq_zero.mp h

/-- The curve `W` satisfies `W(ε_D) = ε_D`. -/
@[simp] theorem mixedCurve_epsilonD : mixedCurve epsilonD = epsilonD := by
  simp only [mixedCurve, not_le.mpr epsilonStar_lt_epsilonD, ite_false, le_refl, ite_true,
    mixedInverse_epsilonD, mixedValue_sigmaD]

/-- The curve `E₂` satisfies `E₂(1/4) = 1/4`. -/
@[simp] theorem twoHeadCurve_quarter : twoHeadCurve (1 / 4) = 1 / 4 := by
  norm_num only [twoHeadCurve, show (1 / 4 : ℝ) ≠ 0 by norm_num, ite_false,
    not_le.mpr epsilonC_lt_quarter, twoHeadInverse_quarter, twoHeadValue,
    twoHeadDensity_two_thirds, twoHeadDenominator]

/-- For `1/3 ≤ r < 1/2`, the split value is the index-two polynomial: `H(r) = (-5r² + 6r - 1)/6`. -/
theorem splitValue_index_two {r : ℝ} (hlo : 1 / 3 ≤ r) (hhi : r < 1 / 2) :
    splitValue r = (-5 * r ^ 2 + 6 * r - 1) / 6 := by
  have hr : 0 < r := by linarith
  have hj : splitIndex r = 2 := by
    unfold splitIndex
    have hceil : ⌈(1 - r) / r⌉₊ = 2 := by
      apply (Nat.ceil_eq_iff (by decide : 2 ≠ 0)).mpr
      constructor
      · norm_num only [Nat.reduceSub, Nat.cast_one]
        apply (lt_div_iff₀ hr).mpr
        linarith
      · apply (div_le_iff₀ hr).mpr
        norm_num
        linarith
    rw [hceil]
    decide
  unfold splitValue
  rw [ite_eq_right hr.ne', hj]
  norm_num

/-- At the split junction of `W` the split argument is `√(2ε*) = (9 - √21)/10`. -/
theorem sqrt_two_epsilonStar : Real.sqrt (2 * epsilonStar) = (9 - Real.sqrt 21) / 10 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  apply (Real.sqrt_eq_iff_eq_sq ?_ ?_).mpr
  · unfold epsilonStar
    nlinarith
  · unfold epsilonStar
    nlinarith
  · nlinarith

/-- At `σ₀` the mixed dual-certificate value equals the split value at the
junction: `mixedValue σ₀ = H(√(2ε*))`. -/
theorem mixedValue_sigmaZero : mixedValue sigmaZero = splitValue (Real.sqrt (2 * epsilonStar)) := by
  have hs : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  rw [sqrt_two_epsilonStar, splitValue_index_two (by nlinarith : (1 / 3 : ℝ) ≤
    (9 - Real.sqrt 21) / 10) (by nlinarith : (9 - Real.sqrt 21) / 10 < (1 / 2 : ℝ))]
  have hd := ne_of_gt (mixedDenominator_pos (by linarith [sigmaZero_bounds.1] : 0 ≤ sigmaZero))
  unfold mixedValue
  apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd))).mpr
  unfold mixedDenominator sigmaZero
  have h3 : (Real.sqrt 21) ^ 3 = 21 * Real.sqrt 21 := by rw [pow_succ, hs]
  have h4 : (Real.sqrt 21) ^ 4 = 441 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]; norm_num
  have h5 : (Real.sqrt 21) ^ 5 = 441 * Real.sqrt 21 := by rw [pow_succ, h4]
  have h6 : (Real.sqrt 21) ^ 6 = 9261 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hs]; norm_num
  ring_nf
  simp only [hs, h3, h4, h5, h6]
  ring

/-- The split and rational mixed branches have exactly the same endpoint value. -/
theorem mixed_branch_match :
    mixedValue (mixedInverse epsilonStar) = splitValue (Real.sqrt (2 * epsilonStar)) := by
  rw [mixedInverse_epsilonStar, mixedValue_sigmaZero]

/-- The split junction of `E₂` satisfies `13/121 ≤ ε_C ≤ 9/80`. -/
theorem epsilonC_bounds : (13 / 121 : ℝ) ≤ epsilonC ∧ epsilonC ≤ 9 / 80 := by
  have hleft := twoHeadDensity_strictAntiOn_full.antitoneOn
    (show zC ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) from ⟨by linarith [zC_spec.1.1], zC_spec.1.2⟩)
    (show (4 / 5 : ℝ) ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) by norm_num) zC_spec.1.2
  have hright := twoHeadDensity_strictAntiOn_full.antitoneOn
    (show (3 / 4 : ℝ) ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) by norm_num)
    (show zC ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) from ⟨by linarith [zC_spec.1.1], zC_spec.1.2⟩)
    zC_spec.1.1
  norm_num [twoHeadDensity, twoHeadDenominator] at hleft hright
  exact ⟨hleft, hright⟩

/-- At `z_C` the two-head dual-certificate value equals the split value at the
junction: `twoHeadValue z_C = H(√(2ε_C))`. -/
theorem twoHeadValue_zC : twoHeadValue zC = splitValue (Real.sqrt (2 * epsilonC)) := by
  have he := epsilonC_bounds
  have he0 : 0 ≤ 2 * epsilonC := by linarith
  have hs := Real.sq_sqrt he0
  have hn := Real.sqrt_nonneg (2 * epsilonC)
  rw [splitValue_index_two (by nlinarith : (1 / 3 : ℝ) ≤ Real.sqrt (2 * epsilonC))
    (by nlinarith : Real.sqrt (2 * epsilonC) < (1 / 2 : ℝ))]
  have hz := zC_spec.1
  have hq := ne_of_gt (twoHeadDenominator_pos (by linarith [hz.1] : (2 / 3 : ℝ) ≤ zC))
  have hid (z : ℝ) (hq : twoHeadDenominator z ≠ 0) :
      (twoHeadValue z + 5 / 3 * twoHeadDensity z + 1 / 6) ^ 2 - 2 * twoHeadDensity z =
        z ^ 2 * (z - 1) ^ 2 * twoHeadRootPolynomial z / (576 * twoHeadDenominator z ^ 4) := by
    unfold twoHeadValue twoHeadDensity twoHeadRootPolynomial
    field_simp
    unfold twoHeadDenominator
    ring
  have hi := hid zC hq
  rw [zC_spec.2, mul_zero, zero_div] at hi
  change (twoHeadValue zC + 5 / 3 * epsilonC + 1 / 6) ^ 2 - 2 * epsilonC = 0 at hi
  have hv : 0 ≤ twoHeadValue zC := by
    unfold twoHeadValue
    change 0 ≤ epsilonC + (3 * zC - 2) ^ 2 * (1 - zC) * (3 * zC - 1) /
      (24 * twoHeadDenominator zC ^ 2)
    have h1 : 0 ≤ 1 - zC := by linarith [hz.2]
    have h2 : 0 ≤ 3 * zC - 1 := by linarith [hz.1]
    have he' : 0 ≤ epsilonC := by linarith
    positivity
  nlinarith

/-- The split and rational two-head branches have exactly the same endpoint value. -/
theorem twoHead_branch_match :
    twoHeadValue (twoHeadInverse epsilonC) = splitValue (Real.sqrt (2 * epsilonC)) := by
  rw [twoHeadInverse_epsilonC, twoHeadValue_zC]

end Erdos1017.Benchmark

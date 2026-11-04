module

public import Erdos1017.Benchmark.BenchmarkProperties
public import Erdos1017.Benchmark.SplitCurve

/-!
# Derivatives of the stationary benchmark curves and split branches

These statements concern the benchmark formulas. They do not establish the
variational hypotheses needed to exclude a contact of the unknown extremal
limit.
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- For `s > 0`, `mixedValue` has derivative `(s + 1)/(3s)` times
`-s(2 + 24s + 93s² + 120s³) / (s² + 8s + 2)³`, the derivative of
`mixedDensity`, at `s`. -/
theorem mixedValue_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt mixedValue
      (((s + 1) / (3 * s)) *
        (-s * (2 + 24 * s + 93 * s ^ 2 + 120 * s ^ 3) / mixedDenominator s ^ 3)) s := by
  have hi := hasDerivAt_id s
  have hn := ((((hasDerivAt_const s (6 : ℝ)).add (hi.const_mul 46)).add
    ((hi.pow 2).const_mul 85)).sub ((hi.pow 3).const_mul 16)).sub
      ((hi.pow 4).const_mul 16)
  have hd := (((hi.pow 2).add (hi.const_mul 8)).add_const 2).pow 2 |>.const_mul 6
  have hq := ne_of_gt (mixedDenominator_pos hs.le)
  convert hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hq)) using 1
  · rfl
  · dsimp [mixedDenominator] at *
    field_simp
    ring

/-- For `z ≥ 2/3`, `twoHeadValue` has derivative `(4 - 3z)/(3z)` times
`z(21z³ - 39z² + 24z - 5) / (8(z² + z - 1)³)`, the derivative of
`twoHeadDensity`, at `z`. -/
theorem twoHeadValue_hasDerivAt {z : ℝ} (hz : 2 / 3 ≤ z) :
    HasDerivAt twoHeadValue
      (((4 - 3 * z) / (3 * z)) *
        (z * (21 * z ^ 3 - 39 * z ^ 2 + 24 * z - 5) /
          (8 * twoHeadDenominator z ^ 3))) z := by
  have hi := hasDerivAt_id z
  have hn := ((((hi.const_mul 3).sub_const 2).pow 2).mul
    ((hasDerivAt_const z (1 : ℝ)).sub hi)).mul ((hi.const_mul 3).sub_const 1)
  have hd := ((((hi.pow 2).add hi).sub_const 1).pow 2).const_mul 24
  have hq := ne_of_gt (twoHeadDenominator_pos hz)
  have hz0 : z ≠ 0 := by linarith
  convert (twoHeadDensity_hasDerivAt hz).add
    (hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hq))) using 1
  · rfl
  · dsimp [twoHeadDenominator] at *
    field_simp
    ring

/-- For `j > 0` and `d < 1/2`, `x ↦ splitPolynomial j (√(1 - 2x))` has
derivative `2(2j + 1)/(j(j + 1)) - 2/(j√(1 - 2d))` at `d`. -/
theorem splitPolynomial_density_hasDerivAt (j : ℕ) (hj : 0 < j)
    {d : ℝ} (hd : d < 1 / 2) :
    HasDerivAt (fun x : ℝ => splitPolynomial j (Real.sqrt (1 - 2 * x)))
      (2 * (2 * (j : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) -
        2 / ((j : ℝ) * Real.sqrt (1 - 2 * d))) d := by
  have hj0 : (j : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hj)
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hr : 0 < 1 - 2 * d := by linarith
  have hs := ((hasDerivAt_const d (1 : ℝ)).sub ((hasDerivAt_id d).const_mul 2)).sqrt hr.ne'
  have hs0 : Real.sqrt (1 - 2 * d) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have hn := ((((hs.pow 2).const_mul (-(2 * (j : ℝ) + 1))).add
    (hs.const_mul (2 * ((j : ℝ) + 1)))).sub_const 1).div_const
      ((j : ℝ) * ((j : ℝ) + 1))
  convert hn using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- For `j > 0` and `d < 1/2`, the slope
`x ↦ 2(2j + 1)/(j(j + 1)) - 2/(j√(1 - 2x))` of the index-`j` split polynomial
in density has derivative `-2/(j√(1 - 2d)³)` at `d`. -/
theorem splitPolynomial_density_slope_hasDerivAt (j : ℕ) (hj : 0 < j)
    {d : ℝ} (hd : d < 1 / 2) :
    HasDerivAt (fun x : ℝ =>
      2 * (2 * (j : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) -
        2 / ((j : ℝ) * Real.sqrt (1 - 2 * x)))
      (-2 / ((j : ℝ) * Real.sqrt (1 - 2 * d) ^ 3)) d := by
  have hj0 : (j : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hj)
  have hr : 0 < 1 - 2 * d := by linarith
  have hs := ((hasDerivAt_const d (1 : ℝ)).sub ((hasDerivAt_id d).const_mul 2)).sqrt hr.ne'
  have hs0 : Real.sqrt (1 - 2 * d) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have h := (hasDerivAt_const d
    (2 * (2 * (j : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)))).sub
      ((hasDerivAt_const d (2 : ℝ)).div (hs.const_mul (j : ℝ)) (mul_ne_zero hj0 hs0))
  convert h using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- For `j > 0` and `d < 1/2`, `-2/(j√(1 - 2d)³)`, the second derivative in
`d` of `splitPolynomial j (√(1 - 2d))`, is negative. -/
theorem splitPolynomial_density_curvature_neg (j : ℕ) (hj : 0 < j)
    {d : ℝ} (hd : d < 1 / 2) :
    -2 / ((j : ℝ) * Real.sqrt (1 - 2 * d) ^ 3) < 0 := by
  have hj0 : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hr : 0 < Real.sqrt (1 - 2 * d) := Real.sqrt_pos.mpr (by linarith)
  exact div_neg_of_neg_of_pos (by norm_num) (mul_pos hj0 (pow_pos hr 3))

/-- If `√(1 - 2d)` lies in the closed split cell `[1/(n + 2), 1/(n + 1)]`,
then `x ↦ H(√(1 - 2x))`, within the set of `x` with `√(1 - 2x)` in that cell,
has derivative `2(2j + 1)/(j(j + 1)) - 2/(j√(1 - 2d))` at `d`, where
`j = n + 1`. -/
theorem splitValue_density_hasDerivWithinAt_cell (n : ℕ) {d : ℝ}
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Set.Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    HasDerivWithinAt (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x)))
      (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) /
        (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) -
          2 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (1 - 2 * d)))
      {x : ℝ | Real.sqrt (1 - 2 * x) ∈
        Set.Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))} d := by
  have hr : 0 < Real.sqrt (1 - 2 * d) := lt_of_lt_of_le (by positivity) hcell.1
  have hd : d < 1 / 2 := by
    have := Real.sqrt_pos.mp hr
    linarith
  exact (splitPolynomial_density_hasDerivAt (n + 1) (by omega) hd).hasDerivWithinAt.congr_of_mem
    (fun x hx => splitValue_on_cell n hx) hcell

/-- If `√(1 - 2d)` lies in the open split cell `(1/(n + 2), 1/(n + 1))`, then
`x ↦ H(√(1 - 2x))` has derivative `2(2j + 1)/(j(j + 1)) - 2/(j√(1 - 2d))` at
`d`, where `j = n + 1`. -/
theorem splitValue_density_hasDerivAt (n : ℕ) {d : ℝ}
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Set.Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    HasDerivAt (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x)))
      (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) /
        (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) -
          2 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (1 - 2 * d))) d := by
  have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 - 2 * x)) d := by fun_prop
  have hnear : ∀ᶠ x in nhds d, Real.sqrt (1 - 2 * x) ∈
      Set.Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) :=
    hc.eventually (isOpen_Ioo.mem_nhds hcell)
  have hr : 0 < Real.sqrt (1 - 2 * d) := lt_trans (by positivity) hcell.1
  have hd : d < 1 / 2 := by
    have := Real.sqrt_pos.mp hr
    linarith
  apply (splitPolynomial_density_hasDerivAt (n + 1) (by omega) hd).congr_of_eventuallyEq
  filter_upwards [hnear] with x hx
  exact splitValue_on_cell n ⟨hx.1.le, hx.2.le⟩

/-- If `√(1 - 2d)` lies in the open split cell `(1/(n + 2), 1/(n + 1))`, then
the derivative of `x ↦ H(√(1 - 2x))` has derivative `-2/(j√(1 - 2d)³)` at `d`,
where `j = n + 1`. -/
theorem splitValue_density_deriv_hasDerivAt (n : ℕ) {d : ℝ}
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Set.Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    HasDerivAt (deriv (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x))))
      (-2 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (1 - 2 * d) ^ 3)) d := by
  have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 - 2 * x)) d := by fun_prop
  have hnear : ∀ᶠ x in nhds d, Real.sqrt (1 - 2 * x) ∈
      Set.Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) :=
    hc.eventually (isOpen_Ioo.mem_nhds hcell)
  have hr : 0 < Real.sqrt (1 - 2 * d) := lt_trans (by positivity) hcell.1
  have hd : d < 1 / 2 := by
    have := Real.sqrt_pos.mp hr
    linarith
  apply (splitPolynomial_density_slope_hasDerivAt (n + 1) (by omega) hd).congr_of_eventuallyEq
  filter_upwards [hnear] with x hx
  exact (splitValue_density_hasDerivAt n hx).deriv

/-- If `√(1 - 2d)` lies in an open split cell `(1/(n + 2), 1/(n + 1))`, then
`x ↦ H(√(1 - 2x))` has negative second derivative at `d`. -/
theorem splitValue_density_curvature_neg (n : ℕ) {d : ℝ}
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Set.Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    deriv (deriv (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x)))) d < 0 := by
  have hr : 0 < Real.sqrt (1 - 2 * d) := lt_trans (by positivity) hcell.1
  have hd : d < 1 / 2 := by
    have := Real.sqrt_pos.mp hr
    linarith
  rw [(splitValue_density_deriv_hasDerivAt n hcell).deriv]
  exact splitPolynomial_density_curvature_neg (n + 1) (by omega) hd

/-- For `m > 0`, the split polynomial of index `m` at `r = 1/m` equals `(m - 1)/m³`. -/
theorem splitPolynomial_reciprocal (m : ℕ) (hm : 0 < m) :
    splitPolynomial m (1 / (m : ℝ)) = ((m : ℝ) - 1) / (m : ℝ) ^ 3 := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold splitPolynomial
  field_simp
  ring

/-- At the cusp `r = 1/m` with `m ≥ 2`, the split value is `H(1/m) = (m - 1)/m³`. -/
theorem splitValue_reciprocal (m : ℕ) (hm : 2 ≤ m) :
    splitValue (1 / (m : ℝ)) = ((m : ℝ) - 1) / (m : ℝ) ^ 3 := by
  have hm' : (m - 1 : ℕ) + 1 = m := by omega
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hcell : 1 / (m : ℝ) ∈
      Set.Icc (1 / (((m - 1 : ℕ) : ℝ) + 2)) (1 / (((m - 1 : ℕ) : ℝ) + 1)) := by
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm'
    rw [hcast]
    refine ⟨?_, le_rfl⟩
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  rw [splitValue_on_cell (m - 1) hcell, hm']
  exact splitPolynomial_reciprocal m (by omega)

/-- For `m ≥ 2` and `j = m - 1`, minus the `d`-slope
`2(2j + 1)/(j(j + 1)) - 2/(jr)` of the index-`j` split polynomial at the cusp
`r = 1/m` equals `U_m = 2 - 2/m`. -/
theorem split_cusp_left_own_slope (m : ℕ) (hm : 2 ≤ m) :
    -(2 * (2 * ((m - 1 : ℕ) : ℝ) + 1) /
      (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1)) -
        2 / (((m - 1 : ℕ) : ℝ) * (1 / (m : ℝ)))) = 2 - 2 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (by omega))
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  field_simp [hm0, hm1]
  ring

/-- For `m > 0`, minus the `d`-slope `2(2m + 1)/(m(m + 1)) - 2/(mr)` of the
index-`m` split polynomial at the cusp `r = 1/m` equals
`L_m = 2 - 2/m - 2/(m + 1)`. -/
theorem split_cusp_right_own_slope (m : ℕ) (hm : 0 < m) :
    -(2 * (2 * (m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 1)) -
        2 / ((m : ℝ) * (1 / (m : ℝ)))) =
      2 - 2 / (m : ℝ) - 2 / ((m : ℝ) + 1) := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- For `m > 0`, the upper cusp slope satisfies `U_m = 2 - 2/m < 2`. -/
theorem split_cusp_upper_slope_lt_two (m : ℕ) (hm : 0 < m) :
    2 - 2 / (m : ℝ) < 2 := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have : 0 < 2 / (m : ℝ) := div_pos (by norm_num) hm0
  linarith

/-- For `m ≥ 4`, the lower cusp slope satisfies `L_m = 2 - 2/m - 2/(m + 1) ≥ 11/10`. -/
theorem split_cusp_lower_slope_ge_eleven_tenths (m : ℕ) (hm : 4 ≤ m) :
    11 / 10 ≤ 2 - 2 / (m : ℝ) - 2 / ((m : ℝ) + 1) := by
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 2 / (m : ℝ) ≤ 1 / 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have h2 : 2 / ((m : ℝ) + 1) ≤ 2 / 5 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

/-- At `m = 3` the lower cusp slope is `L_3 = 2 - 2/3 - 2/4 = 5/6`. -/
theorem split_cusp_lower_slope_three :
    2 - 2 / (3 : ℝ) - 2 / ((3 : ℝ) + 1) = 5 / 6 := by norm_num

/-- At `σ₀` the mixed slope is `(σ₀ + 1)/(3σ₀) = (√21 - 1)/6`. -/
theorem mixed_own_slope_sigmaZero :
    (sigmaZero + 1) / (3 * sigmaZero) = (Real.sqrt 21 - 1) / 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hs0 : sigmaZero ≠ 0 := ne_of_gt (lt_trans (by norm_num) sigmaZero_bounds.1)
  unfold sigmaZero at *
  field_simp
  nlinarith

/-- At `r = √(2ε*)`, minus the `d`-slope `2(2j + 1)/(j(j + 1)) - 2/(jr)` of
the index-two split polynomial (`j = 2`) equals `(√21 - 1)/6`. -/
theorem split_own_slope_epsilonStar :
    -(2 * (2 * (2 : ℝ) + 1) / ((2 : ℝ) * ((2 : ℝ) + 1)) -
        2 / ((2 : ℝ) * Real.sqrt (2 * epsilonStar))) = (Real.sqrt 21 - 1) / 6 := by
  rw [sqrt_two_epsilonStar]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hs0 : 9 - Real.sqrt 21 ≠ 0 := by nlinarith
  field_simp
  nlinarith

end Erdos1017.Benchmark

module

public import Erdos1017.Multipartite.TwoHead.TwoHeadCountLaw
public import Erdos1017.Multipartite.BenchmarkLowDensityGuards
public import Erdos1017.Multipartite.TwoHead.TwoHeadStationaryComparison
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Interior comparison of the two-head count cells

The `t = 0` comparison for the explicit selected two-head count cells. The proof
selects a maximum on a compact fixed-density profile fiber and derives its
stationary alternatives. No optimized-family upper bound or supplied stationary
maximizer is assumed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.TwoHeadInteriorComparison

/-- The `j = 2`, `t = 0` cost after total physical mass is normalized to one. -/
def quadraticCost (a b : ℝ) : ℝ :=
  a * b + (4 * (a - b) * (1 - a - b) - (1 - a - b) ^ 2) / 6

theorem quadraticCost_expansion (a b : ℝ) :
    quadraticCost a b = -5 * a ^ 2 / 6 + b ^ 2 / 2 + 2 * a * b / 3 + a - b / 3 - 1 / 6 := by
  unfold quadraticCost
  ring

/-- The enlarged `t = 0` domain retains density and all physical boundary faces. -/
def profileFiber (ε : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ Set.Icc (0, 0) (1 / 2, 1 / 2) ∧ p.2 ≤ p.1 ∧
    1 - p.1 - p.2 ≤ p.1 ∧ p.1 ^ 2 + p.2 ^ 2 = 2 * ε}

theorem profileFiber_isCompact (ε : ℝ) : IsCompact (profileFiber ε) := by
  have hc : IsClosed (profileFiber ε) :=
    isClosed_Icc.inter ((isClosed_le continuous_snd continuous_fst).inter
      ((isClosed_le (by fun_prop) continuous_fst).inter (isClosed_eq (by fun_prop) continuous_const)))
  exact isCompact_Icc.of_isClosed_subset hc (fun _ hp => hp.1)

/-- Compactness selects an actual maximum of the physical quadratic cost. -/
theorem exists_quadratic_maximum {ε : ℝ} (hne : (profileFiber ε).Nonempty) :
    ∃ p ∈ profileFiber ε, ∀ q ∈ profileFiber ε, quadraticCost q.1 q.2 ≤ quadraticCost p.1 p.2 := by
  obtain ⟨p, hp, hmax⟩ := (profileFiber_isCompact ε).exists_isMaxOn
    (f := fun q => quadraticCost q.1 q.2) hne (by
      unfold quadraticCost
      fun_prop)
  exact ⟨p, hp, fun q hq => hmax hq⟩

/-- The two endpoint density restrictions follow from the physical profile constraints. -/
theorem profile_density_bounds {ε : ℝ} {p : ℝ × ℝ} (hp : p ∈ profileFiber ε) :
    ε ∈ Set.Icc (1 / 10 : ℝ) (1 / 4) := by
  have ha0 := hp.1.1.1
  have hb0 := hp.1.1.2
  have ha1 := hp.1.2.1
  have hb1 := hp.1.2.2
  have hsum : 1 ≤ 2 * p.1 + p.2 := by linarith [hp.2.2.1]
  constructor
  · nlinarith [sq_nonneg (p.1 - 2 * p.2), hp.2.2.2]
  · nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1), mul_nonneg hb0 (sub_nonneg.mpr hb1), hp.2.2.2]

/-- A rational circle rotation preserves the prescribed head-square sum exactly. -/
def circleA (a b t : ℝ) : ℝ := (a * (1 - t ^ 2) + 2 * b * t) / (1 + t ^ 2)
def circleB (a b t : ℝ) : ℝ := (b * (1 - t ^ 2) - 2 * a * t) / (1 + t ^ 2)

theorem circle_density (a b t : ℝ) :
    circleA a b t ^ 2 + circleB a b t ^ 2 = a ^ 2 + b ^ 2 := by
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  unfold circleA circleB
  field_simp
  ring

theorem circleA_hasDerivAt (a b : ℝ) : HasDerivAt (circleA a b) (2 * b) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hn := ((hasDerivAt_const 0 (1 : ℝ)).sub (hi.pow 2)).const_mul a |>.add (hi.const_mul (2 * b))
  have hd := (hasDerivAt_const 0 (1 : ℝ)).add (hi.pow 2)
  convert hn.div hd (by norm_num) using 1
  · funext t
    rfl
  · norm_num [circleA]

theorem circleB_hasDerivAt (a b : ℝ) : HasDerivAt (circleB a b) (-2 * a) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hn := ((hasDerivAt_const 0 (1 : ℝ)).sub (hi.pow 2)).const_mul b |>.sub (hi.const_mul (2 * a))
  have hd := (hasDerivAt_const 0 (1 : ℝ)).add (hi.pow 2)
  convert hn.div hd (by norm_num) using 1
  · funext t
    rfl
  · norm_num [circleB]

/-- A strict interior maximum has its true circle-tangent derivative equal to zero. -/
theorem stationary_of_quadratic_max {ε a b : ℝ}
    (hp : (a, b) ∈ profileFiber ε)
    (hmax : ∀ q ∈ profileFiber ε, quadraticCost q.1 q.2 ≤ quadraticCost a b)
    (hb : 0 < b) (hab : b < a) (ha : a < 1 / 2) (hm : 1 - a - b < a) :
    2 * a ^ 2 + 8 * a * b - 2 * b ^ 2 - a - 3 * b = 0 := by
  let U : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ q.2 < q.1 ∧ q.1 < 1 / 2 ∧ 1 - q.1 - q.2 < q.1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_fst).inter
        ((isOpen_lt continuous_fst continuous_const).inter (isOpen_lt (by fun_prop) continuous_fst)))
  have hc : ContinuousAt (fun t : ℝ => (circleA a b t, circleB a b t)) 0 := by
    unfold circleA circleB
    fun_prop (disch := positivity)
  have hnear : ∀ᶠ t in nhds (0 : ℝ), (circleA a b t, circleB a b t) ∈ U := by
    apply hc.eventually
    apply hU.mem_nhds
    simpa [U, circleA, circleB] using And.intro hb (And.intro hab (And.intro ha hm))
  have hlocal : IsLocalMax (fun t => quadraticCost (circleA a b t) (circleB a b t)) 0 := by
    change ∀ᶠ t in nhds (0 : ℝ), _ ≤ _
    filter_upwards [hnear] with t ht
    have hmem : (circleA a b t, circleB a b t) ∈ profileFiber ε := by
      refine ⟨⟨⟨?_, ht.1.le⟩, ⟨ht.2.2.1.le, ?_⟩⟩, ht.2.1.le, ht.2.2.2.le, ?_⟩
      · exact ht.1.le.trans ht.2.1.le
      · exact ht.2.1.le.trans ht.2.2.1.le
      · rw [circle_density]
        exact hp.2.2.2
    simpa [circleA, circleB] using hmax _ hmem
  have hA := circleA_hasDerivAt a b
  have hB := circleB_hasDerivAt a b
  have hder := ((((((hA.pow 2).const_mul (-5 / 6 : ℝ)).add
    ((hB.pow 2).const_mul (1 / 2))).add ((hA.mul hB).const_mul (2 / 3))).add hA).sub
      (hB.const_mul (1 / 3))).sub_const (1 / 6)
  have hder' : HasDerivAt (fun t => quadraticCost (circleA a b t) (circleB a b t))
      (-(2 / 3) * (2 * a ^ 2 + 8 * a * b - 2 * b ^ 2 - a - 3 * b)) 0 := by
    convert hder using 1
    · funext t
      change quadraticCost (circleA a b t) (circleB a b t) =
        (-5 / 6) * circleA a b t ^ 2 + (1 / 2) * circleB a b t ^ 2 +
          (2 / 3) * (circleA a b t * circleB a b t) + circleA a b t -
            (1 / 3) * circleB a b t - 1 / 6
      rw [quadraticCost_expansion]
      ring
    · norm_num [circleA, circleB]
      ring
  have hzero := hlocal.hasDerivAt_eq_zero hder'
  linarith

/-- The stationary equations force the actual rational E2 profile, with
its parameter in the full physical stationary range. -/
theorem stationary_profile_classification {ε a b : ℝ}
    (hp : (a, b) ∈ profileFiber ε) (hab : b < a) (ha : a < 1 / 2)
    (hstat : 2 * a ^ 2 + 8 * a * b - 2 * b ^ 2 - a - 3 * b = 0) :
    ∃ z ∈ Set.Icc (2 / 3 : ℝ) (4 / 5),
      ε = Benchmark.twoHeadDensity z ∧ quadraticCost a b = Benchmark.twoHeadValue z := by
  let m := 1 - a - b
  have hm : 0 < m := by
    dsimp [m]
    linarith [hp.2.1]
  let z := (a - b) / m
  have hz0 : 0 < z := div_pos (sub_pos.mpr hab) hm
  have hz1 : z < 1 := (div_lt_one hm).mpr (by
    dsimp [m]
    linarith)
  have hzm : z * m = a - b := div_mul_cancel₀ _ hm.ne'
  have hae : a = (1 - m + z * m) / 2 := by
    dsimp [m] at ⊢
    nlinarith [hzm]
  have hbe : b = (1 - m - z * m) / 2 := by
    dsimp [m] at ⊢
    nlinarith [hzm]
  have hconstraint : m * (3 - z) ≤ 1 := by nlinarith [hp.2.2.1, hae]
  have hid : 2 * a ^ 2 + 8 * a * b - 2 * b ^ 2 - a - 3 * b =
      -m * (2 - 3 * z + 2 * m * (z ^ 2 + z - 1)) := by
    rw [hae, hbe]
    ring
  have hs : 2 - 3 * z + 2 * m * (z ^ 2 + z - 1) = 0 := by
    have hprod : m * (2 - 3 * z + 2 * m * (z ^ 2 + z - 1)) = 0 := by
      linarith [hid]
    exact (mul_eq_zero.mp hprod).resolve_left hm.ne'
  have hzg : 2 / 3 < z := by
    by_contra h
    have hz : z ≤ 2 / 3 := le_of_not_gt h
    by_cases hD : z ^ 2 + z - 1 < 0
    · have hbase : 0 < (z - 1) * (5 * z - 4) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hconstraint) hD.le
      have hsmul := congrArg (fun v : ℝ => v * (3 - z)) hs
      nlinarith
    · have hnonneg := mul_nonneg hm.le (le_of_not_gt hD)
      have heq : z = 2 / 3 := by nlinarith
      rw [heq] at hs
      nlinarith
  have hD : 0 < z ^ 2 + z - 1 := by
    simpa [Benchmark.twoHeadDenominator] using Benchmark.twoHeadDenominator_pos hzg.le
  have hzu : z ≤ 4 / 5 := by
    have hmul := mul_nonneg hD.le (sub_nonneg.mpr hconstraint)
    have hsmul := congrArg (fun v : ℝ => v * (3 - z)) hs
    have hprod : 0 ≤ (z - 1) * (5 * z - 4) := by nlinarith
    by_contra h
    have hnegative := mul_neg_of_neg_of_pos (sub_neg.mpr hz1) (by linarith : 0 < 5 * z - 4)
    linarith
  have hD0 : z ^ 2 + z - 1 ≠ 0 := ne_of_gt hD
  have haform : a = z * (5 * z - 3) / (4 * (z ^ 2 + z - 1)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hD0)).mpr
    have haeD := congrArg (fun v : ℝ => v * (2 * (z ^ 2 + z - 1))) hae
    have hsz := congrArg (fun v : ℝ => v * z) hs
    nlinarith
  have hbform : b = z * (1 - z) / (4 * (z ^ 2 + z - 1)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hD0)).mpr
    have hbeD := congrArg (fun v : ℝ => v * (2 * (z ^ 2 + z - 1))) hbe
    have hsz := congrArg (fun v : ℝ => v * z) hs
    nlinarith
  refine ⟨z, ⟨hzg.le, hzu⟩, ?_, ?_⟩
  · have he : Benchmark.twoHeadDensity z = (a ^ 2 + b ^ 2) / 2 := by
      rw [haform, hbform]
      unfold Benchmark.twoHeadDensity Benchmark.twoHeadDenominator
      field_simp [hD0]
      ring
    rw [he]
    nlinarith [hp.2.2.2]
  · rw [haform, hbform]
    unfold quadraticCost Benchmark.twoHeadValue Benchmark.twoHeadDensity Benchmark.twoHeadDenominator
    generalize hq : z ^ 2 + z - 1 = q at hD0 ⊢
    field_simp [hD0]
    rw [← hq]
    ring

/-- The benchmark family is at least the missing density throughout the t=0 range. -/
theorem epsilon_le_twoHeadCurve {ε : ℝ} (hε : ε ∈ Set.Icc (1 / 10 : ℝ) (1 / 4)) :
    ε ≤ Benchmark.twoHeadCurve ε := by
  by_cases hc : ε ≤ Benchmark.epsilonC
  · have hr := Real.sqrt_nonneg (2 * ε)
    have hrsq := Real.sq_sqrt (show 0 ≤ 2 * ε by linarith [hε.1])
    have hbounds : Real.sqrt (2 * ε) ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
      constructor <;> nlinarith [hε.1, hc.trans Benchmark.epsilonC_bounds.2]
    have hvalue := Benchmark.splitValue_on_cell (r := Real.sqrt (2 * ε)) 1
      (by
        norm_num only [Nat.cast_one]
        exact hbounds)
    have hprod : 0 ≤ (1 - 2 * Real.sqrt (2 * ε)) * (4 * Real.sqrt (2 * ε) - 1) :=
      mul_nonneg (by linarith [hbounds.2]) (by linarith [hbounds.1])
    rw [Benchmark.twoHeadCurve, ite_eq_right (by linarith [hε.1] : ε ≠ 0), ite_eq_left hc, hvalue]
    unfold Benchmark.splitPolynomial
    norm_num only [Nat.cast_one, Nat.cast_ofNat]
    nlinarith
  · have he := Benchmark.twoHeadInverse_spec
      (show ε ∈ Set.Icc Benchmark.epsilonC (1 / 4) from ⟨le_of_not_ge hc, hε.2⟩)
    have hval := Benchmark.twoHeadValue_ge_density ⟨he.1.1, he.1.2.trans Benchmark.zC_spec.1.2⟩
    rw [Benchmark.twoHeadCurve, ite_eq_right (by linarith [hε.1] : ε ≠ 0), ite_eq_right hc]
    rwa [he.2] at hval

/-- On the dust-mean-one tail boundary `1 - a - b = a`, the cost is below the actual
split curve at the same density. -/
theorem quadraticCost_le_split_of_tail_boundary {ε a b : ℝ}
    (hp : (a, b) ∈ profileFiber ε) (htail : 1 - a - b = a) :
    quadraticCost a b ≤ Benchmark.splitValue (Real.sqrt (2 * ε)) := by
  have ha0 := hp.1.1.1
  have hb0 := hp.1.1.2
  have ha1 := hp.1.2.1
  have hab := hp.2.1
  have ha3 : 1 / 3 ≤ a := by linarith
  have hr := Real.sqrt_nonneg (2 * ε)
  have hrsq : Real.sqrt (2 * ε) ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Real.sq_sqrt (by linarith [profile_density_bounds hp |>.1] : 0 ≤ 2 * ε)]
    exact hp.2.2.2.symm
  have hra : a ≤ Real.sqrt (2 * ε) := by nlinarith [sq_nonneg b]
  have hrab : Real.sqrt (2 * ε) ≤ a + b := by nlinarith [mul_nonneg ha0 hb0]
  have hsum : Real.sqrt (2 * ε) + a ≤ 1 := by linarith
  have hupper : Real.sqrt (2 * ε) ≤ 1 / 2 := by
    have hprod := mul_nonneg (show 0 ≤ 1 / 2 - a by linarith)
      (show 0 ≤ 5 * a - 3 / 2 by linarith)
    have hbe : b = 1 - 2 * a := by linarith
    rw [hbe] at hrsq
    nlinarith
  have hcell : Real.sqrt (2 * ε) ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := ⟨ha3.trans hra, hupper⟩
  rw [Benchmark.splitValue_on_cell (r := Real.sqrt (2 * ε)) 1
    (by
      norm_num only [Nat.cast_one]
      exact hcell)]
  have hcost : quadraticCost a b = a ^ 2 / 2 + a * b / 3 := by
    unfold quadraticCost
    rw [htail]
    ring
  rw [hcost]
  unfold Benchmark.splitPolynomial
  norm_num only [Nat.cast_one, Nat.cast_ofNat]
  have hprod := mul_nonneg (sub_nonneg.mpr hra) (show 0 ≤ 1 - Real.sqrt (2 * ε) - a by linarith)
  nlinarith

/-- The explicit j=2 quadratic is below the actual two-head benchmark curve
on the complete enlarged t=0 physical domain, including all boundary densities. -/
theorem quadraticCost_le_twoHeadCurve {ε a b : ℝ} (hp : (a, b) ∈ profileFiber ε) :
    quadraticCost a b ≤ Benchmark.twoHeadCurve ε := by
  by_contra h
  have hgap := lt_of_not_ge h
  obtain ⟨⟨A, B⟩, hAB, hmax⟩ := exists_quadratic_maximum ⟨(a, b), hp⟩
  have hlarge : Benchmark.twoHeadCurve ε < quadraticCost A B := hgap.trans_le (hmax _ hp)
  have hε := profile_density_bounds hAB
  have hεcurve := epsilon_le_twoHeadCurve hε
  have hA : A < 1 / 2 := by
    by_contra hA
    have heq : A = 1 / 2 := le_antisymm hAB.1.2.1 (le_of_not_gt hA)
    have hcost : quadraticCost A B = ε := by
      rw [quadraticCost_expansion, heq]
      nlinarith [hAB.2.2.2]
    rw [hcost] at hlarge
    linarith
  have hBA : B < A := by
    by_contra hBA
    have heq : B = A := le_antisymm hAB.2.1 (le_of_not_gt hBA)
    have hcost : quadraticCost A B ≤ ε := by
      rw [quadraticCost_expansion, heq]
      nlinarith [hAB.2.2.2, sq_nonneg (1 - 2 * A)]
    exact (not_lt_of_ge (hcost.trans hεcurve)) hlarge
  have hB : 0 < B := by
    have hB0 := hAB.1.1.2
    nlinarith [hAB.2.2.1]
  have hm : 1 - A - B < A := by
    by_contra hm
    have heq : 1 - A - B = A := le_antisymm hAB.2.2.1 (le_of_not_gt hm)
    have hcost := (quadraticCost_le_split_of_tail_boundary hAB heq).trans
      (Benchmark.splitValue_le_twoHeadCurve ⟨by linarith [hε.1], hε.2⟩)
    exact (not_lt_of_ge hcost) hlarge
  have hstationary := stationary_of_quadratic_max hAB hmax hB hBA hA hm
  obtain ⟨z, hz, heq, hcost⟩ := stationary_profile_classification hAB hBA hA hstationary
  have hupper := Benchmark.twoHeadValue_le_twoHeadCurve_density hz
  rw [← heq, ← hcost] at hupper
  exact (not_lt_of_ge hupper) hlarge

/-- The completed square bounds every index at least three without
an infinite subdivision of reciprocal parameter cells. -/
def indexGap (j : ℕ) (z : ℝ) : ℝ :=
  -z ^ 2 / 2 + 2 * z / ((j : ℝ) + 1) - 1 / ((j : ℝ) * ((j : ℝ) + 1))

theorem indexGap_le_one_twenty_fourth {j : ℕ} (hj : 3 ≤ j) (z : ℝ) :
    indexGap j z ≤ 1 / 24 := by
  have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hid : indexGap j z = ((j : ℝ) - 1) / ((j : ℝ) * ((j : ℝ) + 1) ^ 2) -
      (z - 2 / ((j : ℝ) + 1)) ^ 2 / 2 := by
    unfold indexGap
    field_simp
    ring
  have hconstant : ((j : ℝ) - 1) / ((j : ℝ) * ((j : ℝ) + 1) ^ 2) ≤ 1 / 24 := by
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) * ((j : ℝ) + 1) ^ 2)).mpr
    have hprod := mul_nonneg (show 0 ≤ (j : ℝ) - 3 by linarith)
      (show 0 ≤ (j : ℝ) ^ 2 + 5 * (j : ℝ) - 8 by nlinarith)
    nlinarith
  rw [hid]
  nlinarith [sq_nonneg (z - 2 / ((j : ℝ) + 1))]

/-- A same-density profile at z=1/2 exists and has at least as much dust
as every feasible profile with z at most one half. -/
theorem exists_half_parameter_profile {ε a b : ℝ}
    (hp : (a, b) ∈ profileFiber ε) (hdiff : a - b ≤ (1 - a - b) / 2) :
    ∃ u ∈ Set.Icc (1 - a - b) (2 / 5 : ℝ),
      (1 / 2 - u / 4, 1 / 2 - 3 * u / 4) ∈ profileFiber ε ∧
        quadraticCost (1 / 2 - u / 4) (1 / 2 - 3 * u / 4) = ε + u ^ 2 / 24 := by
  let m := 1 - a - b
  let f : ℝ → ℝ := fun u => ((1 - u) ^ 2 + u ^ 2 / 4) / 4
  have hm0 : 0 ≤ m := by
    dsimp [m]
    linarith [hp.1.2.1, hp.1.2.2]
  have hm4 : m ≤ 2 / 5 := by
    dsimp [m] at ⊢
    linarith [hp.2.2.1]
  have heupper : ε ≤ f m := by
    have hprod := mul_nonneg (show 0 ≤ m / 2 - (a - b) by
      dsimp [m]
      linarith)
      (show 0 ≤ m / 2 + (a - b) by linarith [hp.2.1])
    dsimp [f, m] at *
    nlinarith [hp.2.2.2]
  have helower : f (2 / 5) ≤ ε := by
    dsimp [f]
    norm_num
    exact (profile_density_bounds hp).1
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' hm4
    (show ContinuousOn f (Set.Icc m (2 / 5)) by
      dsimp [f]
      fun_prop) ⟨helower, heupper⟩
  have hu0 : 0 ≤ u := hm0.trans hu.1
  refine ⟨u, hu, ?_, ?_⟩
  · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_, ?_⟩
    · linarith [hu.2]
    · linarith [hu.2]
    · linarith
    · linarith
    · linarith
    · linarith [hu.2]
    · dsimp [f] at heq
      nlinarith
  · unfold quadraticCost
    dsimp [f] at heq
    nlinarith

/-- All higher t=0 cells are dominated by an actual j=2 profile at the
same density, obtained by the intermediate value theorem. -/
theorem higher_index_cost_le_twoHeadCurve {ε a b : ℝ} {j : ℕ}
    (hp : (a, b) ∈ profileFiber ε) (hj : 3 ≤ j)
    (hdiff : a - b ≤ (1 - a - b) / 2) (z : ℝ) :
    ε + (1 - a - b) ^ 2 * indexGap j z ≤ Benchmark.twoHeadCurve ε := by
  obtain ⟨u, hu, hprofile, hcost⟩ := exists_half_parameter_profile hp hdiff
  have hm0 : 0 ≤ 1 - a - b := by linarith [hp.1.2.1, hp.1.2.2]
  have hsq : (1 - a - b) ^ 2 ≤ u ^ 2 := by nlinarith [hu.1]
  have hgap := mul_le_mul_of_nonneg_left (indexGap_le_one_twenty_fourth hj z)
    (sq_nonneg (1 - a - b))
  have hcurve := quadraticCost_le_twoHeadCurve hprofile
  rw [hcost] at hcurve
  nlinarith

/-- The physical t=0 cell before the index is optimized. -/
def physicalCell (j : ℕ) (a b : ℝ) : ℝ :=
  a * b + (2 * (j : ℝ) * (a - b) * (1 - a - b) - (1 - a - b) ^ 2) /
    ((j : ℝ) * ((j : ℝ) + 1))

theorem physicalCell_two (a b : ℝ) : physicalCell 2 a b = quadraticCost a b := by
  unfold physicalCell quadraticCost
  norm_num

theorem physicalCell_gap {j : ℕ} (hj : 0 < j) {a b : ℝ} (hm : 1 - a - b ≠ 0) :
    physicalCell j a b = (a ^ 2 + b ^ 2) / 2 +
      (1 - a - b) ^ 2 * indexGap j ((a - b) / (1 - a - b)) := by
  have hj0 : (j : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hj)
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  unfold physicalCell indexGap
  field_simp
  ring

/-- The literal anchor normalization converts the exact count-cell value
to the physical quadratic expression. -/
theorem cellValue_zero_normalization (j : ℕ) {x S : ℝ} (hD : 1 + x + S ≠ 0) :
    TwoHeadCountLaw.cellValue j 0 x S / (1 + x + S) ^ 2 =
      physicalCell j (1 / (1 + x + S)) (x / (1 + x + S)) := by
  unfold TwoHeadCountLaw.cellValue physicalCell
  norm_num only [Nat.cast_zero, zero_add, zero_mul, zero_div, sub_zero, one_mul]
  by_cases hj : j = 0
  · subst j
    simp
    field_simp
  · have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj
    have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Every admissible t=0 cell with a normalized anchor at most one half
is bounded by the actual two-head curve. The lower count-cell restriction
is needed only for the higher-index domination. -/
theorem cellValue_zero_le_twoHeadCurve {j : ℕ} {x S : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) (hS : 0 < S) (hS1 : S ≤ 1)
    (hanchor : 1 / (1 + x + S) ≤ 1 / 2) (hj : 2 ≤ j)
    (hjlo : ((j : ℝ) - 1) * (1 - x) ≤ S) :
    TwoHeadCountLaw.cellValue j 0 x S / (1 + x + S) ^ 2 ≤
      Benchmark.twoHeadCurve ((1 + x ^ 2) / (2 * (1 + x + S) ^ 2)) := by
  have hD : 0 < 1 + x + S := by positivity
  let a := 1 / (1 + x + S)
  let b := x / (1 + x + S)
  let ε := (1 + x ^ 2) / (2 * (1 + x + S) ^ 2)
  have ha : 0 < a := one_div_pos.mpr hD
  have hb : 0 ≤ b := div_nonneg hx hD.le
  have hba : b ≤ a := (div_le_div_iff_of_pos_right hD).mpr hx1.le
  have hm : 1 - a - b = S / (1 + x + S) := by
    dsimp [a, b]
    field_simp
    ring
  have hmass : 1 - a - b ≤ a := by
    rw [hm]
    exact (div_le_div_iff_of_pos_right hD).mpr hS1
  have hε : a ^ 2 + b ^ 2 = 2 * ε := by
    dsimp [a, b, ε]
    field_simp
  have hp : (a, b) ∈ profileFiber ε :=
    ⟨⟨⟨ha.le, hb⟩, ⟨hanchor, hba.trans hanchor⟩⟩, hba, hmass, hε⟩
  rw [cellValue_zero_normalization j hD.ne']
  change physicalCell j a b ≤ Benchmark.twoHeadCurve ε
  by_cases hj2 : j = 2
  · rw [hj2, physicalCell_two]
    exact quadraticCost_le_twoHeadCurve hp
  · have hj3 : 3 ≤ j := by omega
    have hj3r : (3 : ℝ) ≤ j := by exact_mod_cast hj3
    have htwo : 2 * (1 - x) ≤ S := by
      nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) - 3 by linarith)
        (show 0 ≤ 1 - x by linarith)]
    have hdiff : a - b ≤ (1 - a - b) / 2 := by
      rw [hm]
      dsimp [a, b]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ hD).mpr
      field_simp
      nlinarith
    rw [physicalCell_gap (by omega : 0 < j) (by
      rw [hm]
      positivity), hε]
    have h := higher_index_cost_le_twoHeadCurve hp hj3 hdiff ((a - b) / (1 - a - b))
    nlinarith

/-- The actual selected index supplies every t=0 parameter guard; no
optimized-family value premise is assumed. -/
theorem selected_cell_zero_le_twoHeadCurve {x S : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) (hS : 0 < S) (hS1 : S < 1)
    (hanchor : 1 / (1 + x + S) < 1 / 2) :
    TwoHeadCountLaw.cellValue (TwoHeadCountLaw.selectedIndex x S) 0 x S / (1 + x + S) ^ 2 ≤
      Benchmark.twoHeadCurve ((1 + x ^ 2) / (2 * (1 + x + S) ^ 2)) := by
  have hfloor : ⌊S⌋₊ = 0 := Nat.floor_eq_zero.mpr hS1
  have hspec := TwoHeadCountLaw.selectedIndex_spec hx hx1 hS
  rw [hfloor] at hspec
  have hD : 0 < 1 + x + S := by positivity
  have hsmall : 1 - x < S := by
    have h := (div_lt_iff₀ hD).mp hanchor
    linarith
  have hcond : TwoHeadCountLaw.conditionalMoment x S 0 = S ^ 2 / (1 - x) := by
    simp [TwoHeadCountLaw.conditionalMoment, TwoHeadCountLaw.floorMoment]
  rw [hcond] at hspec
  have hupper := (div_le_iff₀ (show 0 < 1 - x by linarith)).mp hspec.2.2.2
  have hj : 2 ≤ TwoHeadCountLaw.selectedIndex x S := by
    by_contra h
    have hj1 : TwoHeadCountLaw.selectedIndex x S = 1 := by omega
    rw [hj1] at hupper
    norm_num at hupper
    nlinarith
  have hlower := (lt_div_iff₀ (show 0 < 1 - x by linarith)).mp hspec.2.2.1
  have hjlo : ((TwoHeadCountLaw.selectedIndex x S : ℝ) - 1) * (1 - x) ≤ S := by
    nlinarith
  exact cellValue_zero_le_twoHeadCurve hx hx1 hS hS1.le hanchor.le hj hjlo

/-- The exact all-count fixed-profile value inherits the optimized t=0
upper bound through the proved selected finite count law. -/
theorem actual_value_zero_le_twoHeadCurve {x S : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) (hS : 0 < S) (hS1 : S < 1)
    (hanchor : 1 / (1 + x + S) < 1 / 2) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      Benchmark.twoHeadCurve ((1 + x ^ 2) / (2 * (1 + x + S) ^ 2)) := by
  rw [TwoHeadCountLaw.value_eq_selected hx hx1 hS, Nat.floor_eq_zero.mpr hS1]
  exact selected_cell_zero_le_twoHeadCurve hx hx1 hS hS1 hanchor

/-- The actual benchmark includes the optimized two-head curve at the
physical density of every interior t=0 profile covered above. -/
theorem actual_value_zero_le_benchmark {x S : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) (hS : 0 < S) (hS1 : S < 1)
    (hanchor : 1 / (1 + x + S) < 1 / 2) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      benchmark (1 / 2 - (1 + x ^ 2) / (2 * (1 + x + S) ^ 2)) := by
  have hD : 0 < 1 + x + S := by positivity
  have hD2 : 2 < 1 + x + S := by
    have h := (div_lt_iff₀ hD).mp hanchor
    linarith
  have hε0 : 0 < (1 + x ^ 2) / (2 * (1 + x + S) ^ 2) := by positivity
  have hε1 : (1 + x ^ 2) / (2 * (1 + x + S) ^ 2) < 1 / 4 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (1 + x + S) ^ 2)).mpr
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - x by linarith)]
  have hquarter : ¬1 / 2 - (1 + x ^ 2) / (2 * (1 + x + S) ^ 2) ≤ 1 / 4 := by linarith
  have hhalf : 1 / 2 - (1 + x ^ 2) / (2 * (1 + x + S) ^ 2) < 1 / 2 := by linarith
  rw [benchmark, ite_eq_right hquarter, ite_eq_left hhalf]
  have hid : 1 / 2 - (1 / 2 - (1 + x ^ 2) / (2 * (1 + x + S) ^ 2)) =
      (1 + x ^ 2) / (2 * (1 + x + S) ^ 2) := by ring
  rw [hid]
  exact (actual_value_zero_le_twoHeadCurve hx hx1 hS hS1 hanchor).trans (le_max_right _ _)

end Erdos1017.TwoHeadInteriorComparison

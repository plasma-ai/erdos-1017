module

public import Erdos1017.Multipartite.MultipartiteExcessVariation

/-!
# At most two heads at an excess maximum

At a positive interior excess maximum every optimal dual has its derived head
multiplier strictly above one half, the normalized anchor is at most the
square-root density bound, and the maximizer has at most two positive secondary
heads.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- At an actual positive interior excess maximum, every optimal dual has
its own derived head multiplier strictly above one half. -/
theorem exists_high_multiplier_at_excess_maximum {L ε : ℝ} (hε : 0 < ε)
    {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityWindow L (3 / 8) (21 / 50))
    (hxε : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hRL : 1 / Real.sqrt ε - 1 ≤ L)
    (hd : MultipartiteProfiles.density x ∈ Set.Ioo (3 / 8 : ℝ) (21 / 50))
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow L (3 / 8) (21 / 50),
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    (hvalue : benchmark (MultipartiteProfiles.density x) < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) :
    ∃ ℓ : ℝ, 1 / 2 < ℓ ∧
      (∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
        anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1)) ∧
      ∀ j k, j ≠ k → 0 < x.2 j → 0 < x.2 k →
        -MultipartiteCountableMeasure.kernel D (.inl (some j)) (.inl (some k)) ≤ ℓ := by
  obtain ⟨B, hB, hBhalf, _, hBvalue, _⟩ := Benchmark.benchmark_head_count_guards hd
  have hεvalue : ε < MultipartiteProfiles.normalizedValue x := by
    rw [MultipartiteProfiles.density_eq_of_mem_densityFiber hxε] at hBvalue hvalue
    linarith
  have hmaxDensity := MultipartiteProfiles.density_maximum_of_excess_maximum hx hxε hRL hmax
  obtain ⟨ℓ, hrows, hpair, _⟩ := exists_unique_head_multiplier hε hxε hmaxDensity hεvalue hD hopt i hi
  have hT : x.1 < L := (MultipartiteProfiles.total_lt_cutoff_of_above_missing hxε hε hεvalue).trans_le hRL
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hxε hε hεvalue).1
  have hBℓ := benchmark_slope_le_multiplier hx.1 hT hQ hd hmax hD hopt i ℓ B (hrows i hi) hB
  exact ⟨ℓ, hBhalf.trans_le hBℓ, hrows, hpair⟩

/-- The source head cutoff decreases with the multiplier and with the
actual value. This comparison uses strictly positive actual denominators. -/
theorem atom_cutoff_lt_benchmark_cutoff {a r c b ε ℓ B : ℝ}
    (har : a ≤ r) (hr : 0 < r) (hε : 0 < ε)
    (hb : ε < b) (hbc : b < c) (hB : B < 1) (hBℓ : B ≤ ℓ) (hℓ : ℓ < 1) :
    a * (1 - ℓ) / (2 * (c - ℓ * ε)) < r * (1 - B) / (2 * (b - B * ε)) := by
  have hden : 0 < c - ℓ * ε := by nlinarith
  have hdenB : 0 < b - B * ε := by nlinarith
  have hratio : (1 - ℓ) * (b - B * ε) < (1 - B) * (c - ℓ * ε) := by
    have hpositive := add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hB) (sub_pos.mpr hbc))
      (mul_nonneg (sub_nonneg.mpr hBℓ) (sub_nonneg.mpr hb.le))
    nlinarith
  apply (div_lt_div_iff₀ (by positivity : 0 < 2 * (c - ℓ * ε))
    (by positivity : 0 < 2 * (b - B * ε))).mpr
  have hnum := mul_le_mul_of_nonneg_right har (by positivity : 0 ≤ 1 - ℓ)
  have hleft := mul_le_mul_of_nonneg_right hnum hdenB.le
  have hright := mul_lt_mul_of_pos_left hratio hr
  nlinarith

/-- The normalized anchor is at most the square-root density bound; the
actual square-moment equation supplies this estimate. -/
theorem anchor_le_sqrt_missing {L ε : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber L ε) (hε : 0 < ε) :
    1 / (1 + x.1) ≤ Real.sqrt (2 * ε) := by
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1.1]
  have hQ : 0 ≤ ∑' k, (x.2 k) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hmoment : 1 + (∑' k, (x.2 k) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
  have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)
  have hsqrt0 := Real.sqrt_nonneg (2 * ε)
  have ha : 0 ≤ 1 / (1 + x.1) := by positivity
  have ha2 : (1 / (1 + x.1)) ^ 2 ≤ 2 * ε := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    nlinarith
  nlinarith

/-- The actual positive interior excess maximizer has at most two positive
secondary heads. Its multiplier hypothesis is derived for its own optimum. -/
theorem head_count_le_two_at_excess_maximum {L ε : ℝ} (hε : 0 < ε)
    {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityWindow L (3 / 8) (21 / 50))
    (hxε : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hRL : 1 / Real.sqrt ε - 1 ≤ L)
    (hd : MultipartiteProfiles.density x ∈ Set.Ioo (3 / 8 : ℝ) (21 / 50))
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow L (3 / 8) (21 / 50),
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    (hdust : ∀ y ∈ MultipartiteProfiles.densityWindow L (3 / 8) (21 / 50),
      MultipartiteProfiles.benchmarkExcess y = MultipartiteProfiles.benchmarkExcess x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hvalue : benchmark (MultipartiteProfiles.density x) < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) :
    0 < MultipartiteProfiles.dust x ∧ Finite {k // 0 < x.2 k} ∧ Nat.card {k // 0 < x.2 k} ≤ 2 := by
  obtain ⟨ℓ, hℓ, hrows, _⟩ := exists_high_multiplier_at_excess_maximum hε hx hxε hRL hd hmax hvalue hD hopt i hi
  obtain ⟨B, hB, _, hB1, hBvalue, hphi⟩ := Benchmark.benchmark_head_count_guards hd
  have heq : 1 / 2 - MultipartiteProfiles.density x = ε := by
    rw [MultipartiteProfiles.density_eq_of_mem_densityFiber hxε]
    ring
  have hroot : 1 - 2 * MultipartiteProfiles.density x = 2 * ε := by
    linarith
  rw [heq] at hBvalue
  rw [hroot, heq] at hphi
  have hεvalue : ε < MultipartiteProfiles.normalizedValue x := hBvalue.trans hvalue
  have hmaxDensity := MultipartiteProfiles.density_maximum_of_excess_maximum hx hxε hRL hmax
  have hdustMoment := MultipartiteProfiles.greatest_dust_moment_of_excess_maximum hx hRL hdust
  have hmaxMoment : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x := by
    intro y hy
    have hyε : y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε := by
      refine ⟨hy.1, ?_⟩
      change 1 + (∑' k, (y.2 k) ^ 2) = 2 * ε * (1 + y.1) ^ 2
      rw [hy.2.1, hy.2.2]
      exact hxε.2
    have h := hmaxDensity y hyε
    change MultipartiteProfiles.limitValue y / (1 + y.1) ^ 2 ≤
      MultipartiteProfiles.limitValue x / (1 + x.1) ^ 2 at h
    rw [hy.2.1] at h
    exact (div_le_div_iff_of_pos_right (by have := hxε.1.1.1.1; positivity)).mp h
  have hti := head_lt_one_at_greatest_dust hxε.1 hmaxMoment hdustMoment hD hopt i j hij hi hj
  have hℓ1 := (twoRepeat_bounds_of_half_lt_multiplier hε hxε hmaxDensity hεvalue hD hopt
    ℓ hℓ i hi hti (hrows i hi)).2.2
  have hT : x.1 < L := (MultipartiteProfiles.total_lt_cutoff_of_above_missing hxε hε hεvalue).trans_le hRL
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hxε hε hεvalue).1
  have hBℓ := benchmark_slope_le_multiplier hx.1 hT hQ hd hmax hD hopt i ℓ B (hrows i hi) hB
  have hcutoff := atom_cutoff_lt_benchmark_cutoff (anchor_le_sqrt_missing hxε hε)
    (Real.sqrt_pos.mpr (by positivity : 0 < 2 * ε)) hε hBvalue hvalue hB1 hBℓ hℓ1
  have hcutoff2 : (1 / (1 + x.1)) * (1 - ℓ) /
      (2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε)) < 2 := hcutoff.trans hphi
  obtain ⟨hs, hfinite, hcard⟩ := head_count_of_half_lt_multiplier hε hxε hmaxDensity hdustMoment
    hεvalue hD hopt ℓ hℓ hrows i j hij hi hj
  refine ⟨hs, hfinite, hcard.trans ?_⟩
  exact Nat.ceil_le.mpr (by exact hcutoff2.le)

end Erdos1017.MultipartiteCountableDual

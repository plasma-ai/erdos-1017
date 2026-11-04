module

public import Erdos1017.Multipartite.MultipartiteExcessHeadCount
public import Erdos1017.Benchmark.BenchmarkDenseHeadCountGuards
public import Erdos1017.Multipartite.TwoHead.TwoHeadProfileBridge

/-!
# Second head of the selected excess profile

A selected excess maximum on the combined window, whether in the middle interval
or on the dense bridge, cannot have two positive secondary heads
(`selected_excess_second_head_zero`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- The actual density maximum is also the actual fixed-moment maximum. -/
theorem moment_maximum_of_density_maximum {L ε : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber L ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber L ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x) :
    ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x := by
  intro y hy
  have hyε : y ∈ MultipartiteProfiles.densityFiber L ε := by
    refine ⟨hy.1, ?_⟩
    change 1 + (∑' k, (y.2 k) ^ 2) = 2 * ε * (1 + y.1) ^ 2
    rw [hy.2.1, hy.2.2]
    exact hx.2
  have h := hmax y hyε
  change MultipartiteProfiles.limitValue y / (1 + y.1) ^ 2 ≤
    MultipartiteProfiles.limitValue x / (1 + x.1) ^ 2 at h
  rw [hy.2.1] at h
  exact (div_le_div_iff_of_pos_right (by have := hx.1.1.1.1; positivity)).mp h

/-- Sorting turns the actual cardinal bound into literal two-head support. -/
theorem zero_after_two_of_card_le_two {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) [Finite {k // 0 < x.2 k}]
    (hcard : Nat.card {k // 0 < x.2 k} ≤ 2) : ∀ k, 2 ≤ k → x.2 k = 0 := by
  intro k hk
  by_contra hzero
  have hpos : 0 < x.2 k := lt_of_le_of_ne (hx.1.1.2 k) (Ne.symm hzero)
  let f : Fin 3 → {i // 0 < x.2 i} := fun i =>
    ⟨i.val, hpos.trans_le (hx.2.1 (by omega : i.val ≤ k))⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg Subtype.val hij)
  have hle := Nat.card_le_card_of_injective f hf
  have hthree : 3 ≤ Nat.card {k // 0 < x.2 k} := by simpa using hle
  omega

/-- In the middle interval the actual selected excess maximum cannot have
two positive secondary heads. The vertex contradiction applies to every
optimal dual's own multiplier. -/
theorem middle_selected_excess_impossible {L ε : ℝ} (hε : 0 < ε)
    {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityWindow L (3 / 8) (153 / 338))
    (hxε : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hRL : 1 / Real.sqrt ε - 1 ≤ L)
    (hd : MultipartiteProfiles.density x ∈ Set.Ioo (3 / 8 : ℝ) (21 / 50))
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow L (3 / 8) (153 / 338),
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    (hdust : ∀ y ∈ MultipartiteProfiles.densityWindow L (3 / 8) (153 / 338),
      MultipartiteProfiles.benchmarkExcess y = MultipartiteProfiles.benchmarkExcess x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hvalue : benchmark (MultipartiteProfiles.density x) < MultipartiteProfiles.normalizedValue x)
    (h₀ : 0 < x.2 0) (h₁ : 0 < x.2 1) : False := by
  have hsub : MultipartiteProfiles.densityWindow L (3 / 8) (21 / 50) ⊆
      MultipartiteProfiles.densityWindow L (3 / 8) (153 / 338) := by
    intro y hy
    exact ⟨hy.1, hy.2.1, by linarith [hy.2.2]⟩
  have hxmid : x ∈ MultipartiteProfiles.densityWindow L (3 / 8) (21 / 50) :=
    ⟨hx.1, hd.1.le, hd.2.le⟩
  have hmaxmid := fun y hy => hmax y (hsub hy)
  have hdustmid := fun y hy => hdust y (hsub hy)
  obtain ⟨D, hD, hopt⟩ := exists_profile_optimal hxε.1
  obtain ⟨hs, hfinite, hcard⟩ := head_count_le_two_at_excess_maximum hε hxmid hxε hRL hd
    hmaxmid hdustmid hvalue hD hopt.symm 0 1 (by omega) h₀ h₁
  let _ := hfinite
  have hzero := zero_after_two_of_card_le_two hx.1 hcard
  have hmaxDensity := MultipartiteProfiles.density_maximum_of_excess_maximum hx hxε hRL hmax
  have hdustMoment := MultipartiteProfiles.greatest_dust_moment_of_excess_maximum hx hRL hdust
  obtain ⟨B, hB, hBhalf, _, hbaseline, _⟩ := Benchmark.benchmark_head_count_guards hd
  have heq : 1 / 2 - MultipartiteProfiles.density x = ε := by
    rw [MultipartiteProfiles.density_eq_of_mem_densityFiber hxε]
    ring
  rw [heq] at hbaseline
  have hεvalue := hbaseline.trans hvalue
  apply TwoHeadProfileBridge.two_positive_heads_positive_dust_impossible hε hxε
    hmaxDensity hdustMoment hεvalue h₀ h₁ hzero hs
  intro E hE hEopt ℓ hrows
  have hT : x.1 < L := (MultipartiteProfiles.total_lt_cutoff_of_above_missing hxε hε hεvalue).trans_le hRL
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hxε hε hεvalue).1
  have hBℓ := benchmark_slope_le_multiplier hx.1 hT hQ
    (show MultipartiteProfiles.density x ∈ Set.Ioo (3 / 8 : ℝ) (153 / 338) from
      ⟨hd.1, by linarith [hd.2]⟩) hmax hE hEopt 0 ℓ B (hrows 0 h₀) hB
  exact hBhalf.trans_le hBℓ

/-- On the dense bridge, the actual slope bound makes the countable head
cutoff strictly below one, excluding two positive secondary heads. -/
theorem dense_selected_excess_impossible {L ε : ℝ} (hε : 0 < ε)
    {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityWindow L (3 / 8) (153 / 338))
    (hxε : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hRL : 1 / Real.sqrt ε - 1 ≤ L)
    (hd : MultipartiteProfiles.density x ∈ Set.Ico (21 / 50 : ℝ) (153 / 338))
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow L (3 / 8) (153 / 338),
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    (hdust : ∀ y ∈ MultipartiteProfiles.densityWindow L (3 / 8) (153 / 338),
      MultipartiteProfiles.benchmarkExcess y = MultipartiteProfiles.benchmarkExcess x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hvalue : benchmark (MultipartiteProfiles.density x) < MultipartiteProfiles.normalizedValue x)
    (h₀ : 0 < x.2 0) (h₁ : 0 < x.2 1) : False := by
  obtain ⟨B, hB, hBhalf, hbaseline, hphi⟩ :=
    Benchmark.benchmark_dense_head_count_own_multiplier_guards ⟨hd.1, hd.2.le⟩
  have heq : 1 / 2 - MultipartiteProfiles.density x = ε := by
    rw [MultipartiteProfiles.density_eq_of_mem_densityFiber hxε]
    ring
  have hroot : 1 - 2 * MultipartiteProfiles.density x = 2 * ε := by linarith
  rw [heq] at hbaseline
  have hεvalue := hbaseline.trans hvalue
  have hmaxDensity := MultipartiteProfiles.density_maximum_of_excess_maximum hx hxε hRL hmax
  have hdustMoment := MultipartiteProfiles.greatest_dust_moment_of_excess_maximum hx hRL hdust
  have hmaxMoment := moment_maximum_of_density_maximum hxε hmaxDensity
  obtain ⟨D, hD, hopt⟩ := exists_profile_optimal hxε.1
  obtain ⟨ℓ, hrows, _, _⟩ := exists_unique_head_multiplier hε hxε hmaxDensity hεvalue hD hopt.symm 0 h₀
  have hT : x.1 < L := (MultipartiteProfiles.total_lt_cutoff_of_above_missing hxε hε hεvalue).trans_le hRL
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hxε hε hεvalue).1
  have hBℓ := benchmark_slope_le_multiplier hx.1 hT hQ
    (show MultipartiteProfiles.density x ∈ Set.Ioo (3 / 8 : ℝ) (153 / 338) from
      ⟨by linarith [hd.1], hd.2⟩) hmax hD hopt.symm 0 ℓ B (hrows 0 h₀) hB
  have hℓ : 1 / 2 < ℓ := by linarith
  have hti := head_lt_one_at_greatest_dust hxε.1 hmaxMoment hdustMoment hD hopt.symm 0 1 (by omega) h₀ h₁
  have hℓ1 := (twoRepeat_bounds_of_half_lt_multiplier hε hxε hmaxDensity hεvalue hD hopt.symm
    ℓ hℓ 0 h₀ hti (hrows 0 h₀)).2.2
  have hphiℓ := hphi ℓ hBℓ hℓ1
  rw [hroot, heq] at hphiℓ
  have hcutoff := atom_cutoff_lt_benchmark_cutoff (anchor_le_sqrt_missing hxε hε)
    (Real.sqrt_pos.mpr (by positivity : 0 < 2 * ε)) hε hbaseline hvalue hℓ1 le_rfl hℓ1
  have hcutoff1 : (1 / (1 + x.1)) * (1 - ℓ) /
      (2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε)) < 1 := hcutoff.trans_le hphiℓ
  obtain ⟨_, hfinite, hcard⟩ := head_count_of_half_lt_multiplier hε hxε hmaxDensity hdustMoment
    hεvalue hD hopt.symm ℓ hℓ hrows 0 1 (by omega) h₀ h₁
  let _ := hfinite
  have hcard1 : Nat.card {k // 0 < x.2 k} ≤ 1 := hcard.trans (Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using hcutoff1.le))
  let f : Fin 2 → {k // 0 < x.2 k} := fun k =>
    ⟨k.val, h₁.trans_le (hx.1.2.1 (by omega : k.val ≤ 1))⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg Subtype.val hij)
  have hle := Nat.card_le_card_of_injective f hf
  have htwo : 2 ≤ Nat.card {k // 0 < x.2 k} := by simpa using hle
  omega

/-- The actual selected excess profile on the combined window cannot have
a second positive secondary head, including the dense-branch junction. -/
theorem selected_excess_second_head_zero {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityWindow (1 / Real.sqrt (8 / 169 : ℝ) - 1)
      (3 / 8) (153 / 338))
    (hd : MultipartiteProfiles.density x ∈ Set.Ioo (3 / 8 : ℝ) (153 / 338))
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow (1 / Real.sqrt (8 / 169 : ℝ) - 1)
        (3 / 8) (153 / 338),
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    (hdust : ∀ y ∈ MultipartiteProfiles.densityWindow (1 / Real.sqrt (8 / 169 : ℝ) - 1)
        (3 / 8) (153 / 338),
      MultipartiteProfiles.benchmarkExcess y = MultipartiteProfiles.benchmarkExcess x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hvalue : benchmark (MultipartiteProfiles.density x) < MultipartiteProfiles.normalizedValue x) :
    x.2 1 = 0 := by
  have hbase : 1 / 2 - MultipartiteProfiles.density x < benchmark (MultipartiteProfiles.density x) := by
    by_cases hmid : MultipartiteProfiles.density x < 21 / 50
    · obtain ⟨_, _, _, _, hb, _⟩ := Benchmark.benchmark_head_count_guards ⟨hd.1, hmid⟩
      exact hb
    · obtain ⟨_, _, _, hb, _⟩ := Benchmark.benchmark_dense_head_count_guards
        ⟨le_of_not_gt hmid, hd.2.le⟩
      exact hb
  let ε := MultipartiteProfiles.missingDensity x
  have heq : 1 / 2 - MultipartiteProfiles.density x = ε := by
    dsimp [ε, MultipartiteProfiles.density]
    ring
  have hεlower : (8 / 169 : ℝ) < ε := by linarith [hd.2]
  have hε : 0 < ε := by linarith
  have hεvalue : ε < MultipartiteProfiles.normalizedValue x := by rw [heq] at hbase; exact hbase.trans hvalue
  have hxε := (MultipartiteProfiles.mem_canonical_densityFiber_of_above_missing
    (MultipartiteProfiles.mem_densityFiber_missingDensity hx.1) hε hεvalue).1
  have hRL := MultipartiteProfiles.canonical_cutoff_antitone (by norm_num : (0 : ℝ) < 8 / 169) hεlower.le
  by_contra hzero
  have h₁ : 0 < x.2 1 := lt_of_le_of_ne (hx.1.1.1.2 1) (Ne.symm hzero)
  have h₀ : 0 < x.2 0 := h₁.trans_le (hx.1.2.1 (by omega : 0 ≤ 1))
  by_cases hmid : MultipartiteProfiles.density x < 21 / 50
  · exact middle_selected_excess_impossible hε hx hxε hRL ⟨hd.1, hmid⟩ hmax hdust hvalue h₀ h₁
  · exact dense_selected_excess_impossible hε hx hxε hRL ⟨le_of_not_gt hmid, hd.2⟩
      hmax hdust hvalue h₀ h₁

end Erdos1017.MultipartiteCountableDual

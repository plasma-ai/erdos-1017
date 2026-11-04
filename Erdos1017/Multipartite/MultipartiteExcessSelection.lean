module

public import Erdos1017.Multipartite.MultipartiteHeadCount
public import Erdos1017.Benchmark.BenchmarkHeadCountGuards

/-!
# Selecting an interior excess maximum

The missing density, density and benchmark excess of a normalized profile are
defined; one common compact cutoff contains every above-baseline profile in a
closed missing-density interval, and any positive counterexample to the
benchmark bound selects an interior positive excess maximum with greatest dust.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators

/-- The physical missing density after total-mass normalization. -/
def missingDensity (x : Profile) : ℝ :=
  (1 + (∑' i, (x.2 i) ^ 2)) / (2 * (1 + x.1) ^ 2)

/-- The actual density of the normalized complete multipartite profile. -/
def density (x : Profile) : ℝ := 1 / 2 - missingDensity x

/-- The actual normalized value above the explicit benchmark. -/
def benchmarkExcess (x : Profile) : ℝ := normalizedValue x - benchmark (density x)

/-- A compact common cutoff with density in a fixed closed interval. -/
def densityWindow (L lo hi : ℝ) : Set Profile := space L ∩ {x | density x ∈ Set.Icc lo hi}

theorem space_mono {L R : ℝ} (hLR : L ≤ R) : space L ⊆ space R := by
  intro x hx
  exact ⟨⟨hx.1.1, ⟨hx.1.2.1.trans hLR, hx.1.2.2⟩⟩, hx.2⟩

theorem missingDensity_continuousOn (L : ℝ) : ContinuousOn missingDensity (space L) := by
  apply (continuousOn_const.add (squareMoment_continuousOn L)).div (by fun_prop)
  intro x hx
  have hx0 : 0 ≤ x.1 := hx.1.1.1
  positivity

theorem density_continuousOn (L : ℝ) : ContinuousOn density (space L) :=
  continuousOn_const.sub (missingDensity_continuousOn L)

/-- The normalized profile is an actual graph-density point. -/
theorem density_mem_Icc {L : ℝ} {x : Profile} (hx : x ∈ space L) : density x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hp : ∀ i, 0 ≤ x.2 i := hx.1.1.2
  have hsum := atoms_summable hx
  have hsqsum := squares_summable hx
  have hQsum : (∑' i, (x.2 i) ^ 2) ≤ ∑' i, x.2 i :=
    hsqsum.tsum_le_tsum (fun i => by
      simpa only [pow_two] using mul_le_of_le_one_right (hp i) (hx.1.2.2 i)) hsum
  have hsumT : (∑' i, x.2 i) ≤ x.1 := by
    have hs := dust_nonneg hx
    rw [dust_eq_sub_tsum hx] at hs
    linarith
  have hT : 0 ≤ x.1 := hx.1.1.1
  have hden : 0 < 2 * (1 + x.1) ^ 2 := by positivity
  have hmissing0 : 0 ≤ missingDensity x := by
    unfold missingDensity
    exact div_nonneg (by positivity) hden.le
  have hmissingHalf : missingDensity x ≤ 1 / 2 := by
    unfold missingDensity
    apply (div_le_iff₀ hden).mpr
    nlinarith [hQsum.trans hsumT, sq_nonneg x.1]
  constructor <;> unfold density <;> linarith

theorem benchmarkExcess_continuousOn (L : ℝ) : ContinuousOn benchmarkExcess (space L) := by
  exact (normalizedValue_continuousOn L).sub
    (benchmark_continuousOn.comp (density_continuousOn L) (fun _ hx => density_mem_Icc hx))

/-- Fixed normalized density is exactly the previously defined moment
constraint; no frontier function or continuity premise is introduced. -/
theorem density_eq_of_mem_densityFiber {L ε : ℝ} {x : Profile} (hx : x ∈ densityFiber L ε) :
    density x = 1 / 2 - ε := by
  have hden : 0 < 2 * (1 + x.1) ^ 2 := by
    have hT : 0 ≤ x.1 := hx.1.1.1.1
    positivity
  have hmoment : 1 + (∑' i, (x.2 i) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
  have hmissing : missingDensity x = ε := by
    unfold missingDensity
    apply (div_eq_iff hden.ne').mpr
    nlinarith [hmoment]
  unfold density
  rw [hmissing]

theorem mem_densityFiber_missingDensity {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    x ∈ densityFiber L (missingDensity x) := by
  refine ⟨hx, ?_⟩
  change 1 + (∑' i, (x.2 i) ^ 2) = 2 * missingDensity x * (1 + x.1) ^ 2
  have hden : 1 + x.1 ≠ 0 := by
    have hT : 0 ≤ x.1 := hx.1.1.1
    linarith
  unfold missingDensity
  field_simp

theorem densityWindow_isCompact (L lo hi : ℝ) : IsCompact (densityWindow L lo hi) := by
  have hclosed := (density_continuousOn L).preimage_isClosed_of_isClosed
    (space_isCompact L).isClosed (isClosed_Icc : IsClosed (Set.Icc lo hi))
  exact (space_isCompact L).of_isClosed_subset hclosed Set.inter_subset_left

/-- The actual benchmark excess attains its maximum on a common compact
profile cutoff. No supremum frontier is assumed to be continuous. -/
theorem exists_excess_maximum (L lo hi : ℝ) (hne : (densityWindow L lo hi).Nonempty) :
    ∃ x ∈ densityWindow L lo hi, ∀ y ∈ densityWindow L lo hi, benchmarkExcess y ≤ benchmarkExcess x := by
  exact (densityWindow_isCompact L lo hi).exists_isMaxOn hne
    ((benchmarkExcess_continuousOn L).mono Set.inter_subset_left)

/-- Greatest dust can be chosen among actual benchmark-excess maximizers
on the compact common-cutoff window. -/
theorem exists_greatest_dust_excess_maximum (L lo hi : ℝ)
    (hne : (densityWindow L lo hi).Nonempty) :
    ∃ x ∈ densityWindow L lo hi,
      (∀ y ∈ densityWindow L lo hi, benchmarkExcess y ≤ benchmarkExcess x) ∧
      ∀ y ∈ densityWindow L lo hi, benchmarkExcess y = benchmarkExcess x → dust y ≤ dust x := by
  obtain ⟨z, hz, hmax⟩ := exists_excess_maximum L lo hi hne
  let K := densityWindow L lo hi ∩ {x | benchmarkExcess x = benchmarkExcess z}
  have hK : IsCompact K := by
    apply (densityWindow_isCompact L lo hi).of_isClosed_subset
    · exact ((benchmarkExcess_continuousOn L).mono Set.inter_subset_left).preimage_isClosed_of_isClosed
        (densityWindow_isCompact L lo hi).isClosed (isClosed_singleton (x := benchmarkExcess z))
    · exact Set.inter_subset_left
  obtain ⟨x, hx, hdust⟩ := exists_greatest_dust hK ⟨z, hz, rfl⟩ (fun _ hy => hy.1.1)
  refine ⟨x, hx.1, ?_, ?_⟩
  · intro y hy
    rw [hx.2]
    exact hmax y hy
  · intro y hy heq
    exact hdust y ⟨hy, heq.trans hx.2⟩

/-- An actual excess maximum also maximizes the actual value on every
same-density fiber contained in the common cutoff. -/
theorem density_maximum_of_excess_maximum {L R lo hi ε : ℝ} {x : Profile}
    (hx : x ∈ densityWindow L lo hi) (hxε : x ∈ densityFiber R ε) (hRL : R ≤ L)
    (hmax : ∀ y ∈ densityWindow L lo hi, benchmarkExcess y ≤ benchmarkExcess x) :
    ∀ y ∈ densityFiber R ε, normalizedValue y ≤ normalizedValue x := by
  intro y hy
  have hyd : density y = density x :=
    (density_eq_of_mem_densityFiber hy).trans (density_eq_of_mem_densityFiber hxε).symm
  have h := hmax y ⟨space_mono hRL hy.1, by change density y ∈ Set.Icc lo hi; rw [hyd]; exact hx.2⟩
  unfold benchmarkExcess at h
  rw [hyd] at h
  linarith

/-- Greatest dust among excess maximizers gives the greatest-dust choice
needed on the actual fixed-moment optimum fiber. -/
theorem greatest_dust_moment_of_excess_maximum {L R lo hi : ℝ} {x : Profile}
    (hx : x ∈ densityWindow L lo hi) (hRL : R ≤ L)
    (hdust : ∀ y ∈ densityWindow L lo hi, benchmarkExcess y = benchmarkExcess x → dust y ≤ dust x) :
    ∀ y ∈ momentFiber R x.1 (∑' k, (x.2 k) ^ 2),
      limitValue y = limitValue x → dust y ≤ dust x := by
  intro y hy hvalue
  have hyd : density y = density x := by
    unfold density missingDensity
    rw [hy.2.1, hy.2.2]
  apply hdust y ⟨space_mono hRL hy.1, by change density y ∈ Set.Icc lo hi; rw [hyd]; exact hx.2⟩
  unfold benchmarkExcess normalizedValue
  rw [hyd, hy.2.1, hvalue]

/-- Strict excess over the missing-density baseline leaves room below the
canonical total-mass cutoff. -/
theorem total_lt_cutoff_of_above_missing {L ε : ℝ} {x : Profile}
    (hx : x ∈ densityFiber L ε) (hε : 0 < ε) (hvalue : ε < normalizedValue x) :
    x.1 < 1 / Real.sqrt ε - 1 := by
  have h := (above_missing_density_bounds hx hε hvalue).2
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1.1]
  have hsqrt := Real.sqrt_pos.mpr hε
  have hprod := (lt_div_iff₀ hM).mp h
  apply (lt_sub_iff_add_lt).mpr
  apply (lt_div_iff₀ hsqrt).mpr
  nlinarith

/-- A profile above its missing-density baseline already belongs to the
canonical cutoff, with strict room for mass variations. -/
theorem mem_canonical_densityFiber_of_above_missing {L ε : ℝ} {x : Profile}
    (hx : x ∈ densityFiber L ε) (hε : 0 < ε) (hvalue : ε < normalizedValue x) :
    x ∈ densityFiber (1 / Real.sqrt ε - 1) ε ∧ x.1 < 1 / Real.sqrt ε - 1 := by
  have hT := total_lt_cutoff_of_above_missing hx hε hvalue
  refine ⟨⟨?_, hx.2⟩, hT⟩
  exact ⟨⟨hx.1.1.1, ⟨hT.le, hx.1.1.2.2⟩⟩, hx.1.2⟩

/-- One common compact cutoff contains every above-baseline profile in a
closed missing-density interval bounded away from zero. -/
theorem canonical_cutoff_antitone {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) :
    1 / Real.sqrt ε - 1 ≤ 1 / Real.sqrt δ - 1 := by
  have h := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hδ) (Real.sqrt_le_sqrt hδε)
  linarith

/-- Once the two endpoint comparisons are proved, any actual positive
counterexample selects an interior positive excess maximum with greatest
dust. Only continuity of the actual profile value is used. -/
theorem exists_interior_positive_excess_maximum {L lo hi : ℝ}
    {z : Profile} (hz : z ∈ densityWindow L lo hi) (hzvalue : 0 < benchmarkExcess z)
    (hlo : ∀ y ∈ densityWindow L lo hi, density y = lo → benchmarkExcess y ≤ 0)
    (hhi : ∀ y ∈ densityWindow L lo hi, density y = hi → benchmarkExcess y ≤ 0) :
    ∃ x ∈ densityWindow L lo hi, density x ∈ Set.Ioo lo hi ∧ 0 < benchmarkExcess x ∧
      (∀ y ∈ densityWindow L lo hi, benchmarkExcess y ≤ benchmarkExcess x) ∧
      ∀ y ∈ densityWindow L lo hi, benchmarkExcess y = benchmarkExcess x → dust y ≤ dust x := by
  obtain ⟨x, hx, hmax, hdust⟩ := exists_greatest_dust_excess_maximum L lo hi ⟨z, hz⟩
  have hpositive := hzvalue.trans_le (hmax z hz)
  have hlow : lo < density x := by
    apply lt_of_le_of_ne hx.2.1
    intro heq
    exact (not_lt_of_ge (hlo x hx heq.symm)) hpositive
  have hhigh : density x < hi := by
    apply lt_of_le_of_ne hx.2.2
    intro heq
    exact (not_lt_of_ge (hhi x hx heq)) hpositive
  exact ⟨x, hx, ⟨hlow, hhigh⟩, hpositive, hmax, hdust⟩

/-- A genuine middle-interval benchmark counterexample supplies all the
canonical density-selection data required by the mass variations. -/
theorem middle_excess_density_data {x : Profile}
    (hx : x ∈ space (1 / Real.sqrt (2 / 25 : ℝ) - 1))
    (hd : density x ∈ Set.Ioo (3 / 8 : ℝ) (21 / 50))
    (hvalue : benchmark (density x) < normalizedValue x) :
    0 < missingDensity x ∧
      x ∈ densityFiber (1 / Real.sqrt (missingDensity x) - 1) (missingDensity x) ∧
      1 / Real.sqrt (missingDensity x) - 1 ≤ 1 / Real.sqrt (2 / 25 : ℝ) - 1 ∧
      missingDensity x < normalizedValue x := by
  obtain ⟨_, _, _, _, hbaseline, _⟩ := Benchmark.benchmark_head_count_guards hd
  have heq : 1 / 2 - density x = missingDensity x := by unfold density; ring
  rw [heq] at hbaseline
  have hεlower : (2 / 25 : ℝ) < missingDensity x := by
    unfold density at hd
    linarith [hd.2]
  have hε : 0 < missingDensity x := by linarith
  have hεvalue := hbaseline.trans hvalue
  exact ⟨hε, (mem_canonical_densityFiber_of_above_missing (mem_densityFiber_missingDensity hx)
    hε hεvalue).1, canonical_cutoff_antitone (by norm_num) hεlower.le, hεvalue⟩

end Erdos1017.MultipartiteProfiles

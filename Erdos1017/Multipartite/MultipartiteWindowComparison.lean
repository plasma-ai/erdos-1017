module

public import Erdos1017.Multipartite.MultipartiteSelectedExcess

/-!
# Benchmark comparison on the common window

On the common comparison window of the middle and dense bridge, `B` lies above
the missing-density baseline, any counterexample profile lies in the compact
cutoff, and the comparison reduces to the endpoints and the one-secondary-head
family.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators

/-- The common compact cutoff for the complete middle and dense bridge. -/
def comparisonCutoff : ℝ := 1 / Real.sqrt (8 / 169 : ℝ) - 1

/-- The actual benchmark lies above the missing-density baseline throughout
the interior common comparison window. -/
theorem benchmark_gt_missing_on_comparison_window {x : Profile}
    (hd : density x ∈ Set.Ioo (3 / 8 : ℝ) (153 / 338)) :
    missingDensity x < benchmark (density x) := by
  have heq : 1 / 2 - density x = missingDensity x := by unfold density; ring
  by_cases hmid : density x < 21 / 50
  · obtain ⟨_, _, _, _, hb, _⟩ := Benchmark.benchmark_head_count_guards ⟨hd.1, hmid⟩
    rwa [heq] at hb
  · obtain ⟨_, _, _, hb, _⟩ := Benchmark.benchmark_dense_head_count_guards
      ⟨le_of_not_gt hmid, hd.2.le⟩
    rwa [heq] at hb

/-- Any actual profile counterexample in the interior comparison window
already belongs to the common compact cutoff. -/
theorem mem_comparisonCutoff_of_counterexample {L : ℝ} {x : Profile}
    (hx : x ∈ space L) (hd : density x ∈ Set.Ioo (3 / 8 : ℝ) (153 / 338))
    (hvalue : benchmark (density x) < normalizedValue x) : x ∈ space comparisonCutoff := by
  have hεlower : (8 / 169 : ℝ) < missingDensity x := by
    unfold density at hd
    linarith [hd.2]
  have hε : 0 < missingDensity x := by linarith
  have hεvalue := (benchmark_gt_missing_on_comparison_window hd).trans hvalue
  have hcanonical := (mem_canonical_densityFiber_of_above_missing
    (mem_densityFiber_missingDensity hx) hε hεvalue).1
  exact space_mono (canonical_cutoff_antitone (by norm_num : (0 : ℝ) < 8 / 169) hεlower.le)
    hcanonical.1

/-- The completed actual structural argument reduces the common-window
benchmark comparison to its genuine endpoints and one-secondary-head
family comparison. These remaining comparisons are explicit hypotheses. -/
theorem normalizedValue_le_benchmark_on_comparison_window
    (hlow : ∀ L y, y ∈ space L → density y = 3 / 8 → normalizedValue y ≤ benchmark (density y))
    (hhigh : ∀ L y, y ∈ space L → density y = 153 / 338 → normalizedValue y ≤ benchmark (density y))
    (hfamily : ∀ y ∈ densityWindow comparisonCutoff (3 / 8) (153 / 338),
      y.2 1 = 0 → normalizedValue y ≤ benchmark (density y))
    {L : ℝ} {x : Profile} (hx : x ∈ space L)
    (hd : density x ∈ Set.Icc (3 / 8 : ℝ) (153 / 338)) :
    normalizedValue x ≤ benchmark (density x) := by
  by_contra hbound
  have hvalue : benchmark (density x) < normalizedValue x := lt_of_not_ge hbound
  by_cases hloweq : density x = 3 / 8
  · exact (not_lt_of_ge (hlow L x hx hloweq)) hvalue
  by_cases hhigheq : density x = 153 / 338
  · exact (not_lt_of_ge (hhigh L x hx hhigheq)) hvalue
  have hdi : density x ∈ Set.Ioo (3 / 8 : ℝ) (153 / 338) :=
    ⟨lt_of_le_of_ne hd.1 (Ne.symm hloweq), lt_of_le_of_ne hd.2 hhigheq⟩
  have hcanonical := mem_comparisonCutoff_of_counterexample hx hdi hvalue
  have hxwindow : x ∈ densityWindow comparisonCutoff (3 / 8) (153 / 338) := ⟨hcanonical, hd⟩
  have hxpositive : 0 < benchmarkExcess x := sub_pos.mpr hvalue
  obtain ⟨z, hz, hzd, hzpositive, hzmax, hzdust⟩ := exists_interior_positive_excess_maximum
    hxwindow hxpositive
    (fun y hy heq => sub_nonpos.mpr (hlow comparisonCutoff y hy.1 heq))
    (fun y hy heq => sub_nonpos.mpr (hhigh comparisonCutoff y hy.1 heq))
  have hzvalue : benchmark (density z) < normalizedValue z := sub_pos.mp hzpositive
  have hzero := MultipartiteCountableDual.selected_excess_second_head_zero hz hzd hzmax hzdust hzvalue
  exact (not_lt_of_ge (hfamily z hz hzero)) hzvalue

end Erdos1017.MultipartiteProfiles

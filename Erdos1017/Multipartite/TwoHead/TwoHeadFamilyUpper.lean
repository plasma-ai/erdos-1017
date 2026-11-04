module

public import Erdos1017.Multipartite.TwoHead.TwoHeadTailComparison
public import Erdos1017.Multipartite.TwoHead.TwoHeadInteriorComparison
public import Erdos1017.Multipartite.BenchmarkSplitComparison
public import Erdos1017.Multipartite.MultipartiteExcessSelection

/-!
# Benchmark upper bound for the two-head family

The one-secondary-head and dust family is bounded by the benchmark at its own
normalized density. The count law, positive-tail comparisons, interior
optimization and boundary cases are proved in the imported modules.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.TwoHeadFamilyUpper

/-- Every legal anchor-normalized two-independent-part profile obeys the
benchmark upper bound at its actual normalized density. -/
theorem normalized_value_le_benchmark {x S : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hS : 0 ≤ S)
    (hd : 1 / 2 - (1 + x ^ 2) / (2 * (1 + x + S) ^ 2) ∈
      Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      benchmark (1 / 2 - (1 + x ^ 2) / (2 * (1 + x + S) ^ 2)) := by
  let M := 1 + x + S
  let e := (1 + x ^ 2) / (2 * M ^ 2)
  let d := 1 / 2 - e
  have hM : 0 < M := by dsimp [M]; linarith [hx.1]
  change d ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) at hd
  change MultipartiteDust.value (fun _ : Fin 1 => x) S / M ^ 2 ≤ benchmark d
  have hmissing : e ≤ benchmark d := by
    have h := Benchmark.benchmark_ge_missing hd
    simpa only [d, sub_sub_cancel] using h
  by_cases hx1 : x = 1
  · have hvalue : MultipartiteDust.value (fun _ : Fin 1 => x) S = 1 := by
      rw [hx1, TwoHeadCountLaw.value_unit_head hS]
    have heq : MultipartiteDust.value (fun _ : Fin 1 => x) S / M ^ 2 = e := by
      rw [hvalue]
      dsimp only [e]
      rw [hx1]
      field_simp
      ring
    rw [heq]
    exact hmissing
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
  by_cases hshort : x + S ≤ 1
  · have h := TwoHeadFamilyBoundary.normalized_value_le_missing hx.1 hS hshort
    exact h.trans hmissing
  have htotal : 1 < x + S := lt_of_not_ge hshort
  by_cases htail : 1 ≤ S
  · have h := TwoHeadTailComparison.actual_value_le_split hx.1 hxlt htail
    have hsqrt : Real.sqrt (1 - 2 * d) = Real.sqrt (1 + x ^ 2) / M := by
      have he : 0 ≤ e := by dsimp [e]; positivity
      have hrad : 0 ≤ 1 - 2 * d := by dsimp [d]; linarith
      apply (Real.sqrt_eq_iff_eq_sq hrad (by positivity)).mpr
      rw [div_pow, Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)]
      dsimp [d, e]
      field_simp
      ring
    have hsplit := Benchmark.splitValue_le_benchmark hd
    rw [hsqrt] at hsplit
    exact h.trans hsplit
  · have hSpos : 0 < S := by linarith [hx.2]
    have hSlt : S < 1 := lt_of_not_ge htail
    have hanchor : 1 / (1 + x + S) < 1 / 2 := by
      apply (div_lt_iff₀ hM).mpr
      linarith
    exact TwoHeadInteriorComparison.actual_value_zero_le_benchmark hx.1 hxlt hSpos hSlt hanchor

end Erdos1017.TwoHeadFamilyUpper

namespace Erdos1017.MultipartiteProfiles

/-- The restricted-family upper bound uses the actual one-head comparator
and the original profile's two moments, without a family-bound premise. -/
theorem oneHeadValue_le_benchmark {L : ℝ} {x : Profile} (hx : x ∈ space L)
    (hd : density x ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    oneHeadValue x.1 (∑' i, (x.2 i) ^ 2) / (1 + x.1) ^ 2 ≤ benchmark (density x) := by
  let Q := ∑' i, (x.2 i) ^ 2
  have hmass := oneHead_mass_bounds hx
  have hQ : 0 ≤ Q := tsum_nonneg (fun _ => sq_nonneg _)
  have hsqrt : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
  have htotal : 1 + Real.sqrt Q + (x.1 - Real.sqrt Q) = 1 + x.1 := by ring
  have hdensity : 1 / 2 - (1 + (Real.sqrt Q) ^ 2) /
      (2 * (1 + Real.sqrt Q + (x.1 - Real.sqrt Q)) ^ 2) = density x := by
    rw [htotal, hsqrt]
    rfl
  have h := TwoHeadFamilyUpper.normalized_value_le_benchmark
    ⟨hmass.1, hmass.2.1⟩ hmass.2.2 (by rwa [hdensity])
  rw [hdensity, htotal] at h
  rw [oneHeadValue_eq_finite]
  exact h

end Erdos1017.MultipartiteProfiles

module

public import Erdos1017.Multipartite.MultipartiteBenchmarkApplication
public import Erdos1017.Multipartite.TwoHead.TwoHeadFamilyUpper

/-!
# Multipartite profiles below the benchmark

Every compact countable multipartite profile satisfies the benchmark bound at
its normalized graph density, and the unconditional comparison applies to
arbitrary summable heads, including zero masses and unsorted labels, with dust.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

/-- Every actual compact countable multipartite profile satisfies the
original benchmark bound at its actual normalized graph density. -/
theorem normalizedValue_le_benchmark {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    normalizedValue x ≤ benchmark (density x) :=
  normalizedValue_le_benchmark_of_oneHead_family_bound
    (fun _ _ hy hd => oneHeadValue_le_benchmark hy hd) hx

end Erdos1017.MultipartiteProfiles

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- The unconditional profile comparison applies to arbitrary summable
heads, including zero masses and unsorted labels, with genuine dust. -/
theorem normalized_value_le_benchmark (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s)
    (hQ : (∑' i, (p i) ^ 2) ≤ 1) :
    value p s / (1 + (s + ∑' i, p i)) ^ 2 ≤
      benchmark (1 / 2 - (1 + ∑' i, (p i) ^ 2) / (2 * (1 + (s + ∑' i, p i)) ^ 2)) := by
  obtain ⟨x, hx, hxT, _, hxQ, hxvalue⟩ := MultipartiteProfiles.exists_sorted_representative
    p hp hp1 hsum s hs (s + ∑' i, p i) le_rfl hQ
  have h := MultipartiteProfiles.normalizedValue_le_benchmark hx
  unfold MultipartiteProfiles.normalizedValue MultipartiteProfiles.density MultipartiteProfiles.missingDensity at h
  rwa [hxT, hxQ, ← hxvalue] at h

end Erdos1017.MultipartiteCountableDual

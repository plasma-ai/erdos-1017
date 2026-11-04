module

public import Erdos1017.Multipartite.MultipartiteProfileCollision
public import Erdos1017.Multipartite.MultipartiteExcessSelection
public import Erdos1017.Multipartite.DenseMultipartite

/-!
# Benchmark bound on the dense interval

An anchor-normalized profile has strictly positive missing density even with
infinitely many secondary heads and dust, and the countable collision bound with
the scalar dense comparison gives the normalized-profile benchmark bound on the
full upper dense interval.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators

/-- An anchor-normalized actual profile has strictly positive missing
density, even with infinitely many secondary heads and clique dust. -/
theorem missingDensity_pos {L : ℝ} {x : Profile} (hx : x ∈ space L) : 0 < missingDensity x := by
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1]
  have hQ : 0 ≤ ∑' i, (x.2 i) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  unfold missingDensity
  positivity

/-- The actual countable collision bound and the proved scalar dense
comparison give the unconditional normalized-profile benchmark bound on
the full upper dense interval, including its left endpoint. -/
theorem normalizedValue_le_benchmark_of_dense {L : ℝ} {x : Profile}
    (hx : x ∈ space L) (hd : 153 / 338 ≤ density x) :
    normalizedValue x ≤ benchmark (density x) := by
  let a := 1 / (1 + x.1)
  let r := Real.sqrt (2 * missingDensity x)
  let q := (∑' i, (x.2 i) ^ 2) / (1 + x.1) ^ 2
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1]
  have ha : 0 < a := by dsimp [a]; positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * missingDensity x :=
    Real.sq_sqrt (by have := missingDensity_pos hx; positivity)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hmoment : r ^ 2 = a ^ 2 + q := by
    rw [hr2]
    dsimp [a, q, missingDensity]
    field_simp
  have har : a ≤ r := by nlinarith
  have hdensity : density x = (1 - r ^ 2) / 2 := by
    unfold density
    rw [hr2]
    ring
  have hrhi : r ≤ 4 / 13 := by rw [hdensity] at hd; nlinarith
  have hcollision : normalizedValue x ≤ Benchmark.splitValue a + q / 2 := by
    have h := normalizedValue_le_split_add_square hx
    dsimp only [a, q]
    convert h using 1
    field_simp
  rw [hdensity]
  exact DenseMultipartite.collision_bound_le_benchmark ha har hrhi hmoment hcollision

end Erdos1017.MultipartiteProfiles

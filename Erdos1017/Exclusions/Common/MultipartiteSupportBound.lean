module

public import Erdos1017.Exclusions.Common.BenchmarkSupportEnvelope
public import Erdos1017.Multipartite.MultipartiteCollision
public import Erdos1017.SelectedModel.MultipartiteValue.FractionalMultipartiteComparison

/-!
# Sharp support bound for multipartite profiles

Every finite nonnegative multipartite profile of total mass one has value plus
density at most the sharp support constant, by the anchored collision estimate,
and every finite complete multipartite graph obeys the corresponding value plus
edge count bound.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.Multipartite

/-- The anchored collision estimate pays the sharp support constant at
the same normalized part masses and their exact square density. -/
theorem anchored_value_add_density_le {m : ℕ} (a : Option (Fin m) → ℝ)
    (ha : 0 < a none) (hsecondary : ∀ i, 0 ≤ a (some i) ∧ a (some i) ≤ a none)
    (hsum : ∑ i, a i = 1) :
    value a + (1 - ∑ i, a i ^ 2) / 2 ≤ 25 / 48 := by
  have htail : 0 ≤ ∑ i, a (some i) :=
    Finset.sum_nonneg (fun i _ => (hsecondary i).1)
  have hsum' := hsum
  simp only [Fintype.sum_option] at hsum'
  have hanchor : a none ≤ 1 := by
    linarith
  have hcollision := value_le_split_add_collision a ha hsecondary hsum
  have hsupport := Benchmark.splitValue_sub_half_square_le ⟨ha.le, hanchor⟩
  rw [Fintype.sum_option]
  linarith

/-- Every actual finite nonnegative multipartite profile of total mass
one has value plus its own density at most the sharp support constant. -/
theorem value_add_density_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    value a + (1 - ∑ i, a i ^ 2) / 2 ≤ 25 / 48 := by
  classical
  have hne : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ a (Finset.univ_nonempty_iff.mpr hne)
  have hpos : 0 < a i := by
    by_contra h
    have hle : (∑ j, a j) ≤ 0 := Finset.sum_nonpos (fun j _ =>
      (hi j (Finset.mem_univ j)).trans (le_of_not_gt h))
    linarith
  let e : Option (Fin (Fintype.card {j : ι // j ≠ i})) ≃ ι :=
    (Equiv.optionCongr (Fintype.equivFin {j : ι // j ≠ i}).symm).trans
      (Equiv.optionSubtypeNe i)
  have he : e none = i := by rfl
  have h := anchored_value_add_density_le (fun j => a (e j)) (by simpa [he] using hpos)
    (fun j => ⟨ha _, hi _ (Finset.mem_univ _)⟩) ((e.sum_comp a).trans hsum)
  rw [value_reindex e a] at h
  have hsquares : (∑ j, (a (e j)) ^ 2) = ∑ j, (a j) ^ 2 := e.sum_comp (fun j => (a j) ^ 2)
  rwa [hsquares] at h

end Erdos1017.Multipartite

namespace Erdos1017.FractionalMultipartite

/-- The actual graph value and edge count obey the sharp support bound
for every finite complete multipartite graph at its original order. -/
theorem value_add_edge_count_le {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (hG : G.IsCompleteMultipartite) :
    FractionalGraph.value G + (G.edgeSet.ncard : ℝ) ≤ 25 * (n : ℝ) ^ 2 / 48 := by
  obtain ⟨ι, hι, hdec, a, ha, hsum, hdensity, hvalue⟩ := exists_actual_class_model G hn hG
  have h := Multipartite.value_add_density_le a ha hsum
  rw [← hdensity] at h
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnormalized : (FractionalGraph.value G + (G.edgeSet.ncard : ℝ)) / (n : ℝ) ^ 2 ≤
      25 / 48 := by
    rw [add_div]
    linarith
  have hscaled := (div_le_iff₀ (sq_pos_of_pos hnreal)).mp hnormalized
  linarith

end Erdos1017.FractionalMultipartite

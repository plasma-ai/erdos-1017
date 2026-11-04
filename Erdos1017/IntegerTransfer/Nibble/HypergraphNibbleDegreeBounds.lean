module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleExposure

/-!
# Variance and concentration of the degree exposure

This module bounds the variance of the prospective degree in terms of the rank,
maximum-degree and codegree parameters of the nibble, derives concentration of
the degree exposure for surviving vertices, and shows that the expected number
of vertices with atypical exposure is small in a round
(`expected_bad_degree_count`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A sampling coordinate outside the star of `v` affects only few of the edges at `v`. -/
theorem blocker_column_bound (H : Finset (Finset V)) (v : V) (f : Finset V)
    (r : ℕ) (c : ℝ) (hc : 0 ≤ c) (hrank : ∀ e ∈ H, e.card ≤ r)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) :
    ((H.filter (fun e => v ∈ e ∧ f ∈ blockers H v e)).card : ℝ) ≤ r * c := by
  classical
  by_cases hf : f ∈ H
  · by_cases hv : v ∈ f
    · have hempty : H.filter (fun e => v ∈ e ∧ f ∈ blockers H v e) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have hnot := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).2.2).2
        exact hnot (by rw [incident_singleton]; exact Finset.mem_filter.mpr ⟨hf, hv⟩)
      simp [hempty, mul_nonneg (Nat.cast_nonneg r) hc]
    · have hsub : H.filter (fun e => v ∈ e ∧ f ∈ blockers H v e) ⊆
          f.biUnion (fun u => H.filter (fun e => v ∈ e ∧ u ∈ e)) := by
        intro e he
        obtain ⟨heH, hve, hblock⟩ := Finset.mem_filter.mp he
        obtain ⟨u, hu⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hblock).1).2
        obtain ⟨huf, hue⟩ := Finset.mem_inter.mp hu
        exact Finset.mem_biUnion.mpr ⟨u, huf, Finset.mem_filter.mpr ⟨heH, hve, hue⟩⟩
      have hcard : (H.filter (fun e => v ∈ e ∧ f ∈ blockers H v e)).card ≤
          ∑ u ∈ f, codegree H v u :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      calc
        _ ≤ ∑ u ∈ f, (codegree H v u : ℝ) := by exact_mod_cast hcard
        _ ≤ ∑ u ∈ f, c := Finset.sum_le_sum (fun u hu => hcodegree v u (by intro h; subst u; exact hv hu))
        _ = (f.card : ℝ) * c := by simp
        _ ≤ r * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hrank f hf) hc
  · have hempty : H.filter (fun e => v ∈ e ∧ f ∈ blockers H v e) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hf (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).2.2).1).1
    simp [hempty, mul_nonneg (Nat.cast_nonneg r) hc]

private theorem intersection_sum_bound {I A : Type*} [DecidableEq I] [DecidableEq A]
    (P : Finset I) (B : I → Finset A) (L M : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ i ∈ P, ((B i).card : ℝ) ≤ M)
    (hcol : ∀ a, ((P.filter (fun i => a ∈ B i)).card : ℝ) ≤ L) :
    (∑ i ∈ P, ∑ j ∈ P, ((B i ∩ B j).card : ℝ)) ≤ L * M * P.card := by
  have hinner (i : I) (hi : i ∈ P) : (∑ j ∈ P, ((B i ∩ B j).card : ℝ)) ≤ L * M := by
    have hcard (j : I) : ((B i ∩ B j).card : ℝ) =
        ∑ a ∈ B i, if a ∈ B j then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
      simp
    simp_rw [hcard]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ a ∈ B i, L := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
          Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hcol a
      _ = L * (B i).card := by simp [mul_comm]
      _ ≤ L * M := mul_le_mul_of_nonneg_left (hrow i hi) hL
  calc
    _ ≤ ∑ i ∈ P, L * M := Finset.sum_le_sum hinner
    _ = _ := by simp [mul_comm]

/-- A degree-variance bound in the rank, maximum-degree and codegree parameters of the nibble. -/
theorem prospectiveDegree_variance_le_parameters (H : Finset (Finset V)) (p D c : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hrank : ∀ e ∈ H, e.card ≤ r) (hdegree : ∀ v, (degree H v : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) (v : V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X *
      (prospectiveDegree H X v -
        ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card) ^ 2) ≤
      p * (r * c) * (r * D) * degree H v := by
  have hoverlap := intersection_sum_bound (H.filter (fun e => v ∈ e)) (blockers H v)
    (r * c) (r * D) (mul_nonneg (Nat.cast_nonneg _) hc) ?_ ?_
  · have h := (prospectiveDegree_variance_le H p hp hp1 v).trans
      (mul_le_mul_of_nonneg_left hoverlap hp)
    simpa only [degree, mul_assoc] using h
  · intro e he
    have hsub : blockers H v e ⊆ incident H e := Finset.sdiff_subset
    have hcast : ((blockers H v e).card : ℝ) ≤ (incident H e).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcast.trans (incident_card_le_rank_degree H e r D hD
      (hrank e (Finset.mem_filter.mp he).1) hdegree)
  · intro f
    simpa only [Finset.filter_filter] using blocker_column_bound H v f r c hc hrank hcodegree

/-- Quantitative concentration of the degree exposure used for vertices surviving the round. -/
theorem prospectiveDegree_deviation_mass (H : Finset (Finset V)) (p D c t : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 ≤ D) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hrank : ∀ e ∈ H, e.card ≤ r) (hdegree : ∀ v, (degree H v : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) (v : V) :
    t ^ 2 * (∑ X, if t ≤ |prospectiveDegree H X v -
      ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card| then
      CliqueSampling.weight (fun _ => p) X else 0) ≤
      p * (r * c) * (r * D) * degree H v := by
  classical
  calc
    _ ≤ ∑ X, CliqueSampling.weight (fun _ => p) X *
        (prospectiveDegree H X v -
          ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      have hw := CliqueSampling.weight_nonneg (fun _ : Finset V => p) (fun _ => ⟨hp, hp1⟩) X
      split_ifs with h
      · have hs : t ^ 2 ≤ (prospectiveDegree H X v -
            ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card) ^ 2 := by
          nlinarith [sq_abs (prospectiveDegree H X v -
            ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card)]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hs hw
      · simp only [mul_zero]
        exact mul_nonneg hw (sq_nonneg _)
    _ ≤ _ := prospectiveDegree_variance_le_parameters H p D c r hp hp1 hD hc hrank hdegree hcodegree v

/-- The expected number of vertices with atypical degree exposure is small in a nibble round. -/
theorem expected_bad_degree_count (H : Finset (Finset V)) (p D c t : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 ≤ D) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hrank : ∀ e ∈ H, e.card ≤ r) (hdegree : ∀ v, (degree H v : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) :
    t ^ 2 * (∑ X, CliqueSampling.weight (fun _ => p) X *
      ((Finset.univ.filter (fun v => t ≤ |prospectiveDegree H X v -
        ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card|)).card : ℝ)) ≤
      p * (r * c) * (r * D) * D * Fintype.card V := by
  classical
  have hindicator (X : Finset V → Bool) :
      ((Finset.univ.filter (fun v => t ≤ |prospectiveDegree H X v -
        ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card|)).card : ℝ) =
      ∑ v : V, if t ≤ |prospectiveDegree H X v -
        ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card| then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  have hcoef : 0 ≤ p * (r * c) * (r * D) := by positivity
  simp_rw [hindicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ v : V, p * (r * c) * (r * D) * degree H v := by
      apply Finset.sum_le_sum
      intro v _
      have h := prospectiveDegree_deviation_mass H p D c t r hp hp1 hD hc ht hrank hdegree hcodegree v
      simpa only [Finset.mul_sum, mul_ite, mul_one, mul_zero] using h
    _ ≤ ∑ v : V, p * (r * c) * (r * D) * D :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hdegree v) hcoef)
    _ = _ := by simp [mul_comm]

end Erdos1017.HypergraphNibble

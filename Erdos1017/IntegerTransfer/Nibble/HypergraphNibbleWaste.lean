module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleMeans

/-!
# Wasted vertices of a nibble round

This module separates the vertices of a round into survivors, vertices covered
by the retained matching, and wasted vertices (touched but not covered), with
exact accounting, and shows that the expected number of wasted vertices is
second order in the sampling probability (`expected_waste_bound`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The surviving vertices, with an explicit ambient active set for iteration. -/
def survivors (H : Finset (Finset V)) (X : Finset V → Bool) (U : Finset V) : Finset V :=
  U.filter (fun v => ∀ e ∈ incident H {v}, X e = false)

/-- The vertices covered by the actual retained matching. -/
def covered (H : Finset (Finset V)) (X : Finset V → Bool) : Finset V :=
  (retained H X).biUnion id

/-- Touched vertices not covered by a retained matching edge are wasted in this round. -/
def wasted (H : Finset (Finset V)) (X : Finset V → Bool) (U : Finset V) : Finset V :=
  U \ (survivors H X U ∪ covered H X)

theorem survivors_disjoint_covered (H : Finset (Finset V)) (X : Finset V → Bool) (U : Finset V) :
    Disjoint (survivors H X U) (covered H X) := by
  apply Finset.disjoint_left.mpr
  intro v hv hc
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hc
  have hinc : e ∈ incident H {v} := by
    rw [incident_singleton]
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, hve⟩
  have hfalse := (Finset.mem_filter.mp hv).2 e hinc
  have htrue := (Finset.mem_filter.mp he).2.1
  simp_all

theorem covered_card (H : Finset (Finset V)) (X : Finset V → Bool) (r : ℕ)
    (huniform : ∀ e ∈ H, e.card = r) :
    (covered H X).card = r * (retained H X).card := by
  rw [covered, Finset.card_biUnion (retained_pairwise_disjoint H X)]
  calc
    _ = ∑ e ∈ retained H X, r := Finset.sum_congr rfl
      (fun e he => huniform e (Finset.mem_filter.mp he).1)
    _ = _ := by simp [Nat.mul_comm]

/-- Exact accounting separates survivors, matched vertices and actual wasted vertices. -/
theorem round_vertex_accounting (H : Finset (Finset V)) (X : Finset V → Bool)
    (U : Finset V) (r : ℕ) (hsupport : ∀ e ∈ H, e ⊆ U) (huniform : ∀ e ∈ H, e.card = r) :
    (survivors H X U).card + r * (retained H X).card + (wasted H X U).card = U.card := by
  have hsub : survivors H X U ∪ covered H X ⊆ U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_filter.mp hv).1
    · obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
      exact hsupport e (Finset.mem_filter.mp he).1 hve
  have h := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_union_of_disjoint (survivors_disjoint_covered H X U),
    covered_card H X r huniform] at h
  simpa only [wasted, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Double-counting all incidences in a uniform finite hypergraph. -/
theorem sum_degrees (H : Finset (Finset V)) (r : ℕ) (huniform : ∀ e ∈ H, e.card = r) :
    (∑ v : V, degree H v) = r * H.card := by
  have hterm (v : V) : degree H v = ∑ e ∈ H, if v ∈ e then 1 else 0 := by
    simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ H, e.card := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp
    _ = ∑ e ∈ H, r := Finset.sum_congr rfl (fun e he => huniform e he)
    _ = _ := by simp [Nat.mul_comm]

/-- The expected lost vertices are second order in the sampling probability. -/
theorem expected_waste_bound (H : Finset (Finset V)) (p D : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 ≤ D)
    (huniform : ∀ e ∈ H, e.card = r) (hdegree : ∀ v, (degree H v : ℝ) ≤ D) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * ((wasted H X Finset.univ).card : ℝ)) ≤
      p ^ 2 * r ^ 2 * D * H.card := by
  have haccount (X : Finset V → Bool) :
      ((wasted H X Finset.univ).card : ℝ) =
        Fintype.card V - survivorCount H X - r * ((retained H X).card : ℝ) := by
    have h := round_vertex_accounting H X Finset.univ r (fun _ _ => Finset.subset_univ _) huniform
    have hreal : ((survivors H X Finset.univ).card : ℝ) + r * ((retained H X).card : ℝ) +
        ((wasted H X Finset.univ).card : ℝ) = Fintype.card V := by exact_mod_cast h
    rw [survivorCount_eq_card]
    change ((wasted H X Finset.univ).card : ℝ) =
      Fintype.card V - ((survivors H X Finset.univ).card : ℝ) - r * ((retained H X).card : ℝ)
    linarith
  have hlive : (Fintype.card V : ℝ) - p * r * H.card ≤
      ∑ X, CliqueSampling.weight (fun _ => p) X * survivorCount H X := by
    rw [survivorCount_expectation]
    have h := Finset.sum_le_sum (fun (v : V) (_ : v ∈ Finset.univ) =>
      (survival_power_bounds p hp hp1 (degree H v)).1)
    have hdeg : (∑ v : V, (degree H v : ℝ)) = r * (H.card : ℝ) := by
      exact_mod_cast sum_degrees H r huniform
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, ← Finset.sum_mul, hdeg] at h
    nlinarith
  have hmatch := retained_count_expectation_lower H p D r hp hp1 hD
    (fun e he => (huniform e he).le) hdegree
  have hmatchmul := mul_le_mul_of_nonneg_left hmatch (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  simp_rw [haccount, mul_sub]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, CliqueSampling.bernoulli_total, one_mul]
  have hfactor : (∑ X, CliqueSampling.weight (fun _ : Finset V => p) X *
      ((r : ℝ) * ((retained H X).card : ℝ))) =
      r * ∑ X, CliqueSampling.weight (fun _ : Finset V => p) X * ((retained H X).card : ℝ) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _
    ring
  rw [hfactor]
  nlinarith

end Erdos1017.HypergraphNibble

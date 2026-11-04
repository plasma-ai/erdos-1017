module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleMatching

/-!
# Blockers and the prospective degree of a vertex

This module defines the `blockers` of an edge at a vertex and the
`prospectiveDegree`, the degree exposure using only sampling coordinates outside
the vertex's star, and shows that it equals the residual degree whenever the
vertex survives, with its exact expectation and the survival-times-exposure
factorization (`residual_degree_expectation_factor`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge survives at `v`, conditional on no edge incident to `v` being sampled,
precisely when no edge in this set is sampled. -/
def blockers (H : Finset (Finset V)) (v : V) (e : Finset V) : Finset (Finset V) :=
  incident H e \ incident H {v}

/-- The degree exposure that uses only sampling coordinates outside the star of `v`. -/
def prospectiveDegree (H : Finset (Finset V)) (X : Finset V → Bool) (v : V) : ℝ :=
  ∑ e ∈ H, if v ∈ e then (if ∀ f ∈ blockers H v e, X f = false then 1 else 0) else 0

/-- This degree exposure is exactly the residual degree whenever the vertex survives. -/
theorem residual_degree_eq_survival_mul (H : Finset (Finset V))
    (X : Finset V → Bool) (v : V) :
    (degree (residual H X) v : ℝ) = untouched H X {v} * prospectiveDegree H X v := by
  classical
  have hsubset (e : Finset V) (hv : v ∈ e) : incident H {v} ⊆ incident H e := by
    intro f hf
    rw [incident_singleton] at hf
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1,
      ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hf).2, hv⟩⟩⟩
  have hsplit (e : Finset V) (hv : v ∈ e) :
      (∀ f ∈ incident H e, X f = false) ↔
      (∀ f ∈ incident H {v}, X f = false) ∧ (∀ f ∈ blockers H v e, X f = false) := by
    constructor
    · intro h
      exact ⟨fun f hf => h f (hsubset e hv hf), fun f hf => h f (Finset.mem_sdiff.mp hf).1⟩
    · rintro ⟨hstar, hblock⟩ f hf
      by_cases hfv : f ∈ incident H {v}
      · exact hstar f hfv
      · exact hblock f (Finset.mem_sdiff.mpr ⟨hf, hfv⟩)
  simp only [degree, residual, Finset.filter_filter, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter, prospectiveDegree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hv : v ∈ e
  · simp only [hv, and_true, ↓reduceIte, hsplit e hv, untouched]
    split_ifs <;> norm_num <;> tauto
  · simp [hv]

/-- Codegrees cannot increase in the residual hypergraph of any round. -/
theorem residual_codegree_le (H : Finset (Finset V)) (X : Finset V → Bool) (u v : V) :
    codegree (residual H X) u v ≤ codegree H u v := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
    (Finset.mem_filter.mp he).2⟩

omit [Fintype V] in
theorem blockers_eq_incident (H : Finset (Finset V)) (v : V) (e : Finset V) :
    blockers H v e = incident (H \ incident H {v}) e := by
  ext f
  simp only [blockers, incident, Finset.mem_sdiff, Finset.mem_filter]
  tauto

/-- Exact degree expectation after exposing only samples outside the vertex's star. -/
theorem prospectiveDegree_expectation (H : Finset (Finset V)) (p : ℝ) (v : V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * prospectiveDegree H X v) =
      ∑ e ∈ H, if v ∈ e then (1 - p) ^ (blockers H v e).card else 0 := by
  simp only [prospectiveDegree, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hv : v ∈ e
  · simp only [hv, ↓reduceIte, blockers_eq_incident]
    exact untouched_expectation_const (H \ incident H {v}) p e
  · simp [hv]

/-- The expectation splits into survival probability times the conditional degree exposure.
This identity is valid even when the survival probability is zero. -/
theorem residual_degree_expectation_factor (H : Finset (Finset V)) (p : ℝ) (v : V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * (degree (residual H X) v : ℝ)) =
      (1 - p) ^ degree H v *
        (∑ X, CliqueSampling.weight (fun _ => p) X * prospectiveDegree H X v) := by
  rw [residual_degree_expectation, prospectiveDegree_expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hv : v ∈ e
  · simp only [hv, ↓reduceIte]
    have hsub : incident H {v} ⊆ incident H e := by
      intro f hf
      rw [incident_singleton] at hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1,
        ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hf).2, hv⟩⟩⟩
    have hcard : (incident H e).card = degree H v + (blockers H v e).card := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      simpa only [blockers, incident_singleton, degree, Nat.add_comm] using h.symm
    rw [hcard, pow_add]
  · simp [hv]

end Erdos1017.HypergraphNibble

module

public import Erdos1017.IntegerTransfer.CliquePackingSampling

/-!
# One round of the hypergraph nibble

This module defines incident edges, degrees and codegrees of a finite hypergraph
and computes, for one independent edge-sampling round, the exact avoidance
probability of a vertex, the expected residual degree, and a covariance bound on
vertex-survival indicators controlled by the codegree
(`survival_covariance_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges of a finite hypergraph incident to at least one vertex of `U`. -/
def incident (H : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  H.filter (fun e => (e ∩ U).Nonempty)

def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- The indicator that no independently sampled edge meets `U`. -/
def untouched (H : Finset (Finset V)) (X : Finset V → Bool) (U : Finset V) : ℝ :=
  if ∀ e ∈ incident H U, X e = false then 1 else 0

/-- One nibble round deletes every vertex touched by a sampled edge. -/
def residual (H : Finset (Finset V)) (X : Finset V → Bool) : Finset (Finset V) :=
  H.filter (fun e => ∀ f ∈ incident H e, X f = false)

private def miss (b : Bool) : ℝ := if b then 0 else 1

private theorem avoidance_product {α : Type*} [DecidableEq α] (A : Finset α) (X : α → Bool) :
    (∏ e ∈ A, miss (X e)) = if ∀ e ∈ A, X e = false then 1 else 0 := by
  classical
  by_cases h : ∀ e ∈ A, X e = false
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one (fun e he => by rw [h e he]; rfl)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨e, he, hX⟩ := h
    apply Finset.prod_eq_zero he
    cases hval : X e <;> simp_all [miss]

/-- Exact avoidance probability for one independent edge-sampling round. -/
theorem untouched_expectation (H : Finset (Finset V)) (p : Finset V → ℝ) (U : Finset V) :
    (∑ X, CliqueSampling.weight p X * untouched H X U) =
      ∏ e ∈ incident H U, (1 - p e) := by
  classical
  have h := CliqueSampling.bernoulli_product_expectation p
    (fun e b => if e ∈ incident H U then miss b else 1)
  have hfactor (e : Finset V) :
      (1 - p e) * (if e ∈ incident H U then miss false else 1) +
        p e * (if e ∈ incident H U then miss true else 1) =
        if e ∈ incident H U then 1 - p e else 1 := by
    by_cases he : e ∈ incident H U <;> simp [he, miss]
  simp only [hfactor, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const_one, mul_one] at h
  calc
    _ = ∑ X, CliqueSampling.weight p X * ∏ e ∈ incident H U, miss (X e) := by
      apply Finset.sum_congr rfl
      intro X _
      rw [avoidance_product]
      unfold untouched
      split_ifs <;> rfl
    _ = _ := h

/-- For uniform sampling the exact survival law depends only on the incident-edge count. -/
theorem untouched_expectation_const (H : Finset (Finset V)) (p : ℝ) (U : Finset V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * untouched H X U) =
      (1 - p) ^ (incident H U).card := by
  rw [untouched_expectation, Finset.prod_const]

/-- Exact expected residual degree, without an independence assumption on residual edges. -/
theorem residual_degree_expectation (H : Finset (Finset V)) (p : ℝ) (v : V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * (degree (residual H X) v : ℝ)) =
      ∑ e ∈ H, if v ∈ e then (1 - p) ^ (incident H e).card else 0 := by
  classical
  have hdegree (X : Finset V → Bool) :
      (degree (residual H X) v : ℝ) = ∑ e ∈ H, if v ∈ e then untouched H X e else 0 := by
    simp only [degree, residual, Finset.filter_filter, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter, untouched]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp_all
  simp_rw [hdegree, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hv : v ∈ e
  · simp only [hv, ↓reduceIte]
    exact untouched_expectation_const H p e
  · simp [hv]

omit [Fintype V] in
theorem incident_singleton (H : Finset (Finset V)) (v : V) :
    incident H {v} = H.filter (fun e => v ∈ e) := by
  ext e
  by_cases hv : v ∈ e <;> simp [incident, Finset.inter_singleton, hv]

omit [Fintype V] in
theorem incident_union (H : Finset (Finset V)) (U W : Finset V) :
    incident H (U ∪ W) = incident H U ∪ incident H W := by
  ext e
  simp only [incident, Finset.mem_filter, Finset.mem_union,
    Finset.inter_union_distrib_left, Finset.union_nonempty]
  tauto

/-- Joint survival is exactly avoidance of the union of incident-edge sets. -/
theorem untouched_mul (H : Finset (Finset V)) (X : Finset V → Bool) (U W : Finset V) :
    untouched H X U * untouched H X W = untouched H X (U ∪ W) := by
  simp only [untouched, incident_union, Finset.forall_mem_union]
  split_ifs <;> simp_all

omit [Fintype V] in
theorem incident_pair_card (H : Finset (Finset V)) (u v : V) :
    (incident H ({u} ∪ {v})).card + codegree H u v = degree H u + degree H v := by
  have hinter : H.filter (fun e => u ∈ e) ∩ H.filter (fun e => v ∈ e) =
      H.filter (fun e => u ∈ e ∧ v ∈ e) := by ext e; simp; tauto
  simpa only [incident_union, incident_singleton, hinter, degree, codegree] using
    Finset.card_union_add_card_inter (H.filter (fun e => u ∈ e)) (H.filter (fun e => v ∈ e))

/-- Codegree controls the covariance of the actual vertex-survival indicators in one round. -/
theorem survival_covariance_le (H : Finset (Finset V)) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (u v : V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X *
      (untouched H X {u} * untouched H X {v})) -
      (1 - p) ^ degree H u * (1 - p) ^ degree H v ≤ p * codegree H u v := by
  simp_rw [untouched_mul]
  rw [untouched_expectation_const, ← pow_add, ← incident_pair_card H u v, pow_add]
  have hbase : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hpow : (1 - p) ^ (incident H ({u} ∪ {v})).card ≤ 1 :=
    pow_le_one₀ hbase (by linarith)
  have hcode : (1 - p) ^ codegree H u v ≤ 1 := pow_le_one₀ hbase (by linarith)
  have hbern : 1 - (codegree H u v : ℝ) * p ≤ (1 - p) ^ codegree H u v := by
    induction codegree H u v with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.cast_succ]
      have hmul := mul_le_mul_of_nonneg_right ih hbase
      have hkp : 0 ≤ (k : ℝ) * p ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      nlinarith
  have hmul := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hcode)
  nlinarith

end Erdos1017.HypergraphNibble

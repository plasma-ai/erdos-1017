module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphMatchingTransport

/-!
# Pruning high-degree vertices of a hypergraph

Deleting the edges incident to vertices whose degree exceeds a chosen multiple
of the degree scale bounds every remaining degree, and a bounded mean with small
squared degree error controls the total degree loss and the number of vertices
losing a significant degree fraction (`pruned_damaged_count`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices whose actual degree exceeds a chosen multiple of the degree scale. -/
def highDegrees (H : Finset (Finset V)) (C D : ℝ) : Finset V :=
  Finset.univ.filter (fun v => C * D < (degree H v : ℝ))

/-- Deleting edges incident to high-degree vertices bounds every remaining degree. -/
theorem pruned_degree_le (H : Finset (Finset V)) (C D : ℝ) (hCD : 0 ≤ C * D) (v : V) :
    (degree (removeVertices H (highDegrees H C D)) v : ℝ) ≤ C * D := by
  by_cases hv : v ∈ highDegrees H C D
  · have hzero : degree (removeVertices H (highDegrees H C D)) v = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heH, hev⟩ := Finset.mem_filter.mp he
      exact Finset.disjoint_left.mp (Finset.mem_filter.mp heH).2 hev hv
    simpa only [hzero, Nat.cast_zero] using hCD
  · have hbound : (degree H v : ℝ) ≤ C * D := by
      simpa only [highDegrees, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hv
    have hmono : (degree (removeVertices H (highDegrees H C D)) v : ℝ) ≤ degree H v := by
      exact_mod_cast removeVertices_degree_le H (highDegrees H C D) v
    exact hmono.trans hbound

/-- A bounded mean converts the squared degree error into a bound on all high
vertices' incident edges. The multiplier is independent of the thinning scale. -/
theorem highDegrees_incidence_bound (H : Finset (Finset V)) (μ : V → ℝ)
    (C D : ℝ) (hC : 1 ≤ C) (hD : 0 < D) (hμ : ∀ v, μ v ≤ (C - 1) * D) :
    D * (∑ v ∈ highDegrees H C D, (degree H v : ℝ)) ≤
      C * ∑ v : V, ((degree H v : ℝ) - μ v) ^ 2 := by
  have hpoint (v : V) (hv : v ∈ highDegrees H C D) :
      D * (degree H v : ℝ) ≤ C * ((degree H v : ℝ) - μ v) ^ 2 := by
    have hv := (Finset.mem_filter.mp hv).2
    have hm := hμ v
    let z : ℝ := (degree H v : ℝ) - μ v
    have hz : D ≤ z := by dsimp [z]; nlinarith
    have hdeg : (degree H v : ℝ) ≤ C * z := by
      have hmul := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hC)
      dsimp [z] at *
      nlinarith
    have hsq : D * z ≤ z ^ 2 := by nlinarith
    have hm1 := mul_le_mul_of_nonneg_left hdeg hD.le
    have hm2 := mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ C)
    dsimp [z] at *
    nlinarith
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ v ∈ highDegrees H C D, C * ((degree H v : ℝ) - μ v) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ v : V, C * ((degree H v : ℝ) - μ v) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
    _ = _ := (Finset.mul_sum ..).symm

/-- Total degree damage from pruning is controlled by the global squared error. -/
theorem pruned_total_degree_loss (H : Finset (Finset V)) (μ : V → ℝ)
    (r : ℕ) (C D : ℝ) (hC : 1 ≤ C) (hD : 0 < D)
    (huniform : ∀ e ∈ H, e.card = r) (hμ : ∀ v, μ v ≤ (C - 1) * D) :
    D * (∑ v : V, ((degree H v : ℝ) - degree (removeVertices H (highDegrees H C D)) v)) ≤
      r * C * ∑ v : V, ((degree H v : ℝ) - μ v) ^ 2 := by
  let W := highDegrees H C D
  have hcard : (H.card : ℝ) - (removeVertices H W).card ≤ ∑ v ∈ W, (degree H v : ℝ) := by
    have h := removeVertices_edge_loss H W
    have hsub : (removeVertices H W).card ≤ H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hcast : ((H.card - (removeVertices H W).card : ℕ) : ℝ) ≤ ∑ v ∈ W, (degree H v : ℝ) := by
      exact_mod_cast h
    rwa [Nat.cast_sub hsub] at hcast
  have hsum : (∑ v : V, (degree H v : ℝ)) = r * (H.card : ℝ) := by
    exact_mod_cast sum_degrees H r huniform
  have hsum' : (∑ v : V, (degree (removeVertices H W) v : ℝ)) = r * ((removeVertices H W).card : ℝ) := by
    exact_mod_cast sum_degrees (removeVertices H W) r (fun e he => huniform e (Finset.mem_filter.mp he).1)
  have hbound := highDegrees_incidence_bound H μ C D hC hD hμ
  have hm := mul_le_mul_of_nonneg_left hcard (mul_nonneg (Nat.cast_nonneg r) hD.le)
  have hm' := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  rw [Finset.sum_sub_distrib, hsum, hsum']
  dsimp only [W] at *
  nlinarith

/-- Only a controlled number of vertices lose a significant degree fraction. -/
theorem pruned_damaged_count (H : Finset (Finset V)) (μ : V → ℝ)
    (r : ℕ) (C D a : ℝ) (hC : 1 ≤ C) (hD : 0 < D)
    (huniform : ∀ e ∈ H, e.card = r) (hμ : ∀ v, μ v ≤ (C - 1) * D) :
    D * a * (damaged H (highDegrees H C D) a).card ≤
      r * C * ∑ v : V, ((degree H v : ℝ) - μ v) ^ 2 := by
  have hnonneg (v : V) : 0 ≤ (degree H v : ℝ) - degree (removeVertices H (highDegrees H C D)) v := by
    have h : (degree (removeVertices H (highDegrees H C D)) v : ℝ) ≤ degree H v := by
      exact_mod_cast removeVertices_degree_le H (highDegrees H C D) v
    linarith
  have hsum : a * (damaged H (highDegrees H C D) a).card ≤
      ∑ v : V, ((degree H v : ℝ) - degree (removeVertices H (highDegrees H C D)) v) := by
    calc
      _ = ∑ v ∈ damaged H (highDegrees H C D) a, a := by simp [mul_comm]
      _ ≤ ∑ v ∈ damaged H (highDegrees H C D) a,
          ((degree H v : ℝ) - degree (removeVertices H (highDegrees H C D)) v) :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hnonneg v)
  have hmul := mul_le_mul_of_nonneg_left hsum hD.le
  have hbound := pruned_total_degree_loss H μ r C D hC hD huniform hμ
  calc
    _ ≤ D * (∑ v : V, ((degree H v : ℝ) - degree (removeVertices H (highDegrees H C D)) v)) := by
      simpa only [mul_assoc] using hmul
    _ ≤ _ := hbound

end Erdos1017.HypergraphNibble

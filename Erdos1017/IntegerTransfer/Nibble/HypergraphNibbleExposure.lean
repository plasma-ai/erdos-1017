module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleDegrees

/-!
# Second moments of exposures in one nibble round

Shared sampling coordinates bound the covariance of two avoidance events, which
gives a second-moment bound for any finite family of exposures in the same round
and controls the conditional degree variance by the overlaps of the blocker sets
(`prospectiveDegree_variance_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The shared sampling coordinates bound the covariance of two avoidance events. -/
theorem untouched_covariance_le (H : Finset (Finset V)) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (U W : Finset V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * (untouched H X U * untouched H X W)) -
      (1 - p) ^ (incident H U).card * (1 - p) ^ (incident H W).card ≤
        p * (incident H U ∩ incident H W).card := by
  simp_rw [untouched_mul]
  rw [untouched_expectation_const, incident_union, ← pow_add,
    ← Finset.card_union_add_card_inter, pow_add]
  have hbase : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hpow : (1 - p) ^ (incident H U ∪ incident H W).card ≤ 1 :=
    pow_le_one₀ hbase (by linarith)
  have hcode : (1 - p) ^ (incident H U ∩ incident H W).card ≤ 1 :=
    pow_le_one₀ hbase (by linarith)
  have hbern : 1 - ((incident H U ∩ incident H W).card : ℝ) * p ≤
      (1 - p) ^ (incident H U ∩ incident H W).card := by
    have h := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p)
      (incident H U ∩ incident H W).card
    convert h using 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hcode)
  nlinarith

/-- A second-moment bound for any finite family of exposures in the same nibble round. -/
theorem exposure_variance_le {I : Type*} [DecidableEq I]
    (H : Finset (Finset V)) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset I) (A : I → Finset V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X *
      ((∑ i ∈ P, untouched H X (A i)) - ∑ i ∈ P, (1 - p) ^ (incident H (A i)).card) ^ 2) ≤
      p * ∑ i ∈ P, ∑ j ∈ P, ((incident H (A i) ∩ incident H (A j)).card : ℝ) := by
  have hmean (i : I) := untouched_expectation_const H p (A i)
  have hcov (i j : I) :
      (∑ X, CliqueSampling.weight (fun _ => p) X *
        ((untouched H X (A i) - (1 - p) ^ (incident H (A i)).card) *
          (untouched H X (A j) - (1 - p) ^ (incident H (A j)).card))) =
      (∑ X, CliqueSampling.weight (fun _ => p) X * (untouched H X (A i) * untouched H X (A j))) -
        (1 - p) ^ (incident H (A i)).card * (1 - p) ^ (incident H (A j)).card := by
    have hterm (X : Finset V → Bool) :
        CliqueSampling.weight (fun _ => p) X *
          ((untouched H X (A i) - (1 - p) ^ (incident H (A i)).card) *
            (untouched H X (A j) - (1 - p) ^ (incident H (A j)).card)) =
        CliqueSampling.weight (fun _ => p) X * (untouched H X (A i) * untouched H X (A j)) -
          (CliqueSampling.weight (fun _ => p) X * untouched H X (A i)) *
            (1 - p) ^ (incident H (A j)).card -
          (CliqueSampling.weight (fun _ => p) X * untouched H X (A j)) *
            (1 - p) ^ (incident H (A i)).card +
          CliqueSampling.weight (fun _ => p) X *
            ((1 - p) ^ (incident H (A i)).card * (1 - p) ^ (incident H (A j)).card) := by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul, hmean, CliqueSampling.bernoulli_total, one_mul]
    ring
  have hexpand (X : Finset V → Bool) :
      ((∑ i ∈ P, untouched H X (A i)) - ∑ i ∈ P, (1 - p) ^ (incident H (A i)).card) ^ 2 =
      ∑ i ∈ P, ∑ j ∈ P,
        (untouched H X (A i) - (1 - p) ^ (incident H (A i)).card) *
        (untouched H X (A j) - (1 - p) ^ (incident H (A j)).card) := by
    simp only [← Finset.sum_sub_distrib, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  rw [hcov]
  exact untouched_covariance_le H p hp hp1 (A i) (A j)

/-- The conditional degree variance is controlled by overlaps of the actual blocker sets. -/
theorem prospectiveDegree_variance_le (H : Finset (Finset V)) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    (∑ X, CliqueSampling.weight (fun _ => p) X *
      (prospectiveDegree H X v -
        ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p) ^ (blockers H v e).card) ^ 2) ≤
      p * ∑ e ∈ H.filter (fun e => v ∈ e), ∑ f ∈ H.filter (fun f => v ∈ f),
        ((blockers H v e ∩ blockers H v f).card : ℝ) := by
  have h := exposure_variance_le (H \ incident H {v}) p hp hp1 (H.filter (fun e => v ∈ e)) id
  have hsum (X : Finset V → Bool) :
      (∑ e ∈ H.filter (fun e => v ∈ e), untouched (H \ incident H {v}) X e) =
        prospectiveDegree H X v := by
    simp only [Finset.sum_filter, prospectiveDegree, untouched, blockers_eq_incident]
  simp only [id_eq, ← blockers_eq_incident, hsum] at h
  exact h

end Erdos1017.HypergraphNibble

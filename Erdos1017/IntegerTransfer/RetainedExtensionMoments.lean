module

public import Erdos1017.IntegerTransfer.BernoulliConditionalMoments
public import Erdos1017.IntegerTransfer.TransversalMoments

/-!
# Squared degree error over retained bases

This module defines the retention probability of a base clique under partwise
thinning and the sum of squared degree errors over retained bases, and bounds
its expectation with the exact retention probability as a factor
(`retainedSquaredError_expectation_le`), counting deterministic regularity
exceptions after thinning.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] {t u : ℕ}

/-- The exact sampled coordinates of the common base clique. -/
def baseSupport (x : Fin t → A) : Finset (Coordinate (t + u) A) :=
  (MultipartiteExtension.completeEdges t).image
    (fun e => ((Fin.castAdd u e.1, x e.1), (Fin.castAdd u e.2, x e.2)))

omit [Fintype A] in
/-- Base and extension events use disjoint coordinate sets. -/
theorem baseSupport_disjoint (x : Fin t → A) (y : Fin u → A) :
    Disjoint (baseSupport (u := u) x) (support x y) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hv
  obtain ⟨f, hf, hfv⟩ := Finset.mem_image.mp hw
  have heq := (congrArg (fun q => q.2.1.val) he).trans (congrArg (fun q => q.2.1.val) hfv).symm
  have hbound := (Finset.mem_filter.mp hf).2
  simp only [Fin.val_castAdd, coordinate] at heq
  omega

/-- The base-retention event agrees with the explicit coordinate event. -/
theorem present_baseSupport (x : Fin t → A) (X : Coordinate (t + u) A → Bool) :
    BernoulliPresence.present X (baseSupport x) = if BaseRetained x X then 1 else 0 := by
  have heq : (∀ v ∈ baseSupport (u := u) x, X v = true) ↔ BaseRetained x X := by
    constructor
    · intro h i j hij
      exact h _ (Finset.mem_image.mpr ⟨(i, j),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
    · intro h v hv
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      exact h e.1 e.2 (Finset.mem_filter.mp he).2
  simp only [BernoulliPresence.present, heq]

/-- The exact probability of retaining a base clique under partwise thinning. -/
def baseProbability (q : Fin (t + u) × Fin (t + u) → ℝ) : ℝ :=
  ∏ e ∈ MultipartiteExtension.completeEdges t, q (Fin.castAdd u e.1, Fin.castAdd u e.2)

omit [Fintype A] in
/-- A base's retention probability is independent of its vertex values. -/
theorem baseSupport_probability (x : Fin t → A) (q : Fin (t + u) × Fin (t + u) → ℝ) :
    (∏ v ∈ baseSupport (u := u) x, partProbability q v) = baseProbability (t := t) q := by
  rw [baseSupport, Finset.prod_image]
  · rfl
  · intro e _ f _ h
    apply Prod.ext
    · exact Fin.ext (congrArg (fun q => q.1.1.val) h)
    · exact Fin.ext (congrArg (fun q => q.2.1.val) h)

/-- The sum of squared degree errors over retained bases, with no conditioning
or omission of the base-retention factor. -/
def retainedSquaredError (F : (Fin t → A) → Finset (Fin u → A))
    (p : Coordinate (t + u) A → ℝ) (X : Coordinate (t + u) A → Bool) : ℝ :=
  ∑ x : Fin t → A, BernoulliPresence.present X (baseSupport x) *
    (((BernoulliFamily.retained (F x) (support x) X).card : ℝ) -
      BernoulliFamily.mean (F x) (support x) p) ^ 2

/-- Aggregate variance over actually retained bases contains their exact
retention probability. Inverse allocation probabilities affect only n₀. -/
theorem retainedSquaredError_expectation_le
    (F : (Fin t → A) → Finset (Fin u → A))
    (q : Fin (t + u) × Fin (t + u) → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    (∑ X, CliqueSampling.weight (partProbability q) X *
      retainedSquaredError F (partProbability q) X) ≤
      baseProbability (t := t) q * (Fintype.card A : ℝ) ^ t *
        ((Fintype.card A : ℝ) ^ u * ((u : ℝ) * (Fintype.card A : ℝ) ^ (u - 1))) := by
  have hq0 : 0 ≤ baseProbability (t := t) q :=
    Finset.prod_nonneg (fun e _ => (hq _).1)
  simp only [retainedSquaredError, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : Fin t → A, baseProbability (t := t) q *
        ((Fintype.card A : ℝ) ^ u * ((u : ℝ) * (Fintype.card A : ℝ) ^ (u - 1))) := by
      apply Finset.sum_le_sum
      intro x _
      rw [BernoulliFamily.base_variance (F x) (support x) (baseSupport x) (partProbability q)
        (fun y _ => baseSupport_disjoint x y), baseSupport_probability]
      exact mul_le_mul_of_nonneg_left (variance_le_scale (F x) x (partProbability q) (fun v => hq _)) hq0
    _ = _ := by simp; ring

/-- The actual selected subset of any deterministic base family. -/
def retainedBases (B : Finset (Fin t → A)) (X : Coordinate (t + u) A → Bool) : Finset (Fin t → A) :=
  BernoulliFamily.retained B (baseSupport (u := u)) X

/-- Deterministic regularity exceptions are counted after thinning: their
expected number is multiplied by the same base probability as all bases. -/
theorem retainedBases_expectation (B : Finset (Fin t → A))
    (q : Fin (t + u) × Fin (t + u) → ℝ) :
    (∑ X, CliqueSampling.weight (partProbability q) X * ((retainedBases B X).card : ℝ)) =
      B.card * baseProbability (t := t) q := by
  simp only [retainedBases]
  rw [BernoulliFamily.expectation]
  simp only [BernoulliFamily.mean, baseSupport_probability, Finset.sum_const, nsmul_eq_mul]

end Erdos1017.TransversalThinning

module

public import Erdos1017.Multipartite.Physical.PhysicalLabelCounts
public import Erdos1017.Multipartite.Dust.DustCommonRealization

/-!
# Homogeneous kernel on physical labels

`kernel` is the homogeneous kernel on the fixed anchor, head and dust labels,
retaining its dust diagonal; tuple counts give the dust falling factorial, every
finite clique passes the homogeneous dual test, and on the fixed physical graph
clique support supplies independent head multiplicities pointwise.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.DustCommonRealization

/-- The actual homogeneous kernel on the fixed anchor, head and dust labels.
Its dust diagonal is retained: distinct physical dust points share one label. -/
def kernel {m : ℕ} (C : MultipartiteDust.Coefficients m) : Label m → Label m → ℝ
  | .inl i, .inl j => (Multipartite.anchorDual (DustCellRestriction.headDual C)).beta i j
  | .inl none, .inr _ => MultipartiteDust.linear C
  | .inr _, .inl none => MultipartiteDust.linear C
  | .inl (some i), .inr _ => -MultipartiteDust.incident C i
  | .inr _, .inl (some i) => -MultipartiteDust.incident C i
  | .inr _, .inr _ => -MultipartiteDust.penalty C

theorem kernel_symm {m : ℕ} (C : MultipartiteDust.Coefficients m) (i j : Label m) :
    kernel C i j = kernel C j i := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact (Multipartite.anchorDual (DustCellRestriction.headDual C)).beta_symm i j
    | inr j => cases i <;> rfl
  | inr i =>
    cases j with
    | inl j => cases j <;> rfl
    | inr j => rfl

/-- The full weighted kernel integral before removal of physical diagonals. -/
theorem kernel_weighted_sum {m : ℕ} (C : MultipartiteDust.Coefficients m)
    (p : Fin m → ℝ) (s r : ℝ) :
    (∑ a, ∑ b, kernel C a b *
      (Sum.elim (Option.elim' r p) (fun _ => s) a) *
      (Sum.elim (Option.elim' r p) (fun _ => s) b)) / 2 =
      r * ((∑ i, MultipartiteDust.head C i * p i) + MultipartiteDust.linear C * s) -
      (∑ i, ∑ j, MultipartiteDust.pair C i j * (if i < j then 1 else 0) * p i * p j) -
      (∑ i, MultipartiteDust.incident C i * p i * s) - MultipartiteDust.penalty C * s ^ 2 / 2 := by
  have hhead := DustCellRestriction.headDual_objective C p
  unfold Selector.objective MultipartiteDust.objective at hhead
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_div, sub_zero] at hhead
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_unique,
    kernel, Multipartite.anchorDual, Sum.elim_inl, Sum.elim_inr, Option.elim',
    zero_mul, zero_add, Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_mul]
  have hlin₁ : (∑ i, (DustCellRestriction.headDual C).alpha i * p i * r) =
      r * ∑ i, MultipartiteDust.head C i * p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change MultipartiteDust.head C i * p i * r = _
    ring
  have hlin₂ : (∑ i, (DustCellRestriction.headDual C).alpha i * r * p i) =
      r * ∑ i, MultipartiteDust.head C i * p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change MultipartiteDust.head C i * r * p i = _
    ring
  have hinc : (∑ i, MultipartiteDust.incident C i * s * p i) =
      ∑ i, MultipartiteDust.incident C i * p i * s := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpair : (∑ i, ∑ j, (DustCellRestriction.headDual C).beta i j * p i * p j) =
      ∑ i, ∑ j, (DustCellRestriction.headDual C).beta i j * (p i * p j) := by
    simp only [mul_assoc]
  rw [hlin₁, hlin₂, hinc, hpair]
  simp only [show (DustCellRestriction.headDual C).alpha = MultipartiteDust.head C from rfl] at hhead
  nlinarith [hhead]

/-- Actual tuple counts give the dust falling factorial, including k=0 and k=1. -/
theorem kernel_charge_by_counts {m n : ℕ} (C : MultipartiteDust.Coefficients m)
    (label : Fin n → Label m) :
    let p := fun i => (PhysicalPrimal.labelCount label (.inl (some i)) : ℝ)
    let k := PhysicalPrimal.labelCount label (.inr ())
    let r := (PhysicalPrimal.labelCount label (.inl none) : ℝ)
    PhysicalPrimal.charge (fun z => kernel C z.1 z.2) label =
      r * ((∑ i, MultipartiteDust.head C i * p i) + MultipartiteDust.linear C * k) -
      (∑ i, ∑ j, MultipartiteDust.pair C i j * (if i < j then 1 else 0) * p i * p j) -
      (∑ i, MultipartiteDust.incident C i * p i * k) -
      MultipartiteDust.penalty C * k * ((k : ℝ) - 1) / 2 := by
  dsimp only
  let p := fun i => (PhysicalPrimal.labelCount label (.inl (some i)) : ℝ)
  let k := PhysicalPrimal.labelCount label (.inr ())
  let r := (PhysicalPrimal.labelCount label (.inl none) : ℝ)
  have hw : Sum.elim (Option.elim' r p) (fun _ => (k : ℝ)) =
      fun a => (PhysicalPrimal.labelCount label a : ℝ) := by
    funext a
    cases a with
    | inl a => cases a <;> rfl
    | inr a => cases a; rfl
  have hsum := kernel_weighted_sum C p k r
  rw [hw] at hsum
  have hdiag : (∑ a, kernel C a a * (PhysicalPrimal.labelCount label a : ℝ)) =
      -MultipartiteDust.penalty C * k := by
    simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_unique,
      kernel, Multipartite.anchorDual, (DustCellRestriction.headDual C).beta_diag,
      zero_mul, Finset.sum_const_zero, zero_add]
    rfl
  rw [PhysicalPrimal.charge_by_label, hdiag]
  dsimp only [p, k, r] at hsum
  dsimp only [k]
  nlinarith [hsum]

/-- Every actual finite clique passes the homogeneous dual test. Independent
head labels occur at most once; the dust multiplicity is unrestricted. -/
theorem kernel_charge_le_one {m n : ℕ} (C : MultipartiteDust.Coefficients m)
    (hC : C ∈ MultipartiteDust.feasible m) (label : Fin n → Label m)
    (hindependent : ∀ a : Option (Fin m), ∀ i j,
      label i = .inl a → label j = .inl a → i = j) :
    PhysicalPrimal.charge (fun z => kernel C z.1 z.2) label ≤ 1 := by
  let X : Selector.Selection m := fun i =>
    decide (PhysicalPrimal.labelCount label (.inl (some i)) = 1)
  let k := PhysicalPrimal.labelCount label (.inr ())
  have hcount (a : Option (Fin m)) : PhysicalPrimal.labelCount label (.inl a) ≤ 1 :=
    PhysicalPrimal.labelCount_le_one label (.inl a) (hindependent a)
  have hbit (i : Fin m) : Selector.bit (X i) =
      (PhysicalPrimal.labelCount label (.inl (some i)) : ℝ) := by
    have hi := hcount (some i)
    have hz : PhysicalPrimal.labelCount label (.inl (some i)) = 0 ∨
        PhysicalPrimal.labelCount label (.inl (some i)) = 1 := by omega
    rcases hz with hz | hz <;> simp [X, Selector.bit, hz]
  have hr : (PhysicalPrimal.labelCount label (.inl none) : ℝ) ≤ 1 := by
    exact_mod_cast hcount none
  have hnonneg : 0 ≤ (∑ i, MultipartiteDust.head C i * Selector.bit (X i)) +
      MultipartiteDust.linear C * k := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (hC.1.1 (.inl i))
      rw [hbit]
      positivity
    · exact mul_nonneg (hC.1.1 (.inr (.inr (.inr false)))) (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hr hnonneg
  have heq := kernel_charge_by_counts C label
  dsimp only at heq
  simp_rw [← hbit] at heq
  have htest := hC.2 X k
  unfold MultipartiteDust.charge at htest
  simp_rw [← Finset.sum_mul] at heq
  dsimp only [k] at htest hnonneg hmul
  nlinarith [heq]

/-- On the fixed physical graph, clique support itself supplies independent
head multiplicities. This is a pointwise statement, so singular laws are allowed. -/
theorem physical_clique_test {Ω : Type*} {m n : ℕ}
    (C : MultipartiteDust.Coefficients m) (hC : C ∈ MultipartiteDust.feasible m)
    (v : Fin n → Label m × Ω)
    (hv : ∀ i j, i ≠ j → PhysicalCellLift.Adj ({Sum.inr ()} : Finset (Label m)) (v i) (v j)) :
    PhysicalPrimal.charge (fun z => kernel C z.1.1 z.2.1) v ≤ 1 := by
  apply kernel_charge_le_one C hC (fun i => (v i).1)
  intro a i j hi hj
  by_contra hij
  have h := (hv i j hij).2
  simp [hi, hj] at h

end Erdos1017.DustCommonRealization

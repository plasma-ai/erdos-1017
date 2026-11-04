module

public import Erdos1017.Multipartite.Physical.PhysicalPrimalDuality
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Ring

/-!
# Label multiplicities in finite tuples

Finite sums and ordered pair sums regroup by label multiplicities, removing the
index diagonal subtracts one self-kernel per vertex, and an independent part has
multiplicity at most one in every clique.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.PhysicalPrimal

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Actual multiplicity of a label in a finite tuple. -/
def labelCount (label : ι → κ) (a : κ) : ℕ := ∑ i, if label i = a then 1 else 0

/-- Regroup a finite real sum by its actual natural label multiplicities. -/
theorem sum_by_label (label : ι → κ) (f : κ → ℝ) :
    (∑ i, f (label i)) = ∑ a, (labelCount label a : ℝ) * f a := by
  simp only [labelCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Full ordered pairs regroup into products of multiplicities. -/
theorem sum_pairs_by_label (label : ι → κ) (K : κ → κ → ℝ) :
    (∑ i, ∑ j, K (label i) (label j)) =
      ∑ a, ∑ b, K a b * (labelCount label a : ℝ) * (labelCount label b : ℝ) := by
  have hinner (i : ι) := sum_by_label label (K (label i))
  simp_rw [hinner]
  rw [sum_by_label label (fun a => ∑ b, (labelCount label b : ℝ) * K a b)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Removing the index diagonal subtracts one self-kernel per actual vertex,
not one per label. This preserves the k(k−1) dust multiplicity. -/
theorem charge_by_label {n : ℕ} (label : Fin n → κ) (K : κ → κ → ℝ) :
    charge (fun z : κ × κ => K z.1 z.2) label =
      ((∑ a, ∑ b, K a b * (labelCount label a : ℝ) * (labelCount label b : ℝ)) -
        ∑ a, K a a * (labelCount label a : ℝ)) / 2 := by
  classical
  have hpair : (∑ ij : PairIndex n, K (label ij.val.1) (label ij.val.2)) =
      ∑ i, ∑ j, if i ≠ j then K (label i) (label j) else 0 := by
    rw [← Fintype.sum_prod_type (fun ij : Fin n × Fin n =>
      if ij.1 ≠ ij.2 then K (label ij.1) (label ij.2) else 0)]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2))
      (by simp) (fun ij => K (label ij.1) (label ij.2))).symm
  have hterm (i j : Fin n) : (if i ≠ j then K (label i) (label j) else 0) =
      K (label i) (label j) - if i = j then K (label i) (label j) else 0 := by
    by_cases h : i = j <;> simp [h]
  unfold charge
  rw [hpair]
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [sum_pairs_by_label, sum_by_label label (fun a => K a a)]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype κ] in
/-- An independent part has Boolean multiplicity in every actual clique. -/
theorem labelCount_le_one (label : ι → κ) (a : κ)
    (hinj : ∀ i j, label i = a → label j = a → i = j) : labelCount label a ≤ 1 := by
  classical
  have hcount : labelCount label a = (Finset.univ.filter (fun i => label i = a)).card := by
    simp only [labelCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcount, Finset.card_le_one]
  intro i hi j hj
  exact hinj i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

end Erdos1017.PhysicalPrimal

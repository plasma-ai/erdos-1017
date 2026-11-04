module

public import Erdos1017.Multipartite.Dust.DustCellRestriction

/-!
# Head multiplicities alongside existing dust

Natural head multiplicities with default self penalties are combined with an
unrestricted original-dust count; two copies reduce to one and three or more
have nonpositive contribution, so head types can be repeated while retaining
arbitrary dust, with Boolean counts recovering the original rooted test.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Natural head multiplicities with default head self penalties, while the
old dust keeps its own unrestricted count and quadratic coefficient. -/
def repeatedCharge {m : ℕ} (C : Coefficients m) (n : Fin m → ℕ) (d : ℕ) : ℝ :=
  Selector.repeatedCharge (DustCellRestriction.headDual C) n +
    (d : ℝ) * (linear C - ∑ i, incident C i * n i) - penalty C * d * ((d : ℝ) - 1) / 2

/-- Changing one head count retains all interactions with existing dust. -/
theorem repeatedCharge_update {m : ℕ} (C : Coefficients m) (n : Fin m → ℕ)
    (d : ℕ) (i : Fin m) (k : ℕ) :
    repeatedCharge C (Function.update n i k) d = repeatedCharge C n d +
      ((k : ℝ) - n i) * (head C i +
        ∑ j, (DustCellRestriction.headDual C).beta i j * n j - (d : ℝ) * incident C i) -
      head C i * ((k : ℝ) * (k - 1) - (n i : ℝ) * ((n i : ℝ) - 1)) / 2 := by
  have hsum : (∑ j, incident C j * (Function.update n i k j : ℝ)) =
      (∑ j, incident C j * n j) + incident C i * ((k : ℝ) - n i) := by
    have ht (j : Fin m) : incident C j * (Function.update n i k j : ℝ) =
        incident C j * n j + if j = i then incident C i * ((k : ℝ) - n i) else 0 := by
      by_cases h : j = i
      · subst j
        simp only [Function.update_self, ↓reduceIte]
        ring
      · simp [h, Function.update_of_ne]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  unfold repeatedCharge
  rw [Selector.repeatedCharge_update, hsum]
  simp only [show (DustCellRestriction.headDual C).alpha = head C from rfl]
  ring

theorem head_pair_nonpos {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m) (i j : Fin m) :
    (DustCellRestriction.headDual C).beta i j ≤ 0 := by
  dsimp only [DustCellRestriction.headDual]
  split_ifs
  · exact neg_nonpos.mpr (hC.1.1 (.inr (.inl (i, j))))
  · exact neg_nonpos.mpr (hC.1.1 (.inr (.inl (j, i))))
  · norm_num

/-- All exterior head and existing-dust penalties have the correct sign for
count reduction. -/
theorem repeatedRow_nonpos {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (n : Fin m → ℕ) (d : ℕ) (i : Fin m) :
    (∑ j, (DustCellRestriction.headDual C).beta i j * n j) - (d : ℝ) * incident C i ≤ 0 := by
  apply sub_nonpos.mpr
  apply le_trans (Finset.sum_nonpos (fun j _ =>
    mul_nonpos_of_nonpos_of_nonneg (head_pair_nonpos C hC i j) (Nat.cast_nonneg _)))
  exact mul_nonneg (Nat.cast_nonneg _) (hC.1.1 (.inr (.inr (.inl i))))

/-- Two copies of a completed head can be reduced to one in the presence of
any fixed old-dust count. -/
theorem repeatedCharge_two_le {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (n : Fin m → ℕ) (d : ℕ) (i : Fin m) (hi : n i = 2) :
    repeatedCharge C n d ≤ repeatedCharge C (Function.update n i 1) d := by
  have hrow := repeatedRow_nonpos C hC n d i
  rw [repeatedCharge_update, hi]
  norm_num
  linarith

/-- At least three copies have nonpositive own and exterior contribution. -/
theorem repeatedCharge_many_le {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (n : Fin m → ℕ) (d : ℕ) (i : Fin m) (hi : 3 ≤ n i) :
    repeatedCharge C n d ≤ repeatedCharge C (Function.update n i 0) d := by
  have hrow := repeatedRow_nonpos C hC n d i
  have hn : (3 : ℝ) ≤ n i := by exact_mod_cast hi
  have hself := mul_nonneg (mul_nonneg (hC.1.1 (.inl i)) (Nat.cast_nonneg (n i)))
    (sub_nonneg.mpr hn)
  have hcross := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (n i)) hrow
  rw [repeatedCharge_update]
  norm_num
  change 0 ≤ head C i * (n i : ℝ) * ((n i : ℝ) - 3) at hself
  nlinarith

/-- Boolean head counts recover exactly the original rooted all-count test. -/
theorem repeatedCharge_boolean {m : ℕ} (C : Coefficients m) (X : Selector.Selection m) (d : ℕ) :
    repeatedCharge C (fun i => if X i then 1 else 0) d = charge C X d := by
  have hbit (i : Fin m) : ((if X i then 1 else 0 : ℕ) : ℝ) = Selector.bit (X i) := by
    cases X i <;> simp [Selector.bit]
  have hself : (∑ i, (DustCellRestriction.headDual C).alpha i * Selector.bit (X i) *
      (Selector.bit (X i) - 1) / 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases X i <;> simp [Selector.bit]
  unfold repeatedCharge Selector.repeatedCharge
  simp_rw [hbit]
  rw [hself, sub_zero, DustCellRestriction.headDual_objective]
  simp only [objective, charge, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_div, sub_zero]

/-- Head types can all be repeated with their default self penalties while
retaining arbitrary existing dust. No mixed-count feasibility is assumed. -/
theorem repeatedCharge_le_one {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (n : Fin m → ℕ) (d : ℕ) : repeatedCharge C n d ≤ 1 := by
  suffices h : ∀ N : ℕ, ∀ n : Fin m → ℕ, (∑ i, n i) = N → repeatedCharge C n d ≤ 1 by
    exact h _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro n hn
    by_cases hsmall : ∀ i, n i ≤ 1
    · let X : Selector.Selection m := fun i => decide (n i = 1)
      have hnX : n = fun i => if X i then 1 else 0 := by
        funext i
        have hi := hsmall i
        have hz : n i = 0 ∨ n i = 1 := by omega
        rcases hz with hz | hz <;> simp [X, hz]
      rw [hnX, repeatedCharge_boolean]
      exact hC.2 X d
    · push Not at hsmall
      obtain ⟨i, hi⟩ := hsmall
      have hreduce (k : ℕ) (hk : k < n i) :
          repeatedCharge C (Function.update n i k) d ≤ 1 := by
        apply ih (∑ j, Function.update n i k j) ?_ _ rfl
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro j _
          by_cases hj : j = i
          · subst j
            simpa using hk.le
          · simp [Function.update_of_ne hj]
        · exact ⟨i, Finset.mem_univ _, by simpa using hk⟩
      by_cases htwo : n i = 2
      · exact (repeatedCharge_two_le C hC n d i htwo).trans (hreduce 1 (by omega))
      · exact (repeatedCharge_many_le C hC n d i (by omega)).trans (hreduce 0 (by omega))

end Erdos1017.MultipartiteDust

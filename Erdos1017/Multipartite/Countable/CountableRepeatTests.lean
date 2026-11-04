module

public import Erdos1017.Multipartite.MultipartiteCountableKernel

/-!
# Repeat tests in anchored exteriors

A `RepeatContext` is an anchored exterior clique with finitely many other
independent heads and a natural dust count; the default, zero and one repeat
tests are proved from the finite restriction, and all non-anchor interactions in
the exterior row are nonpositive.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- An anchored exterior clique uses finitely many other independent heads
and an arbitrary natural dust count. Prefixes exhaust all such contexts. -/
structure RepeatContext (i : ℕ) where
  size : ℕ
  head_lt : i < size
  selection : Selector.Selection size
  head_absent : selection ⟨i, head_lt⟩ = false
  dustCount : ℕ

def RepeatContext.row {i : ℕ} (S : RepeatContext i) (D : Coefficients) : ℝ :=
  MultipartiteDust.head (restrict S.size D) ⟨i, S.head_lt⟩ +
    ∑ j, (DustCellRestriction.headDual (restrict S.size D)).beta ⟨i, S.head_lt⟩ j *
      Selector.bit (S.selection j) -
    (S.dustCount : ℝ) * MultipartiteDust.incident (restrict S.size D) ⟨i, S.head_lt⟩

def RepeatContext.charge {i : ℕ} (S : RepeatContext i) (D : Coefficients) : ℝ :=
  MultipartiteDust.charge (restrict S.size D) S.selection S.dustCount

/-- The default repeat penalty is proved from the actual finite restriction,
including interactions with the old dust at every count. -/
theorem RepeatContext.default_test {i : ℕ} (S : RepeatContext i)
    {D : Coefficients} (hD : D ∈ feasible) (r : ℕ) :
    (r : ℝ) * S.row D + S.charge D - head D i * r * ((r : ℝ) - 1) / 2 ≤ 1 := by
  have h := MultipartiteDust.single_head_count_test (restrict S.size D)
    (restrict_mem_feasible hD S.size) S.selection ⟨i, S.head_lt⟩ S.head_absent r S.dustCount
  convert h using 1
  unfold RepeatContext.row RepeatContext.charge MultipartiteDust.charge MultipartiteDust.objective
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    zero_div, sub_zero, MultipartiteDust.head, restrict]
  ring

theorem RepeatContext.zero_test {i : ℕ} (S : RepeatContext i)
    {D : Coefficients} (hD : D ∈ feasible) : S.charge D ≤ 1 := by
  simpa using S.default_test hD 0

theorem RepeatContext.one_test {i : ℕ} (S : RepeatContext i)
    {D : Coefficients} (hD : D ∈ feasible) : S.row D + S.charge D ≤ 1 := by
  simpa using S.default_test hD 1

/-- All non-anchor interactions in the exterior row are nonpositive. -/
theorem RepeatContext.row_le_head {i : ℕ} (S : RepeatContext i)
    {D : Coefficients} (hD : D ∈ feasible) : S.row D ≤ head D i := by
  have hC := restrict_mem_feasible hD S.size
  have hsum : (∑ j, (DustCellRestriction.headDual (restrict S.size D)).beta
      ⟨i, S.head_lt⟩ j * Selector.bit (S.selection j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    apply mul_nonpos_of_nonpos_of_nonneg (MultipartiteDust.head_pair_nonpos _ hC _ _)
    cases S.selection j <;> norm_num [Selector.bit]
  have hdust : 0 ≤ (S.dustCount : ℝ) * MultipartiteDust.incident
      (restrict S.size D) ⟨i, S.head_lt⟩ :=
    mul_nonneg (Nat.cast_nonneg _) (hC.1.1 (.inr (.inr (.inl ⟨i, S.head_lt⟩))))
  change head D i + _ - _ ≤ head D i
  linarith

end Erdos1017.MultipartiteCountableDual

module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleRegularRound

/-!
# Active vertex sets across nibble rounds

The ambient and active survivor counts differ by the fixed inactive count, every
residual edge lies in the next active vertex set, and the expected number of
remaining active vertices has a quantitative upper bound allowing exceptions
(`active_survivor_mean_upper`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem sum_active (U : Finset V) (f : V → ℝ) (hf : ∀ v ∉ U, f v = 1) :
    (∑ v, f v) = (∑ v ∈ U, f v) + (Fintype.card V - (U.card : ℝ)) := by
  have hsplit : (∑ v, f v) = (∑ v ∈ U, f v) + ∑ v ∈ Finset.univ \ U, f v := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ U)]
  rw [hsplit]
  congr 1
  calc
    _ = ∑ v ∈ Finset.univ \ U, (1 : ℝ) := Finset.sum_congr rfl
      (fun v hv => hf v (Finset.mem_sdiff.mp hv).2)
    _ = _ := by
      have hcard : U.card ≤ Fintype.card V := by
        simpa using Finset.card_le_card (Finset.subset_univ U)
      simp [Finset.card_sdiff_of_subset (Finset.subset_univ U), Nat.cast_sub hcard]

omit [Fintype V] in
theorem incident_empty_outside_support (H : Finset (Finset V)) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U) (v : V) (hv : v ∉ U) : incident H {v} = ∅ := by
  rw [incident_singleton]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  exact hv (hsupport e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2)

/-- The ambient survivor count differs from the active survivor count by the fixed inactive count. -/
theorem survivorCount_active (H : Finset (Finset V)) (X : Finset V → Bool) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U) :
    survivorCount H X = ((survivors H X U).card : ℝ) + (Fintype.card V - (U.card : ℝ)) := by
  have h := sum_active U (fun v => untouched H X {v}) (fun v hv => by
    simp [untouched, incident_empty_outside_support H U hsupport v hv])
  have hcount : (∑ v ∈ U, untouched H X {v}) = ((survivors H X U).card : ℝ) := by
    simp only [survivors, untouched, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> norm_num
  simpa only [survivorCount, hcount] using h

theorem survivor_mean_active (H : Finset (Finset V)) (p : ℝ) (U : Finset V)
    (hsupport : ∀ e ∈ H, e ⊆ U) :
    (∑ v, (1 - p) ^ degree H v) = (∑ v ∈ U, (1 - p) ^ degree H v) +
      (Fintype.card V - (U.card : ℝ)) := by
  apply sum_active
  intro v hv
  have h := incident_empty_outside_support H U hsupport v hv
  have hdegree : degree H v = 0 := by
    rw [incident_singleton] at h
    simp [degree, h]
  simp [hdegree]

/-- Every residual edge lies entirely in the next active vertex set. -/
theorem residual_supported_on_survivors (H : Finset (Finset V)) (X : Finset V → Bool)
    (U : Finset V) (hsupport : ∀ e ∈ H, e ⊆ U) :
    ∀ e ∈ residual H X, e ⊆ survivors H X U := by
  intro e he v hv
  obtain ⟨heH, havoid⟩ := Finset.mem_filter.mp he
  refine Finset.mem_filter.mpr ⟨hsupport e heH hv, ?_⟩
  intro f hf
  rw [incident_singleton] at hf
  exact havoid f (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1,
    ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hf).2, hv⟩⟩⟩)

omit [Fintype V] in
/-- A quantitative upper bound on the expected remaining active vertices, allowing exceptions. -/
theorem active_survivor_mean_upper (H : Finset (Finset V)) (U W : Finset V)
    (p L M : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hdegree : ∀ v, (degree H v : ℝ) ≤ M)
    (hlower : ∀ v ∈ U, v ∉ W → L ≤ (degree H v : ℝ))
    (hfactor : 0 ≤ 1 - p * L + p ^ 2 * M ^ 2) :
    (∑ v ∈ U, (1 - p) ^ degree H v) ≤
      U.card * (1 - p * L + p ^ 2 * M ^ 2) + W.card := by
  classical
  have hterm (v : V) (hv : v ∈ U) :
      (1 - p) ^ degree H v ≤ (1 - p * L + p ^ 2 * M ^ 2) + (if v ∈ W then 1 else 0) := by
    by_cases hW : v ∈ W
    · simp only [hW, ↓reduceIte]
      have hpow : (1 - p) ^ degree H v ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)
      linarith
    · simp only [hW, ↓reduceIte, add_zero]
      have hpow := (survival_power_bounds p hp hp1 (degree H v)).2
      have hlow := mul_le_mul_of_nonneg_left (hlower v hv hW) hp
      have hsq : (degree H v : ℝ) ^ 2 ≤ M ^ 2 := by
        nlinarith [hdegree v, show (0 : ℝ) ≤ degree H v from Nat.cast_nonneg _]
      have hsqmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg p)
      nlinarith
  have hcount : (∑ v ∈ U, if v ∈ W then (1 : ℝ) else 0) ≤ W.card := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
    simpa using (show ((U ∩ W).card : ℝ) ≤ W.card from by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

end Erdos1017.HypergraphNibble

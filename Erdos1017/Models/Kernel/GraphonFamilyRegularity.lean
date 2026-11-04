module

public import Graphon.Regularity

/-!
# Simultaneous weak regularity for kernel families

One common refinement approximates every kernel in a finite family, with a bound
depending only on the family size and the error, and simultaneous weak
regularity starts from the one-part partition.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.GraphonFamily

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype ι]

/-- One common refinement approximates every kernel in a finite family.
The bound depends on the family size and error, not on the kernels. -/
theorem regularity_refinement (W : ι → Graphon Ω μ)
    (P₀ : MeasurablePartition Ω μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : MeasurablePartition Ω μ,
      Graphon.Refines Q P₀ ∧
      Q.parts.card ≤ 4 ^ (Nat.ceil ((Fintype.card ι : ℝ) / ε ^ 2) + 1) * P₀.parts.card ∧
      ∀ i, Graphon.cutNormDiff (W i) (Graphon.stepify Q (W i)) ≤ ε := by
  classical
  let E : MeasurablePartition Ω μ → ℝ := fun P => ∑ i, Graphon.energy (W i) P
  have hnonneg (P : MeasurablePartition Ω μ) : 0 ≤ E P :=
    Finset.sum_nonneg (fun i _ => Graphon.energy_nonneg (W i) P)
  have hbound (P : MeasurablePartition Ω μ) : E P ≤ Fintype.card ι := by
    calc
      E P ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => Graphon.energy_le_one (W i) P)
      _ = Fintype.card ι := by simp
  have hstep (P : MeasurablePartition Ω μ) (i : ι)
      (hi : ε < Graphon.cutNormDiff (W i) (Graphon.stepify P (W i))) :
      ∃ Q : MeasurablePartition Ω μ, Graphon.Refines Q P ∧
        Q.parts.card ≤ 4 * P.parts.card ∧ E P + ε ^ 2 ≤ E Q := by
    obtain ⟨Q, hQP, hcard, hgain, hmono⟩ :=
      Graphon.energy_increment_pair (W i) P ε hε hi
    refine ⟨Q, hQP, hcard, ?_⟩
    have hsum : (∑ j, (Graphon.energy (W j) P + if j = i then ε ^ 2 else 0)) ≤ E Q := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · subst j
        simpa using hgain
      · simpa [hji] using hmono (W j)
    simpa [E, Finset.sum_add_distrib] using hsum
  have hiter : ∀ n : ℕ, ∀ P : MeasurablePartition Ω μ,
      ∃ Q : MeasurablePartition Ω μ, Graphon.Refines Q P ∧
        Q.parts.card ≤ 4 ^ n * P.parts.card ∧
        ((∀ i, Graphon.cutNormDiff (W i) (Graphon.stepify Q (W i)) ≤ ε) ∨
          E P + n * ε ^ 2 ≤ E Q) := by
    intro n
    induction n with
    | zero =>
      intro P
      exact ⟨P, Graphon.Refines.refl P, by simp, Or.inr (by simp)⟩
    | succ n ih =>
      intro P
      by_cases hgood : ∀ i, Graphon.cutNormDiff (W i) (Graphon.stepify P (W i)) ≤ ε
      · refine ⟨P, Graphon.Refines.refl P, ?_, Or.inl hgood⟩
        have hpow : 1 ≤ 4 ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
        simpa using Nat.mul_le_mul_right P.parts.card hpow
      · push Not at hgood
        obtain ⟨i, hi⟩ := hgood
        obtain ⟨Q, hQP, hQcard, hgain⟩ := hstep P i hi
        obtain ⟨R, hRQ, hRcard, hresult⟩ := ih Q
        refine ⟨R, Graphon.Refines.trans hQP hRQ, ?_, ?_⟩
        · calc
            R.parts.card ≤ 4 ^ n * Q.parts.card := hRcard
            _ ≤ 4 ^ n * (4 * P.parts.card) := Nat.mul_le_mul_left _ hQcard
            _ = 4 ^ (n + 1) * P.parts.card := by rw [pow_succ, Nat.mul_assoc]
        · rcases hresult with hresult | hresult
          · exact Or.inl hresult
          · right
            push_cast
            nlinarith
  let N := Nat.ceil ((Fintype.card ι : ℝ) / ε ^ 2) + 1
  obtain ⟨Q, hQP, hcard, hresult⟩ := hiter N P₀
  refine ⟨Q, hQP, hcard, ?_⟩
  rcases hresult with hresult | hresult
  · exact hresult
  · exfalso
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hceil := (div_le_iff₀ hεsq).mp (Nat.le_ceil ((Fintype.card ι : ℝ) / ε ^ 2))
    have hN : (Fintype.card ι : ℝ) < N * ε ^ 2 := by
      dsimp [N]
      push_cast
      nlinarith
    have hQ := hbound Q
    have hP := hnonneg P₀
    linarith

/-- Simultaneous weak regularity starts from the one-part partition. -/
theorem regularity (W : ι → Graphon Ω μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : MeasurablePartition Ω μ,
      P.parts.card ≤ 4 ^ (Nat.ceil ((Fintype.card ι : ℝ) / ε ^ 2) + 1) ∧
      ∀ i, Graphon.cutNormDiff (W i) (Graphon.stepify P (W i)) ≤ ε := by
  obtain ⟨P, _, hcard, happrox⟩ :=
    regularity_refinement W (Graphon.trivialPartition (α := Ω) (μ := μ)) ε hε
  exact ⟨P, by simpa only [Graphon.trivialPartition_card, mul_one] using hcard, happrox⟩

end Erdos1017.GraphonFamily

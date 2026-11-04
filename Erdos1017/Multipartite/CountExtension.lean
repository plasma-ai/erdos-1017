module

public import Erdos1017.Multipartite.Selector.SelectorSigns

/-!
# Extending a Boolean dual to repeated labels

Repeated labels pay their linear coefficient on each internal pair; two copies
reduce to one without decreasing the charge and three or more copies have
nonpositive own charge, so every finite signed Boolean dual extends to all
natural multiplicities.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

/-- Repeated labels pay their linear coefficient on each internal pair. -/
def repeatedCharge {m : ℕ} (D : Dual m) (n : Fin m → ℕ) : ℝ :=
  objective (fun i => (n i : ℝ)) D -
    ∑ i, D.alpha i * (n i : ℝ) * ((n i : ℝ) - 1) / 2

/-- Changing one multiplicity isolates its exterior row and self penalty. -/
theorem repeatedCharge_update {m : ℕ} (D : Dual m) (n : Fin m → ℕ)
    (i : Fin m) (k : ℕ) :
    repeatedCharge D (Function.update n i k) = repeatedCharge D n +
      ((k : ℝ) - n i) * (D.alpha i + ∑ j, D.beta i j * n j) -
      D.alpha i * ((k : ℝ) * (k - 1) - (n i : ℝ) * (n i - 1)) / 2 := by
  have hcast : (fun j => ((Function.update n i k j : ℕ) : ℝ)) =
      Function.update (fun j => (n j : ℝ)) i (k : ℝ) := by
    funext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  have hsum : (∑ j, D.alpha j * (Function.update n i k j : ℝ) *
      ((Function.update n i k j : ℝ) - 1) / 2) =
      (∑ j, D.alpha j * (n j : ℝ) * ((n j : ℝ) - 1) / 2) +
      D.alpha i * ((k : ℝ) * (k - 1) - (n i : ℝ) * (n i - 1)) / 2 := by
    have hterm (j : Fin m) :
        D.alpha j * (Function.update n i k j : ℝ) *
            ((Function.update n i k j : ℝ) - 1) / 2 =
        D.alpha j * (n j : ℝ) * ((n j : ℝ) - 1) / 2 +
          if j = i then D.alpha i *
            ((k : ℝ) * (k - 1) - (n i : ℝ) * (n i - 1)) / 2 else 0 := by
      by_cases h : j = i
      · subst j
        simp only [Function.update_self, ↓reduceIte]
        ring
      · simp [h, Function.update_of_ne]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp
  unfold repeatedCharge
  rw [hcast, objective_update, hsum]
  ring

/-- Two copies can be reduced to one without decreasing the charge. -/
theorem repeatedCharge_two_le {m : ℕ} (D : Dual m) (n : Fin m → ℕ)
    (hbeta : ∀ i j, D.beta i j ≤ 0) (i : Fin m) (hi : n i = 2) :
    repeatedCharge D n ≤ repeatedCharge D (Function.update n i 1) := by
  have hrow : (∑ j, D.beta i j * (n j : ℝ)) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hbeta i j) (by positivity))
  rw [repeatedCharge_update, hi]
  norm_num
  linarith

/-- At least three copies have nonpositive own charge and can all be dropped. -/
theorem repeatedCharge_many_le {m : ℕ} (D : Dual m) (n : Fin m → ℕ)
    (halpha : ∀ i, 0 ≤ D.alpha i) (hbeta : ∀ i j, D.beta i j ≤ 0)
    (i : Fin m) (hi : 3 ≤ n i) :
    repeatedCharge D n ≤ repeatedCharge D (Function.update n i 0) := by
  have hrow : (∑ j, D.beta i j * (n j : ℝ)) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hbeta i j) (by positivity))
  have hn : (3 : ℝ) ≤ n i := by exact_mod_cast hi
  have hself := mul_nonneg (mul_nonneg (halpha i) (show 0 ≤ (n i : ℝ) by positivity))
    (sub_nonneg.mpr hn)
  have hcross := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (n i : ℝ) by positivity) hrow
  rw [repeatedCharge_update]
  norm_num
  nlinarith

/-- Every finite signed Boolean dual extends to all natural multiplicities.
This is the count reduction used before averaging repeated types into dust. -/
theorem repeatedCharge_le_one {m : ℕ} (D : Dual m) (hD : DualFeasible D)
    (halpha : ∀ i, 0 ≤ D.alpha i) (hbeta : ∀ i j, D.beta i j ≤ 0)
    (n : Fin m → ℕ) : repeatedCharge D n ≤ 1 := by
  suffices h : ∀ N : ℕ, ∀ n : Fin m → ℕ, (∑ i, n i) = N → repeatedCharge D n ≤ 1 by
    exact h _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro n hn
    by_cases hsmall : ∀ i, n i ≤ 1
    · let X : Selection m := fun i => decide (n i = 1)
      have hbit (i : Fin m) : bit (X i) = (n i : ℝ) := by
        have hi := hsmall i
        have hz : n i = 0 ∨ n i = 1 := by omega
        rcases hz with hz | hz <;> simp [X, bit, hz]
      have hself : (∑ i, D.alpha i * (n i : ℝ) * ((n i : ℝ) - 1) / 2) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hi := hsmall i
        have hz : n i = 0 ∨ n i = 1 := by omega
        rcases hz with hz | hz <;> simp [hz]
      have h := hD X
      simpa only [quadratic, hbit, repeatedCharge, hself, sub_zero] using h
    · push Not at hsmall
      obtain ⟨i, hi⟩ := hsmall
      have hreduce (k : ℕ) (hk : k < n i) :
          repeatedCharge D (Function.update n i k) ≤ 1 := by
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
      · exact (repeatedCharge_two_le D n hbeta i htwo).trans (hreduce 1 (by omega))
      · exact (repeatedCharge_many_le D n halpha hbeta i (by omega)).trans
          (hreduce 0 (by omega))

end Erdos1017.Selector

module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomVertexClassification
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Moment data and own count rows of the two-atom system

This module defines the tight moment data, a finite cost measure with the
residual pair demands, and the active dual's own three stationary row
differences, and shows that the derived five-point support makes the residual
factorial polynomial nonnegative, which integrates to the moment inequality.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- A genuine finite cost measure with the original residual pair demands.
It is not a probability measure or a supplied residual count certificate. -/
structure TightMomentData (x : Coefficients) (a b u e : ℝ) where
  law : Measure (ℕ × ℕ)
  finite : IsFiniteMeasure law
  integrable_first_R : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ)) law
  integrable_first_E : Integrable (fun z : ℕ × ℕ => (z.2 : ℝ)) law
  integrable_factor_R : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) * ((z.1 : ℝ) - 1)) law
  integrable_factor_E : Integrable (fun z : ℕ × ℕ => (z.2 : ℝ) * ((z.2 : ℝ) - 1)) law
  integrable_cross : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) * (z.2 : ℝ)) law
  first_R : (∫ z : ℕ × ℕ, (z.1 : ℝ) ∂law) = (b - a) * u
  first_E : (∫ z : ℕ × ℕ, (z.2 : ℝ) ∂law) = b * e
  factor_R : (∫ z : ℕ × ℕ, (z.1 : ℝ) * ((z.1 : ℝ) - 1) ∂law) = u ^ 2
  factor_E : (∫ z : ℕ × ℕ, (z.2 : ℝ) * ((z.2 : ℝ) - 1) ∂law) = e ^ 2
  cross : (∫ z : ℕ × ℕ, (z.1 : ℝ) * (z.2 : ℝ) ∂law) = u * e
  tight : ∀ᵐ z ∂law, countTest z.1 z.2 x = 1

/-- The actual derived five-point support makes the residual factorial
polynomial nonnegative. Integration pays the exact unscaled moment inequality. -/
theorem IntegerFamily.factorial_moment_nonnegative {x : Coefficients}
    (F : IntegerFamily x) {a b u e : ℝ} (D : TightMomentData x a b u e) :
    0 ≤ u ^ 2 - 2 * (u * e - b * e + e ^ 2) -
      ((F.index : ℝ) - 1) * ((b - a) * u - u * e) := by
  let j := F.index
  let P : ℕ × ℕ → ℝ := fun z =>
    (z.1 : ℝ) * ((z.1 : ℝ) - 1) -
      2 * ((z.1 : ℝ) * (z.2 : ℝ) - (z.2 : ℝ) + (z.2 : ℝ) * ((z.2 : ℝ) - 1)) -
      ((j : ℝ) - 1) * ((z.1 : ℝ) - (z.1 : ℝ) * (z.2 : ℝ))
  have hD : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) * (z.2 : ℝ) - (z.2 : ℝ)) D.law :=
    D.integrable_cross.sub D.integrable_first_E
  have hA : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) * (z.2 : ℝ) - (z.2 : ℝ) +
      (z.2 : ℝ) * ((z.2 : ℝ) - 1)) D.law :=
    (D.integrable_cross.sub D.integrable_first_E).add D.integrable_factor_E
  have hB : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) - (z.1 : ℝ) * (z.2 : ℝ)) D.law :=
    D.integrable_first_R.sub D.integrable_cross
  have hC : Integrable (fun z : ℕ × ℕ => (z.1 : ℝ) * ((z.1 : ℝ) - 1) -
      2 * ((z.1 : ℝ) * (z.2 : ℝ) - (z.2 : ℝ) + (z.2 : ℝ) * ((z.2 : ℝ) - 1))) D.law :=
    D.integrable_factor_R.sub (hA.const_mul 2)
  have hP : ∀ᵐ z ∂D.law, 0 ≤ P z := by
    filter_upwards [D.tight] with z hz
    obtain ⟨k, l⟩ := z
    rcases (F.tight k l).mp hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals dsimp only [P, j]
    all_goals norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_add, Nat.cast_ofNat,
      zero_mul, mul_zero, sub_zero, zero_add, one_mul, mul_one]
    all_goals nlinarith [show 0 ≤ (F.index : ℝ) from Nat.cast_nonneg F.index]
  have hnonneg := integral_nonneg_of_ae hP
  change 0 ≤ ∫ z : ℕ × ℕ,
    ((z.1 : ℝ) * ((z.1 : ℝ) - 1) -
      2 * ((z.1 : ℝ) * (z.2 : ℝ) - (z.2 : ℝ) + (z.2 : ℝ) * ((z.2 : ℝ) - 1))) -
      ((j : ℝ) - 1) * ((z.1 : ℝ) - (z.1 : ℝ) * (z.2 : ℝ)) ∂D.law at hnonneg
  rw [integral_sub hC (hB.const_mul ((j : ℝ) - 1)),
    integral_sub D.integrable_factor_R (hA.const_mul 2), integral_const_mul,
    integral_const_mul,
    integral_add hD D.integrable_factor_E,
    integral_sub D.integrable_cross D.integrable_first_E,
    integral_sub D.integrable_first_R D.integrable_cross,
    D.first_R, D.first_E, D.factor_R, D.factor_E, D.cross] at hnonneg
  exact hnonneg

/-- The selected active dual's own three original stationary row differences. -/
structure OwnCountRows (x : Coefficients) (a b u e ell : ℝ) : Prop where
  BE : (1 - x 1) * b = (ell - x 3) * e + (x 0 - x 4) * u
  BA : (1 + ell) * (b - a) = 2 * x 0 * u + (ell + x 1) * e
  AR : (ell - x 0) * a + (x 0 - 1) * b + (x 0 - x 2) * u + (ell - x 4) * e = 0

end Erdos1017.TwoAtomCountGate

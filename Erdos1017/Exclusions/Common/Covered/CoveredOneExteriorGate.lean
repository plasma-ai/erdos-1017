module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorFace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The generic one-exterior boundary gate

This module defines `TightMomentData`, the child cost law of cliques containing
the exterior part, derives the first-moment lower bound from adjacent tight
contacts, and proves the generic one-exterior-part boundary gate by selecting an
optimal vertex, deriving both adjacent count families and constructing a full
repeat penalty.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CoveredOneExterior

/-- The actual child cost law of cliques containing the exterior part.
Its total and first-count demands use the original physical masses. -/
structure TightMomentData (y : Coefficients) (b x e : ℝ) where
  law : Measure ℕ
  finite : IsFiniteMeasure law
  integrable_count : Integrable (fun n : ℕ => (n : ℝ)) law
  mass : law.real univ = b * x
  first : (∫ n : ℕ, (n : ℝ) ∂law) = x * e
  tight : ∀ᵐ n ∂law, test true n y = 1

/-- Adjacent tight contacts force the actual first-moment lower bound.
No normal-cone coefficients or point masses are supplied. -/
theorem first_moment_lower {y : Coefficients} {b x e : ℝ}
    (D : TightMomentData y b x e) (hx : 0 < x) (k : ℕ)
    (hsupport : ∀ n, test true n y = 1 → n = k ∨ n = k + 1) :
    (k : ℝ) * b ≤ e := by
  let : IsFiniteMeasure D.law := D.finite
  have hle : ∀ᵐ n : ℕ ∂D.law, (k : ℝ) ≤ (n : ℝ) := by
    filter_upwards [D.tight] with n hn
    rcases hsupport n hn with rfl | rfl
    · exact le_rfl
    · exact_mod_cast (Nat.le_succ k)
  have hmoment := integral_mono_ae (integrable_const (k : ℝ)) D.integrable_count hle
  rw [integral_const, smul_eq_mul, D.mass, D.first] at hmoment
  apply (mul_le_mul_iff_of_pos_right hx).mp
  nlinarith only [hmoment]

/-- The complete generic one-exterior-part boundary gate. It selects an
actual optimal vertex, derives both adjacent count families, constructs a
full repeat penalty, and uses the genuine cost moment to contradict its
own stationary row. Physical own-data extraction remains explicit. -/
theorem no_optimal_face_with_own_rows_moments {b x e V : ℝ}
    (hb : 0 < b) (hx : 0 < x) (he : 0 < e)
    (hentry : (optimalFace b x e V).Nonempty)
    (hmax : ∀ y ∈ feasible, objective b x e y ≤ V)
    (hown : ∀ y ∈ optimalFace b x e V, ∃ ell,
      (∀ i, 0 < y i) ∧ y 0 < 1 ∧ 1 / 2 < ell ∧
      b * (1 - y 0) = e * (ell - y 2) ∧ Nonempty (TightMomentData y b x e) ∧
      ∀ D : ℝ, (∀ r n, repeatCharge (y 0) (y 1) (y 2) (y 3) D r n ≤ 1) → ell < D) :
    False := by
  obtain ⟨y, hy, hvalue⟩ := exists_optimal_vertex hb hx he hentry hmax
  obtain ⟨ell, hpos, ht, hell, hrow, ⟨M⟩, hrepeat⟩ := hown y ⟨hy.1, hvalue⟩
  obtain ⟨j, k, hk, hkj, hq, hv, ht', hd, _, hsupport⟩ :=
    integer_family_of_vertex y hy hpos ht
  have hfirst := first_moment_lower M hx k (fun n hn => (hsupport n).mp hn)
  have hrepeat' : ell < 2 * ((j : ℝ) - k) ^ 2 / ((j : ℝ) * ((j : ℝ) + 1)) := by
    apply hrepeat
    intro r n
    rw [ht', hv, hd, hq]
    exact integer_family_repeat_feasible j k (by omega) hkj.le r n
  exact contradiction_of_stationary_row j k hk hkj hell hb hfirst ht' hd hrow hrepeat'

end Erdos1017.CoveredOneExterior

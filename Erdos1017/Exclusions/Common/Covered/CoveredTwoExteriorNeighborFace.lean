module

public import Erdos1017.Multipartite.TwoHead.TwoHeadVertexComparison

/-!
# The optimal face of the two-neighbor child

This module defines the `E`-empty child `objective` with `R`-star weight
`(b-a)*u` and its `optimalFace`, which is closed, exposed and compact under
`a<b` and positive masses, so it supplies a vertex whose repeat theorem applies,
and the face cannot carry positive own data with a strict bound against every
one-sided repeat.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology BigOperators Classical

namespace Erdos1017.CoveredTwoExteriorNeighbor

open VertexClassification

/-- The E-empty child has R-star weight (b-a)*u. The fixed AB charge
is outside this linear child objective. -/
def objective (a b c1 c2 u : ℝ) : Coefficients →ₗ[ℝ] ℝ :=
  TwoHeadVertexComparison.objective b c1 c2 u -
    (a * u) • (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ)

theorem objective_apply (a b c1 c2 u : ℝ) (x : Coefficients) :
    objective a b c1 c2 u x = b * c1 * x 0 + b * c2 * x 1 + (b - a) * u * x 2 -
      c1 * c2 * x 3 - c1 * u * x 4 - c2 * u * x 5 - u ^ 2 * x 6 / 2 := by
  simp only [objective, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, TwoHeadVertexComparison.objective_apply]
  ring

def optimalFace (a b c1 c2 u V : ℝ) : Set Coefficients :=
  {x ∈ feasible | objective a b c1 c2 u x = V}

theorem optimalFace_isClosed (a b c1 c2 u V : ℝ) :
    IsClosed (optimalFace a b c1 c2 u V) :=
  TwoHeadVertexComparison.feasible_isClosed.inter
    (isClosed_eq (objective a b c1 c2 u).continuous_of_finiteDimensional continuous_const)

/-- Genuine nonnegative star weights bound every penalty on the actual
fixed-objective face. The changed R coefficient is retained explicitly. -/
theorem penalty_sum_le {a b c1 c2 u V : ℝ} (hab : a ≤ b)
    (hb : 0 ≤ b) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hu : 0 ≤ u)
    {x : Coefficients} (hx : x ∈ optimalFace a b c1 c2 u V) :
    c1 * c2 * x 3 + c1 * u * x 4 + c2 * u * x 5 + u ^ 2 * x 6 / 2 ≤
      b * (c1 + c2) + (b - a) * u - V := by
  obtain ⟨ht1, ht2, hh⟩ := TwoHeadVertexComparison.star_bounds hx.1
  have h1 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hb hc1)
  have h2 := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hb hc2)
  have h3 := mul_le_mul_of_nonneg_left hh (mul_nonneg (sub_nonneg.mpr hab) hu)
  have hobj := hx.2
  rw [objective_apply] at hobj
  nlinarith only [hobj, h1, h2, h3]

/-- The actual E-empty optimal face is compact under a<b and positive
original B,C1,C2,R masses. No upper penalty box is assumed. -/
theorem optimalFace_isCompact {a b c1 c2 u V : ℝ} (hab : a < b)
    (hb : 0 < b) (hc1 : 0 < c1) (hc2 : 0 < c2) (hu : 0 < u) :
    IsCompact (optimalFace a b c1 c2 u V) := by
  let B := b * (c1 + c2) + (b - a) * u - V
  let U : Coefficients := ![1, 1, 1, B / (c1 * c2), B / (c1 * u),
    B / (c2 * u), 2 * B / u ^ 2]
  apply (isCompact_Icc : IsCompact (Icc (0 : Coefficients) U)).of_isClosed_subset
    (optimalFace_isClosed a b c1 c2 u V)
  intro x hx
  refine ⟨hx.1.1, ?_⟩
  obtain ⟨ht1, ht2, hh⟩ := TwoHeadVertexComparison.star_bounds hx.1
  have hp := penalty_sum_le hab.le hb.le hc1.le hc2.le hu.le hx
  have hp3 := mul_nonneg (mul_nonneg hc1.le hc2.le) (hx.1.1 3)
  have hp4 := mul_nonneg (mul_nonneg hc1.le hu.le) (hx.1.1 4)
  have hp5 := mul_nonneg (mul_nonneg hc2.le hu.le) (hx.1.1 5)
  have hp6 := div_nonneg (mul_nonneg (sq_nonneg u) (hx.1.1 6)) (by norm_num : (0 : ℝ) ≤ 2)
  intro i
  dsimp only [U]
  fin_cases i
  · exact ht1
  · exact ht2
  · exact hh
  · change x 3 ≤ B / (c1 * c2)
    apply (le_div_iff₀ (mul_pos hc1 hc2)).mpr
    dsimp only [B]
    nlinarith only [hp, hp4, hp5, hp6]
  · change x 4 ≤ B / (c1 * u)
    apply (le_div_iff₀ (mul_pos hc1 hu)).mpr
    dsimp only [B]
    nlinarith only [hp, hp3, hp5, hp6]
  · change x 5 ≤ B / (c2 * u)
    apply (le_div_iff₀ (mul_pos hc2 hu)).mpr
    dsimp only [B]
    nlinarith only [hp, hp3, hp4, hp6]
  · change x 6 ≤ 2 * B / u ^ 2
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    dsimp only [B]
    nlinarith only [hp, hp3, hp4, hp5]

/-- Actual global optimality makes the corrected fixed-objective face
exposed in the original seven-coordinate feasible set. -/
theorem optimalFace_isExposed (a b c1 c2 u V : ℝ)
    (hmax : ∀ x ∈ feasible, objective a b c1 c2 u x ≤ V) :
    IsExposed ℝ feasible (optimalFace a b c1 c2 u V) := by
  rintro ⟨x, hx⟩
  refine ⟨(objective a b c1 c2 u).toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, fun z hz => (hmax z hz).trans_eq hy.2.symm⟩
  · intro hy
    refine ⟨hy.1, le_antisymm (hmax y hy.1) ?_⟩
    exact hx.2 ▸ hy.2 x hx.1

/-- Select an attained vertex of the full feasible set from the
actual corrected compact optimal face; no active-rank input is used. -/
theorem exists_optimal_vertex {a b c1 c2 u V : ℝ} (hab : a < b)
    (hb : 0 < b) (hc1 : 0 < c1) (hc2 : 0 < c2) (hu : 0 < u)
    (hne : (optimalFace a b c1 c2 u V).Nonempty)
    (hmax : ∀ x ∈ feasible, objective a b c1 c2 u x ≤ V) :
    ∃ x ∈ feasible.extremePoints ℝ, objective a b c1 c2 u x = V := by
  obtain ⟨x, hx⟩ := (optimalFace_isCompact hab hb hc1 hc2 hu (V := V)).extremePoints_nonempty hne
  have hface := optimalFace_isExposed a b c1 c2 u V hmax
  exact ⟨x, hface.isExtreme.extremePoints_subset_extremePoints hx, hx.1.2⟩

/-- Every-optimum positivity licenses `VertexRepeat.vertex_has_repeat`
for the vertex selected from this actual weighted face. -/
theorem exists_optimal_vertex_repeat {a b c1 c2 u V : ℝ} (hab : a < b)
    (hb : 0 < b) (hc1 : 0 < c1) (hc2 : 0 < c2) (hu : 0 < u)
    (hne : (optimalFace a b c1 c2 u V).Nonempty)
    (hmax : ∀ x ∈ feasible, objective a b c1 c2 u x ≤ V)
    (hpos : ∀ x ∈ optimalFace a b c1 c2 u V, ∀ i, 0 < x i) :
    ∃ x ∈ feasible.extremePoints ℝ, objective a b c1 c2 u x = V ∧
      (∀ i, 0 < x i) ∧
      (VertexRepeat.HasRepeat x ∨ VertexRepeat.HasRepeat (VertexRepeat.swap x)) := by
  obtain ⟨x, hx, hvalue⟩ := exists_optimal_vertex hab hb hc1 hc2 hu hne hmax
  have hpositive := hpos x ⟨hx.1, hvalue⟩
  exact ⟨x, hx, hvalue, hpositive, VertexRepeat.vertex_has_repeat x hx hpositive⟩

/-- The corrected face cannot have positive own data and a strict bound
against every genuine one-sided repeat for each actual face optimum. -/
theorem no_optimal_face_with_strict_repeat {a b c1 c2 u V : ℝ} (hab : a < b)
    (hb : 0 < b) (hc1 : 0 < c1) (hc2 : 0 < c2) (hu : 0 < u)
    (hne : (optimalFace a b c1 c2 u V).Nonempty)
    (hmax : ∀ x ∈ feasible, objective a b c1 c2 u x ≤ V)
    (hpos : ∀ x ∈ optimalFace a b c1 c2 u V, ∀ i, 0 < x i)
    (hstrict : ∀ x ∈ optimalFace a b c1 c2 u V, ∀ y : Coefficients,
      (y = x ∨ y = VertexRepeat.swap x) → ∀ D : ℝ, 0 ≤ D →
        (∀ r b n : ℕ, b ≤ 1 →
          Repeat.oneSidedCharge (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) D r b n ≤ 1) →
        x 3 < D) : False := by
  obtain ⟨x, hx, hvalue, _, hrepeat⟩ :=
    exists_optimal_vertex_repeat hab hb hc1 hc2 hu hne hmax hpos
  rcases hrepeat with ⟨D, hD, hbound, hfull⟩ | ⟨D, hD, hbound, hfull⟩
  · exact (not_lt_of_ge hbound) (hstrict x ⟨hx.1, hvalue⟩ x (Or.inl rfl) D hD hfull)
  · have hbound' : D ≤ x 3 := by simpa [VertexRepeat.swap] using hbound
    exact (not_lt_of_ge hbound')
      (hstrict x ⟨hx.1, hvalue⟩ (VertexRepeat.swap x) (Or.inr rfl) D hD hfull)

end Erdos1017.CoveredTwoExteriorNeighbor

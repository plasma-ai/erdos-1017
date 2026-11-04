module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Gram identities along ordered zero triples

Two consecutive Gram equalities along a positive linear combination force
endpoint and diagonal equalities and the matching linear relation; strict scalar
order gives positive coefficients, while weak order still closes the zero
relation at the endpoints.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Erdos1017.OrderedZeroTripleGeometry

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Two consecutive Gram equalities along a positive linear combination force
the endpoint equality, all diagonal equalities, and the matching linear
relation in the second Hilbert space. -/
theorem affine_zero_triple (Ux Uy Uz : H) (Vx Vy Vz : K) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hUy : Uy = α • Ux + β • Uz)
    (hx : ‖Vx‖ ^ 2 ≤ ‖Ux‖ ^ 2)
    (hy : ‖Vy‖ ^ 2 ≤ ‖Uy‖ ^ 2)
    (hz : ‖Vz‖ ^ 2 ≤ ‖Uz‖ ^ 2)
    (hxy : ⟪Ux, Uy⟫ = ⟪Vx, Vy⟫)
    (hyz : ⟪Uy, Uz⟫ = ⟪Vy, Vz⟫)
    (hxz : ⟪Vx, Vz⟫ ≤ ⟪Ux, Uz⟫) :
    ⟪Ux, Uz⟫ = ⟪Vx, Vz⟫ ∧
      ‖Vx‖ ^ 2 = ‖Ux‖ ^ 2 ∧ ‖Vy‖ ^ 2 = ‖Uy‖ ^ 2 ∧
        ‖Vz‖ ^ 2 = ‖Uz‖ ^ 2 ∧ Vy = α • Vx + β • Vz := by
  have hUnorm : ‖Uy‖ ^ 2 = α ^ 2 * ‖Ux‖ ^ 2 + β ^ 2 * ‖Uz‖ ^ 2 +
      2 * α * β * ⟪Ux, Uz⟫ := by
    rw [hUy, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hVnorm : ‖Vy - (α • Vx + β • Vz)‖ ^ 2 =
      ‖Vy‖ ^ 2 - 2 * α * ⟪Vx, Vy⟫ - 2 * β * ⟪Vy, Vz⟫ +
        α ^ 2 * ‖Vx‖ ^ 2 + β ^ 2 * ‖Vz‖ ^ 2 +
          2 * α * β * ⟪Vx, Vz⟫ := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    simp only [inner_add_right, real_inner_smul_right, real_inner_smul_left,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm Vx Vy]
    ring
  have hUyInner : α * ⟪Ux, Uy⟫ + β * ⟪Uy, Uz⟫ = ‖Uy‖ ^ 2 := by
    calc
      α * ⟪Ux, Uy⟫ + β * ⟪Uy, Uz⟫ = ⟪α • Ux + β • Uz, Uy⟫ := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_comm Uy Uz]
      _ = ‖Uy‖ ^ 2 := by rw [← hUy, real_inner_self_eq_norm_sq]
  have hdiff : ‖Vy - (α • Vx + β • Vz)‖ ^ 2 =
      -(‖Uy‖ ^ 2 - ‖Vy‖ ^ 2) -
        α ^ 2 * (‖Ux‖ ^ 2 - ‖Vx‖ ^ 2) -
          β ^ 2 * (‖Uz‖ ^ 2 - ‖Vz‖ ^ 2) -
            2 * α * β * (⟪Ux, Uz⟫ - ⟪Vx, Vz⟫) := by
    rw [hVnorm, ← hxy, ← hyz]
    nlinarith [hUnorm, hUyInner]
  have hαsq : 0 < α ^ 2 := sq_pos_of_pos hα
  have hβsq : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hnorm : 0 ≤ ‖Vy - (α • Vx + β • Vz)‖ ^ 2 := sq_nonneg _
  have htermx : 0 ≤ α ^ 2 * (‖Ux‖ ^ 2 - ‖Vx‖ ^ 2) :=
    mul_nonneg hαsq.le (sub_nonneg.mpr hx)
  have htermy : 0 ≤ ‖Uy‖ ^ 2 - ‖Vy‖ ^ 2 := sub_nonneg.mpr hy
  have htermz : 0 ≤ β ^ 2 * (‖Uz‖ ^ 2 - ‖Vz‖ ^ 2) :=
    mul_nonneg hβsq.le (sub_nonneg.mpr hz)
  have htermxz : 0 ≤ 2 * α * β * (⟪Ux, Uz⟫ - ⟪Vx, Vz⟫) := by
    apply mul_nonneg
    · positivity
    · exact sub_nonneg.mpr hxz
  have hzero : ‖Vy - (α • Vx + β • Vz)‖ ^ 2 = 0 := by linarith
  have hδy : ‖Uy‖ ^ 2 - ‖Vy‖ ^ 2 = 0 := by linarith
  have htermxzero : α ^ 2 * (‖Ux‖ ^ 2 - ‖Vx‖ ^ 2) = 0 := by linarith
  have htermzzero : β ^ 2 * (‖Uz‖ ^ 2 - ‖Vz‖ ^ 2) = 0 := by linarith
  have htermxzzero : 2 * α * β * (⟪Ux, Uz⟫ - ⟪Vx, Vz⟫) = 0 := by linarith
  have hδx : ‖Ux‖ ^ 2 - ‖Vx‖ ^ 2 = 0 :=
    (mul_eq_zero.mp htermxzero).resolve_left hαsq.ne'
  have hδz : ‖Uz‖ ^ 2 - ‖Vz‖ ^ 2 = 0 :=
    (mul_eq_zero.mp htermzzero).resolve_left hβsq.ne'
  have hMxz : ⟪Ux, Uz⟫ - ⟪Vx, Vz⟫ = 0 := by
    have hcoef : 2 * α * β ≠ 0 := ne_of_gt (by positivity)
    exact (mul_eq_zero.mp htermxzzero).resolve_left hcoef
  have hV : Vy = α • Vx + β • Vz := by
    have hn : ‖Vy - (α • Vx + β • Vz)‖ = 0 := by
      nlinarith [norm_nonneg (Vy - (α • Vx + β • Vz))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact ⟨by linarith, by linarith, by linarith, by linarith, hV⟩

/-- Equal first-space features joined by a zero pair have equal second-space
features and no diagonal defect at either endpoint. -/
theorem equal_positive_zero_pair (Ux Uy : H) (Vx Vy : K)
    (hU : Ux = Uy) (hx : ‖Vx‖ ^ 2 ≤ ‖Ux‖ ^ 2)
    (hy : ‖Vy‖ ^ 2 ≤ ‖Uy‖ ^ 2)
    (hxy : ⟪Ux, Uy⟫ = ⟪Vx, Vy⟫) :
    Vx = Vy ∧ ‖Vx‖ ^ 2 = ‖Ux‖ ^ 2 ∧ ‖Vy‖ ^ 2 = ‖Uy‖ ^ 2 := by
  have hinner : ⟪Vx, Vy⟫ = ‖Ux‖ ^ 2 := by
    rw [← hxy, hU, real_inner_self_eq_norm_sq]
  have hdist := norm_sub_sq_real Vx Vy
  have hdistnonpos : ‖Vx - Vy‖ ^ 2 ≤ 0 := by
    rw [hU] at hx
    rw [hU] at hinner
    rw [hdist, hinner]
    linarith
  have hnorm : ‖Vx - Vy‖ = 0 := by
    nlinarith [norm_nonneg (Vx - Vy)]
  have hV : Vx = Vy := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  subst Vy
  have hxEq : ‖Vx‖ ^ 2 = ‖Ux‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hinner
  exact ⟨rfl, hxEq, by simpa only [← hU] using hxEq⟩

private def scalarFeature (a t : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[a, t]

private theorem scalarFeature_norm_sq (a t : ℝ) :
    ‖scalarFeature a t‖ ^ 2 = a ^ 2 + t ^ 2 := by
  simp [scalarFeature, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem scalarFeature_inner (a s t : ℝ) :
    ⟪scalarFeature a s, scalarFeature a t⟫ = a ^ 2 + s * t := by
  simp [scalarFeature, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  ring

/-- Strict scalar order gives positive convex coefficients, so consecutive
zero pair defects force endpoint and diagonal equalities. -/
theorem scalar_strict_zero_triple (a x y z : ℝ) (Vx Vy Vz : K)
    (hxyOrder : x < y) (hyzOrder : y < z)
    (hx : ‖Vx‖ ^ 2 ≤ a ^ 2 + x ^ 2)
    (hy : ‖Vy‖ ^ 2 ≤ a ^ 2 + y ^ 2)
    (hz : ‖Vz‖ ^ 2 ≤ a ^ 2 + z ^ 2)
    (hxy : ⟪Vx, Vy⟫ = a ^ 2 + x * y)
    (hyz : ⟪Vy, Vz⟫ = a ^ 2 + y * z)
    (hxz : ⟪Vx, Vz⟫ ≤ a ^ 2 + x * z) :
    ⟪Vx, Vz⟫ = a ^ 2 + x * z ∧
      ‖Vx‖ ^ 2 = a ^ 2 + x ^ 2 ∧
        ‖Vy‖ ^ 2 = a ^ 2 + y ^ 2 ∧
          ‖Vz‖ ^ 2 = a ^ 2 + z ^ 2 ∧
            Vy = ((z - y) / (z - x)) • Vx + ((y - x) / (z - x)) • Vz := by
  let α : ℝ := (z - y) / (z - x)
  let β : ℝ := (y - x) / (z - x)
  have hden : 0 < z - x := sub_pos.mpr (hxyOrder.trans hyzOrder)
  have hα : 0 < α := div_pos (sub_pos.mpr hyzOrder) hden
  have hβ : 0 < β := div_pos (sub_pos.mpr hxyOrder) hden
  have hsum : α + β = 1 := by
    dsimp [α, β]
    field_simp
    ring
  have hyaff : y = α * x + β * z := by
    dsimp [α, β]
    field_simp
    ring
  have hUaff : scalarFeature a y =
      α • scalarFeature a x + β • scalarFeature a z := by
    ext i
    fin_cases i
    · simp [scalarFeature, ← add_mul, hsum]
    · simp [scalarFeature, hyaff]
  have h := affine_zero_triple
    (scalarFeature a x) (scalarFeature a y) (scalarFeature a z)
    Vx Vy Vz α β hα hβ hUaff
    (by simpa only [scalarFeature_norm_sq] using hx)
    (by simpa only [scalarFeature_norm_sq] using hy)
    (by simpa only [scalarFeature_norm_sq] using hz)
    (by simpa only [scalarFeature_inner] using hxy.symm)
    (by simpa only [scalarFeature_inner] using hyz.symm)
    (by simpa only [scalarFeature_inner] using hxz)
  rcases h with ⟨hinner, hnx, hny, hnz, hV⟩
  exact ⟨by simpa only [scalarFeature_inner] using hinner.symm,
    by simpa only [scalarFeature_norm_sq] using hnx,
    by simpa only [scalarFeature_norm_sq] using hny,
    by simpa only [scalarFeature_norm_sq] using hnz, hV⟩

/-- Weak scalar order still closes the zero relation at the endpoints.
An equal adjacent parameter gives only the corresponding pair's diagonal
equalities, so this statement makes no three-point diagonal claim. -/
theorem scalar_ordered_zero_endpoint (a x y z : ℝ) (Vx Vy Vz : K)
    (hxyOrder : x ≤ y) (hyzOrder : y ≤ z)
    (hx : ‖Vx‖ ^ 2 ≤ a ^ 2 + x ^ 2)
    (hy : ‖Vy‖ ^ 2 ≤ a ^ 2 + y ^ 2)
    (hz : ‖Vz‖ ^ 2 ≤ a ^ 2 + z ^ 2)
    (hxy : ⟪Vx, Vy⟫ = a ^ 2 + x * y)
    (hyz : ⟪Vy, Vz⟫ = a ^ 2 + y * z)
    (hxz : ⟪Vx, Vz⟫ ≤ a ^ 2 + x * z) :
    ⟪Vx, Vz⟫ = a ^ 2 + x * z := by
  by_cases hxyStrict : x < y
  · by_cases hyzStrict : y < z
    · exact (scalar_strict_zero_triple a x y z Vx Vy Vz
        hxyStrict hyzStrict hx hy hz hxy hyz hxz).1
    · have hyzEq : y = z := le_antisymm hyzOrder (le_of_not_gt hyzStrict)
      subst z
      have hpair := equal_positive_zero_pair
        (scalarFeature a y) (scalarFeature a y) Vy Vz rfl
        (by simpa only [scalarFeature_norm_sq] using hy)
        (by simpa only [scalarFeature_norm_sq] using hz)
        (by simpa only [scalarFeature_inner] using hyz.symm)
      simpa only [hpair.1] using hxy
  · have hxyEq : x = y := le_antisymm hxyOrder (le_of_not_gt hxyStrict)
    subst y
    have hpair := equal_positive_zero_pair
      (scalarFeature a x) (scalarFeature a x) Vx Vy rfl
      (by simpa only [scalarFeature_norm_sq] using hx)
      (by simpa only [scalarFeature_norm_sq] using hy)
      (by simpa only [scalarFeature_inner] using hxy.symm)
    simpa only [hpair.1] using hyz

end Erdos1017.OrderedZeroTripleGeometry

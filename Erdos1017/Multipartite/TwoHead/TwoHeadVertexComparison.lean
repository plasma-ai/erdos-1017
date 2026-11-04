module

public import Erdos1017.Multipartite.Selector.VertexRepeat
public import Mathlib.Analysis.Convex.KreinMilman

/-!
# Optimal vertex of the finite coefficient face

The finite coefficient-space step of the two-head comparison. Positive
masses make the optimal face compact, so an optimal vertex is selected
rather than assumed.
The selected physical profile, its multipliers, dust floors and strict
repeat bounds are supplied where the comparison is applied.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TwoHeadVertexComparison

open VertexClassification

/-- The literal objective for an anchor, two secondary parts and positive dust. -/
def objective (a u₁ u₂ h : ℝ) : Coefficients →ₗ[ℝ] ℝ :=
  a • (u₁ • (LinearMap.proj 0 : Coefficients →ₗ[ℝ] ℝ) +
    u₂ • (LinearMap.proj 1 : Coefficients →ₗ[ℝ] ℝ) +
    h • (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ)) -
    (u₁ * u₂) • (LinearMap.proj 3 : Coefficients →ₗ[ℝ] ℝ) -
    (h * u₁) • (LinearMap.proj 4 : Coefficients →ₗ[ℝ] ℝ) -
    (h * u₂) • (LinearMap.proj 5 : Coefficients →ₗ[ℝ] ℝ) -
    (h ^ 2 / 2) • (LinearMap.proj 6 : Coefficients →ₗ[ℝ] ℝ)

theorem objective_apply (a u₁ u₂ h : ℝ) (x : Coefficients) :
    objective a u₁ u₂ h x =
      a * (u₁ * x 0 + u₂ * x 1 + h * x 2) - u₁ * u₂ * x 3 -
        h * u₁ * x 4 - h * u₂ * x 5 - h ^ 2 * x 6 / 2 := by
  simp only [objective, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.proj_apply, smul_eq_mul]
  ring

/-- The face is taken in the original unbounded nonnegative coefficient set. -/
def optimalFace (a u₁ u₂ h V : ℝ) : Set Coefficients :=
  {x ∈ feasible | objective a u₁ u₂ h x = V}

theorem feasible_isClosed : IsClosed feasible := by
  have heq : feasible = Set.Ici (0 : Coefficients) ∩
      ⋂ i : Test, {x : Coefficients | test i x ≤ 1} := by
    ext x
    simp only [feasible, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici,
      Set.mem_iInter, Pi.le_def, Pi.zero_apply]
  rw [heq]
  exact isClosed_Ici.inter (isClosed_iInter fun i =>
    isClosed_le (test i).continuous_of_finiteDimensional continuous_const)

theorem optimalFace_isClosed (a u₁ u₂ h V : ℝ) :
    IsClosed (optimalFace a u₁ u₂ h V) :=
  feasible_isClosed.inter (isClosed_eq (objective a u₁ u₂ h).continuous_of_finiteDimensional
    continuous_const)

/-- Singleton count tests bound all three star coefficients. -/
theorem star_bounds {x : Coefficients} (hx : x ∈ feasible) :
    x 0 ≤ 1 ∧ x 1 ≤ 1 ∧ x 2 ≤ 1 := by
  have h₁ := hx.2 ((true, false), 0)
  have h₂ := hx.2 ((false, true), 0)
  have hv := hx.2 ((false, false), 1)
  norm_num [test, constant, slope] at h₁ h₂ hv
  exact ⟨h₁, h₂, hv⟩

/-- Fixing the objective bounds the sum of its four nonnegative penalty terms. -/
theorem penalty_sum_le {a u₁ u₂ h V : ℝ}
    (ha : 0 ≤ a) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hh : 0 ≤ h)
    {x : Coefficients} (hx : x ∈ optimalFace a u₁ u₂ h V) :
    u₁ * u₂ * x 3 + h * u₁ * x 4 + h * u₂ * x 5 + h ^ 2 * x 6 / 2 ≤
      a * (u₁ + u₂ + h) - V := by
  have hb := star_bounds hx.1
  have hstar : a * (u₁ * x 0 + u₂ * x 1 + h * x 2) ≤ a * (u₁ + u₂ + h) := by
    gcongr
    · simpa using mul_le_mul_of_nonneg_left hb.1 hu₁
    · simpa using mul_le_mul_of_nonneg_left hb.2.1 hu₂
    · simpa using mul_le_mul_of_nonneg_left hb.2.2 hh
  have heq := hx.2
  rw [objective_apply] at heq
  linarith

/-- Every fixed-objective face is compact when all four masses are positive. -/
theorem optimalFace_isCompact {a u₁ u₂ h V : ℝ}
    (ha : 0 < a) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hh : 0 < h) :
    IsCompact (optimalFace a u₁ u₂ h V) := by
  let B := a * (u₁ + u₂ + h) - V
  let U : Coefficients := ![1, 1, 1, B / (u₁ * u₂), B / (h * u₁),
    B / (h * u₂), 2 * B / h ^ 2]
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Coefficients) U)).of_isClosed_subset
    (optimalFace_isClosed a u₁ u₂ h V)
  intro x hx
  refine ⟨hx.1.1, ?_⟩
  have hb := star_bounds hx.1
  have hp := penalty_sum_le ha.le hu₁.le hu₂.le hh.le hx
  have hp₃ := mul_nonneg (mul_nonneg hu₁.le hu₂.le) (hx.1.1 3)
  have hp₄ := mul_nonneg (mul_nonneg hh.le hu₁.le) (hx.1.1 4)
  have hp₅ := mul_nonneg (mul_nonneg hh.le hu₂.le) (hx.1.1 5)
  have hp₆ := div_nonneg (mul_nonneg (sq_nonneg h) (hx.1.1 6)) (by norm_num : (0 : ℝ) ≤ 2)
  intro i
  dsimp only [U]
  fin_cases i
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2
  · apply (le_div_iff₀ (mul_pos hu₁ hu₂)).mpr
    dsimp [B] at ⊢
    nlinarith
  · apply (le_div_iff₀ (mul_pos hh hu₁)).mpr
    dsimp [B] at ⊢
    nlinarith
  · apply (le_div_iff₀ (mul_pos hh hu₂)).mpr
    dsimp [B] at ⊢
    nlinarith
  · apply (le_div_iff₀ (pow_pos hh 2)).mpr
    dsimp [B] at ⊢
    nlinarith

/-- The face of actual global coefficient maximizers is an exposed face. -/
theorem optimalFace_isExposed (a u₁ u₂ h V : ℝ)
    (hmax : ∀ x ∈ feasible, objective a u₁ u₂ h x ≤ V) :
    IsExposed ℝ feasible (optimalFace a u₁ u₂ h V) := by
  rintro ⟨x, hx⟩
  refine ⟨(objective a u₁ u₂ h).toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, fun z hz => (hmax z hz).trans_eq hy.2.symm⟩
  · intro hy
    refine ⟨hy.1, le_antisymm (hmax y hy.1) ?_⟩
    exact hx.2 ▸ hy.2 x hx.1

/-- A genuine optimal vertex is selected from the nonempty compact optimal face. -/
theorem exists_optimal_vertex {a u₁ u₂ h V : ℝ}
    (ha : 0 < a) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hh : 0 < h)
    (hne : (optimalFace a u₁ u₂ h V).Nonempty)
    (hmax : ∀ x ∈ feasible, objective a u₁ u₂ h x ≤ V) :
    ∃ x ∈ feasible.extremePoints ℝ, objective a u₁ u₂ h x = V := by
  obtain ⟨x, hx⟩ := (optimalFace_isCompact ha hu₁ hu₂ hh).extremePoints_nonempty hne
  have hface := optimalFace_isExposed a u₁ u₂ h V hmax
  exact ⟨x, hface.isExtreme.extremePoints_subset_extremePoints hx, hx.1.2⟩

/-- The particular dual's own multiplier and dust floors force every
coefficient to be strictly positive. The premises are finite scalar identities. -/
theorem coefficients_pos_of_own_floors {a u₁ u₂ h ℓ γ : ℝ}
    (ha : 0 < a) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hh : 0 ≤ h)
    {x : Coefficients} (hx : x ∈ feasible) (hℓ : 1 / 2 < ℓ) (hγ : 0 < γ)
    (ht₁ : ℓ ≤ x 0) (ht₂ : ℓ ≤ x 1)
    (hc₁ : γ ≤ (a - u₁) * x 4) (hc₂ : γ ≤ (a - u₂) * x 5)
    (hp : γ ≤ a * x 6) (hrow : γ = a * x 2 - u₁ * x 4 - u₂ * x 5 - h * x 6) :
    ∀ i, 0 < x i := by
  have hc := hx.2 ((true, true), 0)
  norm_num [test, constant, slope] at hc
  have h₄ : 0 < x 4 := by
    by_contra hn
    have hz : x 4 = 0 := le_antisymm (le_of_not_gt hn) (hx.1 4)
    rw [hz, mul_zero] at hc₁
    linarith
  have h₅ : 0 < x 5 := by
    by_contra hn
    have hz : x 5 = 0 := le_antisymm (le_of_not_gt hn) (hx.1 5)
    rw [hz, mul_zero] at hc₂
    linarith
  have h₆ : 0 < x 6 := by
    by_contra hn
    have hz : x 6 = 0 := le_antisymm (le_of_not_gt hn) (hx.1 6)
    rw [hz, mul_zero] at hp
    linarith
  have hv : 0 < x 2 := by
    have hu₁ := mul_nonneg hu₁ (hx.1 4)
    have hu₂ := mul_nonneg hu₂ (hx.1 5)
    have hh := mul_nonneg hh (hx.1 6)
    nlinarith
  intro i
  fin_cases i
  · change 0 < x 0
    linarith
  · change 0 < x 1
    linarith
  · exact hv
  · change 0 < x 3
    linarith
  · exact h₄
  · exact h₅
  · exact h₆

/-- Applying the own-multiplier premises to every optimum licenses them for
the optimal vertex selected here, and hence gives an affordable full repeat. -/
theorem exists_optimal_vertex_repeat {a u₁ u₂ h V : ℝ}
    (ha : 0 < a) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hh : 0 < h)
    (hne : (optimalFace a u₁ u₂ h V).Nonempty)
    (hmax : ∀ x ∈ feasible, objective a u₁ u₂ h x ≤ V)
    (hown : ∀ x ∈ optimalFace a u₁ u₂ h V, ∃ ℓ γ : ℝ,
      1 / 2 < ℓ ∧ 0 < γ ∧ ℓ ≤ x 0 ∧ ℓ ≤ x 1 ∧
        γ ≤ (a - u₁) * x 4 ∧ γ ≤ (a - u₂) * x 5 ∧ γ ≤ a * x 6 ∧
        γ = a * x 2 - u₁ * x 4 - u₂ * x 5 - h * x 6) :
    ∃ x ∈ feasible.extremePoints ℝ, objective a u₁ u₂ h x = V ∧
      (∀ i, 0 < x i) ∧
      (VertexRepeat.HasRepeat x ∨ VertexRepeat.HasRepeat (VertexRepeat.swap x)) := by
  obtain ⟨x, hx, hvalue⟩ := exists_optimal_vertex ha hu₁ hu₂ hh hne hmax
  obtain ⟨ℓ, γ, hℓ, hγ, ht₁, ht₂, hc₁, hc₂, hp, hrow⟩ := hown x ⟨hx.1, hvalue⟩
  have hpos := coefficients_pos_of_own_floors ha hu₁.le hu₂.le hh.le hx.1
    hℓ hγ ht₁ ht₂ hc₁ hc₂ hp hrow
  exact ⟨x, hx, hvalue, hpos, VertexRepeat.vertex_has_repeat x hx hpos⟩

/-- No finite optimum can satisfy the own-floor premises and strict pair
bounds against every full-repeat witness for both secondary types. -/
theorem no_optimal_face_with_strict_repeat {a u₁ u₂ h V : ℝ}
    (ha : 0 < a) (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hh : 0 < h)
    (hne : (optimalFace a u₁ u₂ h V).Nonempty)
    (hmax : ∀ x ∈ feasible, objective a u₁ u₂ h x ≤ V)
    (hown : ∀ x ∈ optimalFace a u₁ u₂ h V, ∃ ℓ γ : ℝ,
      1 / 2 < ℓ ∧ 0 < γ ∧ ℓ ≤ x 0 ∧ ℓ ≤ x 1 ∧
        γ ≤ (a - u₁) * x 4 ∧ γ ≤ (a - u₂) * x 5 ∧ γ ≤ a * x 6 ∧
        γ = a * x 2 - u₁ * x 4 - u₂ * x 5 - h * x 6)
    (hstrict : ∀ x ∈ optimalFace a u₁ u₂ h V, ∀ y : Coefficients,
      (y = x ∨ y = VertexRepeat.swap x) → ∀ D : ℝ, 0 ≤ D →
        (∀ r b n : ℕ, b ≤ 1 →
          Repeat.oneSidedCharge (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) D r b n ≤ 1) →
        x 3 < D) : False := by
  obtain ⟨x, hx, hvalue, _, hrepeat⟩ := exists_optimal_vertex_repeat ha hu₁ hu₂ hh hne hmax hown
  rcases hrepeat with ⟨D, hD, hc, htests⟩ | ⟨D, hD, hc, htests⟩
  · exact (not_lt_of_ge hc) (hstrict x ⟨hx.1, hvalue⟩ x (Or.inl rfl) D hD htests)
  · have hc' : D ≤ x 3 := by simpa [VertexRepeat.swap] using hc
    exact (not_lt_of_ge hc')
      (hstrict x ⟨hx.1, hvalue⟩ (VertexRepeat.swap x) (Or.inr rfl) D hD htests)

end Erdos1017.TwoHeadVertexComparison

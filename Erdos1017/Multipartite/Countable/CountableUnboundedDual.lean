module

public import Erdos1017.Multipartite.Dust.DustUnboundedDual
public import Erdos1017.Multipartite.Countable.CountableMassVariation

/-!
# Bounded homogeneous tests without a unit box

A uniform absolute coefficient bound gives finite-prefix convergence of the
objective without unit-box or head-sign premises, so every uniformly bounded
homogeneous array passing all anchored tests bounds the countable value and
licenses raw-mass competitors at the selected density, even with negative anchor
charges.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators
open Filter

/-- A uniform absolute coefficient bound gives actual finite-prefix
convergence without any unit-box or head-sign premise. -/
theorem objective_restrict_tendsto_of_bound (D : Coefficients) (B : ℝ) (hB : 0 ≤ B)
    (hD : ∀ c, ‖D c‖ ≤ B) (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (s : ℝ) :
    Tendsto (fun n => MultipartiteDust.objective (fun i : Fin n => p i.val) s (restrict n D))
      atTop (nhds (objective p s D)) := by
  have hh : Summable (fun i => head D i * p i) := by
    apply (hsum.mul_left B).of_norm_bounded
    intro i
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp i), head] using
      mul_le_mul_of_nonneg_right (hD (.inl i)) (hp i)
  have hi : Summable (fun i => incident D i * p i) := by
    apply (hsum.mul_left B).of_norm_bounded
    intro i
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp i), incident] using
      mul_le_mul_of_nonneg_right (hD (.inr (.inr (.inl i)))) (hp i)
  have hpair : Summable (fun z : ℕ × ℕ =>
      if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) := by
    apply ((hsum.mul_of_nonneg hsum hp hp).mul_left B).of_norm_bounded
    intro z
    split_ifs
    · simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp _), pair, mul_assoc] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hD (.inr (.inl (z.1, z.2)))) (hp z.1)) (hp z.2)
    · simp only [norm_zero]
      exact mul_nonneg hB (mul_nonneg (hp _) (hp _))
  have hrect : Tendsto (fun n : ℕ => (Finset.range n) ×ˢ (Finset.range n)) atTop atTop :=
    tendsto_finsetProd_atTop.comp (tendsto_atTop_diagonal.comp tendsto_finset_range)
  have hpairs := hpair.hasSum.comp hrect
  have h := (((hh.hasSum.tendsto_sum_nat.add_const (linear D * s)).sub hpairs).sub
    (hi.mul_right s).hasSum.tendsto_sum_nat).sub_const (penalty D * s ^ 2 / 2)
  convert h using 1
  · funext n
    simp only [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.linear,
      MultipartiteDust.pair, MultipartiteDust.incident, MultipartiteDust.penalty, restrict,
      head, pair, incident, linear, penalty, Function.comp_def, Finset.sum_product,
      ← Fin.sum_univ_eq_sum_range]
    congr 3
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.lt_def]
    split_ifs <;> simp
  · rfl

/-- Every uniformly bounded homogeneous array passing all anchored tests
bounds the actual countable value. Anchor charges may be negative and all
magnitudes may exceed one; the internal dust penalty is nonnegative. -/
theorem objective_le_value_of_bounded_tests (D : Coefficients) (B : ℝ) (hB : 0 ≤ B)
    (hD : ∀ c, ‖D c‖ ≤ B) (htest : ∀ n X k, MultipartiteDust.charge (restrict n D) X k ≤ 1)
    (hpen : 0 ≤ penalty D) (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) : objective p s D ≤ value p s := by
  apply le_of_tendsto (objective_restrict_tendsto_of_bound D B hB hD p hp hsum s)
  apply Eventually.of_forall
  intro n
  exact (MultipartiteDust.objective_le_value_of_tests (restrict n D) (htest n) hpen
    (fun i : Fin n => p i.val) (fun i => ⟨hp i.val, hp1 i.val⟩) s hs).trans
      (finite_value_le_value p hp hsum s n)

/-- Unrestricted bounded homogeneous tests also license actual raw-mass
competitors at the selected density, including negative anchor charges. -/
theorem physicalObjective_le_density_maximum_of_bounded_tests {ε : ℝ} (hε : 0 < ε)
    {x : MultipartiteProfiles.Profile}
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε ≤ MultipartiteProfiles.normalizedValue x)
    (D : Coefficients) (B : ℝ) (hB : 0 ≤ B) (hD : ∀ c, ‖D c‖ ≤ B)
    (htest : ∀ n X k, MultipartiteDust.charge (restrict n D) X k ≤ 1) (hpen : 0 ≤ penalty D)
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ a)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s)
    (hmoment : a ^ 2 + (∑' i, (p i) ^ 2) = 2 * ε * (a + s + ∑' i, p i) ^ 2) :
    physicalObjective a p s D / (a + s + ∑' i, p i) ^ 2 ≤
      MultipartiteProfiles.normalizedValue x := by
  have hM : 0 < a + s + ∑' i, p i := by
    have hpSum : 0 ≤ ∑' i, p i := tsum_nonneg hp
    linarith
  have hp' : ∀ i, 0 ≤ p i / a := fun i => div_nonneg (hp i) ha.le
  have hp1' : ∀ i, p i / a ≤ 1 := fun i => (div_le_one ha).mpr (hp1 i)
  have hmoment' : 1 + (∑' i, (p i / a) ^ 2) =
      2 * ε * (1 + (s / a + ∑' i, p i / a)) ^ 2 := by
    simp_rw [div_pow, tsum_div_const]
    field_simp
    nlinarith [hmoment]
  have hobj := objective_le_value_of_bounded_tests D B hB hD htest hpen
    (fun i => p i / a) hp' hp1' (hsum.div_const a) (s / a) (div_nonneg hs ha.le)
  have hden : 0 < (1 + (s / a + ∑' i, p i / a)) ^ 2 := by
    have hsum0 : 0 ≤ ∑' i, p i / a := tsum_nonneg hp'
    have hs0 : 0 ≤ s / a := div_nonneg hs ha.le
    positivity
  rw [← normalized_physicalObjective a ha p s hM D]
  exact ((div_le_div_iff_of_pos_right hden).mpr hobj).trans
    (MultipartiteProfiles.normalized_value_le_density_maximum hε hmax hxvalue
      (fun i => p i / a) hp' hp1' (hsum.div_const a) (s / a) (div_nonneg hs ha.le) hmoment')

end Erdos1017.MultipartiteCountableDual

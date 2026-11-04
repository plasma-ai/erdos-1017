module

public import Erdos1017.Multipartite.MultipartiteCountableDual
public import Erdos1017.Multipartite.MultipartiteActualDust

/-!
# Finite restrictions of a countable dual

A bounded coefficient array has absolutely summable head, incident and pair
contributions, restrictions of a countable dual converge to its full series
objective, and every feasible countable objective is bounded by the continuous
profile limit.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators
open Filter

/-- A bounded coefficient array has an absolutely summable head contribution. -/
theorem head_summable (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    {D : Coefficients} (hD : D ∈ Set.Icc 0 1) : Summable (fun i => head D i * p i) := by
  apply hsum.of_norm_bounded
  intro i
  unfold head
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hD.1 _) (hp i))]
  exact mul_le_of_le_one_left (hp i) (hD.2 _)

theorem incident_summable (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    {D : Coefficients} (hD : D ∈ Set.Icc 0 1) : Summable (fun i => incident D i * p i) := by
  apply hsum.of_norm_bounded
  intro i
  unfold incident
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hD.1 _) (hp i))]
  exact mul_le_of_le_one_left (hp i) (hD.2 _)

theorem pair_summable (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    {D : Coefficients} (hD : D ∈ Set.Icc 0 1) :
    Summable (fun z : ℕ × ℕ => if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) := by
  apply (hsum.mul_of_nonneg hsum hp hp).of_norm_bounded
  intro z
  split_ifs
  · unfold pair
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hD.1 _) (hp _)) (hp _))]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hD.2 _) (hp _)) (hp _)).trans_eq (by simp)
  · simpa only [norm_zero] using mul_nonneg (hp z.1) (hp z.2)

/-- Actual restrictions of one countable dual converge to its full series objective. -/
theorem objective_restrict_tendsto (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (s : ℝ) {D : Coefficients} (hD : D ∈ Set.Icc 0 1) :
    Tendsto (fun n => MultipartiteDust.objective (fun i : Fin n => p i.val) s (restrict n D))
      atTop (nhds (objective p s D)) := by
  have hh := (head_summable p hp hsum hD).hasSum.tendsto_sum_nat
  have hi := ((incident_summable p hp hsum hD).mul_right s).hasSum.tendsto_sum_nat
  have hrect : Tendsto (fun n : ℕ => (Finset.range n) ×ˢ (Finset.range n)) atTop atTop :=
    tendsto_finsetProd_atTop.comp (tendsto_atTop_diagonal.comp tendsto_finset_range)
  have hpairs := (pair_summable p hp hsum hD).hasSum.comp hrect
  have h := (((hh.add_const (linear D * s)).sub hpairs).sub hi).sub_const (penalty D * s ^ 2 / 2)
  convert h using 1
  · funext n
    simp only [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.linear,
      MultipartiteDust.pair, MultipartiteDust.incident, MultipartiteDust.penalty, restrict,
      head, pair, incident, linear, penalty, Function.comp_def, Finset.sum_product,
      ← Fin.sum_univ_eq_sum_range]
    congr 3
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.lt_def]
    split_ifs <;> simp
  · rfl

/-- Every feasible countable objective is bounded by the continuous profile limit. -/
theorem objective_le_profile_limit {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : Coefficients} (hD : D ∈ feasible) :
    objective x.2 (MultipartiteProfiles.dust x) D ≤ MultipartiteProfiles.limitValue x := by
  apply le_of_tendsto_of_tendsto
    (objective_restrict_tendsto x.2 (fun i => hx.1.1.2 i)
      (MultipartiteProfiles.atoms_summable hx) (MultipartiteProfiles.dust x) hD.1)
    (MultipartiteProfiles.actualDustValue_tendsto hx)
  exact Filter.Eventually.of_forall fun n => MultipartiteDust.objective_le_value
    (fun i : Fin n => x.2 i.val) (MultipartiteProfiles.dust x) (restrict n D)
      (restrict_mem_feasible hD n)

end Erdos1017.MultipartiteCountableDual

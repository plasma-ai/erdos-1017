module

public import Erdos1017.Multipartite.Dust.DustCellSurgery
public import Erdos1017.Multipartite.Dust.CountableDustRowSurgery

/-!
# Dust-cell surgery in the countable model

`prependDustHead` inserts a new independent dust-cell head before all old
countable heads; every anchored clique using it is an old clique with two more
dust points, the twice-dust exterior row is uniformly bounded, and the surgery
has an exact countable and physical objective gain.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Insert a new independent dust-cell head before all old countable heads. -/
def prependDustHead (D : Coefficients) : Coefficients
  | .inl 0 => 2 * linear D - penalty D
  | .inl (j + 1) => head D j
  | .inr (.inl (0, 0)) => 0
  | .inr (.inl (0, k + 1)) => 2 * incident D k
  | .inr (.inl (j + 1, 0)) => 2 * incident D j
  | .inr (.inl (j + 1, k + 1)) => pair D j k
  | .inr (.inr (.inl 0)) => 2 * penalty D
  | .inr (.inr (.inl (j + 1))) => incident D j
  | .inr (.inr (.inr b)) => D (.inr (.inr (.inr b)))

/-- Prepend one physical independent mass to an old head sequence. -/
def prependMass (z : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => z
  | j + 1 => p j

theorem prependMass_nonneg (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (z : ℝ) (hz : 0 ≤ z) :
    ∀ j, 0 ≤ prependMass z p j := by
  intro j
  cases j with
  | zero => exact hz
  | succ j => exact hp j

theorem prependMass_summable (p : ℕ → ℝ) (hsum : Summable p) (z : ℝ) :
    Summable (prependMass z p) := by
  apply (summable_nat_add_iff 1).mp
  exact hsum

theorem prependMass_tsum (p : ℕ → ℝ) (hsum : Summable p) (z : ℝ) :
    (∑' j, prependMass z p j) = z + ∑' j, p j :=
  (prependMass_summable p hsum z).tsum_eq_zero_add

theorem prependMass_square_tsum (p : ℕ → ℝ) (hsum : Summable (fun j => (p j) ^ 2)) (z : ℝ) :
    (∑' j, (prependMass z p j) ^ 2) = z ^ 2 + ∑' j, (p j) ^ 2 := by
  have heq : (fun j => (prependMass z p j) ^ 2) = prependMass (z ^ 2) (fun j => (p j) ^ 2) := by
    funext j
    cases j <;> rfl
  rw [heq, prependMass_tsum _ hsum]

theorem restrict_prependDustHead (D : Coefficients) (n : ℕ) :
    restrict (n + 1) (prependDustHead D) = MultipartiteDust.prependDustHead (restrict n D) := by
  funext c
  rcases c with j | (⟨j, k⟩ | (j | b))
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · refine Fin.cases ?_ (fun k => ?_) k <;> rfl
    · refine Fin.cases ?_ (fun k => ?_) k <;> rfl
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · rfl

/-- Every anchored clique using the new head is an old clique with two
additional dust points, at every finite prefix. -/
theorem prependDustHead_tests {D : Coefficients} (hD : D ∈ feasible) :
    ∀ n X k, MultipartiteDust.charge (restrict n (prependDustHead D)) X k ≤ 1 := by
  intro n X k
  cases n with
  | zero =>
    have heq : restrict 0 (prependDustHead D) = restrict 0 D := by
      funext c
      rcases c with j | (⟨j, l⟩ | (j | b))
      · exact Fin.elim0 j
      · exact Fin.elim0 j
      · exact Fin.elim0 j
      · rfl
    rw [heq]
    exact hD.2 0 X k
  | succ n =>
    rw [restrict_prependDustHead]
    exact MultipartiteDust.prependDustHead_tests _ (hD.2 n) X k

/-- The actual twice-dust exterior row is uniformly bounded outside the
unit coefficient box. -/
theorem prependDustHead_bound {D : Coefficients} (hD : D ∈ feasible) :
    ∀ c, ‖prependDustHead D c‖ ≤ 3 := by
  have hc (c : Coordinate) : 0 ≤ D c ∧ D c ≤ 1 := ⟨hD.1.1 c, hD.1.2 c⟩
  intro c
  rw [Real.norm_eq_abs, abs_le]
  rcases c with j | (⟨j, k⟩ | (j | b))
  · cases j with
    | zero =>
      dsimp only [prependDustHead, linear, penalty]
      constructor <;> linarith [hc (.inr (.inr (.inr false))), hc (.inr (.inr (.inr true)))]
    | succ j =>
      dsimp only [prependDustHead, head]
      constructor <;> linarith [hc (.inl j)]
  · cases j with
    | zero =>
      cases k with
      | zero => simp [prependDustHead]
      | succ k =>
        dsimp only [prependDustHead, incident]
        constructor <;> linarith [hc (.inr (.inr (.inl k)))]
    | succ j =>
      cases k with
      | zero =>
        dsimp only [prependDustHead, incident]
        constructor <;> linarith [hc (.inr (.inr (.inl j)))]
      | succ k =>
        dsimp only [prependDustHead, pair]
        constructor <;> linarith [hc (.inr (.inl (j, k)))]
  · cases j with
    | zero =>
      dsimp only [prependDustHead, penalty]
      constructor <;> linarith [hc (.inr (.inr (.inr true)))]
    | succ j =>
      dsimp only [prependDustHead, incident]
      constructor <;> linarith [hc (.inr (.inr (.inl j)))]
  · dsimp only [prependDustHead]
    constructor <;> linarith [hc (.inr (.inr (.inr b)))]

/-- The new independent dust cell has the exact countable objective gain. -/
theorem prependDustHead_gain {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (z s : ℝ) (hz : 0 ≤ z) :
    objective (prependMass z p) (s - z) (prependDustHead D) = objective p s D +
      z * (dustRow p s D - penalty D) + 3 * penalty D * z ^ 2 / 2 := by
  have hleft := (objective_restrict_tendsto_of_bound (prependDustHead D) 3 (by norm_num)
    (prependDustHead_bound hD) (prependMass z p) (prependMass_nonneg p hp z hz)
    (prependMass_summable p hsum z) (s - z)).comp (Filter.tendsto_add_atTop_nat 1)
  have hrow : Filter.Tendsto (fun n => linear D -
      (∑ j ∈ Finset.range n, incident D j * p j) - penalty D * s)
      Filter.atTop (nhds (dustRow p s D)) :=
    (tendsto_const_nhds.sub (incident_summable p hp hsum hD.1).hasSum.tendsto_sum_nat).sub_const
      (penalty D * s)
  have hright := ((objective_restrict_tendsto p hp hsum s hD.1).add
    ((hrow.sub_const (penalty D)).const_mul z)).add_const (3 * penalty D * z ^ 2 / 2)
  apply tendsto_nhds_unique hleft
  apply Filter.Tendsto.congr' _ hright
  apply Filter.Eventually.of_forall
  intro n
  have hmass : (fun j : Fin (n + 1) => prependMass z p j.val) =
      Fin.cons z (fun j : Fin n => p j.val) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  dsimp only [Function.comp_def]
  rw [restrict_prependDustHead, hmass, MultipartiteDust.prependDustHead_gain]
  have hsumFin := Fin.sum_univ_eq_sum_range (fun j => incident D j * p j) n
  simp only [MultipartiteDust.linear, MultipartiteDust.penalty, MultipartiteDust.incident, restrict]
  rw [← hsumFin]
  rfl

/-- The changed anchor row is explicit when a dust cell becomes an
independent head with twice the old dust exterior row. -/
theorem anchorRow_prependDustHead {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (z s : ℝ) :
    anchorRow (prependMass z p) (s - z) (prependDustHead D) =
      anchorRow p s D + z * (linear D - penalty D) := by
  have hseries : Summable (fun j => head (prependDustHead D) j * prependMass z p j) := by
    apply (summable_nat_add_iff 1).mp
    exact head_summable p hp hsum hD.1
  have hh := hseries.tsum_eq_zero_add
  unfold anchorRow
  rw [hh]
  simp only [head, linear, penalty, prependDustHead, prependMass]
  ring

/-- The dust-cell surgery has an exact physical gain at any anchor mass,
including an old-head/anchor correction. -/
theorem physicalObjective_prependDustHead_gain {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (a z s : ℝ) (hz : 0 ≤ z) :
    physicalObjective a (prependMass z p) (s - z) (prependDustHead D) = physicalObjective a p s D +
      z * (dustRow p s D - penalty D + (a - 1) * (linear D - penalty D)) +
        3 * penalty D * z ^ 2 / 2 := by
  simp only [physicalObjective_eq_objective]
  rw [prependDustHead_gain hD p hp hsum z s hz, anchorRow_prependDustHead hD p hp hsum z s]
  ring

end Erdos1017.MultipartiteCountableDual

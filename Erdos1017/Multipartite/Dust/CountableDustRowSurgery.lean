module

public import Erdos1017.Multipartite.Dust.DustRowSurgery
public import Erdos1017.Multipartite.Countable.CountableUnboundedDual
public import Erdos1017.Multipartite.Dust.CountableDustVariation

/-!
# Dust-row surgery in the countable model

`addDustRow` adds the dust row to one countable independent head; the surgery
obeys every anchored count test, stays uniformly bounded despite negative anchor
charges and coefficients above one, and has an exact gain by finite-prefix
limits, so fixed-profile optimality forces the dust-incidence bound.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Add the actual dust row to one countable independent head. -/
def addDustRow (D : Coefficients) (i : ℕ) : Coefficients
  | .inl j => if j = i then head D j + linear D - incident D i else head D j
  | .inr (.inl (j, k)) => pair D j k + if j = i then incident D k else if k = i then incident D j else 0
  | .inr (.inr (.inl j)) => if j = i then incident D j + penalty D else incident D j
  | .inr (.inr (.inr b)) => D (.inr (.inr (.inr b)))

theorem restrict_addDustRow (D : Coefficients) (i n : ℕ) (hi : i < n) :
    restrict n (addDustRow D i) = MultipartiteDust.addDustRow (restrict n D) ⟨i, hi⟩ := by
  funext c
  rcases c with j | (⟨j, k⟩ | (j | b))
  · simp [restrict, head, linear, incident, addDustRow, MultipartiteDust.addDustRow,
      MultipartiteDust.head, MultipartiteDust.linear, MultipartiteDust.incident, Fin.ext_iff]
  · simp [restrict, pair, addDustRow, MultipartiteDust.addDustRow,
      MultipartiteDust.pair, MultipartiteDust.incident, Fin.ext_iff]
  · simp [restrict, incident, penalty, addDustRow, MultipartiteDust.addDustRow,
      MultipartiteDust.incident, MultipartiteDust.penalty, Fin.ext_iff]
  · cases b <;> rfl

/-- The actual surgery obeys every anchored count test, including prefixes
which do not yet contain the modified head. -/
theorem addDustRow_tests {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    ∀ n X k, MultipartiteDust.charge (restrict n (addDustRow D i)) X k ≤ 1 := by
  intro n X k
  by_cases hi : i < n
  · rw [restrict_addDustRow D i n hi]
    exact MultipartiteDust.addDustRow_tests _ (hD.2 n) _ X k
  · have hne (j : Fin n) : j.val ≠ i := by omega
    have heq : restrict n (addDustRow D i) = restrict n D := by
      funext c
      rcases c with j | (⟨j, l⟩ | (j | b)) <;>
        simp [restrict, addDustRow, head, pair, incident, hne]
    rw [heq]
    exact hD.2 n X k

/-- The changed array is uniformly bounded although it can have negative
anchor charges and coefficients larger than one. -/
theorem addDustRow_bound {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    ∀ c, ‖addDustRow D i c‖ ≤ 3 := by
  have hc (c : Coordinate) : 0 ≤ D c ∧ D c ≤ 1 := ⟨hD.1.1 c, hD.1.2 c⟩
  intro c
  rw [Real.norm_eq_abs, abs_le]
  rcases c with j | (⟨j, k⟩ | (j | b))
  · dsimp only [addDustRow, head, linear, incident]
    split_ifs <;> constructor <;>
      linarith [hc (.inl j), hc (.inr (.inr (.inr false))), hc (.inr (.inr (.inl i)))]
  · dsimp only [addDustRow, pair, incident]
    split_ifs <;> constructor <;>
      linarith [hc (.inr (.inl (j, k))), hc (.inr (.inr (.inl j))), hc (.inr (.inr (.inl k)))]
  · dsimp only [addDustRow, incident, penalty]
    split_ifs <;> constructor <;>
      linarith [hc (.inr (.inr (.inl j))), hc (.inr (.inr (.inr true)))]
  · dsimp only [addDustRow]
    constructor <;> linarith [hc (.inr (.inr (.inr b)))]

/-- The exact row-surgery gain survives every countable exterior
interaction by absolutely convergent finite-prefix limits. -/
theorem addDustRow_objective {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (s : ℝ) (i : ℕ) :
    objective p s (addDustRow D i) = objective p s D +
      p i * (dustRow p s D - incident D i * (1 - p i)) := by
  have hleft := objective_restrict_tendsto_of_bound (addDustRow D i) 3 (by norm_num)
    (addDustRow_bound hD i) p hp hsum s
  have hrow : Filter.Tendsto (fun n => linear D -
      (∑ j ∈ Finset.range n, incident D j * p j) - penalty D * s)
      Filter.atTop (nhds (dustRow p s D)) :=
    (tendsto_const_nhds.sub (incident_summable p hp hsum hD.1).hasSum.tendsto_sum_nat).sub_const
      (penalty D * s)
  have hright := (objective_restrict_tendsto p hp hsum s hD.1).add
    ((hrow.sub_const (incident D i * (1 - p i))).const_mul (p i))
  apply tendsto_nhds_unique hleft
  apply Filter.Tendsto.congr' _ hright
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  rw [restrict_addDustRow D i n hn, MultipartiteDust.addDustRow_objective]
  have hsumFin := Fin.sum_univ_eq_sum_range (fun j => incident D j * p j) n
  simp only [MultipartiteDust.linear, MultipartiteDust.penalty, MultipartiteDust.incident, restrict]
  rw [← hsumFin]
  rfl

/-- Actual fixed-profile optimality forces the source dust-incidence bound.
Its competitor has all count tests and a proved bound, not box feasibility. -/
theorem incident_floor_at_optimum {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) :
    dustRow x.2 (MultipartiteProfiles.dust x) D ≤ incident D i * (1 - x.2 i) := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx
  have hpen : 0 ≤ penalty (addDustRow D i) := hD.1.1 _
  have h := objective_le_value_of_bounded_tests (addDustRow D i) 3 (by norm_num)
    (addDustRow_bound hD i) (addDustRow_tests hD i) hpen x.2 hp hx.1.2.2 hsum
    (MultipartiteProfiles.dust x) (MultipartiteProfiles.dust_nonneg hx)
  rw [addDustRow_objective hD x.2 hp hsum _ i, value_eq_profile_limit hx, ← hopt] at h
  have hprod : x.2 i * (dustRow x.2 (MultipartiteProfiles.dust x) D - incident D i * (1 - x.2 i)) ≤ 0 := by
    linarith
  have hnonpos := nonpos_of_mul_nonpos_right hprod hi
  exact sub_nonpos.mp hnonpos

end Erdos1017.MultipartiteCountableDual

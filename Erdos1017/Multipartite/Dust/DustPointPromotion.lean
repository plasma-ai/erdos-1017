module

public import Erdos1017.Multipartite.Dust.CountableDustCellSurgery
public import Erdos1017.Multipartite.Countable.CountablePhysicalCompletion

/-!
# Promoting a dust type to an independent head

Promote one old dust type to a new independent head, retaining its exterior row.
Every finite count test and the unit coefficient box are preserved, and the
deleted internal dust pairs give the exact gain.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

def prependDustPoint {m : ℕ} (C : Coefficients m) : Coefficients (m + 1)
  | .inl j => Fin.cases (linear C) (head C) j
  | .inr (.inl (j, k)) => Fin.cases (Fin.cases 0 (incident C) k)
      (fun j => Fin.cases (incident C j) (fun k => pair C j k) k) j
  | .inr (.inr (.inl j)) => Fin.cases (penalty C) (incident C) j
  | .inr (.inr (.inr b)) => C (.inr (.inr (.inr b)))

theorem prependDustPoint_objective {m : ℕ} (C : Coefficients m)
    (p : Fin m → ℝ) (z s : ℝ) :
    objective (Fin.cons z p) s (prependDustPoint C) = objective p s C +
      z * (linear C - (∑ j, incident C j * p j) - penalty C * s) := by
  simp only [objective, head, pair, incident, linear, penalty, prependDustPoint,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ,
    Fin.succ_pos, Fin.succ_lt_succ_iff, Fin.not_lt_zero, ↓reduceIte,
    zero_mul, mul_zero, zero_add, mul_one]
  have hrow : (∑ j, C (.inr (.inr (.inl j))) * z * p j) =
      z * ∑ j, C (.inr (.inr (.inl j))) * p j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrow]
  ring

theorem prependDustPoint_gain {m : ℕ} (C : Coefficients m)
    (p : Fin m → ℝ) (z s : ℝ) :
    objective (Fin.cons z p) (s - z) (prependDustPoint C) =
      objective p s C + penalty C * z ^ 2 / 2 := by
  rw [prependDustPoint_objective, objective_dust_split, objective_dust_split]
  ring

/-- A selected promoted head contributes exactly one additional old dust point. -/
theorem prependDustPoint_charge {m : ℕ} (C : Coefficients m)
    (X : Selector.Selection (m + 1)) (k : ℕ) :
    charge (prependDustPoint C) X k =
      charge C (fun j => X j.succ) (k + if X 0 then 1 else 0) := by
  have hbits : (fun j => Selector.bit (X j)) =
      Fin.cons (Selector.bit (X 0)) (fun j => Selector.bit (X j.succ)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  rw [DustCellBridge.charge_eq_objective, hbits, prependDustPoint_objective,
    DustCellBridge.charge_eq_objective]
  simp only [penalty, prependDustPoint]
  cases hX : X 0
  · simp [Selector.bit]
  · simp only [↓reduceIte, Selector.bit]
    rw [objective_dust_split, objective_dust_split]
    push_cast
    unfold penalty
    ring

/-- The promoted array retains the actual coefficient box and every count test. -/
theorem prependDustPoint_feasible {m : ℕ} {C : Coefficients m}
    (hC : C ∈ feasible m) : prependDustPoint C ∈ feasible (m + 1) := by
  have hb (c : Coordinate (m + 1)) :
      0 ≤ prependDustPoint C c ∧ prependDustPoint C c ≤ 1 := by
    rcases c with j | (⟨j, k⟩ | (j | b))
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨hC.1.1 _, hC.1.2 _⟩
      · exact ⟨hC.1.1 _, hC.1.2 _⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · refine Fin.cases ?_ (fun k => ?_) k
        · exact ⟨le_rfl, zero_le_one⟩
        · exact ⟨hC.1.1 _, hC.1.2 _⟩
      · refine Fin.cases ?_ (fun k => ?_) k
        · exact ⟨hC.1.1 _, hC.1.2 _⟩
        · exact ⟨hC.1.1 _, hC.1.2 _⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨hC.1.1 _, hC.1.2 _⟩
      · exact ⟨hC.1.1 _, hC.1.2 _⟩
    · exact ⟨hC.1.1 _, hC.1.2 _⟩
  refine ⟨⟨fun c => (hb c).1, fun c => (hb c).2⟩, ?_⟩
  intro X k
  rw [prependDustPoint_charge]
  exact hC.2 _ _

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

def prependDustPoint (D : Coefficients) : Coefficients
  | .inl 0 => linear D
  | .inl (j + 1) => head D j
  | .inr (.inl (0, 0)) => 0
  | .inr (.inl (0, k + 1)) => incident D k
  | .inr (.inl (j + 1, 0)) => incident D j
  | .inr (.inl (j + 1, k + 1)) => pair D j k
  | .inr (.inr (.inl 0)) => penalty D
  | .inr (.inr (.inl (j + 1))) => incident D j
  | .inr (.inr (.inr b)) => D (.inr (.inr (.inr b)))

theorem restrict_prependDustPoint (D : Coefficients) (n : ℕ) :
    restrict (n + 1) (prependDustPoint D) =
      MultipartiteDust.prependDustPoint (restrict n D) := by
  funext c
  rcases c with j | (⟨j, k⟩ | (j | b))
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · refine Fin.cases ?_ (fun k => ?_) k <;> rfl
    · refine Fin.cases ?_ (fun k => ?_) k <;> rfl
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · rfl

theorem prependDustPoint_feasible {D : Coefficients} (hD : D ∈ feasible) :
    prependDustPoint D ∈ feasible := by
  apply feasible_of_all_restrict
  intro n
  cases n with
  | zero =>
    have heq : restrict 0 (prependDustPoint D) = restrict 0 D := by
      funext c
      rcases c with j | (⟨j, k⟩ | (j | b))
      · exact Fin.elim0 j
      · exact Fin.elim0 j
      · exact Fin.elim0 j
      · rfl
    rw [heq]
    exact restrict_mem_feasible hD 0
  | succ n =>
    rw [restrict_prependDustPoint]
    exact MultipartiteDust.prependDustPoint_feasible (restrict_mem_feasible hD n)

/-- The deleted internal dust pairs give the same exact gain with countably
many exterior heads. Actual finite-prefix objectives justify the limit. -/
theorem prependDustPoint_gain {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p)
    (z s : ℝ) (hz : 0 ≤ z) :
    objective (prependMass z p) (s - z) (prependDustPoint D) =
      objective p s D + penalty D * z ^ 2 / 2 := by
  have hleft := (objective_restrict_tendsto (prependMass z p)
    (prependMass_nonneg p hp z hz) (prependMass_summable p hsum z) (s - z)
    (prependDustPoint_feasible hD).1).comp (Filter.tendsto_add_atTop_nat 1)
  have hright := (objective_restrict_tendsto p hp hsum s hD.1).add_const
    (penalty D * z ^ 2 / 2)
  apply tendsto_nhds_unique hleft
  apply Filter.Tendsto.congr' _ hright
  apply Filter.Eventually.of_forall
  intro n
  have hmass : (fun j : Fin (n + 1) => prependMass z p j.val) =
      Fin.cons z (fun j : Fin n => p j.val) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  dsimp only [Function.comp_def]
  rw [restrict_prependDustPoint, hmass, MultipartiteDust.prependDustPoint_gain]
  rfl

end Erdos1017.MultipartiteCountableDual

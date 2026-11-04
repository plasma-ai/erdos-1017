module

public import Erdos1017.Multipartite.Countable.CountableRepeatPenalty
public import Erdos1017.Multipartite.Dust.DustTypeCompletion

/-!
# Completing a countable head into dust

`completeType` completes some mass of one countable head and averages it with
dust, retaining its possible independent atom; the least-repeat penalty makes
the completion feasible for every integer count test, and the objective loss is
the same as in the finite model, by limits of finite-prefix identities.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Complete some mass of one countable head and average it with old dust,
retaining its possible independent atom and all other head coefficients. -/
def completeType (D : Coefficients) (i : ℕ) (P : ℝ) (q : Fin 2 → ℝ) : Coefficients
  | .inl j => head D j
  | .inr (.inl (j, k)) => pair D j k
  | .inr (.inr (.inl j)) =>
      (if j = i then P else -MultipartiteCountableMeasure.kernel D
        (.inl (some i)) (.inl (some j))) * q 0 + incident D j * q 1
  | .inr (.inr (.inr false)) => head D i * q 0 + linear D * q 1
  | .inr (.inr (.inr true)) =>
      P * q 0 ^ 2 + 2 * incident D i * q 0 * q 1 + penalty D * q 1 ^ 2

theorem restrict_completeType (D : Coefficients) (i : ℕ) (P : ℝ) (q : Fin 2 → ℝ)
    (n : ℕ) (hi : i < n) :
    restrict n (completeType D i P q) = MultipartiteDust.completeType
      (restrict n D) ⟨i, hi⟩ P q := by
  funext c
  rcases c with j | (⟨j, k⟩ | (j | b))
  · rfl
  · rfl
  · have hk : (DustCellRestriction.headDual (restrict n D)).beta ⟨i, hi⟩ j =
        MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j.val)) := by
      exact (MultipartiteCountableMeasure.kernel_embed D n
        (.inl (some ⟨i, hi⟩)) (.inl (some j))).symm
    simp only [restrict, incident, completeType, MultipartiteDust.completeType, hk,
      Fin.ext_iff, MultipartiteDust.incident]
  · cases b <;> rfl

/-- Every coefficient and every test is visible in a finite prefix. -/
theorem feasible_of_all_restrict (D : Coefficients)
    (hD : ∀ n, restrict n D ∈ MultipartiteDust.feasible n) : D ∈ feasible := by
  have hb (c : Coordinate) : 0 ≤ D c ∧ D c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | (i | b))
    · exact ⟨(hD (i + 1)).1.1 (.inl ⟨i, by omega⟩),
        (hD (i + 1)).1.2 (.inl ⟨i, by omega⟩)⟩
    · let n := max i j + 1
      have hi : i < n := by dsimp [n]; omega
      have hj : j < n := by dsimp [n]; omega
      exact ⟨(hD n).1.1 (.inr (.inl (⟨i, hi⟩, ⟨j, hj⟩))),
        (hD n).1.2 (.inr (.inl (⟨i, hi⟩, ⟨j, hj⟩)))⟩
    · exact ⟨(hD (i + 1)).1.1 (.inr (.inr (.inl ⟨i, by omega⟩))),
        (hD (i + 1)).1.2 (.inr (.inr (.inl ⟨i, by omega⟩)))⟩
    · exact ⟨(hD 0).1.1 (.inr (.inr (.inr b))), (hD 0).1.2 (.inr (.inr (.inr b)))⟩
  exact ⟨⟨fun c => (hb c).1, fun c => (hb c).2⟩, fun n => (hD n).2⟩

/-- The actual least-repeat penalty licenses partial completion into dust.
All averaged coefficients and every integer count test are proved feasible. -/
theorem completeType_feasible {D : Coefficients} (hD : D ∈ feasible) (i : ℕ)
    (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1) :
    completeType D i (repeatPenalty D i) q ∈ feasible := by
  have hP : 0 ≤ repeatPenalty D i ∧ repeatPenalty D i ≤ 1 :=
    ⟨repeatPenalty_nonneg hD i, (repeatPenalty_le_head hD i).trans (hD.1.2 _)⟩
  apply feasible_of_all_restrict
  intro n
  let N := max n (i + 1)
  have hi : i < N := by dsimp [N]; omega
  have hN : restrict N (completeType D i (repeatPenalty D i) q) ∈
      MultipartiteDust.feasible N := by
    rw [restrict_completeType D i _ q N hi]
    refine ⟨MultipartiteDust.completeType_box (restrict N D) (restrict_mem_feasible hD N)
      ⟨i, hi⟩ _ hP q hq₀ hq, ?_⟩
    apply MultipartiteDust.completeType_tests _ _ _ _ q hq₀ hq
    intro X hX r d
    exact repeatPenalty_test hD ⟨N, hi, X, hX, d⟩ r
  exact restrict_feasible_of_le _ hN (Nat.le_max_left _ _)

/-- Completing mass of one type has the same exact objective loss in the
countable model. The proof takes limits of actual finite-prefix identities. -/
theorem completeType_loss {D : Coefficients} (hD : D ∈ feasible) (i : ℕ)
    (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (hpi : p i = 0)
    (x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    objective (Function.update p i (x + s * q 0)) (s * q 1) D -
      objective (Function.update p i x) s (completeType D i (repeatPenalty D i) q) =
        repeatPenalty D i * (x * (s * q 0) + (s * q 0) ^ 2 / 2) := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) : ∀ j, 0 ≤ Function.update p i y j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hy
    · simpa [Function.update_of_ne, hj] using hp j
  have hold := objective_restrict_tendsto (Function.update p i (x + s * q 0))
    (hnonneg _ (add_nonneg hx (mul_nonneg hs (hq₀ 0))))
    (hsum.update i _) (s * q 1) hD.1
  have hnew := objective_restrict_tendsto (Function.update p i x) (hnonneg _ hx)
    (hsum.update i _) s (completeType_feasible hD i q hq₀ hq).1
  apply tendsto_nhds_unique (hold.sub hnew)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  have hup (y : ℝ) : (fun j : Fin n => Function.update p i y j.val) =
      Function.update (fun j : Fin n => p j.val) ⟨i, hn⟩ y := by
    funext j
    by_cases hj : j.val = i
    · have hji : j = ⟨i, hn⟩ := Fin.ext hj
      subst j
      simp
    · have hji : j ≠ ⟨i, hn⟩ := fun h => hj (congrArg Fin.val h)
      simp [Function.update_of_ne, hj, hji]
  rw [hup, hup, restrict_completeType D i _ q n hn]
  exact (MultipartiteDust.completeType_loss (restrict n D) ⟨i, hn⟩ _ q
    (fun j : Fin n => p j.val) hpi x s).symm

end Erdos1017.MultipartiteCountableDual

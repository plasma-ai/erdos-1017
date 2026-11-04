module

public import Erdos1017.Multipartite.MultipartiteCountableRestriction

/-!
# Extending a finite dual by zero heads

`extendZero` places zero coefficients on omitted independent heads while
retaining the dust coefficients; feasibility of the countable extension is
constructed from the finite dual and its objective equals the finite objective.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Zero coefficients on omitted independent heads give a countable extension.
The genuine dust coefficients are retained. -/
def extendZero {m : ℕ} (D : MultipartiteDust.Coefficients m) : Coefficients
  | .inl i => if hi : i < m then MultipartiteDust.head D ⟨i, hi⟩ else 0
  | .inr (.inl (i, j)) => if hi : i < m then
      if hj : j < m then MultipartiteDust.pair D ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0
  | .inr (.inr (.inl i)) => if hi : i < m then MultipartiteDust.incident D ⟨i, hi⟩ else 0
  | .inr (.inr (.inr b)) => D (.inr (.inr (.inr b)))

theorem restrict_extendZero {m : ℕ} (D : MultipartiteDust.Coefficients m) :
    restrict m (extendZero D) = D := by
  funext c
  rcases c with i | (⟨i, j⟩ | (i | b)) <;>
    simp [restrict, extendZero, head, pair, incident, MultipartiteDust.head,
      MultipartiteDust.pair, MultipartiteDust.incident]

theorem removeLast_restrict (D : Coefficients) (n : ℕ) :
    MultipartiteDust.removeHead (Fin.last n) (restrict (n + 1) D) = restrict n D := by
  funext c
  rcases c with i | (⟨i, j⟩ | (i | b))
  all_goals simp [MultipartiteDust.removeHead, MultipartiteDust.head, MultipartiteDust.pair,
    MultipartiteDust.incident, MultipartiteDust.linear, MultipartiteDust.penalty,
    restrict, head, pair, incident]
  cases b <;> rfl

/-- Prefix feasibility descends by deleting the final head. -/
theorem restrict_feasible_of_le (D : Coefficients) {n : ℕ}
    (hn : restrict n D ∈ MultipartiteDust.feasible n) {k : ℕ} (hkn : k ≤ n) :
    restrict k D ∈ MultipartiteDust.feasible k := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
    subst k
    exact hn
  | succ n ih =>
    by_cases hk : k = n + 1
    · subst k
      exact hn
    · apply ih _ (by omega)
      rw [← removeLast_restrict D n]
      exact MultipartiteDust.removeHead_feasible (Fin.last n) _ hn

/-- Above the original head count, each additional prefix slot is a zero head. -/
theorem restrict_extendZero_succ {m : ℕ} (D : MultipartiteDust.Coefficients m)
    (n : ℕ) (hmn : m ≤ n) :
    restrict (n + 1) (extendZero D) =
      MultipartiteDust.insertHead (Fin.last n) (restrict n (extendZero D)) := by
  funext c
  rcases c with i | (⟨i, j⟩ | (i | b))
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [restrict, head, extendZero, MultipartiteDust.insertHead, Nat.not_lt.mpr hmn]
    · simp [restrict, head, extendZero, MultipartiteDust.insertHead, MultipartiteDust.head]
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [restrict, pair, extendZero, MultipartiteDust.insertHead, Nat.not_lt.mpr hmn]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [restrict, pair, extendZero, MultipartiteDust.insertHead, Nat.not_lt.mpr hmn]
      · simp [restrict, pair, extendZero, MultipartiteDust.insertHead, MultipartiteDust.pair]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [restrict, incident, extendZero, MultipartiteDust.insertHead, Nat.not_lt.mpr hmn]
    · simp [restrict, incident, extendZero, MultipartiteDust.insertHead, MultipartiteDust.incident]
  · cases b <;> rfl

/-- Feasibility of the countable extension is constructed from the finite dual. -/
theorem extendZero_feasible {m : ℕ} {D : MultipartiteDust.Coefficients m}
    (hD : D ∈ MultipartiteDust.feasible m) : extendZero D ∈ feasible := by
  have hprefix (n : ℕ) : restrict n (extendZero D) ∈ MultipartiteDust.feasible n := by
    by_cases hmn : m ≤ n
    · induction n, hmn using Nat.le_induction with
      | base => simpa only [restrict_extendZero] using hD
      | @succ n hmn ih =>
        rw [restrict_extendZero_succ D n hmn]
        exact MultipartiteDust.insertHead_feasible (Fin.last n) _ ih
    · exact restrict_feasible_of_le _ (by simpa only [restrict_extendZero] using hD)
        (Nat.le_of_lt (Nat.lt_of_not_ge hmn))
  refine ⟨⟨?_, ?_⟩, fun n => (hprefix n).2⟩
  · intro c
    rcases c with i | (⟨i, j⟩ | (i | b)) <;> simp only [extendZero]
    all_goals (try split_ifs) <;> first | exact hD.1.1 _ | exact le_rfl
  · intro c
    rcases c with i | (⟨i, j⟩ | (i | b)) <;> simp only [extendZero]
    all_goals (try split_ifs) <;> first | exact hD.1.2 _ | exact zero_le_one

/-- The extension has exactly the finite objective; all omitted head terms vanish. -/
theorem objective_extendZero {m : ℕ} (D : MultipartiteDust.Coefficients m)
    (p : ℕ → ℝ) (s : ℝ) :
    objective p s (extendZero D) = MultipartiteDust.objective (fun i : Fin m => p i.val) s D := by
  have hh : (∑' i, head (extendZero D) i * p i) =
      ∑ i ∈ Finset.range m, head (extendZero D) i * p i := by
    apply tsum_eq_sum
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [head, extendZero, hi]
  have hi : (∑' i, incident (extendZero D) i * p i * s) =
      ∑ i ∈ Finset.range m, incident (extendZero D) i * p i * s := by
    apply tsum_eq_sum
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [incident, extendZero, hi]
  have hp : (∑' z : ℕ × ℕ, if z.1 < z.2 then pair (extendZero D) z.1 z.2 * p z.1 * p z.2 else 0) =
      ∑ z ∈ (Finset.range m) ×ˢ (Finset.range m),
        if z.1 < z.2 then pair (extendZero D) z.1 z.2 * p z.1 * p z.2 else 0 := by
    apply tsum_eq_sum
    intro z hz
    simp only [Finset.mem_product, Finset.mem_range, not_and] at hz
    unfold pair extendZero
    split_ifs <;> simp_all
  unfold objective MultipartiteDust.objective
  rw [hh, hi, hp]
  simp only [Finset.sum_product, ← Fin.sum_univ_eq_sum_range, head, incident, pair,
    linear, penalty, extendZero, Fin.is_lt, ↓reduceDIte]
  congr 3
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Fin.lt_def]
  split_ifs <;> simp

end Erdos1017.MultipartiteCountableDual

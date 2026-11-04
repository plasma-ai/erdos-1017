module

public import Erdos1017.Multipartite.Countable.CountableRepeatPenalty

/-!
# Erasing zero-mass head coefficients

`maskHeads` erases selected independent-head coefficients while keeping the dust
type; erasing any collection of head labels preserves every finite test,
zero-mass labels contribute nothing to the objective, and an optimum may be
chosen with all zero-mass head coefficients erased.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Erase selected independent-head coefficients, keeping the old dust type. -/
def maskHeads {m : ℕ} (C : Coefficients m) (keep : Fin m → Bool) : Coefficients m
  | .inl i => if keep i then head C i else 0
  | .inr (.inl (i, j)) => if keep i && keep j then pair C i j else 0
  | .inr (.inr (.inl i)) => if keep i then incident C i else 0
  | .inr (.inr (.inr b)) => C (.inr (.inr (.inr b)))

theorem maskHeads_charge {m : ℕ} (C : Coefficients m) (keep X : Fin m → Bool) (k : ℕ) :
    charge (maskHeads C keep) X k = charge C (fun i => X i && keep i) k := by
  have hh (i : Fin m) : head (maskHeads C keep) i * Selector.bit (X i) =
      head C i * Selector.bit (X i && keep i) := by
    cases hi : keep i <;> simp [head, maskHeads, Selector.bit, hi]
  have hp (i j : Fin m) : pair (maskHeads C keep) i j * (if i < j then 1 else 0) *
      Selector.bit (X i) * Selector.bit (X j) =
      pair C i j * (if i < j then 1 else 0) *
        Selector.bit (X i && keep i) * Selector.bit (X j && keep j) := by
    cases hi : keep i <;> cases hj : keep j <;> simp [pair, maskHeads, Selector.bit, hi, hj]
  have hi (i : Fin m) : incident (maskHeads C keep) i * Selector.bit (X i) =
      incident C i * Selector.bit (X i && keep i) := by
    cases hi : keep i <;> simp [incident, maskHeads, Selector.bit, hi]
  simp only [charge, hh, hp, hi, linear, penalty, maskHeads]

theorem maskHeads_feasible {m : ℕ} {C : Coefficients m} (hC : C ∈ feasible m)
    (keep : Fin m → Bool) : maskHeads C keep ∈ feasible m := by
  have hb (c : Coordinate m) : 0 ≤ maskHeads C keep c ∧ maskHeads C keep c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | (i | b)) <;> dsimp only [maskHeads]
    all_goals (try split_ifs) <;> first
      | exact ⟨hC.1.1 _, hC.1.2 _⟩
      | exact ⟨le_rfl, zero_le_one⟩
  refine ⟨⟨fun c => (hb c).1, fun c => (hb c).2⟩, ?_⟩
  intro X k
  rw [maskHeads_charge]
  exact hC.2 _ _

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

def maskHeads (D : Coefficients) (keep : ℕ → Bool) : Coefficients
  | .inl i => if keep i then head D i else 0
  | .inr (.inl (i, j)) => if keep i && keep j then pair D i j else 0
  | .inr (.inr (.inl i)) => if keep i then incident D i else 0
  | .inr (.inr (.inr b)) => D (.inr (.inr (.inr b)))

theorem restrict_maskHeads (D : Coefficients) (keep : ℕ → Bool) (n : ℕ) :
    restrict n (maskHeads D keep) = MultipartiteDust.maskHeads (restrict n D)
      (fun i : Fin n => keep i.val) := by
  funext c
  rcases c with i | (⟨i, j⟩ | (i | b)) <;> rfl

/-- Erasing any collection of head labels preserves every finite test. -/
theorem maskHeads_feasible {D : Coefficients} (hD : D ∈ feasible) (keep : ℕ → Bool) :
    maskHeads D keep ∈ feasible := by
  have hb (c : Coordinate) : 0 ≤ maskHeads D keep c ∧ maskHeads D keep c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | (i | b)) <;> dsimp only [maskHeads]
    all_goals (try split_ifs) <;> first
      | exact ⟨hD.1.1 _, hD.1.2 _⟩
      | exact ⟨le_rfl, zero_le_one⟩
  refine ⟨⟨fun c => (hb c).1, fun c => (hb c).2⟩, ?_⟩
  intro n X k
  rw [restrict_maskHeads]
  exact (MultipartiteDust.maskHeads_feasible (restrict_mem_feasible hD n) _).2 X k

/-- Zero-mass labels contribute nothing to any objective series. -/
theorem objective_maskHeads (D : Coefficients) (keep : ℕ → Bool) (p : ℕ → ℝ) (s : ℝ)
    (hp : ∀ i, keep i = false → p i = 0) : objective p s (maskHeads D keep) = objective p s D := by
  have hh (i : ℕ) : head (maskHeads D keep) i * p i = head D i * p i := by
    cases hi : keep i
    · simp [head, maskHeads, hi, hp i hi]
    · simp [head, maskHeads, hi]
  have hi (i : ℕ) : incident (maskHeads D keep) i * p i * s = incident D i * p i * s := by
    cases hi : keep i
    · simp [incident, maskHeads, hi, hp i hi]
    · simp [incident, maskHeads, hi]
  have hpair (z : ℕ × ℕ) :
      (if z.1 < z.2 then pair (maskHeads D keep) z.1 z.2 * p z.1 * p z.2 else 0) =
      (if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) := by
    by_cases hij : z.1 < z.2
    · cases hi : keep z.1
      · simp [hij, pair, maskHeads, hi, hp z.1 hi]
      · cases hj : keep z.2
        · simp [hij, pair, maskHeads, hi, hj, hp z.2 hj]
        · simp [hij, pair, maskHeads, hi, hj]
    · simp [hij]
  simp only [objective, hh, hi, hpair, linear, penalty, maskHeads]

/-- An actual optimum may be chosen with all coefficients of zero-mass heads
erased. Thus those labels impose no artificial exterior repeat constraints. -/
theorem exists_supported_profile_optimal {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) :
    ∃ D ∈ feasible,
      MultipartiteProfiles.limitValue x = objective x.2 (MultipartiteProfiles.dust x) D ∧
      ∀ i, x.2 i = 0 → head D i = 0 ∧ incident D i = 0 ∧
        ∀ j, pair D i j = 0 ∧ pair D j i = 0 := by
  classical
  obtain ⟨D, hD, heq⟩ := exists_profile_optimal hx
  let keep : ℕ → Bool := fun i => decide (x.2 i ≠ 0)
  refine ⟨maskHeads D keep, maskHeads_feasible hD keep, ?_, ?_⟩
  · rw [objective_maskHeads D keep x.2 (MultipartiteProfiles.dust x)]
    · exact heq
    · intro i hi
      simpa [keep] using hi
  · intro i hi
    simp [head, incident, pair, maskHeads, keep, hi]

end Erdos1017.MultipartiteCountableDual

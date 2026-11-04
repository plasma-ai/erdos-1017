module

public import Erdos1017.Multipartite.Countable.CountableDualMask
public import Erdos1017.Multipartite.Countable.CountableMassVariation

/-!
# Rows preserved under erasing zero slots

Erasing zero-mass head slots preserves the anchor row and each retained head's
objective slope, so every optimum can have zero slots erased while keeping all
positive head rows and its original multiplier.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Erasing zero-mass head slots preserves the actual anchor row. -/
theorem anchorRow_maskHeads (D : Coefficients) (keep : ℕ → Bool) (p : ℕ → ℝ) (s : ℝ)
    (hpzero : ∀ j, keep j = false → p j = 0) : anchorRow p s (maskHeads D keep) = anchorRow p s D := by
  have hterm (j : ℕ) : head (maskHeads D keep) j * p j = head D j * p j := by
    cases hj : keep j
    · simp [head, maskHeads, hj, hpzero j hj]
    · simp [head, maskHeads, hj]
  simp only [anchorRow, hterm, linear, maskHeads]

/-- A retained head's exact objective slope is unchanged by erasing other
zero-mass slots. This preserves each optimal dual's own multiplier. -/
theorem headRow_maskHeads {D : Coefficients} (hD : D ∈ feasible) (keep : ℕ → Bool)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (s : ℝ)
    (hpzero : ∀ j, keep j = false → p j = 0) (i : ℕ) (hi : keep i = true) :
    headRow p s (maskHeads D keep) i = headRow p s D i := by
  have hmask := maskHeads_feasible hD keep
  have hpupdate : ∀ j, keep j = false → Function.update p i (p i + 1) j = 0 := by
    intro j hj
    by_cases hji : j = i
    · subst j
      rw [hi] at hj
      contradiction
    · rw [Function.update_of_ne hji]
      exact hpzero j hj
  have hold := objective_update hD p hp hsum s i (p i + 1) (by linarith [hp i])
  have hnew := objective_update hmask p hp hsum s i (p i + 1) (by linarith [hp i])
  rw [objective_maskHeads D keep _ s hpupdate, objective_maskHeads D keep p s hpzero] at hnew
  nlinarith

/-- Every actual optimum can have zero slots erased while preserving all
positive head rows and the anchor row, hence its original multiplier. -/
theorem exists_supported_rows_optimal {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x) :
    ∃ E ∈ feasible,
      objective x.2 (MultipartiteProfiles.dust x) E = MultipartiteProfiles.limitValue x ∧
      anchorRow x.2 (MultipartiteProfiles.dust x) E = anchorRow x.2 (MultipartiteProfiles.dust x) D ∧
      (∀ i, 0 < x.2 i → headRow x.2 (MultipartiteProfiles.dust x) E i =
        headRow x.2 (MultipartiteProfiles.dust x) D i) ∧
      ∀ i, x.2 i = 0 → head E i = 0 ∧ incident E i = 0 ∧
        ∀ j, pair E i j = 0 ∧ pair E j i = 0 := by
  classical
  let keep : ℕ → Bool := fun i => decide (x.2 i ≠ 0)
  have hpzero (i : ℕ) (hi : keep i = false) : x.2 i = 0 := by simpa [keep] using hi
  refine ⟨maskHeads D keep, maskHeads_feasible hD keep, ?_, ?_, ?_, ?_⟩
  · rw [objective_maskHeads D keep x.2 _ hpzero]
    exact hopt
  · exact anchorRow_maskHeads D keep x.2 _ hpzero
  · intro i hi
    exact headRow_maskHeads hD keep x.2 hx.1.1.2 (MultipartiteProfiles.atoms_summable hx)
      (MultipartiteProfiles.dust x) hpzero i (by simp [keep, ne_of_gt hi])
  · intro i hi
    simp [head, incident, pair, maskHeads, keep, hi]

end Erdos1017.MultipartiteCountableDual

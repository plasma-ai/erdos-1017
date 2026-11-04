module

public import Erdos1017.Multipartite.Countable.CountableMassVariation

/-!
# Exchange of two head masses

Swapping two head masses preserves the countable value, so at an optimum the
exchange cannot improve the feasible dual, and different positive head masses
obey the pair-penalty multiplier bound.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

/-- Swapping any two head masses preserves the actual countable value,
including profiles with arbitrarily placed zero masses. -/
theorem value_replaceTwo_swap (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (s : ℝ) (i j : ℕ) (hij : i ≠ j) :
    value (replaceTwo p i j (p j) (p i)) s = value p s := by
  let q := replaceTwo p i j (p j) (p i)
  have hq : ∀ k, 0 ≤ q k := replaceTwo_nonneg p hp i j _ _ (hp j) (hp i)
  have hqsum : Summable q := (hsum.update i _).update j _
  have hqcomp : q = fun k => p (Equiv.swap i j k) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [q, replaceTwo, hij]
    · by_cases hkj : k = j
      · subst k
        simp [q, replaceTwo]
      · simp [q, replaceTwo, Function.update_of_ne, hki, hkj, Equiv.swap_apply_of_ne_of_ne]
  let e : {k // 0 < p k} ≃ {k // 0 < q k} :=
    { toFun := fun k => ⟨Equiv.swap i j k.val, by simpa [hqcomp] using k.property⟩
      invFun := fun k => ⟨Equiv.swap i j k.val, by simpa [hqcomp] using k.property⟩
      left_inv := by intro k; apply Subtype.ext; simp
      right_inv := by intro k; apply Subtype.ext; simp }
  exact (value_eq_of_positive_equiv p q hp hsum hq hqsum s e
    (fun k => by simp [e, hqcomp])).symm

/-- At an actual optimum, exchanging two head masses cannot improve the
old feasible dual. Value invariance supplies the feasible comparison. -/
theorem objective_swap_le_self {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) :
    objective (replaceTwo x.2 i j (x.2 j) (x.2 i)) (MultipartiteProfiles.dust x) D ≤
      objective x.2 (MultipartiteProfiles.dust x) D := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx
  have h := objective_le_value (replaceTwo x.2 i j (x.2 j) (x.2 i))
    (replaceTwo_nonneg x.2 hp i j _ _ (hp j) (hp i)) ((hsum.update i _).update j _)
    (MultipartiteProfiles.dust x) hD
  rw [value_replaceTwo_swap x.2 hp hsum _ i j hij, value_eq_profile_limit hx, ← hopt] at h
  exact h

/-- Different positive head masses obey the pair-penalty multiplier bound
by an actual exchange of their masses at the same optimal profile. -/
theorem pair_le_multiplier_of_ne_mass {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) (hmass : x.2 i ≠ x.2 j) :
    -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) ≤ ℓ := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx
  have hexp := objective_two_updates hD x.2 hp hsum (MultipartiteProfiles.dust x)
    i j hij (x.2 j - x.2 i) (x.2 i - x.2 j) (by linarith) (by linarith)
  have hswap := objective_swap_le_self hx hD hopt i j hij
  rw [show x.2 i + (x.2 j - x.2 i) = x.2 j by ring,
    show x.2 j + (x.2 i - x.2 j) = x.2 i by ring] at hexp
  have hrowi := hrows i hi
  have hrowj := hrows j hj
  have hgain : (-MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) - ℓ) *
      (x.2 i - x.2 j) ^ 2 ≤ 0 := by
    nlinarith [hexp]
  have hnegative := nonpos_of_mul_nonpos_left hgain (sq_pos_of_ne_zero (sub_ne_zero.mpr hmass))
  linarith

end Erdos1017.MultipartiteCountableDual

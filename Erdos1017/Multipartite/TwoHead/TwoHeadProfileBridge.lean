module

public import Erdos1017.Multipartite.TwoHead.TwoHeadVertexComparison
public import Erdos1017.Multipartite.MultipartiteHeadCount

/-!
# Bridges from the coefficient problem to two-head profiles

Bridges from the seven-coordinate coefficient problem to an anchor-normalized
profile with exactly two positive secondary heads. Every finite optimizer is put
in the unit box by proved coefficient clipping. The high-multiplier premise
applies to every optimum of the same profile; profile selection and its
high-slope justification are not part of this module.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.TwoHeadProfileBridge

open VertexClassification

/-- The cross penalty may be lowered to the first star charge without
violating any original Boolean-head and arbitrary-dust count test. -/
theorem update_cross_feasible {x : Coefficients} (hx : x ∈ feasible) :
    Function.update x 3 (x 0) ∈ feasible := by
  constructor
  · intro i
    by_cases hi : i = 3
    · simp [hi, hx.1 0]
    · simpa [Function.update_of_ne, hi] using hx.1 i
  · rintro ⟨⟨a, b⟩, n⟩
    have h00 := hx.2 ((false, false), n)
    have h10 := hx.2 ((true, false), n)
    have h01 := hx.2 ((false, true), n)
    have hn := mul_nonneg (Nat.cast_nonneg n) (hx.1 4)
    cases a <;> cases b <;>
      norm_num [test, constant, slope, Function.update] at * <;> linarith

/-- A head-dust penalty may be lowered to that head's star charge. -/
theorem update_first_incident_feasible {x : Coefficients} (hx : x ∈ feasible) :
    Function.update x 4 (x 0) ∈ feasible := by
  constructor
  · intro i
    by_cases hi : i = 4
    · simp [hi, hx.1 0]
    · simpa [Function.update_of_ne, hi] using hx.1 i
  · rintro ⟨⟨a, b⟩, n⟩
    by_cases hn0 : n = 0
    · subst n
      have ht := hx.2 ((a, b), 0)
      cases a <;> cases b <;>
        norm_num [test, constant, slope, Function.update] at ht ⊢ <;> exact ht
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have h00 := hx.2 ((false, false), n)
    have h01 := hx.2 ((false, true), n)
    have hstar := mul_nonneg (sub_nonneg.mpr hn1) (hx.1 0)
    have hc := hx.1 3
    cases a <;> cases b <;>
      norm_num [test, constant, slope, Function.update] at * <;> nlinarith

/-- The second head-dust clipping retains the same full count constraints. -/
theorem update_second_incident_feasible {x : Coefficients} (hx : x ∈ feasible) :
    Function.update x 5 (x 1) ∈ feasible := by
  constructor
  · intro i
    by_cases hi : i = 5
    · simp [hi, hx.1 1]
    · simpa [Function.update_of_ne, hi] using hx.1 i
  · rintro ⟨⟨a, b⟩, n⟩
    by_cases hn0 : n = 0
    · subst n
      have ht := hx.2 ((a, b), 0)
      cases a <;> cases b <;>
        norm_num [test, constant, slope, Function.update] at ht ⊢ <;> exact ht
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have h00 := hx.2 ((false, false), n)
    have h10 := hx.2 ((true, false), n)
    have hstar := mul_nonneg (sub_nonneg.mpr hn1) (hx.1 1)
    have hc := hx.1 3
    cases a <;> cases b <;>
      norm_num [test, constant, slope, Function.update] at * <;> nlinarith

/-- Clipping the internal dust penalty to the dust star charge is feasible.
Counts above one are compared with the original count-one test. -/
theorem update_dust_penalty_feasible {x : Coefficients} (hx : x ∈ feasible) :
    Function.update x 6 (x 2) ∈ feasible := by
  constructor
  · intro i
    by_cases hi : i = 6
    · simp [hi, hx.1 2]
    · simpa [Function.update_of_ne, hi] using hx.1 i
  · rintro ⟨⟨a, b⟩, n⟩
    by_cases hn : n ≤ 1
    · have ht := hx.2 ((a, b), n)
      interval_cases n <;> cases a <;> cases b <;>
        norm_num [test, constant, slope, Function.update] at ht ⊢ <;> exact ht
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hv := mul_nonneg (hx.1 2)
      (mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) (show 0 ≤ (n : ℝ) - 2 by linarith))
    have hc₁ := mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) (hx.1 4)
    have hc₂ := mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) (hx.1 5)
    have ht := hx.2 ((a, b), 1)
    cases a <;> cases b <;>
      norm_num [test, constant, slope, Function.update] at * <;> nlinarith

/-- Every optimizer of the unbounded finite problem lies in the unit box.
Each penalty has a strictly positive objective weight. -/
theorem optimal_mem_unit_box {u₁ u₂ h V : ℝ}
    (hu₁ : 0 < u₁) (hu₂ : 0 < u₂) (hh : 0 < h)
    {x : Coefficients} (hx : x ∈ TwoHeadVertexComparison.optimalFace 1 u₁ u₂ h V)
    (hmax : ∀ y ∈ feasible, TwoHeadVertexComparison.objective 1 u₁ u₂ h y ≤ V) :
    x ∈ Set.Icc 0 1 := by
  have hcross := hmax _ (update_cross_feasible hx.1)
  have hfirst := hmax _ (update_first_incident_feasible hx.1)
  have hsecond := hmax _ (update_second_incident_feasible hx.1)
  have hdust := hmax _ (update_dust_penalty_feasible hx.1)
  have hvalue := hx.2
  simp only [TwoHeadVertexComparison.objective_apply, one_mul] at hcross hfirst hsecond hdust hvalue
  norm_num [Function.update] at hcross hfirst hsecond hdust
  have hc : x 3 ≤ x 0 := by nlinarith [mul_pos hu₁ hu₂]
  have hc₁ : x 4 ≤ x 0 := by nlinarith [mul_pos hh hu₁]
  have hc₂ : x 5 ≤ x 1 := by nlinarith [mul_pos hh hu₂]
  have hp : x 6 ≤ x 2 := by nlinarith [sq_pos_of_pos hh]
  have hb := TwoHeadVertexComparison.star_bounds hx.1
  refine ⟨hx.1.1, ?_⟩
  intro i
  fin_cases i
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2
  · exact hc.trans hb.1
  · exact hc₁.trans hb.1
  · exact hc₂.trans hb.2.1
  · exact hp.trans hb.2.2

/-- The two-head finite array retains only the used unordered cross slot. -/
def toFinite (x : Coefficients) : MultipartiteDust.Coefficients 2
  | .inl i => ![x 0, x 1] i
  | .inr (.inl (i, j)) => if i = 0 ∧ j = 1 then x 3 else 0
  | .inr (.inr (.inl i)) => ![x 4, x 5] i
  | .inr (.inr (.inr false)) => x 2
  | .inr (.inr (.inr true)) => x 6

def toCountable (x : Coefficients) : MultipartiteCountableDual.Coefficients :=
  MultipartiteCountableDual.extendZero (toFinite x)

def ofCountable (D : MultipartiteCountableDual.Coefficients) : Coefficients :=
  ![MultipartiteCountableDual.head D 0, MultipartiteCountableDual.head D 1,
    MultipartiteCountableDual.linear D, MultipartiteCountableDual.pair D 0 1,
    MultipartiteCountableDual.incident D 0, MultipartiteCountableDual.incident D 1,
    MultipartiteCountableDual.penalty D]

/-- Literal Boolean and dust-count tests coincide under the finite encoding. -/
theorem charge_toFinite (x : Coefficients) (X : Selector.Selection 2) (n : ℕ) :
    MultipartiteDust.charge (toFinite x) X n = test ((X 0, X 1), n) x := by
  cases h₀ : X 0 <;> cases h₁ : X 1 <;>
    simp [MultipartiteDust.charge, MultipartiteDust.head, MultipartiteDust.pair,
      MultipartiteDust.incident, MultipartiteDust.linear, MultipartiteDust.penalty,
      toFinite, Fin.sum_univ_two, Selector.bit, h₀, h₁, test, constant, slope] <;> ring

theorem toFinite_feasible {x : Coefficients} (hx : x ∈ feasible)
    (hbox : x ∈ Set.Icc 0 1) : toFinite x ∈ MultipartiteDust.feasible 2 := by
  have hb (c : MultipartiteDust.Coordinate 2) : 0 ≤ toFinite x c ∧ toFinite x c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | (i | b))
    · fin_cases i
      · exact ⟨hbox.1 0, hbox.2 0⟩
      · exact ⟨hbox.1 1, hbox.2 1⟩
    · fin_cases i <;> fin_cases j <;> simp [toFinite]
      exact ⟨hbox.1 _, hbox.2 _⟩
    · fin_cases i
      · exact ⟨hbox.1 4, hbox.2 4⟩
      · exact ⟨hbox.1 5, hbox.2 5⟩
    · cases b <;> exact ⟨hbox.1 _, hbox.2 _⟩
  refine ⟨⟨fun c => (hb c).1, fun c => (hb c).2⟩, ?_⟩
  intro X n
  rw [charge_toFinite]
  exact hx.2 _

theorem ofCountable_feasible {D : MultipartiteCountableDual.Coefficients}
    (hD : D ∈ MultipartiteCountableDual.feasible) : ofCountable D ∈ feasible := by
  constructor
  · intro i
    fin_cases i <;> exact hD.1.1 _
  · rintro ⟨⟨a, b⟩, n⟩
    let X : Selector.Selection 2 := ![a, b]
    have ht := hD.2 2 X n
    cases a <;> cases b <;>
      simp [ofCountable, test, constant, slope, MultipartiteDust.charge,
        MultipartiteDust.head, MultipartiteDust.pair, MultipartiteDust.incident,
        MultipartiteDust.linear, MultipartiteDust.penalty, MultipartiteCountableDual.restrict,
        MultipartiteCountableDual.head, MultipartiteCountableDual.pair,
        MultipartiteCountableDual.incident, MultipartiteCountableDual.linear,
        MultipartiteCountableDual.penalty, Fin.sum_univ_two, Selector.bit, X,
        mul_left_comm, mul_comm] at ht ⊢ <;> nlinarith

/-- The finite encoding preserves the literal objective, without a box premise. -/
theorem objective_toFinite (x : Coefficients) (u₁ u₂ h : ℝ) :
    MultipartiteDust.objective ![u₁, u₂] h (toFinite x) =
      TwoHeadVertexComparison.objective 1 u₁ u₂ h x := by
  simp [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.pair,
    MultipartiteDust.incident, MultipartiteDust.linear, MultipartiteDust.penalty,
    toFinite, Fin.sum_univ_two, TwoHeadVertexComparison.objective_apply]
  ring

/-- Exactly two supported masses reduce every series objective to seven coordinates. -/
theorem objective_two_support (D : MultipartiteCountableDual.Coefficients)
    (p : ℕ → ℝ) (h : ℝ) (hzero : ∀ k, 2 ≤ k → p k = 0) :
    MultipartiteCountableDual.objective p h D =
      TwoHeadVertexComparison.objective 1 (p 0) (p 1) h (ofCountable D) := by
  have hh : (∑' i, MultipartiteCountableDual.head D i * p i) =
      MultipartiteCountableDual.head D 0 * p 0 + MultipartiteCountableDual.head D 1 * p 1 := by
    rw [tsum_eq_sum (s := {0, 1}) (by
      intro i hi
      have hi' : 2 ≤ i := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        omega
      rw [hzero i hi', mul_zero])]
    norm_num
  have hi : (∑' i, MultipartiteCountableDual.incident D i * p i * h) =
      MultipartiteCountableDual.incident D 0 * p 0 * h +
        MultipartiteCountableDual.incident D 1 * p 1 * h := by
    rw [tsum_eq_sum (s := {0, 1}) (by
      intro i hi
      have hi' : 2 ≤ i := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        omega
      rw [hzero i hi', mul_zero, zero_mul])]
    norm_num
  have hp : (∑' z : ℕ × ℕ, if z.1 < z.2 then
      MultipartiteCountableDual.pair D z.1 z.2 * p z.1 * p z.2 else 0) =
      MultipartiteCountableDual.pair D 0 1 * p 0 * p 1 := by
    rw [tsum_eq_sum (s := {(0, 1)}) (by
      intro z hz
      by_cases hlt : z.1 < z.2
      · simp only [hlt, ↓reduceIte]
        by_cases hi : 2 ≤ z.1
        · rw [hzero z.1 hi, mul_zero, zero_mul]
        · have hj : 2 ≤ z.2 := by
            have hz' : z ≠ (0, 1) := by simpa using hz
            by_contra hj
            apply hz'
            apply Prod.ext <;> omega
          rw [hzero z.2 hj, mul_zero]
      · simp [hlt])]
    simp
  rw [MultipartiteCountableDual.objective, hh, hp, hi]
  simp [TwoHeadVertexComparison.objective_apply, ofCountable]
  ring

theorem head_toCountable (x : Coefficients) (i : ℕ) :
    MultipartiteCountableDual.head (toCountable x) i =
      if i = 0 then x 0 else if i = 1 then x 1 else 0 := by
  rcases i with _ | (_ | i) <;>
    simp [MultipartiteCountableDual.head, toCountable,
      MultipartiteCountableDual.extendZero, MultipartiteDust.head, toFinite]

theorem incident_toCountable (x : Coefficients) (i : ℕ) :
    MultipartiteCountableDual.incident (toCountable x) i =
      if i = 0 then x 4 else if i = 1 then x 5 else 0 := by
  rcases i with _ | (_ | i) <;>
    simp [MultipartiteCountableDual.incident, toCountable,
      MultipartiteCountableDual.extendZero, MultipartiteDust.incident, toFinite]

theorem pair_toCountable (x : Coefficients) (i j : ℕ) :
    MultipartiteCountableDual.pair (toCountable x) i j =
      if i = 0 ∧ j = 1 then x 3 else 0 := by
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
    simp [MultipartiteCountableDual.pair, toCountable,
      MultipartiteCountableDual.extendZero, MultipartiteDust.pair, toFinite]

theorem linear_toCountable (x : Coefficients) :
    MultipartiteCountableDual.linear (toCountable x) = x 2 := rfl

theorem penalty_toCountable (x : Coefficients) :
    MultipartiteCountableDual.penalty (toCountable x) = x 6 := rfl

theorem toCountable_feasible {x : Coefficients} (hx : x ∈ feasible)
    (hbox : x ∈ Set.Icc 0 1) : toCountable x ∈ MultipartiteCountableDual.feasible :=
  MultipartiteCountableDual.extendZero_feasible (toFinite_feasible hx hbox)

/-- The zero extension preserves the objective at every mass function. -/
theorem objective_toCountable (x : Coefficients) (p : ℕ → ℝ) (h : ℝ) :
    MultipartiteCountableDual.objective p h (toCountable x) =
      TwoHeadVertexComparison.objective 1 (p 0) (p 1) h x := by
  rw [toCountable, MultipartiteCountableDual.objective_extendZero]
  have heq : (fun i : Fin 2 => p i.val) = ![p 0, p 1] := by
    funext i
    fin_cases i <;> rfl
  rw [heq, objective_toFinite]

/-- Every unbounded nonnegative coefficient competitor is below the actual
profile value, using the proved unrestricted finite-dual comparison. -/
theorem finite_objective_le_profile {L : ℝ} {z : MultipartiteProfiles.Profile}
    (hz : z ∈ MultipartiteProfiles.space L) {x : Coefficients} (hx : x ∈ feasible) :
    TwoHeadVertexComparison.objective 1 (z.2 0) (z.2 1) (MultipartiteProfiles.dust z) x ≤
      MultipartiteProfiles.limitValue z := by
  have hp (i : Fin 2) : 0 ≤ (![z.2 0, z.2 1] : Fin 2 → ℝ) i ∧
      (![z.2 0, z.2 1] : Fin 2 → ℝ) i ≤ 1 := by
    fin_cases i <;> exact ⟨hz.1.1.2 _, hz.1.2.2 _⟩
  have htest : ∀ X n, MultipartiteDust.charge (toFinite x) X n ≤ 1 := by
    intro X n
    rw [charge_toFinite]
    exact hx.2 _
  have h := MultipartiteDust.objective_le_value_of_tests (toFinite x) htest (hx.1 6)
    ![z.2 0, z.2 1] hp (MultipartiteProfiles.dust z) (MultipartiteProfiles.dust_nonneg hz)
  rw [objective_toFinite] at h
  have heq : (fun i : Fin 2 => z.2 i.val) = ![z.2 0, z.2 1] := by
    funext i
    fin_cases i <;> rfl
  have hbound := MultipartiteCountableDual.finite_value_le_value z.2 hz.1.1.2
    (MultipartiteProfiles.atoms_summable hz) (MultipartiteProfiles.dust z) 2
  rw [heq, MultipartiteCountableDual.value_eq_profile_limit hz] at hbound
  exact h.trans hbound

/-- Two supported secondary heads give a nonempty optimal face of the
original unbounded seven-coordinate problem at the actual profile value. -/
theorem optimalFace_nonempty {L : ℝ} {z : MultipartiteProfiles.Profile}
    (hz : z ∈ MultipartiteProfiles.space L) (hzero : ∀ k, 2 ≤ k → z.2 k = 0) :
    (TwoHeadVertexComparison.optimalFace 1 (z.2 0) (z.2 1)
      (MultipartiteProfiles.dust z) (MultipartiteProfiles.limitValue z)).Nonempty := by
  obtain ⟨D, hD, hvalue⟩ := MultipartiteCountableDual.exists_profile_optimal hz
  refine ⟨ofCountable D, ofCountable_feasible hD, ?_⟩
  rw [← objective_two_support D z.2 (MultipartiteProfiles.dust z) hzero]
  exact hvalue.symm

private theorem objective_prefix (x : Coefficients) (N : ℕ) (hN : 2 ≤ N)
    (p : Fin N → ℝ) (s : ℝ) :
    MultipartiteDust.objective p s (MultipartiteCountableDual.restrict N (toCountable x)) =
      TwoHeadVertexComparison.objective 1 (p ⟨0, by omega⟩) (p ⟨1, by omega⟩) s x := by
  let q : ℕ → ℝ := fun k => if hk : k < N then p ⟨k, hk⟩ else 0
  have hp : (fun i : Fin N => q i.val) = p := by
    funext i
    simp [q]
  have h := MultipartiteCountableDual.objective_restrict_extendZero_of_le (toFinite x) q s N hN
  rw [hp] at h
  have hq : (fun i : Fin 2 => q i.val) = ![p ⟨0, by omega⟩, p ⟨1, by omega⟩] := by
    funext i
    fin_cases i <;> simp [q, show 0 < N by omega, show 1 < N by omega]
  rw [hq, objective_toFinite] at h
  exact h

private theorem repeat_expression (x : Coefficients) (D : ℝ) {i : ℕ}
    (S : MultipartiteCountableDual.RepeatContext i) (r : ℕ) :
    (r : ℝ) * S.row (toCountable x) + S.charge (toCountable x) -
        D * r * ((r : ℝ) - 1) / 2 =
      MultipartiteDust.objective
        (Function.update (fun j => Selector.bit (S.selection j)) ⟨i, S.head_lt⟩ (r : ℝ))
        S.dustCount (MultipartiteCountableDual.restrict S.size (toCountable x)) +
          x 6 * S.dustCount / 2 - D * Repeat.pairs r := by
  have hu := MultipartiteDust.objective_update
    (MultipartiteCountableDual.restrict S.size (toCountable x))
    (fun j => Selector.bit (S.selection j)) S.dustCount ⟨i, S.head_lt⟩ (r : ℝ)
  have hz : Selector.bit (S.selection ⟨i, S.head_lt⟩) = 0 := by
    rw [S.head_absent]
    rfl
  rw [hz, sub_zero] at hu
  have hc := DustCellBridge.charge_eq_objective
    (MultipartiteCountableDual.restrict S.size (toCountable x)) S.selection S.dustCount
  change S.charge (toCountable x) = _ + x 6 * S.dustCount / 2 at hc
  change _ = _ + (r : ℝ) * S.row (toCountable x) at hu
  rw [Repeat.pairs]
  linarith

/-- A finite all-count witness controls every actual countable exterior
when the first secondary head is repeated, including prefixes of size one. -/
theorem repeatPenalty_first_le {x : Coefficients} {D : ℝ} (hD : 0 ≤ D)
    (htest : ∀ r b n : ℕ, b ≤ 1 →
      Repeat.oneSidedCharge (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) D r b n ≤ 1) :
    MultipartiteCountableDual.repeatPenalty (toCountable x) 0 ≤ D := by
  apply MultipartiteCountableDual.repeatPenalty_le_of_tests _ _ _ hD
  intro S r
  rw [repeat_expression]
  by_cases hN : 2 ≤ S.size
  · rw [objective_prefix x S.size hN]
    cases hb : S.selection ⟨1, by omega⟩
    · have ht := htest r 0 S.dustCount (by omega)
      simp [Function.update, Fin.ext_iff, hb, Selector.bit,
        TwoHeadVertexComparison.objective_apply, Repeat.oneSidedCharge, Repeat.pairs] at ⊢ ht
      nlinarith
    · have ht := htest r 1 S.dustCount (by omega)
      simp [Function.update, Fin.ext_iff, hb, Selector.bit,
        TwoHeadVertexComparison.objective_apply, Repeat.oneSidedCharge, Repeat.pairs] at ⊢ ht
      nlinarith
  · have hsize : S.size = 1 := by
      have := S.head_lt
      omega
    rcases S with ⟨N, hi, X, hX, n⟩
    dsimp only at hsize
    subst N
    have ht := htest r 0 n (by omega)
    simp [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.pair,
      MultipartiteDust.incident, MultipartiteDust.linear, MultipartiteDust.penalty,
      MultipartiteCountableDual.restrict, MultipartiteCountableDual.head,
      MultipartiteCountableDual.pair, MultipartiteCountableDual.incident,
      toCountable, MultipartiteCountableDual.extendZero, toFinite,
      Repeat.oneSidedCharge, Repeat.pairs] at ⊢ ht
    nlinarith

/-- The swapped finite witness controls every actual exterior for the second head. -/
theorem repeatPenalty_second_le {x : Coefficients} {D : ℝ} (hD : 0 ≤ D)
    (htest : ∀ r b n : ℕ, b ≤ 1 →
      Repeat.oneSidedCharge (x 1) (x 0) (x 2) (x 3) (x 5) (x 4) (x 6) D r b n ≤ 1) :
    MultipartiteCountableDual.repeatPenalty (toCountable x) 1 ≤ D := by
  apply MultipartiteCountableDual.repeatPenalty_le_of_tests _ _ _ hD
  intro S r
  rw [repeat_expression]
  have hN : 2 ≤ S.size := by
    have := S.head_lt
    omega
  rw [objective_prefix x S.size hN]
  cases hb : S.selection ⟨0, by omega⟩
  · have ht := htest r 0 S.dustCount (by omega)
    simp [Function.update, Fin.ext_iff, hb, Selector.bit,
      TwoHeadVertexComparison.objective_apply, Repeat.oneSidedCharge, Repeat.pairs] at ⊢ ht
    nlinarith
  · have ht := htest r 1 S.dustCount (by omega)
    simp [Function.update, Fin.ext_iff, hb, Selector.bit,
      TwoHeadVertexComparison.objective_apply, Repeat.oneSidedCharge, Repeat.pairs] at ⊢ ht
    nlinarith

/-- The extended array's dust row has the literal two-secondary-part formula. -/
theorem dustRow_toCountable (x : Coefficients) (p : ℕ → ℝ) (s : ℝ) :
    MultipartiteCountableDual.dustRow p s (toCountable x) =
      x 2 - p 0 * x 4 - p 1 * x 5 - s * x 6 := by
  have hi : (∑' i, MultipartiteCountableDual.incident (toCountable x) i * p i) =
      x 4 * p 0 + x 5 * p 1 := by
    rw [tsum_eq_sum (s := {0, 1}) (by
      intro i hi
      have hi' : i ≠ 0 ∧ i ≠ 1 := by simpa using hi
      simp [incident_toCountable, hi'.1, hi'.2])]
    simp [incident_toCountable]
  rw [MultipartiteCountableDual.dustRow, hi, linear_toCountable, penalty_toCountable]
  ring

/-- An actual selected density optimum with exactly two positive secondary
heads and positive dust is impossible when every actual optimal dual's own
stationary multiplier is above one half. The high-slope premise remains explicit. -/
theorem two_positive_heads_positive_dust_impossible {ε : ℝ} (hε : 0 < ε)
    {z : MultipartiteProfiles.Profile}
    (hz : z ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue z)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) z.1 (∑' k, (z.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue z →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust z)
    (hvalue : ε < MultipartiteProfiles.normalizedValue z)
    (h₀ : 0 < z.2 0) (h₁ : 0 < z.2 1) (hzero : ∀ k, 2 ≤ k → z.2 k = 0)
    (hs : 0 < MultipartiteProfiles.dust z)
    (hhigh : ∀ D ∈ MultipartiteCountableDual.feasible,
      MultipartiteCountableDual.objective z.2 (MultipartiteProfiles.dust z) D =
        MultipartiteProfiles.limitValue z → ∀ ℓ : ℝ,
        (∀ k, 0 < z.2 k → MultipartiteCountableDual.headRow z.2 (MultipartiteProfiles.dust z) D k -
          MultipartiteCountableDual.anchorRow z.2 (MultipartiteProfiles.dust z) D = ℓ * (z.2 k - 1)) →
        1 / 2 < ℓ) : False := by
  have hden : 0 < 1 + z.1 := by linarith [hz.1.1.1.1]
  have hmaxMoment : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1)
      z.1 (∑' k, (z.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue z := by
    intro y hy
    have hyDensity : y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε := by
      refine ⟨hy.1, ?_⟩
      change 1 + (∑' k, (y.2 k) ^ 2) = 2 * ε * (1 + y.1) ^ 2
      rw [hy.2.1, hy.2.2]
      exact hz.2
    have h := hmax y hyDensity
    change MultipartiteProfiles.limitValue y / (1 + y.1) ^ 2 ≤
      MultipartiteProfiles.limitValue z / (1 + z.1) ^ 2 at h
    rw [hy.2.1] at h
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mp h
  have hfiniteMax (x : Coefficients) (hx : x ∈ feasible) :
      TwoHeadVertexComparison.objective 1 (z.2 0) (z.2 1) (MultipartiteProfiles.dust z) x ≤
        MultipartiteProfiles.limitValue z := finite_objective_le_profile hz.1 hx
  have hextend (x : Coefficients)
      (hx : x ∈ TwoHeadVertexComparison.optimalFace 1 (z.2 0) (z.2 1)
        (MultipartiteProfiles.dust z) (MultipartiteProfiles.limitValue z)) :
      toCountable x ∈ MultipartiteCountableDual.feasible ∧
      MultipartiteCountableDual.objective z.2 (MultipartiteProfiles.dust z) (toCountable x) =
        MultipartiteProfiles.limitValue z := by
    refine ⟨toCountable_feasible hx.1 (optimal_mem_unit_box h₀ h₁ hs hx hfiniteMax), ?_⟩
    rw [objective_toCountable]
    exact hx.2
  apply TwoHeadVertexComparison.no_optimal_face_with_strict_repeat
    (a := 1) (u₁ := z.2 0) (u₂ := z.2 1) (h := MultipartiteProfiles.dust z)
    (V := MultipartiteProfiles.limitValue z) (by norm_num) h₀ h₁ hs
    (optimalFace_nonempty hz.1 hzero) hfiniteMax
  · intro x hx
    obtain ⟨hE, hEopt⟩ := hextend x hx
    obtain ⟨ℓ, hrows, _, _⟩ := MultipartiteCountableDual.exists_unique_head_multiplier
      hε hz hmax hvalue hE hEopt 0 h₀
    have hℓ := hhigh (toCountable x) hE hEopt ℓ hrows
    have ht₀ := MultipartiteCountableDual.head_lt_one_at_greatest_dust
      hz.1 hmaxMoment hdust hE hEopt 0 1 (by omega) h₀ h₁
    have hγ := MultipartiteCountableDual.positive_gamma_of_half_lt_multiplier
      hε hz hmax hvalue hE hEopt ℓ hℓ hrows 0 h₀ ht₀
    let γ := MultipartiteCountableDual.anchorRow z.2 (MultipartiteProfiles.dust z)
      (toCountable x) - ℓ
    have hγpos : 0 < γ := by
      have hpos : 0 < γ / (1 + z.1) := hγ.2.2.symm ▸ hγ.2.1
      exact (div_pos_iff_of_pos_right hden).mp hpos
    have hstar₀ := (MultipartiteCountableDual.multiplier_le_repeatPenalty
      hε hz hmax hvalue hE hEopt ℓ 0 h₀ (hrows 0 h₀)).trans
        (MultipartiteCountableDual.repeatPenalty_le_head hE 0)
    have hstar₁ := (MultipartiteCountableDual.multiplier_le_repeatPenalty
      hε hz hmax hvalue hE hEopt ℓ 1 h₁ (hrows 1 h₁)).trans
        (MultipartiteCountableDual.repeatPenalty_le_head hE 1)
    have hc₀ := (MultipartiteCountableDual.incident_floor_of_head_multiplier
      hε hz hmax hvalue hE hEopt ℓ hrows 0 h₀ hs).1
    have hc₁ := (MultipartiteCountableDual.incident_floor_of_head_multiplier
      hε hz hmax hvalue hE hEopt ℓ hrows 1 h₁ hs).1
    have hp := MultipartiteCountableDual.penalty_floor_of_head_multiplier
      hε hz hmax hvalue hE hEopt ℓ hrows 0 h₀ hs
    have hr := MultipartiteCountableDual.dust_row_of_head_multiplier
      hε hz hmax hvalue hE hEopt ℓ hrows 0 h₀ hs
    rw [dustRow_toCountable] at hr
    refine ⟨ℓ, γ, hℓ, hγpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [head_toCountable] using hstar₀
    · simpa [head_toCountable] using hstar₁
    · simpa [γ, incident_toCountable, mul_comm] using hc₀
    · simpa [γ, incident_toCountable, mul_comm] using hc₁
    · simpa [γ, penalty_toCountable] using hp
    · dsimp [γ]
      linarith
  · intro x hx y hy D hD htests
    obtain ⟨hE, hEopt⟩ := hextend x hx
    rcases hy with rfl | rfl
    · have hstrict := MultipartiteCountableDual.pair_lt_repeatPenalty_at_greatest_dust
        hz.1 hmaxMoment hdust hE hEopt 0 1 (by omega) h₀ h₁
      have hrepeat := repeatPenalty_first_le hD htests
      simpa [MultipartiteCountableMeasure.kernel, pair_toCountable] using hstrict.trans_le hrepeat
    · have hstrict := MultipartiteCountableDual.pair_lt_repeatPenalty_at_greatest_dust
        hz.1 hmaxMoment hdust hE hEopt 1 0 (by omega) h₁ h₀
      have htests' : ∀ r b n : ℕ, b ≤ 1 →
          Repeat.oneSidedCharge (x 1) (x 0) (x 2) (x 3) (x 5) (x 4) (x 6) D r b n ≤ 1 := by
        simpa [VertexRepeat.swap] using htests
      have hrepeat := repeatPenalty_second_le hD htests'
      simpa [MultipartiteCountableMeasure.kernel, pair_toCountable] using hstrict.trans_le hrepeat

end Erdos1017.TwoHeadProfileBridge

module

public import Erdos1017.Multipartite.Countable.CountableHeadEndpoints
public import Erdos1017.Multipartite.MultipartiteRelabeling
public import Erdos1017.Multipartite.MultipartiteMomentSelection

/-!
# Strict pair bounds at a greatest-dust optimum

Every nonempty compact moment fiber has a greatest-dust value maximizer with an
attained dual whose positive heads satisfy strict pair bounds against the
full-repeat penalties, each positive head coefficient lying below one
(`exists_greatest_dust_strict_optimum`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- A feasible countable objective is bounded by its attained coefficient value. -/
theorem objective_le_value (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (s : ℝ) {D : Coefficients} (hD : D ∈ feasible) : objective p s D ≤ value p s := by
  obtain ⟨E, hE, hmax⟩ := exists_optimal p hp hsum s
  have hb : BddAbove (objective p s '' feasible) := by
    refine ⟨objective p s E, ?_⟩
    rintro _ ⟨F, hF, rfl⟩
    exact hmax F hF
  exact le_csSup hb ⟨D, hD, rfl⟩

/-- A sufficiently penalized positive head pair produces an actual sorted
competitor with the same moments, no lower value, and strictly more dust. -/
theorem exists_sorted_head_endpoint {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j)
    (hpair : repeatPenalty D i ≤
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j))) :
    ∃ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.dust x < MultipartiteProfiles.dust y ∧
      MultipartiteProfiles.limitValue x ≤ MultipartiteProfiles.limitValue y := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx
  have hsqsum := MultipartiteProfiles.squares_summable hx
  have hQ : (∑' k, (x.2 k) ^ 2) ≤ 1 := by
    exact le_of_tendsto hsqsum.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hx.2.2.2)
  let r := Real.sqrt ((x.2 i) ^ 2 + (x.2 j) ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (x.2 i) ^ 2 + (x.2 j) ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hrQ : r ^ 2 ≤ ∑' k, (x.2 k) ^ 2 := by
    rw [hr2]
    simpa only [Finset.sum_pair hij] using
      hsqsum.sum_le_tsum {i, j} (fun _ _ => sq_nonneg _)
  have hr1 : r ≤ 1 := by nlinarith [hrQ.trans hQ]
  have hδ : 0 < x.2 i + x.2 j - r := by nlinarith [mul_pos hi hj]
  have hs := MultipartiteProfiles.dust_nonneg hx
  let s := MultipartiteProfiles.dust x + x.2 i + x.2 j - r
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  let p := replaceTwo x.2 i j 0 0
  have hp0 : ∀ k, 0 ≤ p k := replaceTwo_nonneg x.2 hp i j 0 0 le_rfl le_rfl
  have hpSum : Summable p := (hsum.update i 0).update j 0
  have hpi : p i = 0 := by simp [p, replaceTwo, hij]
  have hpj : p j = 0 := by simp [p, replaceTwo]
  have hold : replaceTwo p i j (x.2 i) (x.2 j) = x.2 := by
    rw [show p = replaceTwo x.2 i j 0 0 from rfl, replaceTwo_replaceTwo, replaceTwo_self]
  obtain ⟨E, hE, hendpoint⟩ := exists_head_endpoint hD i j hij p hp0 hpSum hpi hpj
    (x.2 i) (x.2 j) r (MultipartiteProfiles.dust x) hi hj hr hr2 hs hpair
  rw [hold, hopt] at hendpoint
  have hsort (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
      (huv : u + v = r) (huv2 : u ^ 2 + v ^ 2 = r ^ 2) :
      ∃ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
        MultipartiteProfiles.dust y = s ∧
        value (replaceTwo p i j u v) s = MultipartiteProfiles.limitValue y := by
    let z := replaceTwo x.2 i j u v
    have hz : ∀ k, 0 ≤ z k := replaceTwo_nonneg x.2 hp i j u v hu hv
    have hz1 (k : ℕ) : z k ≤ 1 := by
      by_cases hkj : k = j
      · subst k
        simpa [z, replaceTwo] using hv1
      · by_cases hki : k = i
        · subst k
          simpa [z, replaceTwo, hij] using hu1
        · simpa [z, replaceTwo, Function.update_of_ne, hkj, hki] using hx.1.2.2 k
    have hzsum : Summable z := (hsum.update i u).update j v
    have hT : s + (∑' k, z k) = x.1 := by
      rw [show z = replaceTwo x.2 i j u v from rfl, replaceTwo_tsum _ hsum i j hij]
      dsimp [s]
      rw [MultipartiteProfiles.dust_eq_sub_tsum hx]
      linarith
    have hsq : (∑' k, (z k) ^ 2) = ∑' k, (x.2 k) ^ 2 := by
      rw [show z = replaceTwo x.2 i j u v from rfl,
        replaceTwo_square_tsum _ hsqsum i j hij]
      nlinarith
    obtain ⟨y, hy, hyT, hyd, hyQ, hyvalue⟩ := MultipartiteProfiles.exists_sorted_representative
      z hz hz1 hzsum s hs0 L (hT.le.trans hx.1.2.1) (hsq.le.trans hQ)
    refine ⟨y, ⟨hy, hyT.trans hT, hyQ.trans hsq⟩, hyd, ?_⟩
    simpa only [p, replaceTwo_replaceTwo] using hyvalue
  rcases hendpoint with he | he
  · obtain ⟨y, hy, hyd, hyvalue⟩ := hsort r 0 hr le_rfl hr1 zero_le_one (by ring) (by ring)
    refine ⟨y, hy, ?_, ?_⟩
    · rw [hyd]
      dsimp [s]
      linarith
    · exact he.trans ((objective_le_value _ (replaceTwo_nonneg p hp0 i j r 0 hr le_rfl)
        ((hpSum.update i r).update j 0) s hE).trans_eq hyvalue)
  · obtain ⟨y, hy, hyd, hyvalue⟩ := hsort 0 r le_rfl hr zero_le_one hr1 (by ring) (by ring)
    refine ⟨y, hy, ?_, ?_⟩
    · rw [hyd]
      dsimp [s]
      linarith
    · exact he.trans ((objective_le_value _ (replaceTwo_nonneg p hp0 i j 0 r le_rfl hr)
        ((hpSum.update i 0).update j r) s hE).trans_eq hyvalue)

/-- The anchored clique on two distinct heads gives its literal triangle
constraint in the unrestricted countable coefficient model. -/
theorem anchored_head_pair_test {D : Coefficients} (hD : D ∈ feasible)
    (i j : ℕ) (hij : i ≠ j) :
    head D i + head D j +
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) ≤ 1 := by
  let n := max i j + 1
  have hi : i < n := by dsimp [n]; omega
  have hj : j < n := by dsimp [n]; omega
  let X : Selector.Selection n := fun k => decide (k = ⟨j, hj⟩)
  have habsent : X ⟨i, hi⟩ = false := by simp [X, Fin.ext_iff, hij]
  let S : RepeatContext i := ⟨n, hi, X, habsent, 0⟩
  have hrow : S.row D = head D i +
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) := by
    have hk : (DustCellRestriction.headDual (restrict n D)).beta ⟨i, hi⟩ ⟨j, hj⟩ =
        MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) :=
      (MultipartiteCountableMeasure.kernel_embed D n
        (.inl (some ⟨i, hi⟩)) (.inl (some ⟨j, hj⟩))).symm
    simp [RepeatContext.row, S, X, Selector.bit, hk, MultipartiteDust.head, restrict]
  have hcharge : S.charge D = head D j := by
    simp [RepeatContext.charge, S, X, MultipartiteDust.charge, Selector.bit,
      MultipartiteDust.head, restrict]
  have h := S.one_test hD
  rw [hrow, hcharge] at h
  linarith

/-- Greatest-dust maximality excludes every positive pair whose cross
penalty reaches the least full-repeat penalty of either head. -/
theorem pair_lt_repeatPenalty_at_greatest_dust {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L)
    (hmax : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) :
    -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) < repeatPenalty D i := by
  by_contra h
  obtain ⟨y, hy, hyd, hyv⟩ := exists_sorted_head_endpoint hx hD hopt i j hij hi hj (le_of_not_gt h)
  exact (not_lt_of_ge (hdust y hy (le_antisymm (hmax y hy) hyv))) hyd

/-- The actual optimal dual has the strict pair condition simultaneously
for both full-repeat penalties at the same selected profile. -/
theorem pair_lt_min_repeatPenalty_at_greatest_dust {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L)
    (hmax : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) :
    -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) <
      min (repeatPenalty D i) (repeatPenalty D j) := by
  have hs : MultipartiteCountableMeasure.kernel D (.inl (some j)) (.inl (some i)) =
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) := by
    rcases lt_or_gt_of_ne hij with h | h <;>
      simp [MultipartiteCountableMeasure.kernel, h, not_lt_of_gt h]
  apply lt_min (pair_lt_repeatPenalty_at_greatest_dust hx hmax hdust hD hopt i j hij hi hj)
  rw [← hs]
  exact pair_lt_repeatPenalty_at_greatest_dust hx hmax hdust hD hopt j i (Ne.symm hij) hj hi

/-- Every positive head has linear coefficient strictly below one whenever
another positive secondary head is present at the selected profile. -/
theorem head_lt_one_at_greatest_dust {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L)
    (hmax : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) : head D i < 1 := by
  have hstrict := pair_lt_min_repeatPenalty_at_greatest_dust hx hmax hdust hD hopt i j hij hi hj
  have htriangle := anchored_head_pair_test hD i j hij
  have hK := repeatPenalty_le_head hD j
  have hbox : head D i ≤ 1 := hD.1.2 _
  have hother := hstrict.trans_le (min_le_right _ _)
  linarith

/-- Every nonempty compact moment fiber admits an actual greatest-dust
value maximizer and an attained dual with all positive-head strict pair bounds. -/
theorem exists_greatest_dust_strict_optimum (L T Q : ℝ)
    (hne : (MultipartiteProfiles.momentFiber L T Q).Nonempty) :
    ∃ x ∈ MultipartiteProfiles.momentFiber L T Q,
      (∀ y ∈ MultipartiteProfiles.momentFiber L T Q,
        MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x) ∧
      (∀ y ∈ MultipartiteProfiles.momentFiber L T Q,
        MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
          MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x) ∧
      ∃ D ∈ feasible,
        objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x ∧
        ∀ i j, i ≠ j → 0 < x.2 i → 0 < x.2 j →
          -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) <
            min (repeatPenalty D i) (repeatPenalty D j) ∧ head D i < 1 := by
  obtain ⟨x, hx, hmax, hdust⟩ :=
    MultipartiteProfiles.exists_greatest_dust_moment_maximum L T Q hne
  obtain ⟨D, hD, hopt⟩ := exists_profile_optimal hx.1
  refine ⟨x, hx, hmax, hdust, D, hD, hopt.symm, ?_⟩
  intro i j hij hi hj
  have hmax' : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x := by
    simpa only [hx.2.1, hx.2.2] using hmax
  have hdust' : ∀ y ∈ MultipartiteProfiles.momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x := by
    simpa only [hx.2.1, hx.2.2] using hdust
  exact ⟨pair_lt_min_repeatPenalty_at_greatest_dust hx.1 hmax' hdust' hD hopt.symm i j hij hi hj,
    head_lt_one_at_greatest_dust hx.1 hmax' hdust' hD hopt.symm i j hij hi hj⟩

end Erdos1017.MultipartiteCountableDual

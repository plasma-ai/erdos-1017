module

public import Erdos1017.Multipartite.Dust.DustPointPromotion
public import Erdos1017.Multipartite.MultipartiteLowDensityCarrier

/-!
# Fixed-moment low-density comparison

The fixed-moment low-density comparison uses the countable value. A unit dust
penalty permits a moment-preserving strict improvement over the supplied dual
objective by promoting dust and completing part of one strictly subunit head.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteCountableDual

/-- One-point promotion and full-repeat completion produce a profile with the
same two moments whose countable value exceeds the supplied dual objective. -/
theorem exists_moment_improvement_of_unit_dust {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (hsum : Summable p)
    (s : ℝ) (hs : 0 < s) (hpen : penalty D = 1)
    (i : ℕ) (hi : 0 < p i) (hti : head D i < 1) :
    ∃ q : ℕ → ℝ, (∀ k, 0 ≤ q k) ∧ (∀ k, q k ≤ 1) ∧ Summable q ∧
      ∃ t : ℝ, 0 ≤ t ∧ t + (∑' k, q k) = s + (∑' k, p k) ∧
        (∑' k, (q k) ^ 2) = (∑' k, (p k) ^ 2) ∧ objective p s D < value q t := by
  let η := min s (p i) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηs : η < s := by dsimp [η]; linarith [min_le_left s (p i)]
  have hηi : η < p i := by dsimp [η]; linarith [min_le_right s (p i)]
  have hη1 : η ≤ 1 := hηi.le.trans (hp1 i)
  let u := Real.sqrt ((p i) ^ 2 - η ^ 2)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = (p i) ^ 2 - η ^ 2 := Real.sq_sqrt (by nlinarith)
  have hui : u < p i := by nlinarith [sq_pos_of_pos hη]
  let δ := p i - u
  have hδ : 0 < δ := sub_pos.mpr hui
  have hδeq : p i - δ = u := by dsimp [δ]; ring
  let r := prependMass η p
  have hr : ∀ k, 0 ≤ r k := prependMass_nonneg p hp η hη.le
  have hrsum : Summable r := prependMass_summable p hsum η
  have hr1 (k : ℕ) : r k ≤ 1 := by
    cases k with
    | zero => exact hη1
    | succ k => exact hp1 k
  have hri : r (i + 1) = p i := rfl
  let q := Function.update r (i + 1) u
  have hq (k : ℕ) : 0 ≤ q k := by
    by_cases hk : k = i + 1
    · subst k
      simpa [q] using hu
    · simpa [q, Function.update_of_ne, hk] using hr k
  have hq1 (k : ℕ) : q k ≤ 1 := by
    by_cases hk : k = i + 1
    · subst k
      simpa [q] using hui.le.trans (hp1 i)
    · simpa [q, Function.update_of_ne, hk] using hr1 k
  have hqsum : Summable q := hrsum.update (i + 1) u
  let t := s - η + δ
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htotal : t + (∑' k, q k) = s + (∑' k, p k) := by
    rw [show q = Function.update r (i + 1) u from rfl,
      (hrsum.hasSum.update (i + 1) u).tsum_eq, hri,
      show r = prependMass η p from rfl, prependMass_tsum p hsum η]
    dsimp only [t, δ]
    ring
  have hsqsum : Summable (fun k => (p k) ^ 2) := by
    apply hsum.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hp k, hp1 k]
  have hrsqsum : Summable (fun k => (r k) ^ 2) := by
    have heq : (fun k => (r k) ^ 2) = prependMass (η ^ 2) (fun k => (p k) ^ 2) := by
      funext k
      cases k <;> rfl
    rw [heq]
    exact prependMass_summable _ hsqsum _
  have hqmoment : (∑' k, (q k) ^ 2) = (∑' k, (p k) ^ 2) := by
    have heq : (fun k => (q k) ^ 2) =
        Function.update (fun k => (r k) ^ 2) (i + 1) (u ^ 2) := by
      funext k
      by_cases hk : k = i + 1 <;> simp [q, Function.update_of_ne, hk]
    rw [heq, (hrsqsum.hasSum.update (i + 1) (u ^ 2)).tsum_eq, hri,
      show r = prependMass η p from rfl, prependMass_square_tsum p hsqsum η, hu2]
    ring
  let F := prependDustPoint D
  have hF : F ∈ feasible := prependDustPoint_feasible hD
  obtain ⟨E, hE, hEobj⟩ := exists_completed_head_objective hF r hr hrsum
    (s - η) (by linarith) (i + 1) 1 0 δ hδ (by rw [hri, sub_zero, hδeq]; exact hu)
  have hqdef : Function.update r (i + 1) (r (i + 1) - 0 - δ) = q := by
    rw [hri, sub_zero, hδeq]
  have hobj : objective q t E = objective r (s - η) F -
      repeatPenalty F (i + 1) * (p i * δ - δ ^ 2 / 2) := by
    simp only [physicalObjective_eq_objective, sub_self, zero_mul, add_zero] at hEobj
    rw [hqdef, sub_zero, Function.update_eq_self, hri] at hEobj
    exact hEobj
  have hK : repeatPenalty F (i + 1) < 1 :=
    (repeatPenalty_le_head hF (i + 1)).trans_lt hti
  have hcorrection : p i * δ - δ ^ 2 / 2 = η ^ 2 / 2 := by
    dsimp only [δ]
    nlinarith [hu2]
  have hgain : objective p s D < objective q t E := by
    rw [hobj, show F = prependDustPoint D from rfl,
      show r = prependMass η p from rfl, prependDustPoint_gain hD p hp hsum η s hη.le,
      hpen, hcorrection]
    nlinarith [mul_pos (sub_pos.mpr hK) (sq_pos_of_pos hη)]
  exact ⟨q, hq, hq1, hqsum, t, ht, htotal, hqmoment,
    hgain.trans_le (objective_le_value q hq hqsum t hE)⟩

end Erdos1017.MultipartiteCountableDual

namespace Erdos1017.MultipartiteProfiles

/-- Actual countable value with one secondary head and the remaining dust. -/
def oneHeadValue (T Q : ℝ) : ℝ :=
  MultipartiteCountableDual.value (fun k => if k = 0 then Real.sqrt Q else 0)
    (T - Real.sqrt Q)

/-- The one-head comparator has a legal anchor-normalized mass and dust. -/
theorem oneHead_mass_bounds {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    0 ≤ Real.sqrt (∑' i, (x.2 i) ^ 2) ∧
      Real.sqrt (∑' i, (x.2 i) ^ 2) ≤ 1 ∧
      0 ≤ x.1 - Real.sqrt (∑' i, (x.2 i) ^ 2) := by
  have hQ : (∑' i, (x.2 i) ^ 2) ≤ 1 := by
    apply le_of_tendsto (squares_summable hx).hasSum.tendsto_sum_nat
    exact Filter.Eventually.of_forall fun n => hx.2.2.2 n
  have hQT : (∑' i, (x.2 i) ^ 2) ≤ x.1 ^ 2 := by
    apply le_of_tendsto (squares_summable hx).hasSum.tendsto_sum_nat
    apply Filter.Eventually.of_forall
    intro n
    have hs : 0 ≤ ∑ i ∈ Finset.range n, x.2 i :=
      Finset.sum_nonneg (fun i _ => hx.1.1.2 i)
    have hsum := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.range n)
      (fun i _ => hx.1.1.2 i)
    exact hsum.trans (by nlinarith [hx.2.2.1 n, hx.1.1.1])
  refine ⟨Real.sqrt_nonneg _, ?_, ?_⟩
  · exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hQ⟩
  · exact sub_nonneg.mpr ((Real.sqrt_le_iff).mpr ⟨hx.1.1.1, hQT⟩)

/-- The countable one-head comparator is the actual finite one-head value. -/
theorem oneHeadValue_eq_finite (T Q : ℝ) :
    oneHeadValue T Q =
      MultipartiteDust.value (fun _ : Fin 1 => Real.sqrt Q) (T - Real.sqrt Q) := by
  let p : ℕ → ℝ := fun k => if k = 0 then Real.sqrt Q else 0
  have hp (k : ℕ) : 0 ≤ p k := by dsimp only [p]; split_ifs <;> positivity
  have hsum : Summable p := summable_of_ne_finset_zero (s := {0}) (by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [p, hk])
  have hobj (D : MultipartiteCountableDual.Coefficients) :
      MultipartiteCountableDual.objective p (T - Real.sqrt Q) D =
        MultipartiteDust.objective (fun _ : Fin 1 => Real.sqrt Q) (T - Real.sqrt Q)
          (MultipartiteCountableDual.restrict 1 D) := by
    have hpair : (∑' z : ℕ × ℕ, if z.1 < z.2 then
        MultipartiteCountableDual.pair D z.1 z.2 * p z.1 * p z.2 else 0) = 0 := by
      have hz (z : ℕ × ℕ) : (if z.1 < z.2 then
          MultipartiteCountableDual.pair D z.1 z.2 * p z.1 * p z.2 else 0) = 0 := by
        by_cases hz0 : z.1 = 0 <;> by_cases hz1 : z.2 = 0 <;> simp [p, hz0, hz1]
      simpa only [tsum_zero] using tsum_congr hz
    unfold MultipartiteCountableDual.objective
    rw [hpair]
    have hh : (∑' k, MultipartiteCountableDual.head D k * p k) =
        MultipartiteCountableDual.head D 0 * Real.sqrt Q := by
      rw [tsum_eq_single 0 (by intro k hk; simp [p, hk])]
      simp [p]
    have hi : (∑' k, MultipartiteCountableDual.incident D k * p k * (T - Real.sqrt Q)) =
        MultipartiteCountableDual.incident D 0 * Real.sqrt Q * (T - Real.sqrt Q) := by
      rw [tsum_eq_single 0 (by intro k hk; simp [p, hk])]
      simp [p]
    rw [hh, hi]
    simp [MultipartiteDust.objective, MultipartiteCountableDual.restrict,
      MultipartiteDust.head, MultipartiteDust.linear, MultipartiteDust.pair,
      MultipartiteDust.incident, MultipartiteDust.penalty, MultipartiteCountableDual.head,
      MultipartiteCountableDual.linear, MultipartiteCountableDual.incident,
      MultipartiteCountableDual.penalty]
  change MultipartiteCountableDual.value p (T - Real.sqrt Q) = _
  apply le_antisymm
  · obtain ⟨D, hD, heq⟩ := MultipartiteCountableDual.exists_value_eq p hp hsum (T - Real.sqrt Q)
    rw [heq, hobj]
    exact MultipartiteDust.objective_le_value _ _ _
      (MultipartiteCountableDual.restrict_mem_feasible hD 1)
  · have h := MultipartiteCountableDual.finite_value_le_value p hp hsum (T - Real.sqrt Q) 1
    have hprefix : (fun k : Fin 1 => p k.val) = fun _ : Fin 1 => Real.sqrt Q := by
      funext k
      simp [p, Fin.eq_zero k]
    rwa [hprefix] at h

theorem limitValue_eq_oneHeadValue_of_second_zero {L : ℝ} {x : Profile}
    (hx : x ∈ space L) (hsecond : x.2 1 = 0) :
    limitValue x = oneHeadValue x.1 (∑' k, (x.2 k) ^ 2) := by
  have htail (k : ℕ) (hk : k ≠ 0) : x.2 k = 0 := by
    have hle := hx.2.1 (by omega : 1 ≤ k)
    rw [hsecond] at hle
    exact le_antisymm hle (hx.1.1.2 k)
  have hsum : (∑' k, x.2 k) = x.2 0 := tsum_eq_single 0 (by intro k hk; exact htail k hk)
  have hsq : (∑' k, (x.2 k) ^ 2) = (x.2 0) ^ 2 :=
    tsum_eq_single 0 (by intro k hk; rw [htail k hk]; norm_num)
  have hsqrt : Real.sqrt (∑' k, (x.2 k) ^ 2) = x.2 0 := by
    rw [hsq, Real.sqrt_sq (hx.1.1.2 0)]
  have hheads : (fun k => if k = 0 then Real.sqrt (∑' j, (x.2 j) ^ 2) else 0) = x.2 := by
    funext k
    by_cases hk : k = 0
    · simp [hk, hsqrt]
    · simp [hk, htail k hk]
  rw [oneHeadValue, hheads, hsqrt, ← hsum, ← dust_eq_sub_tsum hx,
    MultipartiteCountableDual.value_eq_profile_limit hx]

/-- The actual compact-profile value is bounded by the one-head comparator
or one third of edge mass, with both moments fixed throughout the proof. -/
theorem limitValue_le_max_oneHead {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    limitValue x ≤ max (oneHeadValue x.1 (∑' i, (x.2 i) ^ 2))
      ((x.1 + (x.1 ^ 2 - ∑' i, (x.2 i) ^ 2) / 2) / 3) := by
  by_contra h
  have hgt := lt_of_not_ge h
  obtain ⟨y, hy, hymax, hydust, D, hD, hopt, hstrict⟩ :=
    MultipartiteCountableDual.exists_greatest_dust_strict_optimum L x.1
      (∑' i, (x.2 i) ^ 2) ⟨x, hx, rfl, rfl⟩
  have hxy := hymax x ⟨hx, rfl, rfl⟩
  have hone : oneHeadValue x.1 (∑' i, (x.2 i) ^ 2) < limitValue y :=
    (le_max_left _ _).trans_lt (hgt.trans_le hxy)
  have hlarge : (y.1 + (y.1 ^ 2 - ∑' i, (y.2 i) ^ 2) / 2) / 3 < limitValue y := by
    rw [hy.2.1, hy.2.2]
    exact (le_max_right _ _).trans_lt (hgt.trans_le hxy)
  have h1 : 0 < y.2 1 := by
    by_contra h1
    have hz : y.2 1 = 0 := le_antisymm (le_of_not_gt h1) (hy.1.1.1.2 1)
    have heq := limitValue_eq_oneHeadValue_of_second_zero hy.1 hz
    rw [hy.2.1, hy.2.2] at heq
    linarith
  have h0 : 0 < y.2 0 := h1.trans_le (hy.1.2.1 (by omega : 0 ≤ 1))
  have hhead (i : ℕ) (hi : 0 < y.2 i) : MultipartiteCountableDual.head D i < 1 := by
    by_cases hi0 : i = 0
    · subst i
      exact (hstrict 0 1 (by omega) h0 h1).2
    · exact (hstrict i 0 hi0 hi h0).2
  have hunit := MultipartiteCountableDual.unit_dust_of_value_gt_third
    hy.1 hD hopt hhead hlarge
  obtain ⟨q, hq, hq1, hqsum, t, ht, htotal, hmoment, hgain⟩ :=
    MultipartiteCountableDual.exists_moment_improvement_of_unit_dust hD y.2
      hy.1.1.1.2 hy.1.1.2.2 (atoms_summable hy.1) (dust y)
      hunit.1 hunit.2.2 0 h0 (hhead 0 h0)
  have hT : t + (∑' k, q k) = y.1 := by
    rw [htotal, dust_eq_sub_tsum hy.1]
    ring
  have hQ : (∑' k, (q k) ^ 2) ≤ 1 := by
    rw [hmoment]
    apply le_of_tendsto (squares_summable hy.1).hasSum.tendsto_sum_nat
    exact Filter.Eventually.of_forall fun n => hy.1.2.2.2 n
  obtain ⟨w, hw, hwT, hwdust, hwQ, hwvalue⟩ := exists_sorted_representative
    q hq hq1 hqsum t ht L (hT.le.trans hy.1.1.2.1) hQ
  have hwmoment : w ∈ momentFiber L x.1 (∑' i, (x.2 i) ^ 2) := by
    refine ⟨hw, ?_, ?_⟩
    · rw [hwT, hT, hy.2.1]
    · rw [hwQ, hmoment, hy.2.2]
  rw [hopt, hwvalue] at hgain
  exact (not_lt_of_ge (hymax w hwmoment)) hgain

end Erdos1017.MultipartiteProfiles

namespace Erdos1017.MultipartiteCountableDual

/-- The fixed-moment comparison holds for every summable normalized profile,
including unsorted heads, zero heads and either endpoint square moment. -/
theorem value_le_max_oneHead (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s)
    (hQ : (∑' i, (p i) ^ 2) ≤ 1) :
    value p s ≤ max
      (MultipartiteProfiles.oneHeadValue (s + ∑' i, p i) (∑' i, (p i) ^ 2))
      (((s + ∑' i, p i) + ((s + ∑' i, p i) ^ 2 - ∑' i, (p i) ^ 2) / 2) / 3) := by
  obtain ⟨x, hx, hxT, hxdust, hxQ, hxvalue⟩ :=
    MultipartiteProfiles.exists_sorted_representative p hp hp1 hsum s hs
      (s + ∑' i, p i) le_rfl hQ
  have h := MultipartiteProfiles.limitValue_le_max_oneHead hx
  rwa [hxT, hxQ, ← hxvalue] at h

end Erdos1017.MultipartiteCountableDual

namespace Erdos1017.MultipartiteDust

/-- Finite head profiles satisfy the same actual fixed-moment comparison. -/
theorem value_le_max_oneHead {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s)
    (hQ : (∑ i, (p i) ^ 2) ≤ 1) :
    value p s ≤ max
      (MultipartiteProfiles.oneHeadValue (s + ∑ i, p i) (∑ i, (p i) ^ 2))
      (((s + ∑ i, p i) + ((s + ∑ i, p i) ^ 2 - ∑ i, (p i) ^ 2) / 2) / 3) := by
  let q : ℕ → ℝ := fun k => if hk : k < m then p ⟨k, hk⟩ else 0
  have hq (k : ℕ) : 0 ≤ q k := by
    dsimp only [q]
    split_ifs with hk
    · exact (hp ⟨k, hk⟩).1
    · exact le_rfl
  have hq1 (k : ℕ) : q k ≤ 1 := by
    dsimp only [q]
    split_ifs with hk
    · exact (hp ⟨k, hk⟩).2
    · exact zero_le_one
  have hqsum : Summable q := summable_of_ne_finset_zero (s := Finset.range m) (by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [q, hk])
  have htotal : (∑' k, q k) = ∑ i, p i := by
    rw [tsum_eq_sum (s := Finset.range m) (by
      intro k hk
      simp only [Finset.mem_range] at hk
      simp [q, hk]), ← Fin.sum_univ_eq_sum_range]
    simp [q]
  have hmoment : (∑' k, (q k) ^ 2) = ∑ i, (p i) ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range m) (by
      intro k hk
      simp only [Finset.mem_range] at hk
      simp [q, hk]), ← Fin.sum_univ_eq_sum_range]
    simp [q]
  have hbound := MultipartiteCountableDual.value_le_max_oneHead q hq hq1 hqsum s hs
    (by rwa [hmoment])
  rw [htotal, hmoment] at hbound
  have hfinite := MultipartiteCountableDual.finite_value_le_value q hq hqsum s m
  have hprefix : (fun i : Fin m => q i.val) = p := by
    funext i
    simp [q]
  rw [hprefix] at hfinite
  exact hfinite.trans hbound

end Erdos1017.MultipartiteDust

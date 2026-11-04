module

public import Erdos1017.Multipartite.Countable.CountableHeadCount
public import Erdos1017.Multipartite.Countable.CountableSupportedRows
public import Erdos1017.Multipartite.Dust.CountableDustMask

/-!
# Conditional head count at a selected optimizer

At the selected density optimizer, a dual's own multiplier above one half gives
the finite head bound when dust is positive and excludes dust-free profiles with
two positive secondary heads; the multiplier exists for an attained dual, with
row stationarity derived rather than postulated.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- At the actual selected density optimizer, every optimal dual's own
multiplier above one half gives the source finite head bound when dust is
positive. Zero slots are erased with its multiplier explicitly preserved. -/
theorem positive_dust_head_count {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ)
    (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j)
    (hs : 0 < MultipartiteProfiles.dust x) :
    Finite {k // 0 < x.2 k} ∧ Nat.card {k // 0 < x.2 k} ≤
      ⌈(1 / (1 + x.1)) * (1 - ℓ) / (2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε))⌉₊ := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.1.2
  have hden : 0 < 1 + x.1 := by linarith [hx.1.1.1.1]
  have hmaxMoment : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x := by
    intro y hy
    have hyDensity : y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε := by
      refine ⟨hy.1, ?_⟩
      change 1 + (∑' k, (y.2 k) ^ 2) = 2 * ε * (1 + y.1) ^ 2
      rw [hy.2.1, hy.2.2]
      exact hx.2
    have h := hmax y hyDensity
    change MultipartiteProfiles.limitValue y / (1 + y.1) ^ 2 ≤
      MultipartiteProfiles.limitValue x / (1 + x.1) ^ 2 at h
    rw [hy.2.1] at h
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mp h
  obtain ⟨E, hE, hEopt, hanchor, hheads, hzero⟩ := exists_supported_rows_optimal hx.1 hD hopt
  have hrowsE (k : ℕ) (hk : 0 < x.2 k) : headRow x.2 (MultipartiteProfiles.dust x) E k -
      anchorRow x.2 (MultipartiteProfiles.dust x) E = ℓ * (x.2 k - 1) := by
    rw [hheads k hk, hanchor]
    exact hrows k hk
  have ht (k : ℕ) (hk : 0 < x.2 k) : head E k < 1 := by
    by_cases hki : k = i
    · subst k
      exact head_lt_one_at_greatest_dust hx.1 hmaxMoment hdust hE hEopt i j hij hi hj
    · exact head_lt_one_at_greatest_dust hx.1 hmaxMoment hdust hE hEopt k i hki hk hi
  have hb (k : ℕ) (hk : 0 < x.2 k) :
      ℓ ≤ twoRepeatPenalty E k ∧ repeatPenalty E k = twoRepeatPenalty E k ∧ ℓ < 1 :=
    twoRepeat_bounds_of_half_lt_multiplier hε hx hmax hxvalue hE hEopt ℓ hℓ k hk (ht k hk) (hrowsE k hk)
  have hK (k : ℕ) (hk : 0 < x.2 k) : ℓ ≤ twoRepeatPenalty E k := (hb k hk).1
  have hpair : ∀ k l, k ≠ l → 0 < x.2 k → 0 < x.2 l →
      -MultipartiteCountableMeasure.kernel E (.inl (some k)) (.inl (some l)) ≤ ℓ := by
    obtain ⟨m, _, hpairm, hunique⟩ := exists_unique_head_multiplier hε hx hmax hxvalue hE hEopt i hi
    have hm : ℓ = m := hunique ℓ hrowsE
    rwa [← hm] at hpairm
  have hstrict : ∀ k l, k ≠ l → 0 < x.2 k → 0 < x.2 l →
      -MultipartiteCountableMeasure.kernel E (.inl (some k)) (.inl (some l)) <
        min (twoRepeatPenalty E k) (twoRepeatPenalty E l) := by
    intro k l hkl hk hl
    have h := pair_lt_min_repeatPenalty_at_greatest_dust hx.1 hmaxMoment hdust hE hEopt k l hkl hk hl
    rwa [(hb k hk).2.1, (hb l hl).2.1] at h
  let g := anchorRow x.2 (MultipartiteProfiles.dust x) E - ℓ
  have hgamma := positive_gamma_of_half_lt_multiplier hε hx hmax hxvalue hE hEopt ℓ hℓ hrowsE i hi (ht i hi)
  have hg : 0 < g := by
    have hdiv : 0 < g / (1 + x.1) := by rw [hgamma.2.2]; exact hgamma.2.1
    have h := mul_pos hdiv hden
    rwa [div_mul_cancel₀ _ hden.ne'] at h
  have hci (k : ℕ) (hk : 0 < x.2 k) : g ≤ incident E k :=
    (incident_floor_of_head_multiplier hε hx hmax hxvalue hE hEopt ℓ hrowsE k hk hs).2
  have hpen : g ≤ penalty E := penalty_floor_of_head_multiplier hε hx hmax hxvalue hE hEopt ℓ hrowsE i hi hs
  obtain ⟨hfinite, hcard⟩ := positive_head_count_le hE x.2 hp hzero ℓ g hℓ hg ht hK hpair hstrict hci hpen
  have hgeq : g = (2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε)) * (1 + x.1) :=
    (div_eq_iff hden.ne').mp hgamma.2.2
  have hratio : (1 - ℓ) / g =
      (1 / (1 + x.1)) * (1 - ℓ) / (2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε)) := by
    rw [hgeq]
    field_simp [hden.ne', hgamma.2.1.ne']
  rw [hratio] at hcard
  exact ⟨hfinite, hcard⟩

/-- A dust-free selected countermaximum with two positive secondary heads
cannot have its own actual multiplier above one half. -/
theorem dust_free_impossible_of_half_lt_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ)
    (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j)
    (hs : MultipartiteProfiles.dust x = 0) : False := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.1.2
  have hden : 0 < 1 + x.1 := by linarith [hx.1.1.1.1]
  have hmaxMoment : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y ≤ MultipartiteProfiles.limitValue x := by
    intro y hy
    have hyDensity : y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε := by
      refine ⟨hy.1, ?_⟩
      change 1 + (∑' k, (y.2 k) ^ 2) = 2 * ε * (1 + y.1) ^ 2
      rw [hy.2.1, hy.2.2]
      exact hx.2
    have h := hmax y hyDensity
    change MultipartiteProfiles.limitValue y / (1 + y.1) ^ 2 ≤
      MultipartiteProfiles.limitValue x / (1 + x.1) ^ 2 at h
    rw [hy.2.1] at h
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mp h
  obtain ⟨F, hF, hFopt, hanchor, hheads, hzeroF⟩ := exists_supported_rows_optimal hx.1 hD hopt
  let E := maskDust F
  have hE : E ∈ feasible := maskDust_feasible hF
  have hEopt : objective x.2 (MultipartiteProfiles.dust x) E = MultipartiteProfiles.limitValue x := by
    rw [hs, show E = maskDust F from rfl, objective_maskDust]
    simpa only [hs] using hFopt
  have hrowsE (k : ℕ) (hk : 0 < x.2 k) : headRow x.2 (MultipartiteProfiles.dust x) E k -
      anchorRow x.2 (MultipartiteProfiles.dust x) E = ℓ * (x.2 k - 1) := by
    have hheads0 : headRow x.2 0 F k = headRow x.2 0 D k := by simpa only [hs] using hheads k hk
    have hanchor0 : anchorRow x.2 0 F = anchorRow x.2 0 D := by simpa only [hs] using hanchor
    simp only [hs, E, headRow_maskDust, anchorRow_maskDust]
    rw [hheads0, hanchor0]
    simpa only [hs] using hrows k hk
  have hzero (k : ℕ) (hk : x.2 k = 0) : head E k = 0 ∧ incident E k = 0 ∧
      ∀ l, pair E k l = 0 ∧ pair E l k = 0 := by
    have hz := hzeroF k hk
    exact ⟨hz.1, rfl, hz.2.2⟩
  have ht (k : ℕ) (hk : 0 < x.2 k) : head E k < 1 := by
    by_cases hki : k = i
    · subst k
      exact head_lt_one_at_greatest_dust hx.1 hmaxMoment hdust hE hEopt i j hij hi hj
    · exact head_lt_one_at_greatest_dust hx.1 hmaxMoment hdust hE hEopt k i hki hk hi
  have hb (k : ℕ) (hk : 0 < x.2 k) :
      ℓ ≤ twoRepeatPenalty E k ∧ repeatPenalty E k = twoRepeatPenalty E k ∧ ℓ < 1 :=
    twoRepeat_bounds_of_half_lt_multiplier hε hx hmax hxvalue hE hEopt ℓ hℓ k hk (ht k hk) (hrowsE k hk)
  have hK (k : ℕ) (hk : 0 < x.2 k) : ℓ ≤ twoRepeatPenalty E k := (hb k hk).1
  have hpair : ∀ k l, k ≠ l → 0 < x.2 k → 0 < x.2 l →
      -MultipartiteCountableMeasure.kernel E (.inl (some k)) (.inl (some l)) ≤ ℓ := by
    obtain ⟨m, _, hpairm, hunique⟩ := exists_unique_head_multiplier hε hx hmax hxvalue hE hEopt i hi
    have hm : ℓ = m := hunique ℓ hrowsE
    rwa [← hm] at hpairm
  have hstrict : ∀ k l, k ≠ l → 0 < x.2 k → 0 < x.2 l →
      -MultipartiteCountableMeasure.kernel E (.inl (some k)) (.inl (some l)) <
        min (twoRepeatPenalty E k) (twoRepeatPenalty E l) := by
    intro k l hkl hk hl
    have h := pair_lt_min_repeatPenalty_at_greatest_dust hx.1 hmaxMoment hdust hE hEopt k l hkl hk hl
    rwa [(hb k hk).2.1, (hb l hl).2.1] at h
  exact hij (positive_heads_unique_of_zero_dust hE x.2 hp hzero ℓ hℓ ht hK hpair hstrict
    rfl (fun _ => rfl) rfl i j hi hj)

/-- The complete conditional head-count consequence at an actual selected
countermaximum: dust-free profiles are excluded and positive dust has the
finite bound, with the original dual's own multiplier retained. -/
theorem head_count_of_half_lt_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ)
    (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) :
    0 < MultipartiteProfiles.dust x ∧ Finite {k // 0 < x.2 k} ∧ Nat.card {k // 0 < x.2 k} ≤
      ⌈(1 / (1 + x.1)) * (1 - ℓ) / (2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε))⌉₊ := by
  have hs : 0 < MultipartiteProfiles.dust x := by
    apply lt_of_le_of_ne (MultipartiteProfiles.dust_nonneg hx.1)
    intro hzero
    exact dust_free_impossible_of_half_lt_multiplier hε hx hmax hdust hxvalue hD hopt ℓ hℓ hrows
      i j hij hi hj hzero.symm
  exact ⟨hs, positive_dust_head_count hε hx hmax hdust hxvalue hD hopt ℓ hℓ hrows i j hij hi hj hs⟩

/-- The multiplier in the conditional head-count theorem exists for an
actual attained dual; row stationarity is derived rather than postulated. -/
theorem exists_head_count_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hdust : ∀ y ∈ MultipartiteProfiles.momentFiber (1 / Real.sqrt ε - 1) x.1 (∑' k, (x.2 k) ^ 2),
      MultipartiteProfiles.limitValue y = MultipartiteProfiles.limitValue x →
        MultipartiteProfiles.dust y ≤ MultipartiteProfiles.dust x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) :
    ∃ D ∈ feasible,
      objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x ∧
      ∃ ℓ : ℝ,
        (∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
          anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1)) ∧
        (∀ k l, k ≠ l → 0 < x.2 k → 0 < x.2 l →
          -MultipartiteCountableMeasure.kernel D (.inl (some k)) (.inl (some l)) ≤ ℓ) ∧
        (1 / 2 < ℓ → 0 < MultipartiteProfiles.dust x ∧ Finite {k // 0 < x.2 k} ∧
          Nat.card {k // 0 < x.2 k} ≤
            ⌈(1 / (1 + x.1)) * (1 - ℓ) / (2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε))⌉₊) := by
  obtain ⟨D, hD, hopt⟩ := exists_profile_optimal hx.1
  obtain ⟨ℓ, hrows, hpair, _⟩ := exists_unique_head_multiplier hε hx hmax hxvalue hD hopt.symm i hi
  exact ⟨D, hD, hopt.symm, ℓ, hrows, hpair, fun hℓ =>
    head_count_of_half_lt_multiplier hε hx hmax hdust hxvalue hD hopt.symm ℓ hℓ hrows i j hij hi hj⟩

end Erdos1017.MultipartiteCountableDual

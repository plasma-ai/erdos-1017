module

public import Erdos1017.Multipartite.TightCounts
public import Erdos1017.Multipartite.Selector.PolyhedralVertex
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Tight-count patterns at an interior vertex

Vertices of the seven-coefficient feasible set: local
finiteness, active constraints at an interior vertex, and the two possible
tight-count patterns. The geometric extremality hypothesis is retained
throughout; no rank or active-equation hypothesis replaces it.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.VertexClassification

open Filter Set
open scoped Topology

/-- Coordinates are `t₁,t₂,v,c,c₁,c₂,p`, in this order. -/
abbrev Coefficients := Fin 7 → ℝ

/-- The two distinguished types remain Boolean before the repetition argument. -/
abbrev State := Bool × Bool

abbrev Test := State × ℕ

def constant (state : State) : Coefficients →ₗ[ℝ] ℝ :=
  (if state.1 then (LinearMap.proj 0 : Coefficients →ₗ[ℝ] ℝ) else 0) +
    (if state.2 then (LinearMap.proj 1 : Coefficients →ₗ[ℝ] ℝ) else 0) -
    (if state.1 && state.2 then (LinearMap.proj 3 : Coefficients →ₗ[ℝ] ℝ) else 0)

def slope (state : State) : Coefficients →ₗ[ℝ] ℝ :=
  (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ) - (if state.1 then (LinearMap.proj 4 : Coefficients →ₗ[ℝ] ℝ) else 0) -
    (if state.2 then (LinearMap.proj 5 : Coefficients →ₗ[ℝ] ℝ) else 0)

/-- Each all-count constraint is a linear inequality in the seven coefficients. -/
def test (i : Test) : Coefficients →ₗ[ℝ] ℝ :=
  constant i.1 + (i.2 : ℝ) • slope i.1 -
    ((i.2 : ℝ) * ((i.2 : ℝ) - 1) / 2) • (LinearMap.proj 6 : Coefficients →ₗ[ℝ] ℝ)

def feasible : Set Coefficients :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i, test i x ≤ 1}

theorem test_eq_value (x : Coefficients) (state : State) (n : ℕ) :
    test (state, n) x = TightCounts.value (constant state x) (slope state x) (x 6) n := by
  simp only [test, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, TightCounts.value]
  ring

/-- A positive quadratic penalty uniformly dominates bounded constant and slope terms. -/
theorem uniform_tail (M a : ℝ) (hM : 0 < M) (ha : 0 < a) :
    ∃ N : ℕ, ∀ (C s p : ℝ), C ≤ M → s ≤ M → a ≤ p →
      ∀ n : ℕ, N ≤ n → TightCounts.value C s p n < 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * M / a + 2)
  refine ⟨N, ?_⟩
  intro C s p hC hs hp n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hratio : 0 < 4 * M / a := div_pos (by positivity) ha
  have hn₂ : 2 < (n : ℝ) := by linarith
  have hlarge : 4 * M < a * ((n : ℝ) - 1) := by
    have h := (div_lt_iff₀ ha).mp (show 4 * M / a < (n : ℝ) - 1 by linarith)
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ n by positivity)
  have hpen := mul_nonneg (sub_nonneg.mpr hp)
    (show 0 ≤ (n : ℝ) * ((n : ℝ) - 1) by apply mul_nonneg <;> linarith)
  have hdecay := mul_pos (show 0 < (n : ℝ) by positivity)
    (show 0 < a * ((n : ℝ) - 1) - 4 * M by linarith)
  have hMscale := mul_pos hM (show 0 < (n : ℝ) - 1 by linarith)
  unfold TightCounts.value
  nlinarith

/-- Each state has a uniform tail cutoff on a neighborhood of a positive-penalty point. -/
theorem state_tail_neighborhood (x : Coefficients) (hp : 0 < x 6) (state : State) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n : ℕ, N ≤ n → test (state, n) y < 1 := by
  let M := |constant state x| + |slope state x| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨N, hN⟩ := uniform_tail M (x 6 / 2) hM (half_pos hp)
  have hC : ∀ᶠ y in 𝓝 x, constant state y < M :=
    (constant state).continuous_of_finiteDimensional.continuousAt.eventually_lt_const
      (by dsimp [M]; have := le_abs_self (constant state x); have := abs_nonneg (slope state x); linarith)
  have hS : ∀ᶠ y in 𝓝 x, slope state y < M :=
    (slope state).continuous_of_finiteDimensional.continuousAt.eventually_lt_const
      (by dsimp [M]; have := le_abs_self (slope state x); have := abs_nonneg (constant state x); linarith)
  have hP : ∀ᶠ y in 𝓝 x, x 6 / 2 < y 6 :=
    (continuous_apply 6).continuousAt.eventually_const_lt (by linarith)
  refine ⟨N, ?_⟩
  filter_upwards [hC, hS, hP] with y hC hS hP
  intro n hn
  rw [test_eq_value]
  exact hN _ _ _ hC.le hS.le hP.le n hn

/-- Near a strictly positive coefficient vector, only finitely many count tests matter. -/
theorem local_finiteness (x : Coefficients) (hx : ∀ i, 0 < x i) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x,
      (∀ i, 0 < y i) ∧ ∀ state n, N ≤ n → test (state, n) y < 1 := by
  choose N hN using state_tail_neighborhood x (hx 6)
  have htail := Filter.eventually_all.mpr hN
  have hpos : ∀ᶠ y in 𝓝 x, ∀ i, 0 < y i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually_const_lt (hx i)
  refine ⟨Finset.univ.sup N, ?_⟩
  filter_upwards [htail, hpos] with y hy hpos
  refine ⟨hpos, ?_⟩
  intro state n hn
  exact hy state n ((Finset.le_sup (Finset.mem_univ state)).trans hn)

/-- A finite window contains at least seven active count constraints at an interior vertex. -/
theorem seven_active_tests (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i) :
    ∃ N : ℕ, 7 ≤ Nat.card {i : State × Fin N // test (i.1, i.2.val) x = 1} := by
  obtain ⟨N, hN⟩ := local_finiteness x hx
  let L : State × Fin N → Coefficients →L[ℝ] ℝ :=
    fun i => (test (i.1, i.2.val)).toContinuousLinearMap
  have hlocal : ∃ U ∈ 𝓝 x, ∀ y ∈ U, (∀ i, L i y ≤ 1) → y ∈ feasible := by
    refine ⟨{y | (∀ i, 0 < y i) ∧ ∀ state n, N ≤ n → test (state, n) y < 1}, hN, ?_⟩
    intro y hy htests
    refine ⟨fun i => (hy.1 i).le, ?_⟩
    rintro ⟨state, n⟩
    by_cases hn : n < N
    · exact htests (state, ⟨n, hn⟩)
    · exact (hy.2 state n (Nat.le_of_not_gt hn)).le
  have hcard := PolyhedralVertex.finrank_le_active_card feasible x L hvertex
    (fun i => hvertex.1.2 (i.1, i.2.val)) hlocal
  refine ⟨N, ?_⟩
  simpa [L, Module.finrank_pi_fintype] using hcard

/-- The finite set of tight counts in a fixed state and window. -/
def tightCounts (x : Coefficients) (N : ℕ) (state : State) : Finset ℕ :=
  (Finset.range N).filter fun n => test (state, n) x = 1

/-- A feasible state has at most two tight counts, regardless of the cutoff. -/
theorem tightCounts_card_le_two (x : Coefficients) (hx : x ∈ feasible)
    (hp : 0 < x 6) (N : ℕ) (state : State) :
    (tightCounts x N state).card ≤ 2 := by
  classical
  let T := tightCounts x N state
  by_cases hT : T.Nonempty
  · let k := T.min' hT
    have hk : k ∈ T := Finset.min'_mem T hT
    have hsub : T ⊆ {k, k + 1} := by
      intro n hn
      have hkn : k ≤ n := Finset.min'_le T n hn
      by_cases heq : k = n
      · simp [← heq]
      · have hlt : k < n := lt_of_le_of_ne hkn heq
        have hkt : test (state, k) x = 1 := (Finset.mem_filter.mp hk).2
        have hnt : test (state, n) x = 1 := (Finset.mem_filter.mp hn).2
        have hadj := TightCounts.tight_counts_adjacent (constant state x) (slope state x)
          (x 6) hp (fun m => by rw [← test_eq_value]; exact hx.2 (state, m))
          k n hlt (by rwa [← test_eq_value]) (by rwa [← test_eq_value])
        simp [hadj]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp_all [T]

/-- Splitting the active tests by Boolean state gives the four tight-count cardinalities. -/
theorem active_card_eq_sum (x : Coefficients) (N : ℕ) :
    Nat.card {i : State × Fin N // test (i.1, i.2.val) x = 1} =
      ∑ state : State, (tightCounts x N state).card := by
  classical
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun state (n : Fin N) => test (state, n.val) x = 1)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro state _
  let e : {n : Fin N // test (state, n.val) x = 1} ≃
      {n : ℕ // n ∈ tightCounts x N state} :=
    { toFun := fun n => ⟨n.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.val.isLt, n.property⟩⟩
      invFun := fun n => ⟨⟨n.val, Finset.mem_range.mp (Finset.mem_filter.mp n.property).1⟩,
        (Finset.mem_filter.mp n.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

/-- At least seven tests among four states force each state to be active. -/
theorem every_state_tight (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i) :
    ∀ state, ∃ n, test (state, n) x = 1 := by
  obtain ⟨N, hN⟩ := seven_active_tests x hvertex hx
  rw [active_card_eq_sum] at hN
  have hbound := tightCounts_card_le_two x hvertex.1 (hx 6) N
  intro state
  have hcard : 0 < (tightCounts x N state).card := by
    have h00 := hbound (false, false)
    have h10 := hbound (true, false)
    have h01 := hbound (false, true)
    have h11 := hbound (true, true)
    simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hN
    rcases state with ⟨a, b⟩
    cases a <;> cases b <;> omega
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hcard
  exact ⟨n, (Finset.mem_filter.mp hn).2⟩

/-- A double-tight state has adjacent tight counts and a nonnegative integral slope. -/
def DoubleTight (x : Coefficients) (state : State) : Prop :=
  ∃ k : ℕ, test (state, k) x = 1 ∧ test (state, k + 1) x = 1

theorem doubleTight_of_card_two (x : Coefficients) (hx : x ∈ feasible)
    (hp : 0 < x 6) (N : ℕ) (state : State)
    (hcard : (tightCounts x N state).card = 2) : DoubleTight x state := by
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  have ha : test (state, a) x = 1 := by
    have : a ∈ tightCounts x N state := by rw [hset]; simp
    exact (Finset.mem_filter.mp this).2
  have hb : test (state, b) x = 1 := by
    have : b ∈ tightCounts x N state := by rw [hset]; simp
    exact (Finset.mem_filter.mp this).2
  have hadj : ∀ m n, m < n → test (state, m) x = 1 → test (state, n) x = 1 → n = m + 1 := by
    intro m n hmn hm hn
    exact TightCounts.tight_counts_adjacent _ _ _ hp
      (fun k => by rw [← test_eq_value]; exact hx.2 (state, k)) m n hmn
      (by rwa [← test_eq_value]) (by rwa [← test_eq_value])
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨a, ha, by simpa [hadj a b hab ha hb] using hb⟩
  · exact ⟨b, hb, by simpa [hadj b a hba hb ha] using ha⟩

/-- No two Boolean states can both fail to be double-tight at an interior vertex. -/
theorem at_most_one_not_doubleTight (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i)
    (state other : State) (hne : state ≠ other) :
    DoubleTight x state ∨ DoubleTight x other := by
  obtain ⟨N, hN⟩ := seven_active_tests x hvertex hx
  rw [active_card_eq_sum] at hN
  have hbound := tightCounts_card_le_two x hvertex.1 (hx 6) N
  by_contra h
  have hs : (tightCounts x N state).card ≤ 1 := by
    have hb := hbound state
    have hn : (tightCounts x N state).card ≠ 2 :=
      fun hc => h (Or.inl (doubleTight_of_card_two x hvertex.1 (hx 6) N state hc))
    omega
  have ho : (tightCounts x N other).card ≤ 1 := by
    have hb := hbound other
    have hn : (tightCounts x N other).card ≠ 2 :=
      fun hc => h (Or.inr (doubleTight_of_card_two x hvertex.1 (hx 6) N other hc))
    omega
  have h00 := hbound (false, false)
  have h10 := hbound (true, false)
  have h01 := hbound (false, true)
  have h11 := hbound (true, true)
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hN
  rcases state with ⟨a, b⟩
  rcases other with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all <;> omega

theorem slope_of_doubleTight (x : Coefficients) (state : State)
    (h : DoubleTight x state) : ∃ k : ℕ, slope state x = x 6 * (k : ℝ) := by
  obtain ⟨k, hk, hk₁⟩ := h
  refine ⟨k, ?_⟩
  exact TightCounts.slope_of_adjacent_tight _ _ _ k
    (by rwa [← test_eq_value]) (by rwa [← test_eq_value])

theorem slope_relation (x : Coefficients) :
    slope (false, false) x + slope (true, true) x =
      slope (true, false) x + slope (false, true) x := by
  simp [slope]
  ring

/-- The fourth slope is integral once the other three are integral. -/
theorem integer_slopes (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i) :
    ∀ state, ∃ z : ℤ, slope state x = x 6 * (z : ℝ) := by
  intro state
  by_cases hd : DoubleTight x state
  · obtain ⟨k, hk⟩ := slope_of_doubleTight x state hd
    exact ⟨(k : ℤ), by simpa using hk⟩
  have hothers : ∀ other, other ≠ state → ∃ k : ℕ, slope other x = x 6 * (k : ℝ) := by
    intro other hne
    exact slope_of_doubleTight x other
      ((at_most_one_not_doubleTight x hvertex hx state other hne.symm).resolve_left hd)
  have hrel := slope_relation x
  rcases state with ⟨a, b⟩
  cases a <;> cases b
  · obtain ⟨k, hk⟩ := hothers (true, false) (by decide)
    obtain ⟨l, hl⟩ := hothers (false, true) (by decide)
    obtain ⟨m, hm⟩ := hothers (true, true) (by decide)
    refine ⟨(k : ℤ) + (l : ℤ) - (m : ℤ), ?_⟩
    push_cast
    nlinarith
  · obtain ⟨j, hj⟩ := hothers (false, false) (by decide)
    obtain ⟨k, hk⟩ := hothers (true, false) (by decide)
    obtain ⟨m, hm⟩ := hothers (true, true) (by decide)
    refine ⟨(j : ℤ) + (m : ℤ) - (k : ℤ), ?_⟩
    push_cast
    nlinarith
  · obtain ⟨j, hj⟩ := hothers (false, false) (by decide)
    obtain ⟨l, hl⟩ := hothers (false, true) (by decide)
    obtain ⟨m, hm⟩ := hothers (true, true) (by decide)
    refine ⟨(j : ℤ) + (m : ℤ) - (l : ℤ), ?_⟩
    push_cast
    nlinarith
  · obtain ⟨j, hj⟩ := hothers (false, false) (by decide)
    obtain ⟨k, hk⟩ := hothers (true, false) (by decide)
    obtain ⟨l, hl⟩ := hothers (false, true) (by decide)
    refine ⟨(k : ℤ) + (l : ℤ) - (j : ℤ), ?_⟩
    push_cast
    nlinarith

/-- Nonnegative integral slopes and one active count force a double-tight state. -/
theorem doubleTight_of_nonneg_slope (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i)
    (state : State) (hs : 0 ≤ slope state x) : DoubleTight x state := by
  obtain ⟨z, hz⟩ := integer_slopes x hvertex hx state
  have hz₀ : (0 : ℝ) ≤ (z : ℝ) := by nlinarith [hx 6]
  have hz₀' : 0 ≤ z := by exact_mod_cast hz₀
  have hk : slope state x = x 6 * (z.toNat : ℝ) := by
    have hcast : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz₀'
    rwa [hcast]
  have h := TightCounts.adjacent_tight_of_integer_slope
    (constant state x) (slope state x) (x 6) (hx 6) z.toNat hk
    (fun n => by rw [← test_eq_value]; exact hvertex.1.2 (state, n))
    (by simpa only [test_eq_value] using every_state_tight x hvertex hx state)
  exact ⟨z.toNat, by simpa only [test_eq_value] using h⟩

/-- The three states other than `11` always have adjacent tight counts. -/
theorem first_three_doubleTight (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i) :
    DoubleTight x (false, false) ∧ DoubleTight x (true, false) ∧
      DoubleTight x (false, true) := by
  have h00 : DoubleTight x (false, false) :=
    doubleTight_of_nonneg_slope x hvertex hx _ (by simpa [slope] using (hx 2).le)
  have h10 : DoubleTight x (true, false) := by
    by_contra h
    have h11 := (at_most_one_not_doubleTight x hvertex hx
      (true, false) (true, true) (by decide)).resolve_left h
    obtain ⟨k, hk⟩ := slope_of_doubleTight x (true, true) h11
    have hs : 0 ≤ slope (true, false) x := by
      have hk₀ : (0 : ℝ) ≤ k := by positivity
      simp [slope] at hk ⊢
      nlinarith [hx 6, hx 5]
    exact h (doubleTight_of_nonneg_slope x hvertex hx _ hs)
  have h01 : DoubleTight x (false, true) := by
    by_contra h
    have h11 := (at_most_one_not_doubleTight x hvertex hx
      (false, true) (true, true) (by decide)).resolve_left h
    obtain ⟨k, hk⟩ := slope_of_doubleTight x (true, true) h11
    have hs : 0 ≤ slope (false, true) x := by
      have hk₀ : (0 : ℝ) ≤ k := by positivity
      simp [slope] at hk ⊢
      nlinarith [hx 6, hx 4]
    exact h (doubleTight_of_nonneg_slope x hvertex hx _ hs)
  exact ⟨h00, h10, h01⟩

/-- A negative slope has its unique maximum at zero. -/
theorem test_lt_zero_of_negative_slope (x : Coefficients) (state : State)
    (hp : 0 < x 6) (hs : slope state x < 0) (n : ℕ) (hn : 0 < n) :
    test (state, n) x < test (state, 0) x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlinear := mul_neg_of_pos_of_neg hn' hs
  have hpen := mul_nonneg hp.le
    (mul_nonneg hn'.le (show 0 ≤ (n : ℝ) - 1 by linarith))
  simp only [test_eq_value, TightCounts.value, Nat.cast_zero, zero_mul, mul_zero, zero_div,
    add_zero, sub_zero]
  nlinarith

/-- Every strictly positive vertex has exactly one of the two tight-count patterns.
The conclusion follows from extremality, not an assumption on active equations. -/
theorem vertex_patterns (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i) :
    DoubleTight x (false, false) ∧ DoubleTight x (true, false) ∧
      DoubleTight x (false, true) ∧
      (DoubleTight x (true, true) ∨
        (slope (true, true) x < 0 ∧ test ((true, true), 0) x = 1 ∧
          ∀ n : ℕ, 0 < n → test ((true, true), n) x < 1)) := by
  obtain ⟨h00, h10, h01⟩ := first_three_doubleTight x hvertex hx
  refine ⟨h00, h10, h01, ?_⟩
  by_cases hs : 0 ≤ slope (true, true) x
  · exact Or.inl (doubleTight_of_nonneg_slope x hvertex hx _ hs)
  · have hs' := lt_of_not_ge hs
    obtain ⟨n, hn⟩ := every_state_tight x hvertex hx (true, true)
    have hn₀ : n = 0 := by
      by_contra hne
      have hlt := test_lt_zero_of_negative_slope x (true, true) (hx 6) hs' n (Nat.pos_of_ne_zero hne)
      have hzero := hvertex.1.2 ((true, true), 0)
      linarith
    subst n
    refine Or.inr ⟨hs', hn, ?_⟩
    intro n hn'
    simpa only [hn] using test_lt_zero_of_negative_slope x (true, true) (hx 6) hs' n hn'

end Erdos1017.VertexClassification

module

public import Erdos1017.Multipartite.Selector.VertexClassification
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorScalar

/-!
# Vertex geometry of the one-exterior feasible set

In coordinates `t,v` (root stars) and `d,q` (penalties), positive quadratic
decay gives a finite local description of the all-count feasible set, a vertex
has at least four active tests and each state at most two adjacent tight counts,
so every positive vertex yields the adjacent-contact integer family.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology BigOperators Classical

namespace Erdos1017.CoveredOneExterior

/-- Coordinates are the root stars t,v and penalties d,q. -/
abbrev Coefficients := Fin 4 → ℝ

def constant (s : Bool) : Coefficients →ₗ[ℝ] ℝ :=
  if s then LinearMap.proj 0 else 0

def slope (s : Bool) : Coefficients →ₗ[ℝ] ℝ :=
  (LinearMap.proj 1 : Coefficients →ₗ[ℝ] ℝ) - if s then LinearMap.proj 2 else 0

def test (s : Bool) (n : ℕ) : Coefficients →ₗ[ℝ] ℝ :=
  constant s + (n : ℝ) • slope s -
    ((n : ℝ) * ((n : ℝ) - 1) / 2) • (LinearMap.proj 3 : Coefficients →ₗ[ℝ] ℝ)

def feasible : Set Coefficients :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ s n, test s n x ≤ 1}

theorem test_eq_value (x : Coefficients) (s : Bool) (n : ℕ) :
    test s n x = TightCounts.value (constant s x) (slope s x) (x 3) n := by
  simp only [test, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, TightCounts.value]
  ring

/-- Positive quadratic decay gives a finite local description of the
actual two-state all-count feasible set. -/
theorem local_finiteness (x : Coefficients) (hx : ∀ i, 0 < x i) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x,
      (∀ i, 0 < y i) ∧ ∀ s n, N ≤ n → test s n y < 1 := by
  have hstate (s : Bool) : ∃ N : ℕ, ∀ᶠ y in 𝓝 x,
      ∀ n : ℕ, N ≤ n → test s n y < 1 := by
    let M := |constant s x| + |slope s x| + 1
    have hM : 0 < M := by dsimp [M]; positivity
    obtain ⟨N, hN⟩ := VertexClassification.uniform_tail M (x 3 / 2) hM (half_pos (hx 3))
    have hC : ∀ᶠ y in 𝓝 x, constant s y < M :=
      (constant s).continuous_of_finiteDimensional.continuousAt.eventually_lt_const (by
        dsimp [M]
        have := le_abs_self (constant s x)
        have := abs_nonneg (slope s x)
        linarith)
    have hS : ∀ᶠ y in 𝓝 x, slope s y < M :=
      (slope s).continuous_of_finiteDimensional.continuousAt.eventually_lt_const (by
        dsimp [M]
        have := le_abs_self (slope s x)
        have := abs_nonneg (constant s x)
        linarith)
    have hP : ∀ᶠ y in 𝓝 x, x 3 / 2 < y 3 :=
      (continuous_apply 3).continuousAt.eventually_const_lt (by linarith [hx 3])
    refine ⟨N, ?_⟩
    filter_upwards [hC, hS, hP] with y hC hS hP
    intro n hn
    rw [test_eq_value]
    exact hN _ _ _ hC.le hS.le hP.le n hn
  choose N hN using hstate
  have htail := Filter.eventually_all.mpr hN
  have hpos : ∀ᶠ y in 𝓝 x, ∀ i, 0 < y i :=
    Filter.eventually_all.mpr (fun i => (continuous_apply i).continuousAt.eventually_const_lt (hx i))
  refine ⟨Finset.univ.sup N, ?_⟩
  filter_upwards [htail, hpos] with y hy hpos
  exact ⟨hpos, fun s n hn => hy s n ((Finset.le_sup (Finset.mem_univ s)).trans hn)⟩

/-- A genuine four-dimensional vertex has at least four active count tests. -/
theorem four_active_tests (x : Coefficients) (hvertex : x ∈ feasible.extremePoints ℝ)
    (hx : ∀ i, 0 < x i) :
    ∃ N : ℕ, 4 ≤ Nat.card {i : Bool × Fin N // test i.1 i.2.val x = 1} := by
  obtain ⟨N, hN⟩ := local_finiteness x hx
  let L : Bool × Fin N → Coefficients →L[ℝ] ℝ :=
    fun i => (test i.1 i.2.val).toContinuousLinearMap
  have hlocal : ∃ U ∈ 𝓝 x, ∀ y ∈ U, (∀ i, L i y ≤ 1) → y ∈ feasible := by
    refine ⟨{y | (∀ i, 0 < y i) ∧ ∀ s n, N ≤ n → test s n y < 1}, hN, ?_⟩
    intro y hy htests
    refine ⟨fun i => (hy.1 i).le, ?_⟩
    intro s n
    by_cases hn : n < N
    · exact htests (s, ⟨n, hn⟩)
    · exact (hy.2 s n (Nat.le_of_not_gt hn)).le
  have hcard := PolyhedralVertex.finrank_le_active_card feasible x L hvertex
    (fun i => hvertex.1.2 i.1 i.2.val) hlocal
  refine ⟨N, ?_⟩
  simpa [L, Module.finrank_pi_fintype] using hcard

def tightCounts (x : Coefficients) (N : ℕ) (s : Bool) : Finset ℕ :=
  (Finset.range N).filter fun n => test s n x = 1

/-- Strict concavity limits each state to two adjacent tight counts. -/
theorem tightCounts_card_le_two (x : Coefficients) (hx : x ∈ feasible)
    (hq : 0 < x 3) (N : ℕ) (s : Bool) : (tightCounts x N s).card ≤ 2 := by
  let T := tightCounts x N s
  by_cases hT : T.Nonempty
  · let k := T.min' hT
    have hk : k ∈ T := Finset.min'_mem T hT
    have hsub : T ⊆ {k, k + 1} := by
      intro n hn
      have hkn : k ≤ n := Finset.min'_le T n hn
      by_cases heq : k = n
      · simp [← heq]
      · have hadj := TightCounts.tight_counts_adjacent (constant s x) (slope s x)
          (x 3) hq (fun m => by rw [← test_eq_value]; exact hx.2 s m)
          k n (lt_of_le_of_ne hkn heq)
          (by rw [← test_eq_value]; exact (Finset.mem_filter.mp hk).2)
          (by rw [← test_eq_value]; exact (Finset.mem_filter.mp hn).2)
        simp [hadj]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [T, Finset.not_nonempty_iff_eq_empty.mp hT]

theorem active_card_eq_sum (x : Coefficients) (N : ℕ) :
    Nat.card {i : Bool × Fin N // test i.1 i.2.val x = 1} =
      ∑ s : Bool, (tightCounts x N s).card := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun s (n : Fin N) => test s n.val x = 1)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  let e : {n : Fin N // test s n.val x = 1} ≃
      {n : ℕ // n ∈ tightCounts x N s} :=
    { toFun := fun n => ⟨n.val.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.val.isLt, n.property⟩⟩
      invFun := fun n => ⟨⟨n.val, Finset.mem_range.mp (Finset.mem_filter.mp n.property).1⟩,
        (Finset.mem_filter.mp n.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

/-- Both states must have adjacent tight counts at an actual positive vertex. -/
theorem adjacent_contacts_of_vertex (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i) (s : Bool) :
    ∃ k : ℕ, test s k x = 1 ∧ test s (k + 1) x = 1 := by
  obtain ⟨N, hN⟩ := four_active_tests x hvertex hx
  rw [active_card_eq_sum, Fintype.sum_bool] at hN
  have hfalse := tightCounts_card_le_two x hvertex.1 (hx 3) N false
  have htrue := tightCounts_card_le_two x hvertex.1 (hx 3) N true
  have hcard : (tightCounts x N s).card = 2 := by cases s <;> omega
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  have ha : test s a x = 1 := by
    have : a ∈ tightCounts x N s := by rw [hset]; simp
    exact (Finset.mem_filter.mp this).2
  have hb : test s b x = 1 := by
    have : b ∈ tightCounts x N s := by rw [hset]; simp
    exact (Finset.mem_filter.mp this).2
  have hadj (m n : ℕ) (hmn : m < n) (hm : test s m x = 1) (hn : test s n x = 1) :
      n = m + 1 :=
    TightCounts.tight_counts_adjacent _ _ _ (hx 3)
      (fun l => by rw [← test_eq_value]; exact hvertex.1.2 s l) m n hmn
      (by rwa [← test_eq_value]) (by rwa [← test_eq_value])
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨a, ha, by simpa [hadj a b hab ha hb] using hb⟩
  · exact ⟨b, hb, by simpa [hadj b a hba hb ha] using ha⟩

/-- All family coefficients and all tight counts are derived from genuine
vertex geometry; no active-rank or finite-support list is supplied. -/
theorem integer_family_of_vertex (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hx : ∀ i, 0 < x i) (ht : x 0 < 1) :
    ∃ j k : ℕ, 1 ≤ k ∧ k < j ∧
      x 3 = 2 / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      x 1 = 2 * (j : ℝ) / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      x 0 = 1 - (k : ℝ) * ((k : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      x 2 = 2 * ((j : ℝ) - k) / ((j : ℝ) * ((j : ℝ) + 1)) ∧
      (∀ n, test false n x = 1 ↔ n = j ∨ n = j + 1) ∧
      (∀ n, test true n x = 1 ↔ n = k ∨ n = k + 1) := by
  obtain ⟨j, hj, hj1⟩ := adjacent_contacts_of_vertex x hvertex hx false
  obtain ⟨k, hk, hk1⟩ := adjacent_contacts_of_vertex x hvertex hx true
  have hs0 := TightCounts.slope_of_adjacent_tight _ _ _ j
    (by rwa [← test_eq_value]) (by rwa [← test_eq_value])
  have hs1 := TightCounts.slope_of_adjacent_tight _ _ _ k
    (by rwa [← test_eq_value]) (by rwa [← test_eq_value])
  simp [slope] at hs0 hs1
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    simp [hj0, test_eq_value, constant, slope, TightCounts.value] at hj
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp [hk0, test_eq_value, constant, slope, TightCounts.value] at hk
    linarith
  have hjr : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hJ : (j : ℝ) * ((j : ℝ) + 1) ≠ 0 := by positivity
  have hq : x 3 * ((j : ℝ) * ((j : ℝ) + 1)) = 2 := by
    simp only [test_eq_value, TightCounts.value] at hj
    simp [constant, slope] at hj
    nlinarith only [hj, hs0]
  have hqe : x 3 = 2 / ((j : ℝ) * ((j : ℝ) + 1)) := (eq_div_iff hJ).mpr hq
  have hjk : k < j := by
    have hr : (k : ℝ) < j := by nlinarith [hx 2, hx 3]
    exact_mod_cast hr
  have hv : x 1 = 2 * (j : ℝ) / ((j : ℝ) * ((j : ℝ) + 1)) := by
    rw [hs0, hqe]
    ring
  have ht' : x 0 = 1 - (k : ℝ) * ((k : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) := by
    simp only [test_eq_value, TightCounts.value] at hk
    simp [constant, slope] at hk
    rw [hqe] at hs1 hk
    field_simp [hJ] at hs1 hk ⊢
    nlinarith only [hs1, hk]
  have hd : x 2 = 2 * ((j : ℝ) - k) / ((j : ℝ) * ((j : ℝ) + 1)) := by
    rw [hqe] at hs1
    rw [hv] at hs1
    field_simp [hJ] at hs1 ⊢
    nlinarith only [hs1]
  refine ⟨j, k, hkpos, hjk, hqe, hv, ht', hd, ?_, ?_⟩
  · intro n
    have hmax := TightCounts.integer_slope_maximum_iff (constant false x) (slope false x)
      (x 3) (hx 3) j n (by simpa [slope] using hs0)
    simpa only [← test_eq_value, hj] using hmax
  · intro n
    have hmax := TightCounts.integer_slope_maximum_iff (constant true x) (slope true x)
      (x 3) (hx 3) k n (by simpa [slope] using hs1)
    simpa only [← test_eq_value, hk] using hmax

end Erdos1017.CoveredOneExterior

module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Active tests at an extreme point

At an extreme point every direction annihilating the active tests is zero, the
active evaluations separate coefficient vectors, and a local finite description
has at least `dim E` active tests without assuming linear independence.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Erdos1017.PolyhedralVertex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- At an extreme point, every direction annihilating the active tests is zero.
Only local sufficiency of the finite tests is needed; additional strict
constraints can be incorporated in the neighborhood `U`. -/
theorem active_direction_eq_zero
    (S : Set E) (x : E) (L : ι → E →L[ℝ] ℝ)
    (hx : x ∈ S.extremePoints ℝ)
    (hfeas : ∀ i, L i x ≤ 1)
    (hlocal : ∃ U ∈ 𝓝 x, ∀ y ∈ U, (∀ i, L i y ≤ 1) → y ∈ S)
    (v : E) (hactive : ∀ i, L i x = 1 → L i v = 0) : v = 0 := by
  obtain ⟨U, hU, hlocal⟩ := hlocal
  have hmove : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ U := by
    have hlim : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using hmove.tendsto
    exact hlim.eventually hU
  have htest (i : ι) : ∀ᶠ t : ℝ in 𝓝 0, L i (x + t • v) ≤ 1 := by
    by_cases hi : L i x = 1
    · filter_upwards [] with t
      simp [map_add, map_smul, hi, hactive i hi]
    · have hi' : L i x < 1 := lt_of_le_of_ne (hfeas i) hi
      have hcont : ContinuousAt (fun t : ℝ => L i (x + t • v)) 0 := by fun_prop
      have hlim : Tendsto (fun t : ℝ => L i (x + t • v)) (𝓝 0) (𝓝 (L i x)) := by
        simpa using hcont.tendsto
      filter_upwards [hlim.eventually_lt_const hi'] with t ht
      exact ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, L i (x + t • v) ≤ 1 :=
    Filter.eventually_all.mpr htest
  have hS : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ S := by
    filter_upwards [hnear, hall] with t ht htests
    exact hlocal _ ht htests
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hS
  have hhalf : 0 < δ / 2 := by linarith
  have hplus : x + (δ / 2) • v ∈ S := by
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hhalf]
    linarith
  have hminus : x - (δ / 2) • v ∈ S := by
    have ht : -(δ / 2) ∈ Metric.ball (0 : ℝ) δ := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hhalf]
      linarith
    simpa [neg_smul, sub_eq_add_neg] using hball ht
  have heq := hx.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) x ((δ / 2) • v))
  have hzero : (δ / 2) • v = 0 := by
    apply add_left_cancel (a := x)
    simpa using heq
  exact (smul_eq_zero.mp hzero).resolve_left (ne_of_gt hhalf)

/-- The active test evaluations separate every pair of coefficient vectors. -/
theorem active_evaluation_injective
    (S : Set E) (x : E) (L : ι → E →L[ℝ] ℝ)
    (hx : x ∈ S.extremePoints ℝ)
    (hfeas : ∀ i, L i x ≤ 1)
    (hlocal : ∃ U ∈ 𝓝 x, ∀ y ∈ U, (∀ i, L i y ≤ 1) → y ∈ S) :
    Function.Injective (fun v : E => fun i : {i : ι // L i x = 1} => L i.val v) := by
  intro v w h
  apply sub_eq_zero.mp
  apply active_direction_eq_zero S x L hx hfeas hlocal (v - w)
  intro i hi
  have heq := congrFun h (⟨i, hi⟩ : {i : ι // L i x = 1})
  simpa only [map_sub, sub_eq_zero] using heq

/-- A local finite description of an extreme point has at least `dim E`
active tests, with no assumption of linear independence among the tests. -/
theorem finrank_le_active_card [FiniteDimensional ℝ E]
    (S : Set E) (x : E) (L : ι → E →L[ℝ] ℝ)
    (hx : x ∈ S.extremePoints ℝ)
    (hfeas : ∀ i, L i x ≤ 1)
    (hlocal : ∃ U ∈ 𝓝 x, ∀ y ∈ U, (∀ i, L i y ≤ 1) → y ∈ S) :
    Module.finrank ℝ E ≤ Nat.card {i : ι // L i x = 1} := by
  classical
  let A := {i : ι // L i x = 1}
  let T : E →ₗ[ℝ] (A → ℝ) := LinearMap.pi fun i => (L i.val).toLinearMap
  have hT : Function.Injective T :=
    active_evaluation_injective S x L hx hfeas hlocal
  have hr := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Module.finrank_pi_fintype, Nat.card_eq_fintype_card, A] using hr

end Erdos1017.PolyhedralVertex

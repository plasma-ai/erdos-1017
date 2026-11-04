module

public import Erdos1017.Multipartite.TightCounts
public import Erdos1017.Multipartite.Selector.PolyhedralVertex
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Coefficient space of the two-atom count system

This module sets up coordinates `h, v, p, q, r` with charges `-p, -q, -r`, the
`B + kR + lE` count tests in the `AB = 1`, `AR = -BR` slice, unanchored tests,
charge coordinates, objective weights and the physical objective with its fixed
`AB` contribution.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- Coordinates are h,v,p,q,r, with actual charges -p,-q,-r. -/
abbrev Coefficients := Fin 5 → ℝ

/-- The genuine B+kR+lE count test in the AB=1, AR=-BR slice. -/
def countTest (k l : ℕ) : Coefficients →ₗ[ℝ] ℝ :=
  (k : ℝ) • (LinearMap.proj 0 : Coefficients →ₗ[ℝ] ℝ) +
    (l : ℝ) • (LinearMap.proj 1 : Coefficients →ₗ[ℝ] ℝ) -
    ((k : ℝ) * ((k : ℝ) - 1) / 2) • (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ) -
    ((l : ℝ) * ((l : ℝ) - 1) / 2) • (LinearMap.proj 3 : Coefficients →ₗ[ℝ] ℝ) -
    ((k : ℝ) * (l : ℝ)) • (LinearMap.proj 4 : Coefficients →ₗ[ℝ] ℝ)

/-- The unanchored kR+lE test is retained before penalties become positive. -/
def unanchoredTest (k l : ℕ) : Coefficients →ₗ[ℝ] ℝ :=
  -((k : ℝ) * ((k : ℝ) - 1) / 2) • (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ) -
    ((l : ℝ) * ((l : ℝ) - 1) / 2) • (LinearMap.proj 3 : Coefficients →ₗ[ℝ] ℝ) -
    ((k : ℝ) * (l : ℝ)) • (LinearMap.proj 4 : Coefficients →ₗ[ℝ] ℝ)

/-- The A+kR test allows signed h on the entire optimal face. -/
def firstAtomTest (k : ℕ) : Coefficients →ₗ[ℝ] ℝ :=
  -(k : ℝ) • (LinearMap.proj 0 : Coefficients →ₗ[ℝ] ℝ) -
    ((k : ℝ) * ((k : ℝ) - 1) / 2) • (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ)

/-- All sliced clique tests are imposed, with no count cutoff. The p,q
nonnegativity also records their pure-clique consequences. -/
def feasible : Set Coefficients :=
  {x | 0 ≤ x 2 ∧ 0 ≤ x 3 ∧ (∀ k l, countTest k l x ≤ 1) ∧
    (∀ k l, unanchoredTest k l x ≤ 1) ∧ ∀ k, firstAtomTest k x ≤ 1}

theorem countTest_apply (x : Coefficients) (k l : ℕ) :
    countTest k l x = x 0 * k + x 1 * l - x 2 * k * ((k : ℝ) - 1) / 2 -
      x 3 * l * ((l : ℝ) - 1) / 2 - x 4 * k * l := by
  simp only [countTest, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  ring

theorem unanchoredTest_apply (x : Coefficients) (k l : ℕ) :
    unanchoredTest k l x = -x 2 * k * ((k : ℝ) - 1) / 2 -
      x 3 * l * ((l : ℝ) - 1) / 2 - x 4 * k * l := by
  simp only [unanchoredTest, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  ring

theorem firstAtomTest_apply (x : Coefficients) (k : ℕ) :
    firstAtomTest k x = -x 0 * k - x 2 * k * ((k : ℝ) - 1) / 2 := by
  simp only [firstAtomTest, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  ring

/-- Positive coefficients make every non-B count test nonpositive. -/
theorem mem_feasible_of_nonnegative (x : Coefficients) (hx : ∀ i, 0 ≤ x i)
    (hcount : ∀ k l, countTest k l x ≤ 1) : x ∈ feasible := by
  refine ⟨hx 2, hx 3, hcount, ?_, ?_⟩
  · intro k l
    rw [unanchoredTest_apply]
    have hk : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
      simpa using TightCounts.gap_nonneg 0 k
    have hl : 0 ≤ (l : ℝ) * ((l : ℝ) - 1) := by
      simpa using TightCounts.gap_nonneg 0 l
    have hp := mul_nonneg (hx 2) hk
    have hq := mul_nonneg (hx 3) hl
    have hr := mul_nonneg (mul_nonneg (hx 4) (Nat.cast_nonneg k)) (Nat.cast_nonneg l)
    nlinarith
  · intro k
    rw [firstAtomTest_apply]
    have hk : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
      simpa using TightCounts.gap_nonneg 0 k
    have hp := mul_nonneg (hx 2) hk
    have hh := mul_nonneg (hx 0) (Nat.cast_nonneg k)
    nlinarith

theorem feasible_isClosed : IsClosed feasible := by
  have heq : feasible = {x : Coefficients | 0 ≤ x 2} ∩ {x : Coefficients | 0 ≤ x 3} ∩
      (⋂ k : ℕ, ⋂ l : ℕ, {x | countTest k l x ≤ 1}) ∩
      (⋂ k : ℕ, ⋂ l : ℕ, {x | unanchoredTest k l x ≤ 1}) ∩
      (⋂ k : ℕ, {x | firstAtomTest k x ≤ 1}) := by
    ext x
    simp only [feasible, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [heq]
  exact ((((isClosed_le continuous_const (continuous_apply 2)).inter
    (isClosed_le continuous_const (continuous_apply 3))).inter
    (isClosed_iInter (fun k => isClosed_iInter (fun l =>
      isClosed_le (countTest k l).continuous_of_finiteDimensional continuous_const)))).inter
    (isClosed_iInter (fun k => isClosed_iInter (fun l =>
      isClosed_le (unanchoredTest k l).continuous_of_finiteDimensional continuous_const)))).inter
    (isClosed_iInter (fun k =>
      isClosed_le (firstAtomTest k).continuous_of_finiteDimensional continuous_const))

/-- Actual charge coordinates, used only for the compact optimal-face bound. -/
def chargeCoordinate (x : Coefficients) (i : Fin 5) : ℝ := if i < 2 then x i else -x i

theorem chargeCoordinate_le_one {x : Coefficients} (hx : x ∈ feasible) :
    ∀ i, chargeCoordinate x i ≤ 1 := by
  have hh := hx.2.2.1 1 0
  have hv := hx.2.2.1 0 1
  have hr := hx.2.2.2.1 1 1
  norm_num [countTest_apply, unanchoredTest_apply] at hh hv hr
  intro i
  fin_cases i <;> simp only [chargeCoordinate] <;> norm_num <;> linarith [hx.1, hx.2.1]

/-- Positive physical coefficients for h,v,-p,-q,-r. -/
def objectiveWeights (a b u e : ℝ) : Fin 5 → ℝ :=
  ![u * (b - a), b * e, u ^ 2 / 2, e ^ 2 / 2, u * e]

def linearObjective (a b u e : ℝ) : Coefficients →ₗ[ℝ] ℝ :=
  (u * (b - a)) • (LinearMap.proj 0 : Coefficients →ₗ[ℝ] ℝ) +
    (b * e) • (LinearMap.proj 1 : Coefficients →ₗ[ℝ] ℝ) -
    (u ^ 2 / 2) • (LinearMap.proj 2 : Coefficients →ₗ[ℝ] ℝ) -
    (e ^ 2 / 2) • (LinearMap.proj 3 : Coefficients →ₗ[ℝ] ℝ) -
    (u * e) • (LinearMap.proj 4 : Coefficients →ₗ[ℝ] ℝ)

/-- The literal physical objective includes the fixed original AB contribution. -/
def objective (a b u e : ℝ) (x : Coefficients) : ℝ := a * b + linearObjective a b u e x

theorem objective_apply (a b u e : ℝ) (x : Coefficients) :
    objective a b u e x = a * b + u * (b - a) * x 0 + b * e * x 1 -
      u ^ 2 * x 2 / 2 - e ^ 2 * x 3 / 2 - u * e * x 4 := by
  simp only [objective, linearObjective, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  ring

theorem linearObjective_eq_sum (a b u e : ℝ) (x : Coefficients) :
    linearObjective a b u e x = ∑ i, objectiveWeights a b u e i * chargeCoordinate x i := by
  simp [linearObjective, objectiveWeights, chargeCoordinate, Fin.sum_univ_succ]
  ring

theorem objectiveWeights_pos {a b u e : ℝ} (hab : a < b) (hb : 0 < b)
    (hu : 0 < u) (he : 0 < e) : ∀ i, 0 < objectiveWeights a b u e i := by
  have hba : 0 < b - a := sub_pos.mpr hab
  intro i
  fin_cases i <;> norm_num [objectiveWeights] <;> positivity

end Erdos1017.TwoAtomCountGate

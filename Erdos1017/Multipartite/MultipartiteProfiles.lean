module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Compact space of sorted profiles

A profile is a total secondary mass with a decreasing sequence of atomic masses,
dust being the difference; the sorted bounded profile space is compact in the
product topology, dust is upper semicontinuous, and the square moment is
continuous by the tail bound `L²/(n+1)`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators
open Set

/-- Total secondary mass and a decreasing sequence of atomic masses.
The difference between total mass and atomic mass is the dust. -/
abbrev Profile := ℝ × (ℕ → ℝ)

/-- Partial sums keep the compactification definition independent of a
choice of summation theorem. Each coordinate is in the anchor-normalized box. -/
def space (L : ℝ) : Set Profile :=
  Icc (0, 0) (L, 1) ∩ {x | Antitone x.2 ∧
    (∀ n, ∑ i ∈ Finset.range n, x.2 i ≤ x.1) ∧
    ∀ n, ∑ i ∈ Finset.range n, (x.2 i) ^ 2 ≤ 1}

/-- The sorted bounded profile space is compact in the product topology. -/
theorem space_isCompact (L : ℝ) : IsCompact (space L) := by
  apply isCompact_Icc.inter_right
  have hanti : IsClosed {x : Profile | Antitone x.2} := by
    change IsClosed {x : Profile | ∀ i j, i ≤ j → x.2 j ≤ x.2 i}
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) (by fun_prop)
  have hsum : IsClosed {x : Profile | ∀ n, ∑ i ∈ Finset.range n, x.2 i ≤ x.1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun n => isClosed_le (by fun_prop) continuous_fst
  have hsquare : IsClosed {x : Profile | ∀ n, ∑ i ∈ Finset.range n, (x.2 i) ^ 2 ≤ 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun n => isClosed_le (by fun_prop) continuous_const
  exact hanti.inter (hsum.inter hsquare)

/-- Residual mass after the first `n` atoms. -/
def residual (n : ℕ) (x : Profile) : ℝ := x.1 - ∑ i ∈ Finset.range n, x.2 i

/-- The residual infimum is the dust coordinate on the compactification. -/
def dust (x : Profile) : ℝ := ⨅ n : ℕ, residual n x

theorem residual_nonneg {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    0 ≤ residual n x := sub_nonneg.mpr (hx.2.2.1 n)

theorem residual_continuous (n : ℕ) : Continuous (residual n) := by
  unfold residual
  fun_prop

/-- Dust is upper semicontinuous although the total atomic mass need not be continuous. -/
theorem dust_upperSemicontinuousOn (L : ℝ) : UpperSemicontinuousOn dust (space L) := by
  apply upperSemicontinuousOn_ciInf
  · intro x hx
    exact ⟨0, by rintro _ ⟨n, rfl⟩; exact residual_nonneg hx n⟩
  · intro n
    exact (residual_continuous n).upperSemicontinuous.upperSemicontinuousOn (space L)

/-- Greatest dust is attained on every nonempty compact subfamily.
Applications must separately establish compactness of the optimizing moment fiber. -/
theorem exists_greatest_dust {L : ℝ} {K : Set Profile}
    (hK : IsCompact K) (hne : K.Nonempty) (hsub : K ⊆ space L) :
    ∃ x ∈ K, ∀ y ∈ K, dust y ≤ dust x := by
  exact UpperSemicontinuousOn.exists_isMaxOn hne hK
    ((dust_upperSemicontinuousOn L).mono hsub)

/-- Sorting and the total-mass constraint give a uniform coordinate bound. -/
theorem coordinate_bound {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    x.2 n ≤ L / (n + 1) := by
  have hsum : (∑ i ∈ Finset.range (n + 1), x.2 n) ≤
      ∑ i ∈ Finset.range (n + 1), x.2 i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hx.2.1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have htotal := (hx.2.2.1 (n + 1)).trans hx.1.2.1
  have hden : (0 : ℝ) < n + 1 := by positivity
  apply (le_div_iff₀ hden).mpr
  push_cast at hsum
  nlinarith

/-- Every finite tail has square mass bounded uniformly by `L²/(n+1)`.
This is the quantitative estimate needed for continuity of the square moment. -/
theorem square_tail_bound {L : ℝ} {x : Profile} (hx : x ∈ space L) (n N : ℕ) :
    (∑ i ∈ (Finset.range N).filter (fun i => n ≤ i), (x.2 i) ^ 2) ≤ L ^ 2 / (n + 1) := by
  let S := (Finset.range N).filter (fun i => n ≤ i)
  have hL : 0 ≤ L := hx.1.1.1.trans hx.1.2.1
  have hfactor : 0 ≤ L / ((n : ℝ) + 1) := div_nonneg hL (by positivity)
  have hfirst : (∑ i ∈ S, x.2 i) ≤ L := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hx.1.1.2 i))
    exact (hx.2.2.1 N).trans hx.1.2.1
  calc
    (∑ i ∈ S, (x.2 i) ^ 2) ≤ ∑ i ∈ S, (L / ((n : ℝ) + 1)) * x.2 i := by
      apply Finset.sum_le_sum
      intro i hi
      have hni := (Finset.mem_filter.mp hi).2
      have hi' := (hx.2.1 hni).trans (coordinate_bound hx n)
      nlinarith [mul_le_mul_of_nonneg_right hi' (hx.1.1.2 i)]
    _ = (L / ((n : ℝ) + 1)) * ∑ i ∈ S, x.2 i := (Finset.mul_sum _ _ _).symm
    _ ≤ (L / ((n : ℝ) + 1)) * L := mul_le_mul_of_nonneg_left hfirst hfactor
    _ = L ^ 2 / ((n : ℝ) + 1) := by ring

theorem atoms_summable {L : ℝ} {x : Profile} (hx : x ∈ space L) : Summable x.2 :=
  summable_of_sum_range_le (fun i => hx.1.1.2 i) hx.2.2.1

theorem squares_summable {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    Summable (fun i => (x.2 i) ^ 2) :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) hx.2.2.2

/-- The semicontinuous dust definition is exactly total mass minus the
convergent series of independent-part masses. -/
theorem dust_eq_sub_tsum {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    dust x = x.1 - ∑' i, x.2 i := by
  have hanti : Antitone (fun n => residual n x) := by
    intro n N hn
    unfold residual
    apply sub_le_sub_left
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun i _ _ => hx.1.1.2 i)
  have hbdd : BddBelow (range (fun n => residual n x)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact residual_nonneg hx n⟩
  exact tendsto_nhds_unique (tendsto_atTop_ciInf hanti hbdd)
    (tendsto_const_nhds.sub (atoms_summable hx).hasSum.tendsto_sum_nat)

/-- Unlike total atomic mass, the square moment is continuous in the product
compactification: sorted coordinates have a common summable square bound. -/
theorem squareMoment_continuousOn (L : ℝ) :
    ContinuousOn (fun x : Profile => ∑' i, (x.2 i) ^ 2) (space L) := by
  have hseries : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using h
  apply continuousOn_tsum (fun i => (show Continuous (fun x : Profile => (x.2 i) ^ 2) by
    fun_prop).continuousOn) (hseries.mul_left (L ^ 2))
  intro n x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hbound := coordinate_bound hx n
  have hsq := mul_self_le_mul_self (hx.1.1.2 n) hbound
  calc
    (x.2 n) ^ 2 ≤ (L / ((n : ℝ) + 1)) ^ 2 := by nlinarith
    _ = L ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by rw [div_pow]; ring

end Erdos1017.MultipartiteProfiles

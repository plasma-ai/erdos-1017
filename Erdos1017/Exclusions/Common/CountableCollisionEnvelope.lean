module

public import Erdos1017.Multipartite.MultipartiteProfileCollision
public import Erdos1017.Multipartite.MultipartiteCountableRestriction

/-!
# Countable collision envelope

The unrestricted countable collision envelope `value_le_split_add_square`
follows by restricting one bounded feasible coefficient family, without sorting
the heads.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos1017.MultipartiteCountableDual

/-- The unrestricted countable collision envelope follows by restricting
one actual bounded feasible coefficient family. Heads need not be sorted,
and no normalized atomic-square bound is imposed. -/
theorem value_le_split_add_square (p : ℕ → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) :
    value p s ≤ (1 + (∑' i, p i) + s) ^ 2 *
      Benchmark.splitValue (1 / (1 + (∑' i, p i) + s)) + (∑' i, (p i) ^ 2) / 2 := by
  obtain ⟨D, hD, hvalue⟩ := exists_value_eq p (fun i => (hp i).1) hsum s
  rw [hvalue]
  let M : ℝ := 1 + (∑' i, p i) + s
  let Mₙ : ℕ → ℝ := fun n => 1 + (∑ i : Fin n, p i.val) + s
  have hM : 1 ≤ M := by
    have htotal : 0 ≤ ∑' i, p i := tsum_nonneg (fun i => (hp i).1)
    dsimp only [M]
    linarith
  have hMₙ (n : ℕ) : 1 ≤ Mₙ n := by
    have htotal : 0 ≤ ∑ i : Fin n, p i.val := Finset.sum_nonneg (fun i _ => (hp i.val).1)
    dsimp only [Mₙ]
    linarith
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hMₙpos (n : ℕ) : 0 < Mₙ n := zero_lt_one.trans_le (hMₙ n)
  have hpLimit : Tendsto (fun n => ∑ i : Fin n, p i.val) atTop (nhds (∑' i, p i)) := by
    simpa only [Fin.sum_univ_eq_sum_range] using hsum.hasSum.tendsto_sum_nat
  have hMLimit : Tendsto Mₙ atTop (nhds M) :=
    (tendsto_const_nhds.add hpLimit).add_const s
  have hInvLimit : Tendsto (fun n => 1 / Mₙ n) atTop (nhds (1 / M)) :=
    tendsto_const_nhds.div hMLimit hMpos.ne'
  have hInvMem : 1 / M ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hMpos).mpr hM⟩
  have hInvMemₙ (n : ℕ) : 1 / Mₙ n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg zero_le_one (hMₙpos n).le, (div_le_one (hMₙpos n)).mpr (hMₙ n)⟩
  have hSplitLimit : Tendsto (fun n => Benchmark.splitValue (1 / Mₙ n)) atTop
      (nhds (Benchmark.splitValue (1 / M))) := by
    have hc : Tendsto Benchmark.splitValue (nhdsWithin (1 / M) (Icc (0 : ℝ) 1))
        (nhds (Benchmark.splitValue (1 / M))) := Benchmark.splitValue_continuousOn _ hInvMem
    exact hc.comp (tendsto_nhdsWithin_iff.mpr ⟨hInvLimit, Eventually.of_forall hInvMemₙ⟩)
  have hsq : Summable (fun i => (p i) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hsum
    intro i
    nlinarith [(hp i).1, (hp i).2]
  have hSqLimit : Tendsto (fun n => ∑ i : Fin n, (p i.val) ^ 2) atTop
      (nhds (∑' i, (p i) ^ 2)) := by
    convert hsq.hasSum.tendsto_sum_nat using 1
    funext n
    exact Fin.sum_univ_eq_sum_range (fun i => (p i) ^ 2) n
  have hboundLimit := ((hMLimit.pow 2).mul hSplitLimit).add (hSqLimit.div_const 2)
  apply le_of_tendsto_of_tendsto
    (objective_restrict_tendsto p (fun i => (hp i).1) hsum s hD.1) hboundLimit
  apply Eventually.of_forall
  intro n
  exact (MultipartiteDust.objective_le_value (fun i : Fin n => p i.val) s (restrict n D)
    (restrict_mem_feasible hD n)).trans
    (MultipartiteDust.value_le_split_add_square (fun i : Fin n => p i.val) (fun i => hp i.val) s hs)

end Erdos1017.MultipartiteCountableDual

module

public import Erdos1017.Multipartite.MultipartiteBenchmarkTheorem
public import Erdos1017.Multipartite.ClosedAnchoring
public import Mathlib.Logic.Equiv.Option

/-!
# Benchmark bound for finite multipartite partition values

Every finite nonnegative weighted complete multipartite graph of total mass one
satisfies the benchmark bound at its graph density (`value_le_benchmark`), from
the countable result with a designated positive largest part.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.Multipartite

private theorem exists_reindexed_primal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (a : κ → ℝ) (w : Selection ι → ℝ)
    (hw : PrimalFeasible (fun i => a (e i)) w) :
    ∃ v, PrimalFeasible a v ∧ cost v = cost w := by
  classical
  let E := Equiv.arrowCongr e (Equiv.refl Bool)
  let v : Selection κ → ℝ := fun X => w (E.symm X)
  have hsum (f : Selection κ → ℝ) : (∑ X, v X * f X) = ∑ X, w X * f (E X) := by
    rw [← E.sum_comp]
    simp [v]
  refine ⟨v, ⟨fun X => hw.1 _, ?_, ?_⟩, ?_⟩
  · intro X hX
    apply hw.2.1
    rintro ⟨i, j, hij, hi, hj⟩
    apply hX
    exact ⟨e i, e j, fun h => hij (e.injective h), hi, hj⟩
  · intro i j hij
    rw [hsum]
    simpa [E, Equiv.arrowCongr_apply] using
      hw.2.2 (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))
  · simpa [cost] using hsum (fun _ => 1)

/-- Relabeling independent parts preserves the actual finite partition value. -/
theorem value_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (a : κ → ℝ) : value (fun i => a (e i)) = value a := by
  unfold value
  apply congrArg sInf
  ext c
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, heq⟩ := exists_reindexed_primal e a w hw
    exact ⟨v, hv, heq⟩
  · rintro ⟨w, hw, rfl⟩
    have hw' : PrimalFeasible (fun i => (fun j => a (e j)) (e.symm i)) w := by
      simpa using hw
    obtain ⟨v, hv, heq⟩ := exists_reindexed_primal e.symm (fun j => a (e j)) w hw'
    exact ⟨v, hv, heq⟩

end Erdos1017.Multipartite

namespace Erdos1017.Selector

/-- A finite selector dual can ignore the unused dust type at every count. -/
theorem value_le_zero_dust {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : value p ≤ MultipartiteDust.value p 0 := by
  obtain ⟨D, hD, halpha, hbeta⟩ := exists_bounded_optimal p hp
  let C := DustCellBridge.coefficients D (fun _ => 0) ∅
  have hobj (q : Fin m → ℝ) (s : ℝ) :
      MultipartiteDust.objective q s C = objective q D := by
    rw [DustCellBridge.objective_eq_averagedValue]
    have hmask : DustCellBridge.maskedMass ∅ q = q := by
      funext i
      simp [DustCellBridge.maskedMass]
    rw [hmask]
    simp [averagedValue, dustLinear, dustPenalty]
  have hC : C ∈ MultipartiteDust.feasible m := by
    constructor
    · have hbox (c : MultipartiteDust.Coordinate m) : 0 ≤ C c ∧ C c ≤ 1 := by
        rcases c with i | (⟨i, j⟩ | (i | b))
        · simpa [C, DustCellBridge.coefficients, DustCellBridge.maskedDual, removeZeros] using
            halpha i
        · have hb := hbeta i j
          have hmin : min (D.alpha i) (D.alpha j) ≤ 1 := (min_le_left _ _).trans (halpha i).2
          simpa [C, DustCellBridge.coefficients, DustCellBridge.maskedDual, removeZeros] using
            (show 0 ≤ -D.beta i j ∧ -D.beta i j ≤ 1 by constructor <;> linarith)
        · simp [C, DustCellBridge.coefficients, DustCellBridge.mixedRow]
        · cases b <;> simp [C, DustCellBridge.coefficients, dustLinear, dustPenalty]
      exact ⟨fun c => (hbox c).1, fun c => (hbox c).2⟩
    · intro X k
      rw [DustCellBridge.charge_eq_objective, hobj]
      simpa [C, MultipartiteDust.penalty, DustCellBridge.coefficients, dustPenalty, quadratic] using
        hD.1 X
  rw [← optimal_objective_eq_value p hp D hD]
  rw [← hobj p 0]
  exact le_csSup ((MultipartiteDust.feasible_isCompact m).image
    (MultipartiteDust.objective_continuous p 0)).bddAbove ⟨C, hC, rfl⟩

/-- The unconditional countable result applies to every finite head vector
whose secondary square moment is at most one. -/
theorem normalized_value_le_benchmark {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hQ : (∑ i, (p i) ^ 2) ≤ 1) :
    value p / (1 + ∑ i, p i) ^ 2 ≤
      benchmark (1 / 2 - (1 + ∑ i, (p i) ^ 2) / (2 * (1 + ∑ i, p i) ^ 2)) := by
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
  have hbound := MultipartiteCountableDual.normalized_value_le_benchmark q hq hq1 hqsum
    0 le_rfl (by rwa [hmoment])
  rw [zero_add, htotal, hmoment] at hbound
  have hfinite := MultipartiteCountableDual.finite_value_le_value q hq hqsum 0 m
  have hprefix : (fun i : Fin m => q i.val) = p := by funext i; simp [q]
  rw [hprefix] at hfinite
  have hden : 0 < (1 + ∑ i, p i) ^ 2 := by
    have hsum : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => (hp i).1)
    positivity
  exact ((div_le_div_iff_of_pos_right hden).mpr ((value_le_zero_dust p hp).trans hfinite)).trans
    hbound

end Erdos1017.Selector

namespace Erdos1017.Multipartite

/-- A designated positive largest part gives the full finite benchmark
comparison, including normalized secondary square moments above one. -/
theorem anchored_value_le_benchmark {m : ℕ} (a : Option (Fin m) → ℝ)
    (ha : 0 < a none) (hsecondary : ∀ i, 0 ≤ a (some i) ∧ a (some i) ≤ a none)
    (hsum : ∑ i, a i = 1) :
    value a ≤ benchmark ((1 - ∑ i, (a i) ^ 2) / 2) := by
  let p : Fin m → ℝ := fun i => a (some i) / a none
  have hp (i : Fin m) : 0 ≤ p i ∧ p i ≤ 1 :=
    ⟨div_nonneg (hsecondary i).1 ha.le, (div_le_one ha).mpr (hsecondary i).2⟩
  have hT : ∑ i, p i = (1 - a none) / a none := by
    dsimp [p]
    rw [← Finset.sum_div]
    congr 1
    simp only [Fintype.sum_option] at hsum
    linarith
  have hM : 1 + ∑ i, p i = 1 / a none := by
    rw [hT]
    field_simp
    ring
  have hQ : a none ^ 2 * ∑ i, (p i) ^ 2 = ∑ i, (a (some i)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [p]
    field_simp
  by_cases hsmall : (∑ i, (p i) ^ 2) ≤ 1
  · have h := Selector.normalized_value_le_benchmark p hp hsmall
    have hdensity : 1 / 2 - (1 + ∑ i, (p i) ^ 2) / (2 * (1 + ∑ i, p i) ^ 2) =
        (1 - ∑ i, (a i) ^ 2) / 2 := by
      rw [hM, Fintype.sum_option]
      field_simp
      nlinarith [hQ]
    have hvalue : value a = Selector.value p / (1 + ∑ i, p i) ^ 2 := by
      rw [largest_part_anchoring a ha hsecondary, hM]
      change a none ^ 2 * Selector.value p = Selector.value p / (1 / a none) ^ 2
      field_simp
    rwa [← hvalue, hdensity] at h
  · have hlarge : a none ^ 2 < ∑ i, (a (some i)) ^ 2 := by
      nlinarith [mul_pos (sq_pos_of_pos ha) (sub_pos.mpr (lt_of_not_ge hsmall))]
    have hsq : (∑ i, (a i) ^ 2) ≤ a none := by
      calc
        (∑ i, (a i) ^ 2) ≤ ∑ i, a none * a i := by
          apply Finset.sum_le_sum
          intro i _
          cases i with
          | none => ring_nf; exact le_rfl
          | some i =>
            simpa only [pow_two] using
              mul_le_mul_of_nonneg_right (hsecondary i).2 (hsecondary i).1
        _ = a none := by rw [← Finset.mul_sum, hsum, mul_one]
    have hhalf : a none < 1 / 2 := by
      rw [Fintype.sum_option] at hsq
      nlinarith [sq_nonneg (a none - 1 / 2)]
    have hd : (1 - ∑ i, (a i) ^ 2) / 2 ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) := by
      constructor
      · linarith
      · linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a i))]
    calc
      value a ≤ a none ^ 2 := value_le_largest_part_sq a ha hsecondary
      _ ≤ 1 / 2 - (1 - ∑ i, (a i) ^ 2) / 2 := by
        rw [Fintype.sum_option]
        linarith
      _ ≤ benchmark ((1 - ∑ i, (a i) ^ 2) / 2) := Benchmark.benchmark_ge_missing hd

/-- Every finite nonnegative weighted complete multipartite graph of total
mass one satisfies the benchmark bound at its actual graph density. -/
theorem value_le_benchmark {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    value a ≤ benchmark ((1 - ∑ i, (a i) ^ 2) / 2) := by
  classical
  have hne : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ a (Finset.univ_nonempty_iff.mpr hne)
  have hpos : 0 < a i := by
    by_contra h
    have hle : (∑ j, a j) ≤ 0 := Finset.sum_nonpos (fun j _ =>
      (hi j (Finset.mem_univ j)).trans (le_of_not_gt h))
    linarith
  let e : Option (Fin (Fintype.card {j : ι // j ≠ i})) ≃ ι :=
    (Equiv.optionCongr (Fintype.equivFin {j : ι // j ≠ i}).symm).trans
      (Equiv.optionSubtypeNe i)
  have he : e none = i := by rfl
  have h := anchored_value_le_benchmark (fun j => a (e j)) (by simpa [he] using hpos)
    (fun j => ⟨ha _, hi _ (Finset.mem_univ _)⟩) ((e.sum_comp a).trans hsum)
  rw [value_reindex e a] at h
  have hsquares : (∑ j, (a (e j)) ^ 2) = ∑ j, (a j) ^ 2 := e.sum_comp (fun j => (a j) ^ 2)
  rwa [hsquares] at h

end Erdos1017.Multipartite

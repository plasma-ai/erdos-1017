module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorSumTwo
public import Erdos1017.Multipartite.Dust.DustPaddedCells

/-!
# Sharp selector bound below total load two

Appending labels with zero dual charge preserves the objective and Boolean
feasibility, so equal dummy loads fill the deficit to total load two at the cost
of their square mass; arbitrarily fine dummy loads give the sharp bound, and
primal-dual attainment gives the value bound.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators Classical

namespace Erdos1017.Selector.Sharp

/-- Appended labels carry zero dual charge; their actual loads may be positive. -/
def appendZeroDual {m : ℕ} (D : Dual m) (n : ℕ) : Dual (m + n) where
  alpha := Fin.addCases D.alpha (fun _ => 0)
  beta := Fin.addCases (fun i => Fin.addCases (D.beta i) (fun _ => 0)) (fun _ _ => 0)
  beta_symm i j := by
    refine Fin.addCases ?_ ?_ i <;> intro i
    · refine Fin.addCases ?_ ?_ j <;> intro j
      · simpa using D.beta_symm i j
      · simp
    · refine Fin.addCases ?_ ?_ j <;> intro j <;> simp
  beta_diag i := by
    refine Fin.addCases ?_ ?_ i <;> intro i
    · simpa using D.beta_diag i
    · simp

/-- Restriction to the original coordinates preserves the exact objective. -/
theorem appendZeroDual_objective {m : ℕ} (D : Dual m) (n : ℕ) (p : Fin (m + n) → ℝ) :
    objective p (appendZeroDual D n) = objective (fun i => p (Fin.castAdd n i)) D := by
  simp [objective, appendZeroDual, Fin.sum_univ_add]

/-- Boolean feasibility is preserved by ignoring the appended coordinates. -/
theorem appendZeroDual_feasible {m : ℕ} (D : Dual m) (hD : DualFeasible D) (n : ℕ) :
    DualFeasible (appendZeroDual D n) := by
  intro X
  rw [quadratic, appendZeroDual_objective]
  exact hD (fun i => X (Fin.castAdd n i))

/-- Equal positive dummy loads fill the deficit to two. Their only error
in the sharp bound is their explicitly computed square mass. -/
theorem objective_le_smallTotal_error {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hs : ∑ i, p i ≤ 2)
    (D : Dual m) (hD : DualFeasible D) (n : ℕ) (hn : 0 < n)
    (hfill : 2 - (∑ i, p i) ≤ n) :
    objective p D ≤ (2 + ∑ i, (p i) ^ 2) / 3 + (2 - (∑ i, p i)) ^ 2 / (3 * n) := by
  let s : ℝ := 2 - ∑ i, p i
  let q := DustPaddedCells.target p s n
  have hs0 : 0 ≤ s := sub_nonneg.mpr hs
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := DustPaddedCells.target_cube p hp s hs0 n hn hfill
  have hsum : ∑ i, q i = 2 := by
    dsimp [q]
    rw [Fin.sum_univ_add]
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ s hnreal.ne']
    dsimp [s]
    ring
  have hsq : (∑ i, (q i) ^ 2) = (∑ i, (p i) ^ 2) + s ^ 2 / n := by
    dsimp [q]
    rw [Fin.sum_univ_add]
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hb := objective_le_sumTwo q hq hsum (appendZeroDual D n) (appendZeroDual_feasible D hD n)
  rw [appendZeroDual_objective, hsq] at hb
  change objective p D ≤ (2 + (∑ i, (p i) ^ 2)) / 3 + s ^ 2 / (3 * n)
  calc
    objective p D ≤ (2 + ((∑ i, (p i) ^ 2) + s ^ 2 / n)) / 3 := by
      simpa only [q, DustPaddedCells.target_head] using hb
    _ = _ := by ring

/-- Arbitrarily fine dummy loads give the sharp bound below total load two. -/
theorem objective_le_smallTotal {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hs : ∑ i, p i ≤ 2)
    (D : Dual m) (hD : DualFeasible D) :
    objective p D ≤ (2 + ∑ i, (p i) ^ 2) / 3 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let s : ℝ := 2 - ∑ i, p i
  have hs0 : 0 ≤ s := sub_nonneg.mpr hs
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (s ^ 2 / (3 * ε)))
  have hnreal : (0 : ℝ) < n := hs0.trans_lt ((le_max_left _ _).trans_lt hn)
  have hn0 : 0 < n := by exact_mod_cast hnreal
  have hfill : s ≤ n := (le_max_left _ _).trans hn.le
  have hsmall : s ^ 2 / (3 * n) < ε := by
    have hb := (div_lt_iff₀ (show 0 < 3 * ε by positivity)).mp
      ((le_max_right _ _).trans_lt hn)
    apply (div_lt_iff₀ (show (0 : ℝ) < 3 * n by positivity)).mpr
    nlinarith
  exact (objective_le_smallTotal_error p hp hs D hD n hn0 hfill).trans
    (by change (2 + ∑ i, (p i) ^ 2) / 3 + s ^ 2 / (3 * n) ≤ _; linarith)

/-- Exact finite primal-dual attainment supplies the corresponding value bound. -/
theorem value_le_smallTotal {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hs : ∑ i, p i ≤ 2) :
    value p ≤ (2 + ∑ i, (p i) ^ 2) / 3 := by
  obtain ⟨_, _, _, D, hD, hvalue, _, _⟩ := value_attained p hp
  rw [← hvalue]
  exact objective_le_smallTotal p hp hs D hD.1

end Erdos1017.Selector.Sharp

module

public import Erdos1017.Multipartite.Countable.CountableSupportedRows

/-!
# Erasing unused dust coefficients

`maskDust` erases unused dust coefficients while retaining all independent-head
charges, for use at a profile with zero dust mass; every dust count reduces to
the count-zero head test, and the objective, anchor row and head rows are
unchanged.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

/-- Erase unused dust coefficients while retaining all independent-head
charges. This is used only at a profile whose actual dust mass is zero. -/
def maskDust (D : Coefficients) : Coefficients
  | .inl i => head D i
  | .inr (.inl (i, j)) => pair D i j
  | .inr (.inr _) => 0

/-- Every dust count reduces to the original count-zero head test. -/
theorem maskDust_feasible {D : Coefficients} (hD : D ∈ feasible) : maskDust D ∈ feasible := by
  have hb (c : Coordinate) : 0 ≤ maskDust D c ∧ maskDust D c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | b)
    · exact ⟨hD.1.1 _, hD.1.2 _⟩
    · exact ⟨hD.1.1 _, hD.1.2 _⟩
    · exact ⟨le_rfl, zero_le_one⟩
  refine ⟨⟨fun c => (hb c).1, fun c => (hb c).2⟩, ?_⟩
  intro n X k
  have h := hD.2 n X 0
  simpa only [MultipartiteDust.charge, MultipartiteDust.head, MultipartiteDust.pair,
    MultipartiteDust.linear, MultipartiteDust.incident, MultipartiteDust.penalty,
    restrict, head, pair, linear, incident, penalty, maskDust, zero_mul, mul_zero,
    sub_zero, add_zero, Nat.cast_zero, Finset.sum_const_zero, zero_div] using h

theorem objective_maskDust (D : Coefficients) (p : ℕ → ℝ) :
    objective p 0 (maskDust D) = objective p 0 D := by
  simp only [objective, head, pair, incident, linear, penalty, maskDust, zero_mul, mul_zero,
    add_zero, sub_zero, tsum_zero, zero_pow (by decide : 2 ≠ 0), zero_div]

theorem anchorRow_maskDust (D : Coefficients) (p : ℕ → ℝ) :
    anchorRow p 0 (maskDust D) = anchorRow p 0 D := by
  simp only [anchorRow, head, linear, maskDust, mul_zero, add_zero]

theorem headRow_maskDust (D : Coefficients) (p : ℕ → ℝ) (i : ℕ) :
    headRow p 0 (maskDust D) i = headRow p 0 D i := by
  simp only [headRow, head, incident, MultipartiteCountableMeasure.kernel, pair,
    maskDust, zero_mul, mul_zero, sub_zero]

end Erdos1017.MultipartiteCountableDual

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Outside-peak box certificates for counts six to eight

A rational weighted-square bound for the normalized missing inventory, and the
incompatibility of the closed outside-peak box with that inventory for
reciprocal counts six, seven and eight.
-/

@[expose] public section

namespace Erdos1017.CuspOutsideHole

/-- A rational weighted-square bound for the normalized missing inventory.
No sign hypothesis on either mass variable is needed. -/
theorem weighted_inventory_bound {w p t W Z H : ℝ} (hw : 2 ≤ w)
    (hp : p ^ 2 ≤ W) (ht : t ^ 2 + Z ≤ H) :
    w * (W + 2 * p * t - 2 * p ^ 2 + Z) ≤
      w * (w - 1) * W + (w - 1) * Z + H := by
  have hw0 : 0 ≤ w := by linarith
  have hproduct : 0 ≤ w * (w - 2) * (W - p ^ 2) :=
    mul_nonneg (mul_nonneg hw0 (sub_nonneg.mpr hw)) (sub_nonneg.mpr hp)
  have hgap : 0 ≤ H - t ^ 2 - Z := by linarith
  have hnonneg := add_nonneg (add_nonneg (sq_nonneg (w * p - t)) hproduct) hgap
  have hid : (w * p - t) ^ 2 + w * (w - 2) * (W - p ^ 2) + (H - t ^ 2 - Z) =
      w * (w - 1) * W + (w - 1) * Z + H -
        w * (W + 2 * p * t - 2 * p ^ 2 + Z) := by ring
  rw [hid] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- The complete closed outside-peak box for reciprocal count six is
incompatible with the displayed raw normalized inventory. -/
theorem outside_six_contradiction {p t W Z : ℝ}
    (hinventory : 1 ≤ W + 2 * p * t - 2 * p ^ 2 + Z)
    (hp : p ^ 2 ≤ W) (ht : t ^ 2 + Z ≤ 11 / 5)
    (hW : W ≤ 24 / 1015) (hZ : Z ≤ 18 / 35) : False := by
  have hbound := weighted_inventory_bound (w := 8) (by norm_num) hp ht
  norm_num at hbound
  nlinarith

/-- The complete closed outside-peak box for reciprocal count seven is
incompatible with the displayed raw normalized inventory. -/
theorem outside_seven_contradiction {p t W Z : ℝ}
    (hinventory : 1 ≤ W + 2 * p * t - 2 * p ^ 2 + Z)
    (hp : p ^ 2 ≤ W) (ht : t ^ 2 + Z ≤ 51 / 20)
    (hW : W ≤ 91 / 3280) (hZ : Z ≤ 217 / 400) : False := by
  have hbound := weighted_inventory_bound (w := 9) (by norm_num) hp ht
  norm_num at hbound
  nlinarith

/-- The complete closed outside-peak box for reciprocal count eight is
incompatible with the displayed raw normalized inventory. -/
theorem outside_eight_contradiction {p t W Z : ℝ}
    (hinventory : 1 ≤ W + 2 * p * t - 2 * p ^ 2 + Z)
    (hp : p ^ 2 ≤ W) (ht : t ^ 2 + Z ≤ 25 / 9)
    (hW : W ≤ 232 / 13365) (hZ : Z ≤ 128 / 243) : False := by
  have hbound := weighted_inventory_bound (w := 11) (by norm_num) hp ht
  norm_num at hbound
  nlinarith

end Erdos1017.CuspOutsideHole

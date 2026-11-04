module

public import Erdos1017.Multipartite.TwoHead.TwoHeadFamilyCertificates

/-!
# Scalar bounds for the positive tail-count branches

The comparisons use exact polynomial identities and leave count-cell selection
to the family proof.
-/

@[expose] public section

namespace Erdos1017.TwoHeadTailScalar

def tailPolynomial (S x : ℝ) : ℝ :=
  -(1 - x) * S ^ 2 + (3 - 4 * x + 5 * x ^ 2) * S - 2 * x ^ 4 + 4 * x ^ 3 - 6 * x ^ 2

theorem tailPolynomial_nonneg {S x : ℝ} (hS : S ∈ Set.Icc (1 : ℝ) 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ tailPolynomial S x := by
  have hx0 : 0 ≤ x := hx.1
  have hx2 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hN1 : 0 ≤ tailPolynomial 1 x := by
    have hid : tailPolynomial 1 x = (1 - x) * (2 * (1 - x) * (1 - x ^ 2) + x) := by
      unfold tailPolynomial
      ring
    rw [hid]
    have ht : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
    positivity
  have hN2 : 0 ≤ tailPolynomial 2 x := by
    have hid : tailPolynomial 2 x = 2 * (1 - x) ^ 2 + 2 * x ^ 2 +
        2 * x ^ 3 * (2 - x) := by
      unfold tailPolynomial
      ring
    rw [hid]
    have ht : 0 ≤ 2 - x := by linarith [hx.2]
    positivity
  have hid : tailPolynomial S x = (2 - S) * tailPolynomial 1 x +
      (S - 1) * tailPolynomial 2 x + (1 - x) * (S - 1) * (2 - S) := by
    unfold tailPolynomial
    ring
  rw [hid]
  have hS1 : 0 ≤ S - 1 := sub_nonneg.mpr hS.1
  have hS2 : 0 ≤ 2 - S := sub_nonneg.mpr hS.2
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  positivity

theorem large_index_count_le_splitLower {S x : ℝ} (hS : S ∈ Set.Icc (1 : ℝ) 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x + (1 - x) * S / 4 ≤ TwoHeadFamilyCertificates.splitLower S x := by
  have hden : 0 < 1 + x + S := by linarith [hx.1, hS.1]
  have hid : 4 * (1 + x + S) *
      (TwoHeadFamilyCertificates.rationalLower S x - (x + (1 - x) * S / 4)) =
        tailPolynomial S x := by
    unfold TwoHeadFamilyCertificates.rationalLower tailPolynomial
    field_simp
    ring
  have hpoly := tailPolynomial_nonneg hS hx
  have hgap : x + (1 - x) * S / 4 ≤ TwoHeadFamilyCertificates.rationalLower S x := by
    have hnonneg : 0 ≤ TwoHeadFamilyCertificates.rationalLower S x -
        (x + (1 - x) * S / 4) := by
      apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * (1 + x + S))).mp
      rwa [hid]
    linarith
  exact hgap.trans (TwoHeadFamilyCertificates.rationalLower_le_splitLower hS.1 hx.1)

theorem two_count_bound_le {x : ℝ} (hx : 1 / 2 ≤ x) :
    (3 + 2 * x) / 5 ≤ 16 * (1 + x ^ 2) / 25 := by
  have hgap := mul_nonneg (show 0 ≤ x - 1 / 2 by linarith)
    (show 0 ≤ x - 1 / 8 by linarith)
  nlinarith

end Erdos1017.TwoHeadTailScalar

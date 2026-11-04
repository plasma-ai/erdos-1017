module

public import Erdos1017.Multipartite.MultipartiteProfileCollision
public import Erdos1017.Multipartite.TwoHead.TwoHeadFamilyCertificates
public import Erdos1017.Multipartite.TwoHead.TwoHeadTailAlgebra
public import Erdos1017.Multipartite.TwoHead.TwoHeadTailScalar

/-!
# Split comparator bound for the tail count cells

The selected count cells with dust mean at least one are bounded by the split
comparator. Fixed-profile count-law equality and the finite tensor certificate
are imported from their separately proved modules.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TwoHeadTailComparison

open TwoHeadCountLaw

private theorem radius_bounds {x S : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hS : 1 ≤ S) :
    0 < Real.sqrt (1 + x ^ 2) / (1 + x + S) ∧
      Real.sqrt (1 + x ^ 2) / (1 + x + S) ≤ 1 / 2 := by
  have hM : 0 < 1 + x + S := by linarith [hx.1]
  have hρ0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hρ : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  refine ⟨div_pos hρ hM, ?_⟩
  apply (div_le_iff₀ hM).mpr
  nlinarith [sq_nonneg (S - 1), mul_nonneg hx.1 (sub_nonneg.mpr hS)]

private theorem value_le_split_of_small_radius {x S : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hS : 0 ≤ S)
    (hr : Real.sqrt (1 + x ^ 2) / (1 + x + S) ≤ 4 / 13) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hM : 0 < 1 + x + S := by linarith [hx.1]
  have hM2 : 0 < (1 + x + S) ^ 2 := sq_pos_of_pos hM
  have hρ0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hρ1 : 1 ≤ Real.sqrt (1 + x ^ 2) := by nlinarith [sq_nonneg x]
  have ha : 0 < 1 / (1 + x + S) := by positivity
  have har : 1 / (1 + x + S) ≤ Real.sqrt (1 + x ^ 2) / (1 + x + S) :=
    div_le_div_of_nonneg_right hρ1 hM.le
  have hraw := MultipartiteDust.value_le_split_add_square (fun _ : Fin 1 => x)
    (fun _ => hx) S hS
  simp only [Fin.sum_univ_one] at hraw
  have hnorm : MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (1 / (1 + x + S)) + (x ^ 2 / (1 + x + S) ^ 2) / 2 := by
    apply (div_le_iff₀ hM2).mpr
    convert hraw using 1
    field_simp
  have hsq : (Real.sqrt (1 + x ^ 2) / (1 + x + S)) ^ 2 =
      (1 / (1 + x + S)) ^ 2 + x ^ 2 / (1 + x + S) ^ 2 := by
    rw [div_pow, hρsq]
    field_simp
  exact DenseMultipartite.collision_bound_le_split ha har hr hsq hnorm

theorem value_le_split_of_three_le_dust {x S : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hS : 3 ≤ S) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hM : 0 < 1 + x + S := by linarith [hx.1]
  have hρ0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  apply value_le_split_of_small_radius hx (by linarith)
  apply (div_le_iff₀ hM).mpr
  have hsmall : 13 * Real.sqrt (1 + x ^ 2) ≤ 4 * (4 + x) := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ 13 * Real.sqrt (1 + x ^ 2))
      (by linarith [hx.1] : 0 ≤ 4 * (4 + x))).mp
    nlinarith [hx.1, hx.2]
  linarith

private theorem cell_le_split_of_polynomial {j t : ℕ} {x S : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hS : 1 ≤ S)
    (hj : 0 < j)
    (hpoly : cellValue j t x S ≤ (1 + x + S) ^ 2 *
      Benchmark.splitPolynomial j (Real.sqrt (1 + x ^ 2) / (1 + x + S))) :
    cellValue j t x S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hM : 0 < 1 + x + S := by linarith [hx.1]
  have hr := radius_bounds hx hS
  have hsplit := TwoHeadFamilyBoundary.splitPolynomial_le_splitValue j hj
    (show Real.sqrt (1 + x ^ 2) / (1 + x + S) ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hr.1.le, by linarith [hr.2]⟩)
  apply le_trans _ hsplit
  apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
  simpa only [mul_comm] using hpoly

private theorem cell_le_split_of_lower {j t : ℕ} {x S : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hS : 1 ≤ S)
    (hlower : cellValue j t x S ≤ TwoHeadFamilyCertificates.splitLower S x) :
    cellValue j t x S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hM : 0 < 1 + x + S := by linarith [hx.1]
  have hr := radius_bounds hx hS
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hfloor := TwoHeadFamilyBoundary.splitValue_lower_bound
    (show Real.sqrt (1 + x ^ 2) / (1 + x + S) ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hr.1.le, by linarith [hr.2]⟩)
  apply le_trans _ hfloor
  apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
  convert hlower using 1
  unfold TwoHeadFamilyCertificates.splitLower
  rw [div_pow, hρsq]
  field_simp

private theorem kappa_nonneg {x S : ℝ} (hx : 0 ≤ x) (hS : 1 ≤ S) :
    0 ≤ (S + x - Real.sqrt (1 + x ^ 2)) / (Real.sqrt (1 + x ^ 2) + 1) := by
  have hρ0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hρhi : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    apply (sq_le_sq₀ hρ0 (by linarith : 0 ≤ 1 + x)).mp
    nlinarith
  exact div_nonneg (by linarith) (by positivity)

private theorem kappa_gt_two_fifths {x S : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hS : 2 ≤ S) :
    2 / 5 < (S + x - Real.sqrt (1 + x ^ 2)) / (Real.sqrt (1 + x ^ 2) + 1) := by
  have hρ0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hρhi : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    apply (sq_le_sq₀ hρ0 (by linarith [hx.1] : 0 ≤ 1 + x)).mp
    nlinarith [hx.1]
  have hρsmall : Real.sqrt (1 + x ^ 2) < 3 / 2 := by
    nlinarith [hx.1, hx.2, mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  apply (lt_div_iff₀ (by positivity : 0 < Real.sqrt (1 + x ^ 2) + 1)).mpr
  linarith

private theorem kappa_ge_half_sub_one {x S : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hS : S ∈ Set.Icc (1 : ℝ) 2) :
    (S - 1) / 2 ≤ (S + x - Real.sqrt (1 + x ^ 2)) / (Real.sqrt (1 + x ^ 2) + 1) := by
  have hρ0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hρlo : 1 ≤ Real.sqrt (1 + x ^ 2) := by nlinarith [sq_nonneg x]
  have hρhi := TwoHeadFamilyCertificates.sqrt_one_add_sq_le x
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hprod := mul_nonneg (show 0 ≤ 2 - S by linarith [hS.2])
    (show 0 ≤ Real.sqrt (1 + x ^ 2) - 1 by linarith)
  apply (le_div_iff₀ (by positivity : 0 < Real.sqrt (1 + x ^ 2) + 1)).mpr
  nlinarith

private theorem adjacent_cell_le_split (t : ℕ) {x S : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hS : 1 ≤ S) :
    cellValue (t + 1) t x S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hj : 0 < t + 1 := by omega
  have hM : 0 < 1 + x + S := by linarith [hx.1]
  have hκ := kappa_nonneg hx.1 hS
  have hid := TwoHeadTailAlgebra.comparison_identity (t + 1) t hj hM.ne'
  have hJ : 0 < ((t + 1 : ℕ) : ℝ) * (((t + 1 : ℕ) : ℝ) + 1) := by positivity
  have hnonneg : 0 ≤ 2 * (((t + 1 : ℕ) : ℝ) + 1) * x ^ 2 *
      ((S + x - Real.sqrt (1 + x ^ 2)) / (Real.sqrt (1 + x ^ 2) + 1)) := by positivity
  apply cell_le_split_of_polynomial hx hS hj
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left hJ).mp
  rw [hid]
  convert hnonneg using 1
  push_cast
  ring

private theorem three_one_tail_le_split {x S : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hS : S ∈ Set.Ico (5 / 3 : ℝ) 2)
    (hRlo : 2 * S < conditionalMoment x S 1) :
    cellValue 3 1 x S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  let κ := (S + x - Real.sqrt (1 + x ^ 2)) / (Real.sqrt (1 + x ^ 2) + 1)
  have hM : 0 < 1 + x + S := by linarith [hx.1, hS.1]
  have hκ : (S - 1) / 2 ≤ κ := kappa_ge_half_sub_one ⟨hx.1.le, hx.2.le⟩
    ⟨by linarith [hS.1], hS.2.le⟩
  have hclear := (lt_div_iff₀ (show 0 < 1 - x by linarith [hx.2])).mp hRlo
  unfold conditionalMoment floorMoment at hclear
  norm_num only [Nat.cast_ofNat] at hclear
  have hxlo : S * (2 - S) / 2 ≤ x := by nlinarith
  have hp₁ := mul_nonneg (sub_nonneg.mpr hxlo) (show 0 ≤ S - 1 by linarith [hS.1])
  have hp₂ := mul_nonneg hx.1.le (sub_nonneg.mpr hκ)
  have hη : 0 < 2 - S := by linarith [hS.2]
  have hSS : 1 < S * (S - 1) := by nlinarith [sq_nonneg (S - 5 / 3), hS.1]
  have hp₃ := mul_pos (sub_pos.mpr hSS) hη
  have hgap : 0 < 4 * x * κ - (2 - S) := by nlinarith
  have hp := mul_pos hx.1 hgap
  have hid := TwoHeadTailAlgebra.comparison_identity 3 1 (by omega) hM.ne'
  norm_num only [Nat.cast_ofNat] at hid
  have hident : 8 * x ^ 2 * (S + x - Real.sqrt (1 + x ^ 2)) /
      (Real.sqrt (1 + x ^ 2) + 1) - x * 1 * (4 - 2 * S) =
        2 * x * (4 * x * κ - (2 - S)) := by
    dsimp only [κ]
    ring
  rw [hident] at hid
  apply cell_le_split_of_polynomial ⟨hx.1.le, hx.2.le⟩ (by linarith [hS.1]) (by omega)
  nlinarith

private theorem four_two_le_split {x S : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hS : S ∈ Set.Ico (2 : ℝ) 3)
    (hRlo : 3 * S < conditionalMoment x S 2) :
    cellValue 4 2 x S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  let κ := (S + x - Real.sqrt (1 + x ^ 2)) / (Real.sqrt (1 + x ^ 2) + 1)
  have hM : 0 < 1 + x + S := by linarith [hx.1, hS.1]
  have hSpos : 0 < S := by linarith [hS.1]
  have hratio := TwoHeadTailAlgebra.conditional_ratio_le 2 hx.1.le hx.2 hSpos
    (by norm_num; exact hS.1) (by norm_num; exact hS.2.le)
  have hlo : 3 < conditionalMoment x S 2 / S := (lt_div_iff₀ hSpos).mpr hRlo
  have hxratio : 3 - S < x / (1 - x) := by linarith
  have hxclear := (lt_div_iff₀ (show 0 < 1 - x by linarith [hx.2])).mp hxratio
  have hxlo : (3 - S) / 2 < x := by
    nlinarith [mul_nonneg hx.1.le (show 0 ≤ S - 2 by linarith [hS.1])]
  have hκ : 2 / 5 < κ := kappa_gt_two_fifths ⟨hx.1.le, hx.2.le⟩ hS.1
  have hp₁ := mul_pos hx.1 (sub_pos.mpr hκ)
  have hgap : 0 < 10 * x * κ - 2 * (3 - S) := by nlinarith
  have hp := mul_pos hx.1 hgap
  have hid := TwoHeadTailAlgebra.comparison_identity 4 2 (by omega) hM.ne'
  norm_num only [Nat.cast_ofNat] at hid
  have hident : 10 * x ^ 2 * (S + x - Real.sqrt (1 + x ^ 2)) /
      (Real.sqrt (1 + x ^ 2) + 1) - x * 1 * (6 - 2 * S) =
        x * (10 * x * κ - 2 * (3 - S)) := by
    dsimp only [κ]
    ring
  rw [hident] at hid
  apply cell_le_split_of_polynomial ⟨hx.1.le, hx.2.le⟩ (by linarith [hS.1]) (by omega)
  nlinarith

private theorem large_one_le_split (j : ℕ) (hj : 4 ≤ j) {x S : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hS : S ∈ Set.Icc (1 : ℝ) 2)
    (hRlo : ((j : ℝ) - 1) * S ≤ conditionalMoment x S 1) :
    cellValue j 1 x S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hjpos : 0 < j := by omega
  have hjreal : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hcount := TwoHeadTailAlgebra.cellValue_le_count_bound j 1 hjpos hx.2 hRlo
  have hquot : S / (j : ℝ) ≤ S / 4 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hjpos)).mpr
    nlinarith [mul_nonneg (show 0 ≤ S by linarith [hS.1])
      (show 0 ≤ (j : ℝ) - 4 by linarith)]
  have hp := mul_le_mul_of_nonneg_left hquot (show 0 ≤ 1 - x by linarith [hx.2])
  have hbound : cellValue j 1 x S ≤ x + (1 - x) * S / 4 := by
    rw [mul_div_assoc] at hcount ⊢
    linarith
  apply cell_le_split_of_lower ⟨hx.1.le, hx.2.le⟩ hS.1
  exact hbound.trans (TwoHeadTailScalar.large_index_count_le_splitLower hS ⟨hx.1.le, hx.2.le⟩)

private theorem large_two_le_split (j : ℕ) (hj : 5 ≤ j) {x S : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hS : S ∈ Set.Ico (2 : ℝ) 3)
    (hRlo : ((j : ℝ) - 1) * S < conditionalMoment x S 2) :
    cellValue j 2 x S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hjpos : 0 < j := by omega
  have hjreal : (5 : ℝ) ≤ j := by exact_mod_cast hj
  have hSpos : 0 < S := by linarith [hS.1]
  have hratio := TwoHeadTailAlgebra.conditional_ratio_le 2 hx.1.le hx.2 hSpos
    (by norm_num; exact hS.1) (by norm_num; exact hS.2.le)
  have hlo : 4 < conditionalMoment x S 2 / S := by
    apply (lt_div_iff₀ hSpos).mpr
    nlinarith [mul_nonneg hSpos.le (show 0 ≤ (j : ℝ) - 5 by linarith)]
  have hxratio : 1 < x / (1 - x) := by linarith [hS.2]
  have hxhalf : 1 / 2 ≤ x := by
    have h := (lt_div_iff₀ (show 0 < 1 - x by linarith [hx.2])).mp hxratio
    linarith
  have hcount := TwoHeadTailAlgebra.cellValue_le_count_bound j 2 hjpos hx.2 hRlo.le
  have hquot : S / (j : ℝ) ≤ 3 / 5 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hjpos)).mpr
    linarith [hS.2]
  have hp := mul_le_mul_of_nonneg_left hquot (show 0 ≤ 1 - x by linarith [hx.2])
  have hbound : cellValue j 2 x S ≤ (3 + 2 * x) / 5 := by
    rw [mul_div_assoc] at hcount
    nlinarith
  have hρ0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hρsq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)]
  have hM : 0 < 1 + x + S := by linarith [hx.1, hS.1]
  have hsmall : Real.sqrt (1 + x ^ 2) / (1 + x + S) < 9 / 25 := by
    have hlin : 25 * Real.sqrt (1 + x ^ 2) < 9 * (3 + x) := by
      apply (sq_lt_sq₀ (by positivity : 0 ≤ 25 * Real.sqrt (1 + x ^ 2))
        (by linarith [hx.1] : 0 ≤ 9 * (3 + x))).mp
      nlinarith [hx.1, hx.2]
    apply (div_lt_iff₀ hM).mpr
    linarith [hS.1]
  have hgap := mul_pos (show 0 < 1 + x ^ 2 by positivity) (sub_pos.mpr hsmall)
  have hlower : 16 * (1 + x ^ 2) / 25 < TwoHeadFamilyCertificates.splitLower S x := by
    unfold TwoHeadFamilyCertificates.splitLower
    nlinarith
  apply cell_le_split_of_lower ⟨hx.1.le, hx.2.le⟩ (by linarith [hS.1])
  exact (hbound.trans (TwoHeadTailScalar.two_count_bound_le hxhalf)).trans hlower.le

theorem actual_value_le_split {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hS : 1 ≤ S) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      Benchmark.splitValue (Real.sqrt (1 + x ^ 2) / (1 + x + S)) := by
  have hSpos : 0 < S := by linarith
  by_cases hx0 : x = 0
  · subst x
    simpa using (TwoHeadFamilyBoundary.zero_head_normalization hSpos.le).le
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxpos, hx1⟩
  have hxC : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx, hx1.le⟩
  by_cases hS3 : 3 ≤ S
  · exact value_le_split_of_three_le_dust hxC hS3
  have hS3' : S < 3 := lt_of_not_ge hS3
  let j := selectedIndex x S
  have hjspec := selectedIndex_spec hx hx1 hSpos
  have hjfloor := TwoHeadTailAlgebra.floor_lt_selectedIndex hxpos hx1 hSpos
  rw [value_eq_selected hx hx1 hSpos]
  by_cases hS2 : S < 2
  · have ht : ⌊S⌋₊ = 1 := (Nat.floor_eq_iff hSpos.le).mpr (by norm_num; exact ⟨hS, hS2⟩)
    have hjlo : 2 ≤ j := by rw [ht] at hjfloor; change 1 < j at hjfloor; omega
    have hRlo : ((j : ℝ) - 1) * S < conditionalMoment x S 1 := by
      simpa only [ht] using hjspec.2.2.1
    rw [ht]
    change cellValue j 1 x S / (1 + x + S) ^ 2 ≤ _
    by_cases hj2 : j = 2
    · rw [hj2]
      exact adjacent_cell_le_split 1 hxC hS
    by_cases hj3 : j = 3
    · rw [hj3]
      by_cases hSfive : S ≤ 5 / 3
      · apply cell_le_split_of_lower hxC hS
        have hcert := TwoHeadFamilyCertificates.branchValue_lt_splitLower ⟨hS, hSfive⟩ hxC
        simpa only [cellValue_three_one, TwoHeadFamilyCertificates.branchValue] using hcert.le
      · apply three_one_tail_le_split hxI ⟨(lt_of_not_ge hSfive).le, hS2⟩
        simpa only [hj3, Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] using hRlo
    · exact large_one_le_split j (by omega) hxI ⟨hS, hS2.le⟩ hRlo.le
  · have hS2' : 2 ≤ S := le_of_not_gt hS2
    have ht : ⌊S⌋₊ = 2 := (Nat.floor_eq_iff hSpos.le).mpr (by norm_num; exact ⟨hS2', hS3'⟩)
    have hjlo : 3 ≤ j := by rw [ht] at hjfloor; change 2 < j at hjfloor; omega
    have hRlo : ((j : ℝ) - 1) * S < conditionalMoment x S 2 := by
      simpa only [ht] using hjspec.2.2.1
    rw [ht]
    change cellValue j 2 x S / (1 + x + S) ^ 2 ≤ _
    by_cases hj3 : j = 3
    · rw [hj3]
      exact adjacent_cell_le_split 2 hxC hS
    by_cases hj4 : j = 4
    · rw [hj4]
      apply four_two_le_split hxI ⟨hS2', hS3'⟩
      simpa only [hj4, Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num] using hRlo
    · exact large_two_le_split j (by omega) hxI ⟨hS2', hS3'⟩ hRlo

end Erdos1017.TwoHeadTailComparison

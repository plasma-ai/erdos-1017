module

public import Erdos1017.IntegerTransfer.ResidualAllocationExpectation

/-!
# Mass budget of large and unselected profile layers

This module defines the large profile layers meeting the common matching size
threshold and the two-vertex profile mass, shows that these use disjoint parts
of the fractional objective, and bounds the unmatched expected pair cost by the
two-vertex cost plus a uniformly small contribution from layers below the
allocation floor.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ C b n : ℕ}

/-- Profile layers large enough for the common matching size threshold. -/
def largeLayers (n C : ℕ) (mass : Finset (Fin ℓ) → ℝ) (α₀ : ℝ) :
    Finset (Finset (Fin ℓ) × Fin C) :=
  Finset.univ.filter (fun s => 3 ≤ s.1.card ∧ α₀ ≤ allocationDensity n C (mass s.1))

/-- The exact fractional cost of the two-vertex profiles. -/
def pairProfileMass (mass : Finset (Fin ℓ) → ℝ) : ℝ :=
  ∑ K, if K.card = 2 then mass K else 0

/-- Equal splitting into the fixed layer count preserves any profile sum. -/
theorem sum_layers (f : Finset (Fin ℓ) → ℝ) (hC : 0 < C) :
    (∑ s : Finset (Fin ℓ) × Fin C, f s.1 / C) = ∑ K, f K := by
  have hCp : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro K _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem largeLayers_mem (mass : Finset (Fin ℓ) → ℝ) (α₀ : ℝ)
    (s : Finset (Fin ℓ) × Fin C) :
    s ∈ largeLayers n C mass α₀ ↔ 3 ≤ s.1.card ∧ α₀ ≤ allocationDensity n C (mass s.1) := by
  simp only [largeLayers, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every selected layer has positive mass and a clique size in the fixed cap. -/
theorem largeLayers_card_bounds (mass : Finset (Fin ℓ) → ℝ)
    (hcard : ∀ K, mass K ≠ 0 → 2 ≤ K.card ∧ K.card ≤ b)
    (α₀ : ℝ) (hα₀ : 0 < α₀) (hn : 0 < n) (hC : 0 < C)
    (s : Finset (Fin ℓ) × Fin C) (hs : s ∈ largeLayers n C mass α₀) :
    3 ≤ s.1.card ∧ s.1.card ≤ b := by
  have hs := (largeLayers_mem mass α₀ s).mp hs
  have hden : 0 < (C : ℝ) * (n : ℝ) ^ 2 :=
    mul_pos (by exact_mod_cast hC) (sq_pos_of_pos (by exact_mod_cast hn))
  have hmass : 0 < mass s.1 := (div_pos_iff_of_pos_right hden).mp (hα₀.trans_le hs.2)
  exact ⟨hs.1, (hcard s.1 hmass.ne').2⟩

/-- The two-vertex mass and all large-layer masses use disjoint parts of the
original fractional objective. -/
theorem pair_add_large_mass_le (mass : Finset (Fin ℓ) → ℝ) (hmass : ∀ K, 0 ≤ mass K)
    (α₀ : ℝ) (hC : 0 < C) :
    pairProfileMass mass +
      (∑ i : largeLayers n C mass α₀, mass i.val.1 / C) ≤ ∑ K, mass K := by
  classical
  have htwo : pairProfileMass mass = ∑ s : Finset (Fin ℓ) × Fin C,
      if s.1.card = 2 then mass s.1 / C else 0 := by
    have h := sum_layers (ℓ := ℓ) (C := C) (fun K => if K.card = 2 then mass K else 0) hC
    simpa only [ite_div, zero_div, pairProfileMass] using h.symm
  have hlarge : (∑ i : largeLayers n C mass α₀, mass i.val.1 / C) =
      ∑ s : Finset (Fin ℓ) × Fin C, if s ∈ largeLayers n C mass α₀ then mass s.1 / C else 0 := by
    rw [Finset.sum_coe_sort (largeLayers n C mass α₀) (fun s => mass s.1 / C)]
    simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [htwo, hlarge, ← Finset.sum_add_distrib, ← sum_layers mass hC]
  apply Finset.sum_le_sum
  intro s _
  have hnonneg : 0 ≤ mass s.1 / C := div_nonneg (hmass _) (Nat.cast_nonneg C)
  by_cases hs : s ∈ largeLayers n C mass α₀
  · have hnot : s.1.card ≠ 2 := by have := ((largeLayers_mem mass α₀ s).mp hs).1; omega
    simp only [hnot, ite_false, hs, ite_true, zero_add, le_refl]
  · simp only [hs, ite_false, add_zero]
    split_ifs
    · exact le_rfl
    · exact hnonneg

/-- The unmatched expected pair cost is the two-vertex cost plus a uniformly
small contribution from the profiles below the allocation floor. -/
theorem unselected_layer_mass_le (mass : Finset (Fin ℓ) → ℝ)
    (hmass : ∀ K, 0 ≤ mass K)
    (hcard : ∀ K, mass K ≠ 0 → 2 ≤ K.card ∧ K.card ≤ b)
    (α₀ : ℝ) (hα₀ : 0 < α₀) (hn : 0 < n) (hC : 0 < C) :
    (∑ s : Finset (Fin ℓ) × Fin C,
      if s ∈ largeLayers n C mass α₀ then 0 else (s.1.card.choose 2 : ℝ) * mass s.1 / C) ≤
        pairProfileMass mass + (2 ^ ℓ * C : ℕ) * (b.choose 2 : ℝ) * α₀ * (n : ℝ) ^ 2 := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint (s : Finset (Fin ℓ) × Fin C) :
      (if s ∈ largeLayers n C mass α₀ then 0 else (s.1.card.choose 2 : ℝ) * mass s.1 / C) ≤
        (if s.1.card = 2 then mass s.1 / C else 0) + (b.choose 2 : ℝ) * α₀ * (n : ℝ) ^ 2 := by
    by_cases hs : s ∈ largeLayers n C mass α₀
    · rw [ite_eq_left hs]
      exact add_nonneg (by split_ifs; exact div_nonneg (hmass _) hCp.le; exact le_rfl) (by positivity)
    rw [ite_eq_right hs]
    by_cases hz : mass s.1 = 0
    · simp only [hz, mul_zero, zero_div, ite_self, zero_add]
      positivity
    have hbounds := hcard s.1 hz
    by_cases htwo : s.1.card = 2
    · simp only [htwo, Nat.choose_self, Nat.cast_one, one_mul, ite_true]
      exact le_add_of_nonneg_right (by positivity)
    have hthree : 3 ≤ s.1.card := by omega
    have hsmall : allocationDensity n C (mass s.1) < α₀ := by
      exact lt_of_not_ge (fun h => hs ((largeLayers_mem mass α₀ s).mpr ⟨hthree, h⟩))
    have hsmall' : mass s.1 / C ≤ α₀ * (n : ℝ) ^ 2 := by
      have h := (div_lt_iff₀ (mul_pos hCp (sq_pos_of_pos hnp))).mp hsmall
      apply (div_le_iff₀ hCp).mpr
      nlinarith only [h.le]
    have hr : (s.1.card.choose 2 : ℝ) ≤ b.choose 2 := by exact_mod_cast Nat.choose_le_choose 2 hbounds.2
    rw [ite_eq_right htwo]
    calc
      _ = (s.1.card.choose 2 : ℝ) * (mass s.1 / C) := by ring
      _ ≤ (b.choose 2 : ℝ) * (α₀ * (n : ℝ) ^ 2) :=
        mul_le_mul hr hsmall' (div_nonneg (hmass _) hCp.le) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ s : Finset (Fin ℓ) × Fin C,
        ((if s.1.card = 2 then mass s.1 / C else 0) + (b.choose 2 : ℝ) * α₀ * (n : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun s _ => hpoint s)
    _ = _ := by
      rw [Finset.sum_add_distrib, Fintype.sum_prod_type]
      have hinner (K : Finset (Fin ℓ)) :
          (∑ _ : Fin C, if K.card = 2 then mass K / C else 0) = if K.card = 2 then mass K else 0 := by
        by_cases hK : K.card = 2 <;> simp only [hK, ite_true, ite_false, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero]
        field_simp
      simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul, pairProfileMass, Nat.cast_mul]
      ring

end Erdos1017.MultipartiteAllocation

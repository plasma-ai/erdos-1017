module

public import Erdos1017.Models.PhysicalPrimal.FiniteSignatureBins

/-!
# Finite hub certificate

Hub-plus-subset clique tests give the penalty for a homogeneous bin and the
retained-bin estimate, and a finite hub certificate forces strictly negative
charge at every omitted order, with bounded subclique tests as hypotheses rather
than assumed matrix coercivity.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Actual hub-plus-subset clique tests give the penalty for a homogeneous bin. -/
theorem actual_bin_penalty (W : Finset α) (h k : ℕ) (hh : 0 < h) (hk : 2 ≤ k)
    (hkW : k ≤ W.card) (H : Fin h → α → ℝ) (sees : Fin h → Bool)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0) (γ : ℝ) (hγ : 0 < γ)
    (hcover : ∀ a ∈ W, γ ≤ (h : ℝ)⁻¹ * ∑ i, H i a)
    (hmissing : ∀ i, sees i = false → ∀ a ∈ W, H i a = 0)
    (htest : ∀ i, sees i = true → ∀ S ∈ W.powersetCard k,
      (∑ a ∈ S, H i a) + pairCharge S y ≤ 1) :
    2 * (γ - 1 / k) / (k - 1) ≤ -subsetAverage W 2 (fun S => pairCharge S y) := by
  have hW : (0 : ℝ) < W.card := by exact_mod_cast (show 0 < W.card by omega)
  apply hub_bin_penalty h k hh hk (fun i => (∑ a ∈ W, H i a) / W.card) sees
    (-subsetAverage W 2 (fun S => pairCharge S y)) γ hγ
  · have hsum := Finset.sum_le_sum hcover
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    rw [Finset.sum_comm] at hsum
    rw [← Finset.sum_div, mul_div]
    apply (le_div_iff₀ hW).mpr
    simpa [mul_comm] using hsum
  · intro i hi
    have hz : (∑ a ∈ W, H i a) = 0 := Finset.sum_eq_zero (fun a ha => hmissing i hi a ha)
    rw [hz, zero_div]
  · intro i hi
    have havg := averaged_hub_test W k hk hkW
      (fun S => ∑ a ∈ S, H i a) (fun S => pairCharge S y) (by
        intro S hS
        have hs := htest i hi S hS
        simpa [Finset.powersetCard_one, ← pairCharge_eq_sum_pairs _ y hy] using hs)
    rw [subsetAverage_singleton_sum] at havg
    simpa only [mul_neg, sub_neg_eq_add] using havg

/-- The retained-bin estimate from actual hub signatures and actual small-clique tests. -/
theorem retained_charge_bound (U : Finset α) (h k B T N : ℕ)
    (hh : 0 < h) (hk : 2 ≤ k) (hkB : k ≤ B) (hTB : T ≤ B) (hT : 0 < T)
    (hN : T + 2 ^ h ≤ N) (signature : α → (Fin h → Bool)) (H : Fin h → α → ℝ)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0)
    (hlower : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → -3 ≤ y a b)
    (γ p₀ : ℝ) (hγ : 0 < γ) (hp₀ : 0 ≤ p₀)
    (hp₀eq : p₀ = 2 * (γ - 1 / k) / (k - 1))
    (hsize : 3 * (2 ^ h : ℕ) / 2 + 4 ≤ (T : ℝ) * p₀)
    (hcover : ∀ a ∈ U, γ ≤ (h : ℝ)⁻¹ * ∑ i, H i a)
    (hmissing : ∀ a ∈ U, ∀ i, signature a i = false → H i a = 0)
    (hhub : ∀ i (S : Finset α), S ⊆ U → S.card = k →
      (∀ a ∈ S, signature a i = true) → (∑ a ∈ S, H i a) + pairCharge S y ≤ 1)
    (hsmall : ∀ S : Finset α, S ⊆ U → S.card ≤ N → pairCharge S y ≤ 1)
    (hn : 0 < (Finset.univ.biUnion (retainedBins U signature B)).card) :
    pairCharge (Finset.univ.biUnion (retainedBins U signature B)) y ≤
      3 * ((Finset.univ.biUnion (retainedBins U signature B)).card : ℝ) / 2 -
        (p₀ / (2 * T)) * ((Finset.univ.biUnion (retainedBins U signature B)).card : ℝ) ^ 2 / 2 := by
  let W := retainedBins U signature B
  let m := Fintype.card (RetainedIndex U signature B)
  have hm : m ≤ 2 ^ h := by
    simpa [m] using retainedIndex_card_le U signature B
  have hsub (i : Fin m) : W i ⊆ U := Finset.filter_subset _ _
  have hcap (i : Fin m) : B ≤ (W i).card := retainedBins_capacity U signature B i
  have hdisj := retainedBins_disjoint U signature B
  have hdiag (i : Fin m) : p₀ ≤ -subsetAverage (W i) 2 (fun S => pairCharge S y) ∧
      -subsetAverage (W i) 2 (fun S => pairCharge S y) ≤ 3 := by
    let s := ((Fintype.equivFin (RetainedIndex U signature B)).symm i).val
    have hsig (a : α) (ha : a ∈ W i) : signature a = s := (Finset.mem_filter.mp ha).2
    constructor
    · rw [hp₀eq]
      apply actual_bin_penalty (W i) h k hh hk (hkB.trans (hcap i)) H s y hy γ hγ
        (fun a ha => hcover a (hsub i ha))
      · intro j hj a ha
        exact hmissing a (hsub i ha) j (by rw [hsig a ha]; exact hj)
      · intro j hj S hS
        have hSW := (Finset.mem_powersetCard.mp hS).1
        apply hhub j S (hSW.trans (hsub i)) (Finset.mem_powersetCard.mp hS).2
        intro a ha
        rw [hsig a (hSW ha)]
        exact hj
    · have hl := subsetAverage_pairCharge_lower (W i) (hk.trans (hkB.trans (hcap i))) y hy (-3)
        (fun a ha b hb hab => hlower a (hsub i ha) b (hsub i hb) hab)
      linarith
  have htests (v : Fin m → Finset α) (hv : ∀ i, v i ⊆ W i)
      (_hcards : ∀ i, (v i).card ≤ T) (hcards : (∑ i, (v i).card) ≤ T + m) :
      binCharge (fun _ S => pairCharge S y) (fun _ _ => y) v ≤ 1 := by
    have hvdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) v := by
      intro i hi j hj hij
      exact (hdisj hi hj hij).mono (hv i) (hv j)
    rw [binCharge_eq_union v hvdisj y hy]
    apply hsmall
    · intro a ha
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      exact hsub i (hv i hi)
    · rw [Finset.card_biUnion hvdisj]
      exact hcards.trans ((Nat.add_le_add_left hm T).trans hN)
  have hsize' : 3 * (m : ℝ) / 2 + 4 ≤ (T : ℝ) * p₀ := by
    have hm' : (m : ℝ) ≤ (2 ^ h : ℕ) := by exact_mod_cast hm
    linarith
  have hsum : (∑ i, ((W i).card : ℝ)) = (Finset.univ.biUnion W).card := by
    rw [Finset.card_biUnion hdisj]
    norm_cast
  have hb := binCharge_bound_of_small_tests W T hT (fun i => hTB.trans (hcap i))
    (fun _ S => pairCharge S y) (fun _ _ => y) p₀ hp₀ hdiag htests hsize'
    (Finset.univ.biUnion W).card hsum (by exact_mod_cast hn)
  rwa [binCharge_eq_union W hdisj y hy] at hb

/-- A finite hub certificate forces strictly negative charge at every omitted order.
The hypotheses are actual bounded subclique tests, not pre-assumed matrix coercivity. -/
theorem omitted_clique_negative (U : Finset α) (h k B T C N : ℕ)
    (hh : 0 < h) (hk : 2 ≤ k) (hkB : k ≤ B) (hTB : T ≤ B) (hT : 0 < T)
    (hC : 2 ≤ C) (hN : T + 2 ^ h ≤ N) (hNC : 2 ^ h * (B - 1) + C ≤ N)
    (signature : α → (Fin h → Bool)) (H : Fin h → α → ℝ)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0) (hupper : ∀ a b, y a b ≤ 1)
    (hlower : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → -3 ≤ y a b)
    (γ p₀ : ℝ) (hγ : 0 < γ) (hp₀ : 0 < p₀)
    (hp₀eq : p₀ = 2 * (γ - 1 / k) / (k - 1))
    (hsize : 3 * (2 ^ h : ℕ) / 2 + 4 ≤ (T : ℝ) * p₀)
    (hcutoff : 4 * ((2 ^ h * (B - 1) : ℕ) + 4 : ℝ) ≤ (p₀ / (2 * T)) * C)
    (hcover : ∀ a ∈ U, γ ≤ (h : ℝ)⁻¹ * ∑ i, H i a)
    (hmissing : ∀ a ∈ U, ∀ i, signature a i = false → H i a = 0)
    (hhub : ∀ i (S : Finset α), S ⊆ U → S.card = k →
      (∀ a ∈ S, signature a i = true) → (∑ a ∈ S, H i a) + pairCharge S y ≤ 1)
    (hsmall : ∀ S : Finset α, S ⊆ U → S.card ≤ N → pairCharge S y ≤ 1)
    (hlarge : N < U.card) : pairCharge U y < 0 := by
  let D := discarded U signature B
  let R := Finset.univ.biUnion (retainedBins U signature B)
  let L := 2 ^ h * (B - 1)
  let δ : ℝ := p₀ / (2 * T)
  have hD : D.card ≤ L := by simpa [D, L] using discarded_card_le U signature B
  have hdisj : Disjoint D R := discarded_retained_disjoint U signature B
  have hcoverU : D ∪ R = U := discarded_union_retained U signature B
  have hcard : D.card + R.card = U.card := by rw [← Finset.card_union_of_disjoint hdisj, hcoverU]
  have hCR : C < R.card := by dsimp [L] at hD; omega
  have hRpos : 0 < R.card := by omega
  have hretained := retained_charge_bound U h k B T N hh hk hkB hTB hT hN signature H y hy
    hlower γ p₀ hγ hp₀.le hp₀eq hsize hcover hmissing hhub hsmall hRpos
  have hsmallD : pairCharge D y ≤ 1 := by
    apply hsmall D (Finset.filter_subset _ _)
    dsimp [L] at hD
    omega
  have hD' : (D.card : ℝ) ≤ L := by exact_mod_cast hD
  have hfull := discarded_charge_bound D R hdisj y hupper L R.card δ hD' rfl hsmallD hretained
  rw [hcoverU] at hfull
  have hδ : 0 < δ := div_pos hp₀ (mul_pos (by norm_num) (by exact_mod_cast hT))
  have hCR' : (C : ℝ) < R.card := by exact_mod_cast hCR
  have hthreshold : 4 * ((L : ℝ) + 4) ≤ δ * R.card :=
    hcutoff.trans (mul_le_mul_of_nonneg_left hCR'.le hδ.le)
  exact omitted_charge_negative L δ R.card (pairCharge U y) (Nat.cast_nonneg _)
    (by exact_mod_cast (show 2 < R.card by omega)) hthreshold hfull

end Erdos1017.FiniteArity

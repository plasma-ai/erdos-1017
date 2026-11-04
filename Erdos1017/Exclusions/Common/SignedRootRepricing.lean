module

public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Signed root repricing of a charge

This module defines the signed edit that increases a root row and pays for it on
the original neighbor square, and shows that every clique inequality and
product-almost-everywhere clique test survives it, the gain with one root being
`(2-k)` times the sum of the `k` leaf increments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace Erdos1017.SignedRootRepricing

private theorem sum_off_diagonal {n : ℕ} (h : Fin n → ℝ) (i : Fin n) :
    (∑ j, if i = j then 0 else h j) = (∑ j, h j) - h i := by
  have heq : (∑ j, h j) = (∑ j, if i = j then h j else 0) +
      (∑ j, if i = j then 0 else h j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  simpa using (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using heq.symm))

private theorem root_penalty_sum {n : ℕ} (h : Fin n → ℝ) (r : Fin n)
    (hr : h r = 0) :
    (∑ i, ∑ j, if i = j then 0 else
      (-h i - h j + (if i = r then 2 * h j else 0) +
        (if j = r then 2 * h i else 0))) / 2 =
      (3 - (n : ℝ)) * ∑ i, h i := by
  have hsplit (i j : Fin n) :
      (if i = j then 0 else
        (-h i - h j + (if i = r then 2 * h j else 0) +
          (if j = r then 2 * h i else 0))) =
      -(if j = i then 0 else h i) - (if i = j then 0 else h j) +
        (if i = r then 2 * h j else 0) + (if j = r then 2 * h i else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hir : i = r
      · subst i
        simp [hr]
      · simp [hir]
    · simp [hij, Ne.symm hij]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  have hc (i : Fin n) : (∑ j, if j = i then 0 else h i) = ((n : ℝ) - 1) * h i := by
    simpa [eq_comm, sub_mul] using sum_off_diagonal (fun _ => h i) i
  simp_rw [hc, sum_off_diagonal]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring_nf
  simp
  ring

/-- Increase the root row and pay for it on the original neighbor square.
The subtraction retains all signed original internal charges. -/
def increment {Ω : Type*} (I N : Set Ω) (h : Ω → ℝ) (x y : Ω) : ℝ := by
  classical
  exact (if x ∈ I then h y else 0) + (if y ∈ I then h x else 0) -
    if x ∈ N ∧ y ∈ N then h x + h y else 0

/-- The edited charge remains zero on every original nonedge. -/
def charge {Ω : Type*} (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I N : Set Ω) (h : Ω → ℝ) (x y : Ω) : ℝ :=
  if G x y = true then Y x y + increment I N h x y else 0

theorem increment_symm {Ω : Type*} (I N : Set Ω) (h : Ω → ℝ) (x y : Ω) :
    increment I N h x y = increment I N h y x := by
  by_cases hx : x ∈ N <;> by_cases hy : y ∈ N <;>
    simp only [increment, hx, hy, and_self, false_and, and_false,
      ↓reduceIte] <;> ring

theorem charge_symm {Ω : Type*} (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hG : ∀ x y, G x y = G y x) (hY : ∀ x y, Y x y = Y y x)
    (I N : Set Ω) (h : Ω → ℝ) (x y : Ω) :
    charge G Y I N h x y = charge G Y I N h y x := by
  simp only [charge, hG x y, hY x y, increment_symm I N h x y]

theorem charge_zero_of_nonedge {Ω : Type*} (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I N : Set Ω) (h : Ω → ℝ) {x y : Ω} (hxy : G x y = false) :
    charge G Y I N h x y = 0 := by
  simp [charge, hxy]

theorem norm_increment_le {Ω : Type*} (I N : Set Ω) (h : Ω → ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hh : ∀ x, ‖h x‖ ≤ H) (x y : Ω) :
    ‖increment I N h x y‖ ≤ 4 * H := by
  classical
  have ha : ‖if x ∈ I then h y else 0‖ ≤ H := by split_ifs <;> simp_all
  have hb : ‖if y ∈ I then h x else 0‖ ≤ H := by split_ifs <;> simp_all
  have hc : ‖if x ∈ N ∧ y ∈ N then h x + h y else 0‖ ≤ 2 * H := by
    split_ifs
    · exact (norm_add_le _ _).trans (by linarith [hh x, hh y])
    · simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH)
  have hs := norm_sub_le ((if x ∈ I then h y else 0) + (if y ∈ I then h x else 0))
    (if x ∈ N ∧ y ∈ N then h x + h y else 0)
  have hab := norm_add_le (if x ∈ I then h y else 0) (if y ∈ I then h x else 0)
  change ‖_ - _‖ ≤ _
  linarith

/-- A bounded signed edit need not remain in the original compact charge
box. Its actual bound is enough for the scalar sampling comparison. -/
theorem norm_charge_le {Ω : Type*} (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I N : Set Ω) (h : Ω → ℝ) (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hY : ∀ x y, ‖Y x y‖ ≤ B) (hh : ∀ x, ‖h x‖ ≤ H) (x y : Ω) :
    ‖charge G Y I N h x y‖ ≤ B + 4 * H := by
  unfold charge
  split_ifs
  · exact (norm_add_le _ _).trans (by linarith [hY x y, norm_increment_le I N h H hH hh x y])
  · simpa using (add_nonneg hB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hH))

/-- With one root and all other vertices in its neighborhood, the exact
clique gain is `(2-k)` times the sum of the `k` leaf increments. -/
theorem tupleCharge_eq_of_root {Ω : Type*} {n : ℕ}
    (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I N : Set Ω) (h : Ω → ℝ)
    (v : Fin n → Ω) (hv : FiniteArity.TupleClique G v) (r : Fin n)
    (hI : ∀ i, v i ∈ I ↔ i = r) (hN : ∀ i, v i ∈ N ↔ i ≠ r)
    (hr : h (v r) = 0) :
    FiniteArity.tupleCharge (charge G Y I N h) v =
      FiniteArity.tupleCharge Y v + (3 - (n : ℝ)) * ∑ i, h (v i) := by
  have hp (i j : Fin n) :
      (if i = j then 0 else charge G Y I N h (v i) (v j)) =
      (if i = j then 0 else Y (v i) (v j)) +
      (if i = j then 0 else
        (-h (v i) - h (v j) + (if i = r then 2 * h (v j) else 0) +
          (if j = r then 2 * h (v i) else 0))) := by
    by_cases hij : i = j
    · simp [hij]
    · rw [ite_eq_right hij, ite_eq_right hij, ite_eq_right hij, charge,
        ite_eq_left (hv i j hij)]
      simp only [increment, hI, hN]
      by_cases hi : i = r
      · subst i
        have hj : j ≠ r := Ne.symm hij
        simp [hj, hr]
        ring
      · by_cases hj : j = r
        · subst j
          simp [hi, hr]
          ring
        · simp [hi, hj]
          ring
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  simp_rw [hp, Finset.sum_add_distrib]
  rw [add_div, root_penalty_sum (fun i => h (v i)) r hr]

private theorem tupleCharge_mono {Ω : Type*} {n : ℕ} (Y Z : Ω → Ω → ℝ)
    (v : Fin n → Ω) (hYZ : ∀ i j, i ≠ j → Y (v i) (v j) ≤ Z (v i) (v j)) :
    FiniteArity.tupleCharge Y v ≤ FiniteArity.tupleCharge Z v := by
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simpa only [ite_eq_right hij] using hYZ i j hij

private theorem charge_le_one {Ω : Type*} (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hYsym : ∀ x y, Y x y = Y y x) (hY : ∀ x y, Y x y ≤ 1)
    (I N : Set Ω) (hdisjoint : Disjoint I N)
    (hrow : ∀ x ∈ I, ∀ y, G x y = true ↔ y ∈ N)
    (h : Ω → ℝ) (hpos : ∀ x, 0 ≤ h x)
    (hcap : ∀ x ∈ I, ∀ y ∈ N, Y x y + h y ≤ 1)
    {x y : Ω} (hxy : G x y = true) (hyx : G y x = true) :
    charge G Y I N h x y ≤ 1 := by
  classical
  rw [charge, ite_eq_left hxy]
  by_cases hx : x ∈ I
  · have hyN : y ∈ N := (hrow x hx y).mp hxy
    have hxN : x ∉ N := fun h => Set.disjoint_left.mp hdisjoint hx h
    have hyI : y ∉ I := fun h => Set.disjoint_left.mp hdisjoint h hyN
    simpa [increment, hx, hxN, hyI] using hcap x hx y hyN
  · by_cases hy : y ∈ I
    · have hxN : x ∈ N := (hrow y hy x).mp hyx
      have hyN : y ∉ N := fun h => Set.disjoint_left.mp hdisjoint hy h
      simpa [increment, hx, hy, hyN, hYsym x y] using hcap y hy x hxN
    · have hi : increment I N h x y ≤ 0 := by
        simp only [increment, hx, hy, ↓reduceIte, zero_add, zero_sub]
        split_ifs
        · linarith [hpos x, hpos y]
        · norm_num
      linarith [hY x y]

/-- The signed root edit preserves each original clique inequality. Cliques
without a root only lose charge; two-point cliques use the new pair cap. -/
theorem tupleCharge_le_one {Ω : Type*} {n : ℕ}
    (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hYsym : ∀ x y, Y x y = Y y x) (hY : ∀ x y, Y x y ≤ 1)
    (I N : Set Ω) (hdisjoint : Disjoint I N)
    (hrow : ∀ x ∈ I, ∀ y, G x y = true ↔ y ∈ N)
    (h : Ω → ℝ) (hpos : ∀ x, 0 ≤ h x) (hzero : ∀ x ∉ N, h x = 0)
    (hcap : ∀ x ∈ I, ∀ y ∈ N, Y x y + h y ≤ 1)
    (v : Fin n → Ω) (hv : FiniteArity.TupleClique G v)
    (hold : FiniteArity.tupleCharge Y v ≤ 1) :
    FiniteArity.tupleCharge (charge G Y I N h) v ≤ 1 := by
  classical
  by_cases hn : n ≤ 1
  · rw [FiniteArity.tupleCharge_small hn]
    norm_num
  by_cases htwo : n = 2
  · subst n
    have hp := charge_le_one G Y hYsym hY I N hdisjoint hrow h hpos hcap
      (hv 0 1 (by decide)) (hv 1 0 (by decide))
    have hq := charge_le_one G Y hYsym hY I N hdisjoint hrow h hpos hcap
      (hv 1 0 (by decide)) (hv 0 1 (by decide))
    simp only [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
      Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
      Fin.succ_ne_zero, Fin.zero_ne_one, ↓reduceIte,
      Fin.sum_univ_zero, add_zero, zero_add]
    linarith
  have hthree : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  by_cases hroot : ∃ r, v r ∈ I
  · obtain ⟨r, hr⟩ := hroot
    have hNroot : v r ∉ N := fun h => Set.disjoint_left.mp hdisjoint hr h
    have hNi : ∀ i, v i ∈ N ↔ i ≠ r := by
      intro i
      constructor
      · intro hi hir
        subst i
        exact hNroot hi
      · intro hir
        exact (hrow (v r) hr (v i)).mp (hv r i hir.symm)
    have hIi : ∀ i, v i ∈ I ↔ i = r := by
      intro i
      constructor
      · intro hi
        by_contra hir
        exact Set.disjoint_left.mp hdisjoint hi ((hNi i).mpr hir)
      · rintro rfl
        exact hr
    rw [tupleCharge_eq_of_root G Y I N h v hv r hIi hNi (hzero _ hNroot)]
    have hs : 0 ≤ ∑ i, h (v i) := Finset.sum_nonneg (fun i _ => hpos (v i))
    have hc : (3 - (n : ℝ)) * ∑ i, h (v i) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hs
    linarith
  · push Not at hroot
    apply (tupleCharge_mono (charge G Y I N h) Y v ?_).trans hold
    intro i j hij
    rw [charge, ite_eq_left (hv i j hij)]
    have hi : increment I N h (v i) (v j) ≤ 0 := by
      simp only [increment, hroot i, hroot j, ↓reduceIte, zero_add, zero_sub]
      split_ifs
      · linarith [hpos (v i), hpos (v j)]
      · norm_num
    linarith

/-- Only pairwise facts on the actual tuple are needed. This form permits
one common product-null exception in the physical application. -/
theorem tupleCharge_le_one_of_pairwise {Ω : Type*} {n : ℕ}
    (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I N : Set Ω) (hdisjoint : Disjoint I N)
    (h : Ω → ℝ) (hpos : ∀ x, 0 ≤ h x) (hzero : ∀ x ∉ N, h x = 0)
    (v : Fin n → Ω) (hv : FiniteArity.TupleClique G v)
    (hYsym : ∀ i j, i ≠ j → Y (v i) (v j) = Y (v j) (v i))
    (hY : ∀ i j, i ≠ j → Y (v i) (v j) ≤ 1)
    (hrow : ∀ i j, i ≠ j → v i ∈ I → v j ∈ N)
    (hcap : ∀ i j, i ≠ j → v i ∈ I → Y (v i) (v j) + h (v j) ≤ 1)
    (hold : FiniteArity.tupleCharge Y v ≤ 1) :
    FiniteArity.tupleCharge (charge G Y I N h) v ≤ 1 := by
  classical
  let A : Fin n → Fin n → Bool := fun i j => if i = j then false else G (v i) (v j)
  let Z : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else Y (v i) (v j)
  let R : Set (Fin n) := {i | v i ∈ I}
  let S : Set (Fin n) := {i | v i ∈ N}
  let g : Fin n → ℝ := fun i => h (v i)
  have hRS : Disjoint R S := Set.disjoint_left.mpr (fun i hi hN =>
    Set.disjoint_left.mp hdisjoint hi hN)
  have hZsym : ∀ i j, Z i j = Z j i := by
    intro i j
    by_cases hij : i = j
    · simp [Z, hij]
    · simp only [Z, hij, Ne.symm hij, ↓reduceIte]
      exact hYsym i j hij
  have hZ : ∀ i j, Z i j ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · simp [Z, hij]
    · simpa [Z, hij] using hY i j hij
  have hArow : ∀ i ∈ R, ∀ j, A i j = true ↔ j ∈ S := by
    intro i hi j
    by_cases hij : i = j
    · have hj : j ∉ S := fun hj => Set.disjoint_left.mp hRS (hij ▸ hi) hj
      simp [A, hij, hj]
    · have hj : j ∈ S := hrow i j hij hi
      simp [A, hij, hv i j hij, hj]
  have hZcap : ∀ i ∈ R, ∀ j ∈ S, Z i j + g j ≤ 1 := by
    intro i hi j hj
    have hij : i ≠ j := by
      rintro rfl
      exact Set.disjoint_left.mp hRS hi hj
    simpa [Z, g, hij] using hcap i j hij hi
  have hAid : FiniteArity.TupleClique A id := by
    intro i j hij
    simp [A, hij, hv i j hij]
  have hZold : FiniteArity.tupleCharge Z id = FiniteArity.tupleCharge Y v := by
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [Z, hij]
  have hnew : FiniteArity.tupleCharge (charge A Z R S g) id =
      FiniteArity.tupleCharge (charge G Y I N h) v := by
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · simp [charge, A, Z, R, S, g, increment, hij, hv i j hij]
  rw [← hnew]
  exact tupleCharge_le_one A Z hZsym hZ R S hRS hArow g (fun i => hpos (v i))
    (fun i hi => hzero (v i) hi) hZcap id hAid (hZold ▸ hold)

section PhysicalTests

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem measurable_increment (I N : Set Ω) (hI : MeasurableSet I) (hN : MeasurableSet N)
    (h : Ω → ℝ) (hh : Measurable h) : Measurable (Function.uncurry (increment I N h)) :=
  ((Measurable.ite (hI.preimage measurable_fst) (hh.comp measurable_snd) measurable_const).add
    (Measurable.ite (hI.preimage measurable_snd) (hh.comp measurable_fst) measurable_const)).sub
    (Measurable.ite ((hN.preimage measurable_fst).inter (hN.preimage measurable_snd))
      ((hh.comp measurable_fst).add (hh.comp measurable_snd)) measurable_const)

omit [IsProbabilityMeasure μ] in
theorem measurable_charge (G : Ω → Ω → Bool) (hG : Measurable (Function.uncurry G))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (I N : Set Ω) (hI : MeasurableSet I) (hN : MeasurableSet N)
    (h : Ω → ℝ) (hh : Measurable h) :
    Measurable (Function.uncurry (charge G Y I N h)) :=
  Measurable.ite (hG (measurableSet_singleton true))
    (hY.add (measurable_increment I N hI hN h hh)) measurable_const

theorem integrable_charge (G : Ω → Ω → Bool) (hG : Measurable (Function.uncurry G))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (I N : Set Ω) (hI : MeasurableSet I) (hN : MeasurableSet N)
    (h : Ω → ℝ) (hh : Measurable h) (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hYbound : ∀ x y, ‖Y x y‖ ≤ B) (hhbound : ∀ x, ‖h x‖ ≤ H) :
    Integrable (Function.uncurry (charge G Y I N h)) (μ.prod μ) :=
  Integrable.of_bound (measurable_charge G hG Y hY I N hI hN h hh).aestronglyMeasurable
    (B + 4 * H) (Eventually.of_forall (fun p => norm_charge_le G Y I N h B H hB hH
      hYbound hhbound p.1 p.2))

/-- Every actual product-almost-everywhere clique test survives signed root
repricing. Pair exceptions are transferred at each distinct coordinate. -/
theorem feasibleOrder (G : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I N : Set Ω) (hdisjoint : Disjoint I N)
    (h : Ω → ℝ) (hpos : ∀ x, 0 ≤ h x) (hzero : ∀ x ∉ N, h x = 0)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hY : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 ≤ 1)
    (hrow : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → G p.1 p.2 = true → p.2 ∈ N)
    (hcap : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ I → G p.1 p.2 = true → Y p.1 p.2 + h p.2 ≤ 1)
    (n : ℕ) (hold : FiniteArity.FeasibleOrder μ G Y n) :
    FiniteArity.FeasibleOrder μ G (charge G Y I N h) n := by
  have hpair : ∀ᵐ p ∂μ.prod μ,
      Y p.1 p.2 = Y p.2 p.1 ∧ Y p.1 p.2 ≤ 1 ∧
        (p.1 ∈ I → G p.1 p.2 = true → p.2 ∈ N) ∧
        (p.1 ∈ I → G p.1 p.2 = true → Y p.1 p.2 + h p.2 ≤ 1) := by
    filter_upwards [hYsym, hY, hrow, hcap] with p hs hy hr hc
    exact ⟨hs, hy, hr, hc⟩
  filter_upwards [hold, FiniteArity.ae_all_pairs μ n _ hpair] with v hv hp hc
  apply tupleCharge_le_one_of_pairwise G Y I N hdisjoint h hpos hzero v hc
    (fun i j hij => (hp i j hij).1)
    (fun i j hij => (hp i j hij).2.1)
    (fun i j hij hi => (hp i j hij).2.2.1 hi (hc i j hij))
    (fun i j hij hi => (hp i j hij).2.2.2 hi (hc i j hij))
  exact hv hc

end PhysicalTests

end Erdos1017.SignedRootRepricing

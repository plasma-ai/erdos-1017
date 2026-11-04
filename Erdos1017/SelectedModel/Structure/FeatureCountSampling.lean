module

public import Erdos1017.SelectedModel.Structure.FeatureSupportSampling
public import Erdos1017.Multipartite.Physical.PhysicalLabelCounts
public import Erdos1017.SelectedModel.Structure.ZeroPairCountTransfer

/-!
# Charge of natural count vectors

This module defines `multiplicityCharge`, the charge of natural multiplicities
with the diagonal subtracted once per vertex, and shows it agrees with the
ordered tuple charge and the zero-pair polynomial, so a fixed physical test
proves the count constraint for support types by sampling repeated types inside
clique cells.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.FiniteArity

/-- The charge of actual natural multiplicities, subtracting the physical
coordinate diagonal once per vertex rather than once per feature type. -/
def multiplicityCharge {κ : Type*} [Fintype κ] (K : κ → κ → ℝ) (k : κ → ℕ) : ℝ :=
  ((∑ a, ∑ b, K a b * (k a : ℝ) * (k b : ℝ)) - ∑ a, K a a * (k a : ℝ)) / 2

/-- Every natural count vector with the prescribed total is realized by an
actual ordered label tuple of that length. -/
theorem exists_label_with_counts {κ : Type*} [Fintype κ] [DecidableEq κ]
    (k : κ → ℕ) (n : ℕ) (htotal : ∑ a, k a = n) :
    ∃ label : Fin n → κ, ∀ a, PhysicalPrimal.labelCount label a = k a := by
  classical
  let e : Fin n ≃ (a : κ) × Fin (k a) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma]
    simpa only [Fintype.card_fin] using htotal.symm)
  refine ⟨fun i => (e i).1, ?_⟩
  intro a
  unfold PhysicalPrimal.labelCount
  rw [e.sum_comp (fun p : (a : κ) × Fin (k a) => if p.1 = a then 1 else 0)]
  rw [Fintype.sum_sigma]
  change (∑ x : κ, ∑ _y : Fin (k x), if x = a then (1 : ℕ) else 0) = k a
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp

/-- Distinct physical coordinates carrying one label give multiplicity at
least two, so only genuinely repeated labels need clique-cell sampling. -/
theorem two_le_labelCount_of_eq {κ : Type*} [DecidableEq κ] {n : ℕ}
    (label : Fin n → κ) (i j : Fin n) (hij : i ≠ j) (heq : label i = label j) :
    2 ≤ PhysicalPrimal.labelCount label (label i) := by
  classical
  have hcard : PhysicalPrimal.labelCount label (label i) =
      (Finset.univ.filter (fun a => label a = label i)).card := by
    simp only [PhysicalPrimal.labelCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcard]
  have hsub : ({i, j} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun a => label a = label i) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp
    · have haj := Finset.mem_singleton.mp ha
      simp only [haj, Finset.mem_filter, Finset.mem_univ, true_and]
      exact heq.symm
  have h := Finset.card_le_card hsub
  simpa [hij] using h

/-- The ordinary ordered tuple charge equals the exact natural count
polynomial. This equality makes no symmetry or diagonal-kernel convention. -/
theorem tupleCharge_eq_multiplicityCharge {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (label : Fin n → κ) (K : κ → κ → ℝ) :
    tupleCharge K label = multiplicityCharge K (PhysicalPrimal.labelCount label) := by
  classical
  have hterm (i j : Fin n) : (if i = j then 0 else K (label i) (label j)) =
      K (label i) (label j) - if i = j then K (label i) (label j) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  unfold tupleCharge pairCharge crossSum
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [PhysicalPrimal.sum_pairs_by_label, PhysicalPrimal.sum_by_label label (fun a => K a a)]
  unfold multiplicityCharge
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A fixed physical test proves the natural count constraint for actual
support types. Repeated types are sampled inside their physical clique cells;
single-use types may use the full physical space. -/
theorem multiplicity_test_le_of_feature_support
    {Ω E κ : Type*} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (F : Ω → E) (hF : Measurable F) (J : E →ₗᵢ[ℝ] E) (ℓ : ℝ)
    (C : κ → Set Ω) (hC : ∀ a, MeasurableSet (C a))
    (hstrict : ∀ᵐ p ∂μ.prod μ, 0 < ⟪J (F p.1), F p.2⟫ → A p.1 p.2 = true)
    (hcharge : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = true → Y p.1 p.2 = ⟪J (F p.1), F p.2⟫ - ℓ)
    (n : ℕ) (htest : FeasibleOrder μ A Y n) (k : κ → ℕ) (htotal : ∑ a, k a = n)
    (hclique : ∀ a, 2 ≤ k a → ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ C a → p.2 ∈ C a → A p.1 p.2 = true)
    (w : κ → E)
    (hw : ∀ a, 0 < k a → w a ∈ ((μ.restrict (C a)).map F).support)
    (hpositive : ∀ a b, a ≠ b → 0 < k a → 0 < k b → 0 < ⟪J (w a), w b⟫) :
    multiplicityCharge (fun a b => ⟪J (w a), w b⟫ - ℓ) k ≤ 1 := by
  classical
  obtain ⟨label, hlabel⟩ := exists_label_with_counts k n htotal
  have hcount (i : Fin n) : 0 < k (label i) := by
    rw [← hlabel]
    unfold PhysicalPrimal.labelCount
    exact lt_of_lt_of_le (by simp) (Finset.single_le_sum (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i))
  have h := tuple_test_le_of_feature_support μ A Y F hF J ℓ n label C hC
    (fun i j hij heq => hclique (label i) (by
      rw [← hlabel]
      exact two_le_labelCount_of_eq label i j hij heq))
    hstrict hcharge htest w (fun i => hw (label i) (hcount i))
    (fun i j _ hij => hpositive (label i) (label j) hij (hcount i) (hcount j))
  have ht : tupleCharge (fun x y : E => ⟪J x, y⟫ - ℓ) (fun i => w (label i)) =
      tupleCharge (fun a b => ⟪J (w a), w b⟫ - ℓ) label := rfl
  rw [ht, tupleCharge_eq_multiplicityCharge] at h
  simpa only [show PhysicalPrimal.labelCount label = k from funext hlabel] using h

/-- Fixing the outside types at count one leaves their internal charge
constant and their incidences with repeated types linear in the counts. -/
theorem multiplicityCharge_sum_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι ⊕ κ → ι ⊕ κ → ℝ) (k : κ → ℕ)
    (hsym : ∀ i j, K (Sum.inr j) (Sum.inl i) = K (Sum.inl i) (Sum.inr j)) :
    multiplicityCharge K (Sum.elim (fun _ => 1) k) =
      multiplicityCharge (fun i j => K (Sum.inl i) (Sum.inl j)) (fun _ => 1) +
        (∑ j, (∑ i, K (Sum.inl i) (Sum.inr j)) * (k j : ℝ)) +
          multiplicityCharge (fun i j => K (Sum.inr i) (Sum.inr j)) k := by
  have hcross : (∑ i, ∑ j, K (Sum.inl i) (Sum.inr j) * (k j : ℝ)) =
      ∑ j, (∑ i, K (Sum.inl i) (Sum.inr j)) * (k j : ℝ) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  unfold multiplicityCharge
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Nat.cast_one,
    mul_one, Finset.sum_add_distrib, hsym]
  rw [hcross]
  simp only [Finset.sum_mul]
  ring

/-- Reindexing the types preserves their exact multiplicity charge. -/
theorem multiplicityCharge_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (K : κ → κ → ℝ) (k : κ → ℕ) :
    multiplicityCharge (fun i j => K (e i) (e j)) (fun i => k (e i)) =
      multiplicityCharge K k := by
  have hinner (i : ι) :
      (∑ j, K (e i) (e j) * (k (e i) : ℝ) * (k (e j) : ℝ)) =
        ∑ b, K (e i) b * (k (e i) : ℝ) * (k b : ℝ) :=
    e.sum_comp (fun b => K (e i) b * (k (e i) : ℝ) * (k b : ℝ))
  unfold multiplicityCharge
  simp_rw [hinner]
  rw [e.sum_comp (fun a => ∑ b, K a b * (k a : ℝ) * (k b : ℝ)),
    e.sum_comp (fun a => K a a * (k a : ℝ))]

private theorem symmetric_sum_eq_diagonal_add_twice_upper {n : ℕ}
    (B : Fin n → Fin n → ℝ) (hB : ∀ i j, B i j = B j i) :
    (∑ i, ∑ j, B i j) = (∑ i, B i i) + 2 * ∑ i, ∑ j, if i < j then B i j else 0 := by
  have hterm (i j : Fin n) : B i j = (if i = j then B i i else 0) +
      (if i < j then B i j else 0) + (if j < i then B j i else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, ne_of_lt hij, not_lt_of_ge hij.le]
    · subst j
      simp
    · simp [hij, (ne_of_lt hij).symm, not_lt_of_ge hij.le, hB i j]
  have hsum : (∑ i, ∑ j, B i j) =
      ∑ i, ∑ j, ((if i = j then B i i else 0) +
        (if i < j then B i j else 0) + (if j < i then B j i else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hterm i j
  rw [hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then B j i else 0)]
  ring

/-- The zero-pair polynomial is exactly the charge of a repeated ordered
tuple, including its actual self-pair multiplicities. -/
theorem countCharge_eq_multiplicityCharge {n : ℕ} (h ℓ : ℝ) (x : Fin n → ℝ)
    (M : Fin n → Fin n → ℝ) (hsym : ∀ i j, M i j = M j i) (k : Fin n → ℕ) :
    ZeroPairCount.countCharge h ℓ x (fun i => M i i) M k =
      h + (∑ i, x i * (k i : ℝ)) + multiplicityCharge (fun i j => M i j - ℓ) k := by
  let B : Fin n → Fin n → ℝ := fun i j => (M i j - ℓ) * (k i : ℝ) * (k j : ℝ)
  have hB : ∀ i j, B i j = B j i := by
    intro i j
    dsimp only [B]
    rw [hsym i j]
    ring
  have hsum := symmetric_sum_eq_diagonal_add_twice_upper B hB
  have hdiag : (∑ i, (M i i - ℓ) * Repeat.pairs (k i)) =
      ((∑ i, B i i) - ∑ i, (M i i - ℓ) * (k i : ℝ)) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [B, Repeat.pairs]
    ring
  unfold ZeroPairCount.countCharge multiplicityCharge
  rw [hdiag]
  change h + (∑ i, x i * (k i : ℝ)) +
      ((∑ i, B i i) - ∑ i, (M i i - ℓ) * (k i : ℝ)) / 2 +
        (∑ i, ∑ j, if i < j then B i j else 0) =
      h + (∑ i, x i * (k i : ℝ)) +
        ((∑ i, ∑ j, B i j) - ∑ i, (M i i - ℓ) * (k i : ℝ)) / 2
  rw [hsum]
  ring

/-- Count one on every original type recovers its ordinary physical tuple
charge, with no convention on values of the kernel at equal feature types. -/
theorem tupleCharge_eq_multiplicityCharge_one {κ : Type*} {n : ℕ}
    (K : κ → κ → ℝ) (v : Fin n → κ) :
    tupleCharge K v = multiplicityCharge (fun i j => K (v i) (v j)) (fun _ => 1) := by
  have h := tupleCharge_eq_multiplicityCharge (fun i : Fin n => i)
    (fun i j => K (v i) (v j))
  have hid : PhysicalPrimal.labelCount (fun i : Fin n => i) = fun _ => 1 := by
    funext i
    simp [PhysicalPrimal.labelCount]
  rw [hid] at h
  exact h

end Erdos1017.FiniteArity

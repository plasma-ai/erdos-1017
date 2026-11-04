module

public import Erdos1017.SelectedModel.Flows.CompletedAtomicRelationFlow

/-!
# Column integrals over atoms

Projecting a column onto an original atom recovers its restricted source
fraction, extended by zero to the original law, and projecting onto a finite
union of atoms gives the finite sum of the restricted assignment fractions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.MissingFlow.CompletedAtomicRelation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {H : Set Ω} {Z : Set (Ω × Ω)} {I : ℕ → Set Ω}
  {q : ℕ → Lp ℝ 2 (μ.restrict H)}

/-- Projection onto an original atom recovers its actual restricted source
fraction, extended by zero to the original source law. -/
theorem setIntegral_column_on_atom (hH : MeasurableSet H)
    (hI : ∀ i, MeasurableSet (I i))
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q)
    (hdisjoint : Pairwise (fun j k => Disjoint (I j) (I k))) (i : ℕ) :
    (fun x => ∫ y in I i, density μ H Z I q (y, x) ∂μ) =ᵐ[μ]
      H.indicator (fun x => q i x) := by
  have hrow (x y : Ω) (hy : y ∈ I i) :
      density μ H Z I q (y, x) =
        (μ.real (I i))⁻¹ * RestrictedAtomicAssignment.liftFraction H q i x := by
    have hterm (j : ℕ) (hji : j ≠ i) :
        AtomicAssignment.recipientDensity μ (I j) y *
          RestrictedAtomicAssignment.liftFraction H q j x = 0 := by
      have hyj : y ∉ I j := fun hyj => Set.disjoint_left.mp (hdisjoint hji) hyj hy
      simp only [AtomicAssignment.recipientDensity, indicator_of_notMem hyj, zero_mul]
    have hd : (y, x) ∉ diffuseRelation Z I :=
      fun hp => hp.2.1 (mem_iUnion.mpr ⟨i, hy⟩)
    change (∑' j, AtomicAssignment.recipientDensity μ (I j) y *
      RestrictedAtomicAssignment.liftFraction H q j x) +
        normalizedDensity μ (diffuseRelation Z I) (y, x) = _
    rw [normalizedDensity_eq_zero_of_notMem _ _ hd, add_zero, tsum_eq_single i hterm]
    simp only [AtomicAssignment.recipientDensity, indicator_of_mem hy]
  have hcolumn (x : Ω) :
      (∫ y in I i, density μ H Z I q (y, x) ∂μ) =
        μ.real (I i) * ((μ.real (I i))⁻¹ *
          RestrictedAtomicAssignment.liftFraction H q i x) := by
    rw [setIntegral_congr_fun (hI i) (hrow x), setIntegral_const, smul_eq_mul]
  by_cases hi : μ (I i) = 0
  · have hzero : (q i : Ω → ℝ) =ᵐ[μ.restrict H] 0 := by
      filter_upwards [hq.support i] with x hx
      apply hx
      have hle : NormalizedAtomicFractions.atomSectionMass μ Z I i x ≤ μ.real (I i) :=
        measureReal_mono inter_subset_left
      have hm : μ.real (I i) = 0 := by simp only [measureReal_def, hi, ENNReal.toReal_zero]
      exact not_lt_of_ge (hm ▸ hle)
    have hlift := indicator_ae_eq_zero_of_restrict_ae_eq_zero hH hzero
    filter_upwards [hlift] with x hx
    rw [hcolumn]
    simp only [measureReal_def, hi, ENNReal.toReal_zero, zero_mul, hx, Pi.zero_apply]
  · have hm : μ.real (I i) ≠ 0 :=
      ne_of_gt (ENNReal.toReal_pos hi (measure_ne_top μ (I i)))
    exact Eventually.of_forall (fun x => by
      change (∫ y in I i, density μ H Z I q (y, x) ∂μ) =
        H.indicator (fun x => q i x) x
      rw [hcolumn, ← mul_assoc, mul_inv_cancel₀ hm, one_mul]
      rfl)

/-- Projection onto a finite union of original atoms is the corresponding
finite sum of actual restricted assignment fractions on the original law. -/
theorem setIntegral_column_on_finset (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (hI : ∀ i, MeasurableSet (I i))
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q)
    (hdisjoint : Pairwise (fun j k => Disjoint (I j) (I k))) (P : Finset ℕ) :
    (fun x => ∫ y in ⋃ i ∈ P, I i, density μ H Z I q (y, x) ∂μ) =ᵐ[μ]
      H.indicator (fun x => ∑ i ∈ P, q i x) := by
  have hcolumns : ∀ᵐ x ∂μ, ∀ i,
      (∫ y in I i, density μ H Z I q (y, x) ∂μ) =
        H.indicator (fun x => q i x) x :=
    ae_all_iff.mpr (setIntegral_column_on_atom hH hI hq hdisjoint)
  filter_upwards [hcolumns, (integrable_nonnegative hZ hH hI hq).1.prod_left_ae]
    with x hx hcolumn
  rw [integral_biUnion_finset P (fun i _ => hI i)
    (fun i _ j _ hij => hdisjoint hij) (fun _ _ => hcolumn.integrableOn)]
  simp_rw [hx]
  by_cases hxH : x ∈ H
  · simp only [indicator_of_mem hxH]
  · simp only [indicator_of_notMem hxH, Finset.sum_const_zero]

end Erdos1017.MissingFlow.CompletedAtomicRelation

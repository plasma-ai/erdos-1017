module

public import Erdos1017.Multipartite.Physical.PhysicalPrimalAssembly
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Symmetrizing joint tuple laws

Averaging all coordinate orders of a joint law (`symmetrize`) is invariant under
every coordinate permutation and preserves mass, full ordered balance,
permutation-stable support properties and joint product absolute continuity.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- Relabel the coordinates of an actual joint tuple law. -/
def permuteTuple {k : ℕ} (σ : Equiv.Perm (Fin k)) (v : Fin k → V) : Fin k → V :=
  fun i => v (σ i)

theorem permuteTuple_measurable {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Measurable (permuteTuple (V := V) σ) :=
  Measurable.of_eval (fun i => measurable_pi_apply (σ i))

private def permutePair {k : ℕ} (σ : Equiv.Perm (Fin k)) : PairIndex k ≃ PairIndex k where
  toFun ij := ⟨(σ ij.val.1, σ ij.val.2), fun h => ij.property (σ.injective h)⟩
  invFun ij := ⟨(σ.symm ij.val.1, σ.symm ij.val.2), fun h => ij.property (σ.symm.injective h)⟩
  left_inv ij := by apply Subtype.ext; simp
  right_inv ij := by apply Subtype.ext; simp

/-- Relabeling a parent retains its entire ordered pair occupation. -/
theorem orderOccupation_permute {k : ℕ} (σ : Equiv.Perm (Fin k))
    (ρ : Measure (Fin k → V)) :
    orderOccupation k (ρ.map (permuteTuple σ)) = orderOccupation k ρ := by
  classical
  unfold orderOccupation
  simp_rw [Measure.map_map ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
    (permuteTuple_measurable σ)]
  exact Fintype.sum_equiv (permutePair σ) _ _ (fun _ => rfl)

theorem orderOccupation_smul (k : ℕ) (c : ℝ≥0∞) (ρ : Measure (Fin k → V)) :
    orderOccupation k (c • ρ) = c • orderOccupation k ρ := by
  unfold orderOccupation
  simp_rw [Measure.map_smul _
    (((measurable_pi_apply _).prodMk (measurable_pi_apply _)).aemeasurable)]
  exact Finset.smul_sum.symm

/-- Average all coordinate orders of one genuine joint law. -/
def symmetrize (k : ℕ) (ρ : Measure (Fin k → V)) : Measure (Fin k → V) :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℝ≥0∞)⁻¹ •
    ∑ σ : Equiv.Perm (Fin k), ρ.map (permuteTuple σ)

private theorem perm_card_ne_zero (k : ℕ) :
    (Fintype.card (Equiv.Perm (Fin k)) : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- The finite symmetrization is invariant under every coordinate permutation. -/
theorem symmetrize_invariant (k : ℕ) (ρ : Measure (Fin k → V))
    (τ : Equiv.Perm (Fin k)) :
    (symmetrize k ρ).map (permuteTuple τ) = symmetrize k ρ := by
  classical
  unfold symmetrize
  rw [Measure.map_smul _ (permuteTuple_measurable τ).aemeasurable,
    Measure.map_finset_sum (permuteTuple_measurable τ).aemeasurable]
  simp_rw [Measure.map_map (permuteTuple_measurable τ) (permuteTuple_measurable _)]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun _ => rfl)

/-- Symmetrization preserves the mass of every finite or infinite parent law. -/
theorem symmetrize_univ (k : ℕ) (ρ : Measure (Fin k → V)) :
    symmetrize k ρ Set.univ = ρ Set.univ := by
  classical
  simp only [symmetrize, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.map_apply (permuteTuple_measurable _) MeasurableSet.univ,
    Set.preimage_univ, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (perm_card_ne_zero k) (by finiteness), one_mul]

instance symmetrize_finite (k : ℕ) (ρ : Measure (Fin k → V)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (symmetrize k ρ) :=
  ⟨by rw [symmetrize_univ]; exact measure_lt_top _ _⟩

@[simp] theorem symmetrize_zero (k : ℕ) : symmetrize k (0 : Measure (Fin k → V)) = 0 := by
  simp [symmetrize]

/-- Full ordered balance is unchanged by coordinate symmetrization. -/
theorem orderOccupation_symmetrize (k : ℕ) (ρ : Measure (Fin k → V)) :
    orderOccupation k (symmetrize k ρ) = orderOccupation k ρ := by
  classical
  rw [symmetrize, orderOccupation_smul, orderOccupation_finsetSum]
  simp_rw [orderOccupation_permute]
  have hsum : (∑ _ : Equiv.Perm (Fin k), orderOccupation k ρ) =
      (Fintype.card (Equiv.Perm (Fin k)) : ℝ≥0∞) • orderOccupation k ρ := by
    ext s hs
    simp [Measure.smul_apply]
  rw [hsum, smul_smul,
    ENNReal.inv_mul_cancel (perm_card_ne_zero k) (by finiteness), one_smul]

/-- Averaging coordinate orders preserves every permutation-stable support property. -/
theorem ae_symmetrize (k : ℕ) (ρ : Measure (Fin k → V)) (P : (Fin k → V) → Prop)
    (hPm : MeasurableSet {v | P v})
    (hP : ∀ᵐ v ∂ρ, P v) (hperm : ∀ v σ, P v → P (permuteTuple σ v)) :
    ∀ᵐ v ∂symmetrize k ρ, P v := by
  apply Measure.ae_smul_measure
  rw [← Measure.sum_fintype, Measure.ae_sum_iff]
  intro σ
  apply (ae_map_iff (permuteTuple_measurable σ).aemeasurable hPm).mpr
  exact hP.mono (fun v hv => hperm v σ hv)

/-- Joint product absolute continuity is retained before taking a weak limit. -/
theorem symmetrize_absolutelyContinuous (μ : Measure V) [IsProbabilityMeasure μ]
    (k : ℕ) (ρ : Measure (Fin k → V))
    (hρ : ρ ≪ Measure.pi (fun _ : Fin k => μ)) :
    symmetrize k ρ ≪ Measure.pi (fun _ : Fin k => μ) := by
  apply Measure.AbsolutelyContinuous.smul_left
  rw [← Measure.sum_fintype]
  apply Measure.absolutelyContinuous_sum_left
  intro σ
  have h := hρ.map (permuteTuple_measurable σ)
  have heq := (FiniteArity.measurePreserving_subtuple μ σ.toEmbedding).map_eq
  change (Measure.pi (fun _ : Fin k => μ)).map (permuteTuple σ) = _ at heq
  rwa [heq] at h

end Erdos1017.PhysicalPrimal

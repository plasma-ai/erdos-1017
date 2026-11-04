module

public import Erdos1017.Models.Decorated.DecoratedKernel

/-!
# Absolute continuity of finite product measures

Coordinatewise absolute continuity passes to finite heterogeneous products of
probability measures (`pi_fin_absolutelyContinuous`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.DecoratedKernel

variable {C : Type*} [MeasurableSpace C]

/-- Coordinatewise absolute continuity passes to finite heterogeneous
products of probability measures. -/
theorem pi_fin_absolutelyContinuous (n : ℕ) :
    ∀ (ρ σ : Fin n → Measure C) [∀ i, IsProbabilityMeasure (ρ i)]
      [∀ i, IsProbabilityMeasure (σ i)],
      (∀ i, ρ i ≪ σ i) → Measure.pi ρ ≪ Measure.pi σ := by
  induction n with
  | zero =>
    intro ρ σ _ _ _
    rw [Measure.pi_of_empty _ (fun i : Fin 0 => Fin.elim0 i),
      Measure.pi_of_empty _ (fun i : Fin 0 => Fin.elim0 i)]
  | succ n ih =>
    intro ρ σ _ _ hac
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => C) 0).symm
    have hprod := (hac 0).prod (ih (fun i => ρ i.succ) (fun i => σ i.succ) (fun i => hac i.succ))
    have h := hprod.map e.measurable
    have hρ := (measurePreserving_piFinSuccAbove ρ 0).symm
    have hσ := (measurePreserving_piFinSuccAbove σ 0).symm
    rw [← hρ.map_eq, ← hσ.map_eq]
    exact h

theorem pi_absolutelyContinuous_of_coordinates {ι : Type*} [Fintype ι]
    (ρ σ : ι → Measure C) [∀ i, IsProbabilityMeasure (ρ i)] [∀ i, IsProbabilityMeasure (σ i)]
    (hac : ∀ i, ρ i ≪ σ i) : Measure.pi ρ ≪ Measure.pi σ := by
  let e := (Fintype.equivFin ι).symm
  have h := (pi_fin_absolutelyContinuous (Fintype.card ι)
    (fun i => ρ (e i)) (fun i => σ (e i)) (fun i => hac (e i))).map
      (MeasurableEquiv.piCongrLeft (fun _ : ι => C) e).measurable
  rw [(measurePreserving_piCongrLeft ρ e).map_eq,
    (measurePreserving_piCongrLeft σ e).map_eq] at h
  exact h

end Erdos1017.DecoratedKernel

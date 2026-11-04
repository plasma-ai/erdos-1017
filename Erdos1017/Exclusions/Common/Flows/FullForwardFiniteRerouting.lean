module

public import Erdos1017.Exclusions.Common.Flows.FiniteFlowRedirection
public import Erdos1017.Exclusions.Common.Flows.DiffuseFlowEndpointRemainder

/-!
# Finite rerouting of a full forward flow

Finitely many missing rectangles with disjoint sources give one full forward
flow, with atomic recipients allowed to coincide, and an avoided whole-row fiber
stays avoided when every recipient set is disjoint from it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Finitely many actual missing rectangles give one full forward flow.
Sources are disjoint; atomic recipients may coincide. -/
theorem finiteRedirect (hq : S.IsFullForwardFlow q) {n : ℕ}
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (hpos : ∀ i, 0 < μ.real (C i))
    (hdis : Pairwise (Disjoint on P)) (θ : Fin n → ℝ)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hPL : ∀ i, ∀ᵐ y ∂μ, y ∈ P i → y ∈ S.L)
    (hrect : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C i → p.2 ∈ P i →
      p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L) :
    S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ) :=
  ⟨MissingFlow.integrable_finiteRedirect q hq.integrable C P hC hP θ,
    MissingFlow.finiteRedirect_nonnegative q hq.nonnegative C P θ hdis hθ,
    MissingFlow.supply_finiteRedirect_eq_indicator q hq.integrable C P hC hP hpos θ
      hdis S.L hPL hq.supply,
    MissingFlow.support_finiteRedirect q C P θ _ hq.support hrect⟩

/-- An old avoided whole-row fiber remains avoided when every actual
recipient set is disjoint from that fiber. -/
theorem finiteRedirect_avoids (_hq : S.IsFullForwardFlow q) {n : ℕ}
    (C P : Fin n → Set Ω) (θ : Fin n → ℝ) (i : S.I)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i)
    (hC : ∀ j, Disjoint (C j) {x | S.ρ x = i}) :
    ∀ᵐ p ∂μ.prod μ, MissingFlow.finiteRedirect μ q C P θ p ≠ 0 → S.ρ p.1 ≠ i := by
  apply MissingFlow.support_finiteRedirect q C P θ {p | S.ρ p.1 ≠ i} havoid
  intro j
  exact Eventually.of_forall (fun p hx _ heq => Set.disjoint_left.mp (hC j) hx heq)

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

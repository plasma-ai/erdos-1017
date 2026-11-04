module

public import Erdos1017.Exclusions.Common.SelectedLowAtomReceivers
public import Erdos1017.Exclusions.Common.Flows.FiniteSmallFlowRecipientSets

/-!
# Small simultaneous receivers for low atoms

Receiver labels are chosen once and then arbitrarily small simultaneous
receivers are constructed, where atomic receiver subsets may share a label.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Choose actual receiver labels once, then construct arbitrarily small
simultaneous receivers. Atomic receiver subsets may have the same original
label, but all selected subsets are disjoint in the original atomless law. -/
theorem exists_small_finite_low_receivers (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (i : S.I) {n : ℕ}
    (j : Fin n → S.I)
    (hjL : ∀ a, ∀ᵐ x ∂μ.restrict {x | S.ρ x = j a}, x ∈ S.L)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    ∃ κ : Fin n → Option S.I, ∀ ε > 0, ∃ C : Fin n → Set Ω,
      (∀ a, MeasurableSet (C a)) ∧ (∀ a, 0 < μ.real (C a)) ∧
      Pairwise (Disjoint on C) ∧
      (∀ a, μ.real (C a) + (∫ x in C a, MissingFlow.receipt μ q x ∂μ) < ε) ∧
      (∀ a, C a ⊆ S.H) ∧ (∀ a, Disjoint (C a) {x | S.ρ x = i}) ∧
      (∀ a, κ a = none → C a ⊆ S.D) ∧
      (∀ a k, κ a = some k → k ≠ i ∧ C a ⊆ {x | S.ρ x = k} ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H)) ∧
      (∀ a, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C a → S.ρ p.2 = j a →
        p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L) := by
  choose B hB hBp hBH hBi hkind hrect using
    (fun a => hq.exists_low_atom_receiver hW i (j a) (hjL a) havoid)
  have hlabel (a : Fin n) : ∃ k : Option S.I,
      (k = none → B a ⊆ S.D) ∧
      (∀ r, k = some r → r ≠ i ∧ B a ⊆ {x | S.ρ x = r} ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = r}, x ∈ S.H)) := by
    rcases hkind a with ⟨k, hki, hBk, hkH⟩ | hBD
    · refine ⟨some k, ?_, ?_⟩
      · intro h
        cases h
      · intro r hr
        have he : k = r := Option.some.inj hr
        subst r
        exact ⟨hki, hBk, hkH⟩
    · refine ⟨none, fun _ => hBD, ?_⟩
      intro r hr
      cases hr
  choose κ hκD hκI using hlabel
  refine ⟨κ, ?_⟩
  intro ε hε
  obtain ⟨C, hCB, hC, hCp, hdis, hsmall⟩ :=
    exists_disjoint_positive_small_flow_recipients q hq.integrable n B hB hBp ε hε
  refine ⟨C, hC, hCp, hdis, hsmall, (fun a => (hCB a).trans (hBH a)),
    (fun a => (hBi a).mono_left (hCB a)), ?_, ?_, ?_⟩
  · intro a ha
    exact (hCB a).trans (hκD a ha)
  · intro a k hk
    obtain ⟨hki, hBk, hkH⟩ := hκI a k hk
    exact ⟨hki, (hCB a).trans hBk, hkH⟩
  · intro a
    exact (hrect a).mono (fun _ hp hx hy => hp (hCB a hx) hy)

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

module

public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentCompactness

/-!
# Feasibility is invariant under almost-everywhere changes

A fixed `L²` assignment has the same feasibility when each allowed set and the
diffuse zero set agree almost everywhere (`feasible_congr`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.ReverseAssignment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem feasible_of_congr {allowed allowed' : ℕ → Set Ω} {δ δ' : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ}
    (hallowed : ∀ i, ∀ᵐ x ∂μ, x ∈ allowed i ↔ x ∈ allowed' i)
    (hδ : ∀ᵐ x ∂μ, δ x = 0 ↔ δ' x = 0) (hq : Feasible allowed δ q) :
    Feasible allowed' δ' q := by
  have hcommon : ∀ᵐ x ∂μ, ∀ i, x ∈ allowed i ↔ x ∈ allowed' i :=
    ae_all_iff.mpr hallowed
  have hpattern (J : Finset ℕ) :
      finitePattern allowed δ J =ᵐ[μ] finitePattern allowed' δ' J := by
    filter_upwards [hcommon, hδ] with x hx hδx
    apply propext
    constructor
    · rintro ⟨hz, hJ⟩
      exact ⟨hδx.mp hz, fun i => (hJ i).trans (hx i)⟩
    · rintro ⟨hz, hJ⟩
      exact ⟨hδx.mpr hz, fun i => (hJ i).trans (hx i).symm⟩
  refine ⟨hq.box, ?_, hq.partial_sum, ?_⟩
  · intro i
    filter_upwards [hq.support i, hallowed i] with x hs hx hnot
    exact hs (fun hi => hnot (hx.mp hi))
  · intro J
    rw [← Measure.restrict_congr_set (hpattern J)]
    exact hq.full_pattern J

/-- A fixed actual L² assignment has the same feasibility when each allowed
set and the diffuse zero set agree almost everywhere. -/
theorem feasible_congr {allowed allowed' : ℕ → Set Ω} {δ δ' : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ}
    (hallowed : ∀ i, ∀ᵐ x ∂μ, x ∈ allowed i ↔ x ∈ allowed' i)
    (hδ : ∀ᵐ x ∂μ, δ x = 0 ↔ δ' x = 0) :
    Feasible allowed δ q ↔ Feasible allowed' δ' q :=
  ⟨feasible_of_congr hallowed hδ,
    feasible_of_congr (fun i => (hallowed i).mono (fun _ hx => hx.symm))
      (hδ.mono (fun _ hx => hx.symm))⟩

end Erdos1017.ReverseAssignment

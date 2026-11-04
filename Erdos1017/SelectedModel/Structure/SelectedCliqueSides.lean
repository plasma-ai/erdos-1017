module

public import Erdos1017.SelectedModel.Structure.SelectedZeroBipartition
public import Erdos1017.SelectedModel.PhysicalPrimal.IndependentRowRemainder
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.SelectedModel.FullDiffuseCompletion

/-!
# Two clique sides outside the independent rows

Removing exactly the whole independent row fibers of the selected model leaves
two physical clique sides, cut by the same row map, and the diffuse-completion
theorem makes the whole remainder a clique in the original model.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Removing exactly the whole independent row fibers leaves two physical
clique sides of the original model. The same actual row map is used for
the cut, the positive fiber family and the remainder construction. -/
theorem FullStationaryClass.exists_independent_rows_two_clique_sides
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    ∃ (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D : Set Ω) (C : Bool → Set Ω),
      StronglyMeasurable ρ ∧
      (∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x) ∧ I.Countable ∧
      (∀ r ∈ I, MeasurableSet {x | ρ x = r} ∧ 0 < μ {x | ρ x = r} ∧
        (∀ᵐ p ∂(μ.restrict {x | ρ x = r}).prod (μ.restrict {x | ρ x = r}),
          adjacencyKernel W p.1 p.2 = 0) ∧
        KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
          (adjacencyKernel W) (chargeKernel W) 4 m ρ r) ∧
      I.Pairwise (fun r t => Disjoint {x | ρ x = r} {x | ρ x = t}) ∧
      D = (⋃ r ∈ I, {x | ρ x = r})ᶜ ∧ MeasurableSet D ∧
      (∀ b, MeasurableSet (C b)) ∧
      (∀ x ∈ D, x ∈ C false ∨ x ∈ C true) ∧
      ∀ b, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C b → p.2 ∈ C b →
        PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
  classical
  obtain ⟨ρ, B, hρ, hrow, hB, hcross⟩ := hW.exists_zero_relation_bipartition hd hgap hmax
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  let A := KernelOperator.positiveFiberValues μ ρ
  have hA : A.Countable := KernelOperator.positiveFiberValues_countable ρ hρ.measurable
  have hexhaust : ∀ᵐ p ∂μ.prod μ,
      (shiftedKernel W m p.1 =ᵐ[μ] shiftedKernel W m p.2) ↔
        ∃ r ∈ A, ρ p.1 = r ∧ ρ p.2 = r := by
    filter_upwards [KernelOperator.ae_rowMap_eq_iff (shiftedKernel W m) ρ hrow,
      KernelOperator.ae_equal_features_mem_positiveFiberValues ρ hρ.measurable] with p hp hpositive
    constructor
    · intro heq
      have hρeq := hp.mpr heq
      exact ⟨ρ p.1, hpositive hρeq, rfl, hρeq.symm⟩
    · rintro ⟨r, _, hx, hy⟩
      exact hp.mp (hx.trans hy.symm)
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hY : ∀ᵐ p ∂μ.prod μ, chargeKernel W p.1 p.2 =
      shiftedKernel W m p.1 p.2 + m * adjacencyKernel W p.1 p.2 := by
    filter_upwards with p
    change W.moment CappedColor.charge p =
      shiftedMoment W m p + m * W.moment CappedColor.adjacency p
    rw [shiftedMoment_eq]
    ring
  have hstructure := hW.strict_gap_structure hd hgap
  have hdata (r : Lp ℝ 2 μ) (hr : r ∈ A) :
      KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
        (adjacencyKernel W) (chargeKernel W) 4 m ρ r :=
    KernelOperator.positive_row_fiber_structure (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) ρ hρ hrow r hr
      (shiftedKernel_measurable W m) hsym 4 m hW.moment_mem hstructure.strict_support hY
  obtain ⟨I, D, _, hI, hfibers, hdisjoint, hDeq, hD, hneD, _⟩ :=
    KernelOperator.exists_independent_row_remainder (shiftedKernel W m)
      (adjacencyKernel W) (chargeKernel W) 4 m ρ hρ hrow A hA
      (fun _ hr => hr) hexhaust hdata
  let C : Bool → Set Ω := fun b => D ∩ if b then Bᶜ else B
  have hC (b : Bool) : MeasurableSet (C b) := by
    cases b
    · exact hD.inter hB
    · exact hD.inter hB.compl
  refine ⟨ρ, I, D, C, hρ, hrow, hI, hfibers, hdisjoint, hDeq, hD, hC, ?_, ?_⟩
  · intro x hx
    by_cases hxb : x ∈ B
    · exact Or.inl ⟨hx, hxb⟩
    · exact Or.inr ⟨hx, hxb⟩
  · intro b
    filter_upwards [hcross, hneD, hW.moment_mem,
      PhysicalRepresentative.adjacency_ae_eq W m] with p hp hne hm hadj hx hy
    have hzero : shiftedKernel W m p.1 p.2 ≠ 0 := by
      intro hz
      have hcrossing := hp hz (hne hz hx.1 hy.1)
      cases b
      · exact hcrossing.elim (fun h => h.2 hy.2) (fun h => h.2 hx.2)
      · exact hcrossing.elim (fun h => hx.2 h.1) (fun h => hy.2 h.1)
    have hpos : 0 < shiftedMoment W m p := lt_of_le_of_ne hm.1 hzero.symm
    rw [hadj]
    simp only [positiveAdjacency, hpos, ↓reduceIte]

/-- The actual diffuse-completion theorem makes this same measurable
remainder a clique in the original model, retaining every whole independent
fiber and its original row-homogeneity payload. -/
theorem FullStationaryClass.exists_independent_rows_complete_remainder
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    ∃ (ρ : Ω → Lp ℝ 2 μ) (I : Set (Lp ℝ 2 μ)) (D : Set Ω),
      StronglyMeasurable ρ ∧
      (∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x) ∧ I.Countable ∧
      (∀ r ∈ I, MeasurableSet {x | ρ x = r} ∧ 0 < μ {x | ρ x = r} ∧
        (∀ᵐ p ∂(μ.restrict {x | ρ x = r}).prod (μ.restrict {x | ρ x = r}),
          adjacencyKernel W p.1 p.2 = 0) ∧
        KernelOperator.WholeRowFiberData μ (shiftedKernel W m)
          (adjacencyKernel W) (chargeKernel W) 4 m ρ r) ∧
      I.Pairwise (fun r t => Disjoint {x | ρ x = r} {x | ρ x = t}) ∧
      D = (⋃ r ∈ I, {x | ρ x = r})ᶜ ∧ MeasurableSet D ∧
      ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → W.moment CappedColor.adjacency p = 1 := by
  obtain ⟨ρ, I, D, C, hρ, hrow, hI, hfibers, hdisjoint, hDeq, hD, hC, hcover, hclique⟩ :=
    hW.exists_independent_rows_two_clique_sides hd hgap hmax
  refine ⟨ρ, I, D, hρ, hrow, hI, hfibers, hdisjoint, hDeq, hD, ?_⟩
  exact hW.ae_complete_diffuse_of_two_clique_cover hd hgap D hD C hC
    (Filter.Eventually.of_forall hcover) hclique

end Erdos1017.CappedModel

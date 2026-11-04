module

public import Erdos1017.SelectedModel.SelectedMiddleExclusion
public import Erdos1017.SelectedModel.Structure.OrderedZeroBipartition

/-!
# Zero-relation bipartition of the selected model

The selected model has a measurable cut crossed by almost every zero pair with
distinct whole shifted rows, constructed from the canonical geometry
(`exists_zero_relation_bipartition`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual selected model has a measurable cut crossed by almost
every zero pair with distinct whole shifted rows. Canonical geometry
constructs the cut; the conclusion is for the original raw kernel. -/
theorem FullStationaryClass.exists_zero_relation_bipartition
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    ∃ (ρ : Ω → Lp ℝ 2 μ) (B : Set Ω), StronglyMeasurable ρ ∧
      (∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x) ∧ MeasurableSet B ∧
      ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = 0 → ρ p.1 ≠ ρ p.2 →
        (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B) := by
  classical
  obtain ⟨σ, _, ι, hcount, φ, V, ρ, S, hfeature, hρ, hS, hSae,
    hgeometry, hrowS, hcoords, hnone⟩ := hW.exists_canonical_middle_exclusion hd hgap hmax
  have : Countable ι := hcount
  let ν := 2 * (c - m * d)
  let Z : Set (Ω × Ω) := (S ×ˢ S) ∩
    {p | KernelOperator.canonicalPairing ν σ φ V p.1 p.2 = 0}
  have hφ := hfeature.scalar_measurable
  have hV := hfeature.feature_measurable
  have hhat : StronglyMeasurable (fun p : Ω × Ω =>
      KernelOperator.canonicalPairing ν σ φ V p.1 p.2) := by
    unfold KernelOperator.canonicalPairing
    fun_prop
  have hZ : MeasurableSet Z := (hS.prod hS).inter
    (measurableSet_eq_fun hhat.measurable measurable_const)
  have hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z := by
    filter_upwards with p
    have heq : KernelOperator.canonicalPairing ν σ φ V p.2 p.1 =
        KernelOperator.canonicalPairing ν σ φ V p.1 p.2 := by
      unfold KernelOperator.canonicalPairing
      rw [real_inner_comm (V p.1) (V p.2)]
      ring
    change ((p.1 ∈ S ∧ p.2 ∈ S) ∧
      KernelOperator.canonicalPairing ν σ φ V p.1 p.2 = 0) ↔
      ((p.2 ∈ S ∧ p.1 ∈ S) ∧
        KernelOperator.canonicalPairing ν σ φ V p.2 p.1 = 0)
    rw [heq]
    tauto
  have hnoMiddle : ∀ᵐ y ∂μ,
      OrderedZeroRelation.leftNeighborMass μ Z φ y = 0 ∨
        OrderedZeroRelation.rightNeighborMass μ Z φ y = 0 := by
    filter_upwards [hSae, hnone] with y hy hn
    have hleft : {x | (x, y) ∈ Z ∧ φ x < φ y} =
        {x | x ∈ S ∧ φ x < φ y ∧
          KernelOperator.canonicalPairing ν σ φ V x y = 0} := by
      ext x
      simp only [Z, Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq, hy, and_true]
      tauto
    have hright : {z | (y, z) ∈ Z ∧ φ y < φ z} =
        {z | z ∈ S ∧ φ y < φ z ∧
          KernelOperator.canonicalPairing ν σ φ V y z = 0} := by
      ext z
      simp only [Z, Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq, hy, true_and]
      tauto
    simpa only [OrderedZeroRelation.leftNeighborMass, OrderedZeroRelation.rightNeighborMass,
      hleft, hright] using hn
  have hequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → φ p.1 = φ p.2 → ρ p.1 = ρ p.2 := by
    filter_upwards with p hp hφeq
    exact (hcoords p.1 hp.1.1 p.2 hp.1.2).mpr
      ⟨hφeq, (hgeometry.equal_scalar_zero_pair hp.1.1 hp.1.2 hφeq hp.2).1⟩
  obtain ⟨B, hB, hcross⟩ := OrderedZeroRelation.exists_measurable_cut_of_ae_no_middle
    Z hZ φ hφ.measurable hsym hnoMiddle ρ hequal
  refine ⟨ρ, B, hρ, hSae.mono (fun x hx => hrowS x hx), hB, ?_⟩
  filter_upwards [hcross, hfeature.representation,
    Measure.quasiMeasurePreserving_fst.ae hSae,
    Measure.quasiMeasurePreserving_snd.ae hSae] with p hp hrep hx hy hzero hne
  apply hp ?_ hne
  refine ⟨⟨hx, hy⟩, ?_⟩
  exact hrep.symm.trans hzero

end Erdos1017.CappedModel

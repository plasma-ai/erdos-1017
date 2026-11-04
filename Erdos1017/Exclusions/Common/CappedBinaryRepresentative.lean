module

public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.Models.Capped.CappedAveraging
public import Erdos1017.Models.Capped.CappedShiftedSelection

/-!
# Scalar charge representative for binary-support models

This module constructs a globally symmetric, bounded, measurable scalar `charge`
for a full model with binary support, retaining the original charge moment and
every imposed order, so such a model has its own scalar representative and all
scalar tests (`exists_scalar_representative`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.BinaryRepresentative

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- Binary adjacency makes the averaged model strictly supported at the
auxiliary threshold -4 and makes its shifted sampled charge deterministic. -/
theorem averaged_binary_data (W : Model Ω ν) (G : Ω × Ω → Bool)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p = if G p = true then 1 else 0) :
    (∀ᵐ p ∂ν.prod ν, (averaged W).moment CappedColor.adjacency p =
      if 0 < shiftedMoment (averaged W) (-4) p then 1 else 0) ∧
    (∀ᵐ p ∂ν.prod ν, ∀ᵐ c ∂(averaged W).kernel p,
      shiftedColor (-4) c = shiftedMoment (averaged W) (-4) p) := by
  have hbinary : ∀ᵐ p ∂ν.prod ν,
      (averaged W).moment CappedColor.adjacency p =
        (if 0 < shiftedMoment (averaged W) (-4) p then 1 else 0) ∧
      (1 - (averaged W).moment CappedColor.adjacency p) *
        shiftedMoment (averaged W) (-4) p = 0 := by
    filter_upwards [hA] with p hp
    have ha := (adjacency_moment_averaged W p).trans hp
    have hlo := neg_three_adjacency_moment_le_charge (averaged W) p
    have hhi := charge_moment_le_adjacency (averaged W) p
    by_cases hg : G p = true
    · rw [ite_eq_left hg] at ha
      have hpos : 0 < shiftedMoment (averaged W) (-4) p := by
        rw [shiftedMoment_eq, ha]
        rw [ha] at hlo
        linarith
      simp only [ha, hpos, ↓reduceIte, sub_self, zero_mul, and_self]
    · rw [ite_eq_right hg] at ha
      have hy : (averaged W).moment CappedColor.charge p = 0 := by
        rw [ha] at hlo hhi
        linarith
      have hz : shiftedMoment (averaged W) (-4) p = 0 := by
        rw [shiftedMoment_eq, ha, hy]
        ring
      simp only [ha, hz, lt_self_iff_false, ↓reduceIte, mul_zero, and_self]
  refine ⟨hbinary.mono (fun _ hp => hp.1), ?_⟩
  apply shiftedColor_deterministic_of_complementary (averaged W) (-4)
    (hbinary.mono (fun _ hp => hp.2))
  intro p
  rw [conditionalCharge_averaged]
  exact averaged_deterministic W p

/-- A globally symmetric bounded physical charge, zero on the displayed
binary nonedges. Its actual moment identity is proved from binary support. -/
def charge (W : Model Ω ν) (G : Ω × Ω → Bool) (p : Ω × Ω) : ℝ :=
  if G p = true then PhysicalRepresentative.charge (averaged W) (-4) p.1 p.2 else 0

omit [IsProbabilityMeasure ν] in
theorem measurable_charge (W : Model Ω ν) (G : Ω × Ω → Bool) (hG : Measurable G) :
    Measurable (charge W G) :=
  Measurable.ite (hG (measurableSet_singleton true))
    (PhysicalRepresentative.measurable_charge (averaged W) (-4)) measurable_const

omit [IsProbabilityMeasure ν] in
theorem charge_symm (W : Model Ω ν) (G : Ω × Ω → Bool)
    (hsym : ∀ x y, G (x, y) = G (y, x)) (x y : Ω) : charge W G (x, y) = charge W G (y, x) := by
  simp only [charge, hsym x y, PhysicalRepresentative.charge_symm (averaged W) (-4) x y]

omit [IsProbabilityMeasure ν] in
theorem charge_mem_Icc (W : Model Ω ν) (G : Ω × Ω → Bool) (p : Ω × Ω) :
    charge W G p ∈ Icc (-3 : ℝ) 1 := by
  unfold charge
  split_ifs
  · exact PhysicalRepresentative.charge_mem_Icc (averaged W) (-4) p.1 p.2
  · constructor <;> norm_num

omit [IsProbabilityMeasure ν] in
theorem charge_zero (W : Model Ω ν) (G : Ω × Ω → Bool) (p : Ω × Ω) (hp : G p = false) :
    charge W G p = 0 := by simp only [charge, hp, Bool.false_eq_true, ↓reduceIte]

omit [IsProbabilityMeasure ν] in
/-- The constructed bounded representative retains the actual original
charge moment; no sampled-charge determinism is assumed for the original model. -/
theorem charge_ae_eq (W : Model Ω ν) (G : Ω × Ω → Bool)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p = if G p = true then 1 else 0) :
    ∀ᵐ p ∂ν.prod ν, charge W G p = chargeKernel W p.1 p.2 := by
  have hstrict := (averaged_binary_data W G hA).1
  filter_upwards [hA, PhysicalRepresentative.charge_ae_eq (averaged W) (-4) hstrict] with p hp hy
  have heq : chargeKernel (averaged W) p.1 p.2 = W.moment CappedColor.charge p :=
    charge_moment_averaged W p
  rw [heq] at hy
  by_cases hg : G p = true
  · exact (ite_eq_left hg).trans hy
  · rw [ite_eq_right hg] at hp
    have hlo := neg_three_adjacency_moment_le_charge W p
    have hhi := charge_moment_le_adjacency W p
    have hz : chargeKernel W p.1 p.2 = 0 := by
      change W.moment CappedColor.charge p = 0
      rw [hp] at hlo hhi
      linarith
    rw [charge, ite_eq_right hg, hz]

/-- Every actual imposed order transfers to the exact displayed binary
graph and the actual constructed scalar charge. -/
theorem full_feasible (W : Model Ω ν) (hW : FullFeasible W)
    (G : Ω × Ω → Bool)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p = if G p = true then 1 else 0) :
    ∀ n, FiniteArity.FeasibleOrder ν (fun x y => G (x, y))
      (fun x y => charge W G (x, y)) n := by
  have hdata := averaged_binary_data W G hA
  have hV : FullFeasible (averaged W) := fun r => feasible_averaged W (hW r)
  have hpair : ∀ᵐ p ∂ν.prod ν,
      PhysicalRepresentative.adjacency (averaged W) (-4) p.1 p.2 = G p ∧
      charge W G p = PhysicalRepresentative.charge (averaged W) (-4) p.1 p.2 := by
    filter_upwards [hA, PhysicalRepresentative.adjacency_moment_ae_eq (averaged W) (-4) hdata.1]
      with p hp hrep
    rw [adjacency_moment_averaged W p, hp] at hrep
    have hg : PhysicalRepresentative.adjacency (averaged W) (-4) p.1 p.2 = G p := by
      cases h₁ : G p <;>
        cases h₂ : PhysicalRepresentative.adjacency (averaged W) (-4) p.1 p.2 <;>
        simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at hrep ⊢ <;> norm_num at hrep
    refine ⟨hg, ?_⟩
    by_cases h : G p = true
    · exact ite_eq_left h
    · have hf : G p = false := Bool.eq_false_iff.mpr h
      rw [charge, ite_eq_right h,
        PhysicalRepresentative.charge_zero_of_nonedge (averaged W) (-4) p.1 p.2 (hg.trans hf)]
  intro n
  have hpairs := FiniteArity.ae_all_pairs ν n _ hpair
  filter_upwards [PhysicalRepresentative.full_feasible (averaged W) hV (-4) hdata.1 hdata.2 n,
    hpairs] with v hv hp hc
  have hc' : FiniteArity.TupleClique (PhysicalRepresentative.adjacency (averaged W) (-4)) v := by
    intro i j hij
    rw [(hp i j hij).1]
    exact hc i j hij
  have heq : FiniteArity.tupleCharge (fun x y => charge W G (x, y)) v =
      FiniteArity.tupleCharge (PhysicalRepresentative.charge (averaged W) (-4)) v := by
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
    · simp only [hij, ↓reduceIte, (hp i j hij).2]
  rw [heq]
  exact hv hc'

/-- Actual full binary-support models supply their own globally measurable
bounded scalar charge and all scalar tests; determinism is not assumed. -/
theorem exists_scalar_representative (W : Model Ω ν) (hW : FullFeasible W)
    (G : Ω × Ω → Bool) (hG : Measurable G) (hsym : ∀ x y, G (x, y) = G (y, x))
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p = if G p = true then 1 else 0) :
    ∃ Y : Ω × Ω → ℝ, Measurable Y ∧ (∀ x y, Y (x, y) = Y (y, x)) ∧
      (∀ p, Y p ∈ Icc (-3 : ℝ) 1) ∧ (∀ p, G p = false → Y p = 0) ∧
      (∀ᵐ p ∂ν.prod ν, Y p = chargeKernel W p.1 p.2) ∧
      ∀ n, FiniteArity.FeasibleOrder ν (fun x y => G (x, y)) (fun x y => Y (x, y)) n :=
  ⟨charge W G, measurable_charge W G hG, charge_symm W G hsym,
    charge_mem_Icc W G, charge_zero W G, charge_ae_eq W G hA, full_feasible W hW G hA⟩

end Erdos1017.CappedModel.BinaryRepresentative

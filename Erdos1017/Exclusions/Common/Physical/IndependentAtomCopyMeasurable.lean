module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyRealization
public import Erdos1017.Exclusions.Common.FullScalarSamplingComparison

/-!
# Measurability and density limit of the marked copy

The marked adjacency and charge are symmetric, measurable and bounded, with zero
charge on nonedges, so the copied scalar competitor obeys the full density
limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*}

private theorem markedAdjacency_eq (A : Ω → Ω → Bool) (x y : Ω) (z w : Ω × Bool) :
    markedAdjacency A x y z w =
      if z.2 = true then (if w.2 = true then false else A x w.1 && A y w.1)
      else (if w.2 = true then A x z.1 && A y z.1 else A z.1 w.1) := by
  cases hz : z.2 <;> cases hw : w.2 <;> simp [markedAdjacency, markedPoint, adjacency, hz, hw]

private theorem rawMarkedCharge_eq (Y : Ω → Ω → ℝ) (I : Set Ω) (x y : Ω)
    (z w : Ω × Bool) :
    charge Y I x y (markedPoint z) (markedPoint w) =
      if z.2 = true then (if w.2 = true then 0
        else Y x w.1 + Y y w.1 + Y x y * I.indicator (fun _ => 1) w.1)
      else (if w.2 = true then Y x z.1 + Y y z.1 + Y x y * I.indicator (fun _ => 1) z.1
        else Y z.1 w.1) := by
  cases hz : z.2 <;> cases hw : w.2 <;> simp [markedPoint, charge, hz, hw]

theorem markedAdjacency_symm (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (x y : Ω) (z w : Ω × Bool) :
    markedAdjacency A x y z w = markedAdjacency A x y w z := by
  rw [markedAdjacency_eq, markedAdjacency_eq]
  cases z.2 <;> cases w.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  exact hsym _ _

theorem markedCharge_symm (A : Ω → Ω → Bool) (hA : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (hY : ∀ x y, Y x y = Y y x) (I : Set Ω) (x y : Ω)
    (z w : Ω × Bool) : markedCharge A Y I x y z w = markedCharge A Y I x y w z := by
  unfold markedCharge
  rw [markedAdjacency_symm A hA x y z w]
  congr 1
  rw [rawMarkedCharge_eq, rawMarkedCharge_eq]
  cases z.2 <;> cases w.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  exact hY _ _

variable [MeasurableSpace Ω]

theorem measurable_markedAdjacency (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (x y : Ω) :
    Measurable (Function.uncurry (markedAdjacency A x y)) := by
  have hl : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  have hr : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have hboth (f : ((Ω × Bool) × (Ω × Bool)) → Ω) (hf : Measurable f) :
      Measurable (fun p => A x (f p) && A y (f p)) :=
    (measurable_of_finite (fun b : Bool × Bool => b.1 && b.2)).comp
      ((hA.comp (measurable_const.prodMk hf)).prodMk
        (hA.comp (measurable_const.prodMk hf)))
  have he : Function.uncurry (markedAdjacency A x y) =
      fun p : (Ω × Bool) × (Ω × Bool) =>
        if p.1.2 = true then (if p.2.2 = true then false else A x p.2.1 && A y p.2.1)
        else (if p.2.2 = true then A x p.1.1 && A y p.1.1 else A p.1.1 p.2.1) := by
    funext p
    exact markedAdjacency_eq A x y p.1 p.2
  rw [he]
  exact Measurable.ite hl
    (Measurable.ite hr measurable_const (hboth _ (measurable_fst.comp measurable_snd)))
    (Measurable.ite hr (hboth _ (measurable_fst.comp measurable_fst))
      (hA.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))))

theorem measurable_markedCharge (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I : Set Ω) (hI : MeasurableSet I) (x y : Ω) :
    Measurable (Function.uncurry (markedCharge A Y I x y)) := by
  have hrow : Measurable (fun z => Y x z + Y y z + Y x y * I.indicator (fun _ => 1) z) :=
    ((hY.comp (measurable_const.prodMk measurable_id)).add
      (hY.comp (measurable_const.prodMk measurable_id))).add
        (measurable_const.mul (measurable_const.indicator hI))
  have hl : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  have hr : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have hraw : Measurable (fun p : (Ω × Bool) × (Ω × Bool) =>
      charge Y I x y (markedPoint p.1) (markedPoint p.2)) := by
    have he : (fun p : (Ω × Bool) × (Ω × Bool) =>
        charge Y I x y (markedPoint p.1) (markedPoint p.2)) =
        fun p => if p.1.2 = true then (if p.2.2 = true then 0
          else Y x p.2.1 + Y y p.2.1 + Y x y * I.indicator (fun _ => 1) p.2.1)
        else (if p.2.2 = true then Y x p.1.1 + Y y p.1.1 +
          Y x y * I.indicator (fun _ => 1) p.1.1 else Y p.1.1 p.2.1) := by
      funext p
      exact rawMarkedCharge_eq Y I x y p.1 p.2
    rw [he]
    exact Measurable.ite hl
      (Measurable.ite hr measurable_const (hrow.comp (measurable_fst.comp measurable_snd)))
      (Measurable.ite hr (hrow.comp (measurable_fst.comp measurable_fst))
        (hY.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd))))
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_markedAdjacency A hA x y) measurable_const)
    hraw measurable_const

omit [MeasurableSpace Ω] in
theorem markedCharge_bound (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I : Set Ω)
    (B : ℝ) (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω) (z w : Ω × Bool) :
    ‖markedCharge A Y I x y z w‖ ≤ 3 * B := by
  have hrow (a : Ω) : ‖Y x a + Y y a + Y x y * I.indicator (fun _ => 1) a‖ ≤ 3 * B := by
    have hi : ‖Y x y * I.indicator (fun _ => (1 : ℝ)) a‖ ≤ B := by
      by_cases ha : a ∈ I
      · simpa only [indicator_of_mem ha, mul_one] using hY x y
      · simpa only [indicator_of_notMem ha, mul_zero, norm_zero] using hB
    exact (norm_add_le _ _).trans (by linarith [norm_add_le (Y x a) (Y y a), hY x a, hY y a])
  unfold markedCharge
  split_ifs
  · rw [rawMarkedCharge_eq]
    split_ifs
    · simpa only [norm_zero] using (show 0 ≤ 3 * B by positivity)
    · exact hrow _
    · exact hrow _
    · exact (hY _ _).trans (by linarith)
  · simpa only [norm_zero] using (show 0 ≤ 3 * B by positivity)

omit [MeasurableSpace Ω] in
theorem markedCharge_zero_of_nonedge (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I : Set Ω) (x y : Ω) (z w : Ω × Bool) (h : markedAdjacency A x y z w = false) :
    markedCharge A Y I x y z w = 0 := by
  simp only [markedCharge, h, Bool.false_eq_true, ite_false]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual copied scalar competitor obeys the genuine full density
limit. Its feasibility, boundedness and symmetry are constructed. -/
theorem ae_copy_objective_le_densityLimit
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hYsym : ∀ x y, Y x y = Y y x)
    (I : Set Ω) (hI : MeasurableSet I) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hindependent : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = true → 0 ≤ Y p.1 p.2 → ∀ t : unitInterval,
      FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure μ t)
          (markedCharge A Y I p.1 p.2) ≤
        FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
          (CappedModel.universalMeasure μ t) (markedAdjacency A p.1 p.2)) := by
  filter_upwards [ae_all_marked_feasibleOrder A hsym Y I
    (Eventually.of_forall (fun p => hYsym p.1 p.2)) hindependent hfull] with p hp hxy hq t
  exact FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    _ (markedAdjacency_symm A hsym p.1 p.2) (measurable_markedAdjacency A hA p.1 p.2)
    _ (measurable_markedCharge A hA Y hY I hI p.1 p.2) (3 * B)
    (fun z => markedCharge_bound A Y I B hB hbound p.1 p.2 z.1 z.2)
    (Eventually.of_forall (fun z => markedCharge_symm A hsym Y hYsym I p.1 p.2 z.1 z.2))
    (Eventually.of_forall (fun z => markedCharge_zero_of_nonedge A Y I p.1 p.2 z.1 z.2))
    (hp hxy hq t)

end Erdos1017.IndependentAtomCopy

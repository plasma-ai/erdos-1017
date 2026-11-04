module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyMeasurable
public import Erdos1017.Models.Capped.CappedUniversalValues

/-!
# Density and objective of the independent atom copy

The extension of a kernel by an independent fresh type with zero
self-interaction and a prescribed row is defined, and the exact density and
objective of the marked copy are computed, retaining the copied row integral, at
both normalized and unnormalized fresh mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An independent fresh type has zero self interaction and a prescribed
row against the old carrier. -/
def extension (K : Ω × Ω → ℝ) (f : Ω → ℝ) (z w : Ω × Bool) : ℝ :=
  if z.2 = true then (if w.2 = true then 0 else f w.1)
  else (if w.2 = true then f z.1 else K (z.1, w.1))

theorem integral_extension_coins (t : unitInterval) (a b k : ℝ) :
    (∫ c : Bool × Bool,
      if c.1 = true then (if c.2 = true then 0 else b)
      else (if c.2 = true then a else k)
      ∂(bernoulliMeasure true false t).prod (bernoulliMeasure true false t)) =
      (t : ℝ) * (1 - (t : ℝ)) * (a + b) + (1 - (t : ℝ)) ^ 2 * k := by
  rw [integral_prod _ Integrable.of_finite]
  simp only [integral_bernoulliMeasure, Bool.false_eq_true, ite_false, ite_true, smul_eq_mul]
  ring

/-- Exact integration of the actual marked law retains its old and new
cross blocks, without assuming a constant copied row. -/
theorem integral_extension (t : unitInterval) (K : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hK : StronglyMeasurable K) (hf : StronglyMeasurable f)
    (B F : ℝ) (hB : ∀ p, ‖K p‖ ≤ B) (hF : ∀ x, ‖f x‖ ≤ F) :
    (∫ p, extension K f p.1 p.2
      ∂(CappedModel.universalMeasure μ t).prod (CappedModel.universalMeasure μ t)) =
      (1 - (t : ℝ)) ^ 2 * (∫ p, K p ∂μ.prod μ) +
        2 * (t : ℝ) * (1 - (t : ℝ)) * ∫ x, f x ∂μ := by
  let J : (Ω × Ω) × (Bool × Bool) → ℝ := fun p =>
    if p.2.1 = true then (if p.2.2 = true then 0 else f p.1.2)
    else (if p.2.2 = true then f p.1.1 else K p.1)
  have hl : MeasurableSet {p : (Ω × Ω) × (Bool × Bool) | p.2.1 = true} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  have hr : MeasurableSet {p : (Ω × Ω) × (Bool × Bool) | p.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  have hJ : StronglyMeasurable J := (Measurable.ite hl
    (Measurable.ite hr measurable_const (hf.measurable.comp (measurable_snd.comp measurable_fst)))
    (Measurable.ite hr (hf.measurable.comp (measurable_fst.comp measurable_fst))
      (hK.measurable.comp measurable_fst))).stronglyMeasurable
  have hi : Integrable J
      ((μ.prod μ).prod ((bernoulliMeasure true false t).prod (bernoulliMeasure true false t))) := by
    apply Integrable.of_bound hJ.aestronglyMeasurable (max 0 (max B F))
    filter_upwards with p
    dsimp only [J]
    split_ifs
    · simpa only [norm_zero] using le_max_left 0 (max B F)
    · exact (hF _).trans ((le_max_right B F).trans (le_max_right 0 _))
    · exact (hF _).trans ((le_max_right B F).trans (le_max_right 0 _))
    · exact (hB _).trans ((le_max_left B F).trans (le_max_right 0 _))
  have hmap := integral_map_of_stronglyMeasurable
    (μ := (CappedModel.universalMeasure μ t).prod (CappedModel.universalMeasure μ t))
    (CappedModel.universal_pair_shuffle (μ := μ) t).measurable hJ
  rw [(CappedModel.universal_pair_shuffle (μ := μ) t).map_eq] at hmap
  change (∫ p, J ((p.1.1, p.2.1), (p.1.2, p.2.2))
    ∂(CappedModel.universalMeasure μ t).prod (CappedModel.universalMeasure μ t)) = _
  rw [← hmap, integral_prod _ hi]
  change (∫ p : Ω × Ω, ∫ c : Bool × Bool,
    if c.1 = true then (if c.2 = true then 0 else f p.2)
    else (if c.2 = true then f p.1 else K p)
      ∂(bernoulliMeasure true false t).prod (bernoulliMeasure true false t) ∂μ.prod μ) = _
  simp_rw [integral_extension_coins]
  have hKi : Integrable K (μ.prod μ) := Integrable.of_bound hK.aestronglyMeasurable B
    (Eventually.of_forall hB)
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable F
    (Eventually.of_forall hF)
  have hfst : Integrable (fun p : Ω × Ω => f p.1) (μ.prod μ) := hfi.comp_fst μ
  have hsnd : Integrable (fun p : Ω × Ω => f p.2) (μ.prod μ) := hfi.comp_snd μ
  have hsum : Integrable (fun p : Ω × Ω => f p.1 + f p.2) (μ.prod μ) := hfst.add hsnd
  rw [integral_add (hsum.const_mul _) (hKi.const_mul _),
    integral_const_mul, integral_const_mul, integral_add hfst hsnd,
    integral_fun_fst, integral_fun_snd]
  simp only [probReal_univ, one_smul]
  ring

/-- The copied row is supported precisely on the old common neighborhood. -/
def rowCharge (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I : Set Ω) (x y z : Ω) : ℝ :=
  if (A x z && A y z) = true then Y x z + Y y z + Y x y * I.indicator (fun _ => 1) z else 0

def rowAdjacency (A : Ω → Ω → Bool) (x y z : Ω) : ℝ :=
  if (A x z && A y z) = true then 1 else 0

omit [MeasurableSpace Ω] in
theorem markedCharge_eq_extension (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I : Set Ω) (x y : Ω) (hzero : ∀ z w, A z w = false → Y z w = 0)
    (z w : Ω × Bool) :
    markedCharge A Y I x y z w = extension (Function.uncurry Y) (rowCharge A Y I x y) z w := by
  cases hz : z.2 <;> cases hw : w.2 <;>
    simp only [markedCharge, markedAdjacency, markedPoint, hz, hw,
      Bool.false_eq_true, ite_false, ite_true, charge, adjacency, extension, rowCharge]
  cases ha : A z.1 w.1
  · simp only [Bool.false_eq_true, ite_false, hzero _ _ ha, Function.uncurry_apply_pair]
  · simp only [ite_true, Function.uncurry_apply_pair]

omit [MeasurableSpace Ω] in
theorem markedAdjacency_eq_extension (A : Ω → Ω → Bool) (x y : Ω) (z w : Ω × Bool) :
    (if markedAdjacency A x y z w = true then (1 : ℝ) else 0) =
      extension (fun p => if A p.1 p.2 = true then 1 else 0) (rowAdjacency A x y) z w := by
  cases hz : z.2 <;> cases hw : w.2 <;>
    simp only [markedAdjacency, markedPoint, hz, hw, Bool.false_eq_true, ite_false, ite_true,
      adjacency, extension, rowAdjacency]

theorem measurable_rowCharge (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (I : Set Ω) (hI : MeasurableSet I) (x y : Ω) : Measurable (rowCharge A Y I x y) := by
  have he : Measurable (fun z : Ω => ((x, true), (z, false))) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have hm := (measurable_markedCharge A hA Y hY I hI x y).comp he
  change Measurable (fun z => markedCharge A Y I x y (x, true) (z, false)) at hm
  change Measurable (fun z =>
    if (A x z && A y z) = true then Y x z + Y y z + Y x y * I.indicator (fun _ => 1) z else 0)
  simpa only [Function.uncurry_apply_pair, markedCharge, markedAdjacency, markedPoint,
    Bool.false_eq_true,
    ite_true, ite_false, adjacency, charge, rowCharge] using hm

theorem measurable_rowAdjacency (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (x y : Ω) : Measurable (rowAdjacency A x y) := by
  have he : Measurable (fun z : Ω => ((x, true), (z, false))) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have hm := (measurable_markedAdjacency A hA x y).comp he
  change Measurable (fun z => markedAdjacency A x y (x, true) (z, false)) at hm
  have h : Measurable (fun z : Ω =>
      if markedAdjacency A x y (x, true) (z, false) = true then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun hm measurable_const)
    (measurable_const (a := (1 : ℝ))) (measurable_const (a := (0 : ℝ)))
  change Measurable (fun z => if (A x z && A y z) = true then (1 : ℝ) else 0)
  simpa only [markedAdjacency, markedPoint, Bool.false_eq_true,
    ite_true, ite_false, adjacency, rowAdjacency] using h

omit [MeasurableSpace Ω] in
theorem rowCharge_bound (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I : Set Ω)
    (B : ℝ) (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y z : Ω) :
    ‖rowCharge A Y I x y z‖ ≤ 3 * B := by
  simpa only [markedCharge, markedAdjacency, markedPoint, Bool.false_eq_true,
    ite_true, ite_false, adjacency, charge, rowCharge] using
    markedCharge_bound A Y I B hB hY x y (x, true) (z, false)

/-- Exact density of the actual independent copy at its normalized mass. -/
theorem density_marked (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (x y : Ω) (t : unitInterval) :
    FiniteCappedSamplingCost.physicalDensity (CappedModel.universalMeasure μ t)
        (markedAdjacency A x y) =
      (1 - (t : ℝ)) ^ 2 * FiniteCappedSamplingCost.physicalDensity μ A +
        (t : ℝ) * (1 - (t : ℝ)) * ∫ z, rowAdjacency A x y z ∂μ := by
  unfold FiniteCappedSamplingCost.physicalDensity
  simp_rw [markedAdjacency_eq_extension]
  have hK : StronglyMeasurable (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0) :=
    (Measurable.ite (measurableSet_eq_fun hA measurable_const)
      measurable_const measurable_const).stronglyMeasurable
  rw [integral_extension (μ := μ) t _ _ hK
    (measurable_rowAdjacency A hA x y).stronglyMeasurable 1 1
    (fun p => by split_ifs <;> norm_num) (fun z => by
      unfold rowAdjacency
      split_ifs <;> norm_num)]
  ring

/-- Exact objective retains the actual copied row integral; absent old
pairs have zero charge by the explicitly stated scalar support condition. -/
theorem objective_marked (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (I : Set Ω) (hI : MeasurableSet I) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω)
    (hzero : ∀ z w, A z w = false → Y z w = 0) (t : unitInterval) :
    FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure μ t)
        (markedCharge A Y I x y) =
      (1 - (t : ℝ)) ^ 2 * FiniteCappedSamplingCost.physicalObjective μ Y +
        (t : ℝ) * (1 - (t : ℝ)) * ∫ z, rowCharge A Y I x y z ∂μ := by
  unfold FiniteCappedSamplingCost.physicalObjective
  simp_rw [markedCharge_eq_extension A Y I x y hzero]
  rw [integral_extension t _ _ hY.stronglyMeasurable
    (measurable_rowCharge A hA Y hY I hI x y).stronglyMeasurable B (3 * B)
    (fun p => hbound p.1 p.2) (rowCharge_bound A Y I B hB hbound x y)]
  dsimp only [Function.uncurry]
  ring

/-- The unnormalized fresh mass has zero quadratic self contribution. -/
theorem density_marked_mass (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (x y : Ω) (τ : ℝ) (hτ : 0 ≤ τ) :
    FiniteCappedSamplingCost.physicalDensity
        (CappedModel.universalMeasure μ (CappedModel.universalFraction τ hτ))
        (markedAdjacency A x y) =
      (FiniteCappedSamplingCost.physicalDensity μ A + τ * ∫ z, rowAdjacency A x y z ∂μ) /
        (1 + τ) ^ 2 := by
  rw [density_marked A hA]
  simp only [CappedModel.universalFraction]
  field_simp [show 1 + τ ≠ 0 by linarith]
  ring

theorem objective_marked_mass (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (I : Set Ω) (hI : MeasurableSet I) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω)
    (hzero : ∀ z w, A z w = false → Y z w = 0) (τ : ℝ) (hτ : 0 ≤ τ) :
    FiniteCappedSamplingCost.physicalObjective
        (CappedModel.universalMeasure μ (CappedModel.universalFraction τ hτ))
        (markedCharge A Y I x y) =
      (FiniteCappedSamplingCost.physicalObjective μ Y + τ * ∫ z, rowCharge A Y I x y z ∂μ) /
        (1 + τ) ^ 2 := by
  rw [objective_marked A hA Y hY I hI B hB hbound x y hzero]
  simp only [CappedModel.universalFraction]
  field_simp [show 1 + τ ≠ 0 by linarith]
  ring

end Erdos1017.IndependentAtomCopy

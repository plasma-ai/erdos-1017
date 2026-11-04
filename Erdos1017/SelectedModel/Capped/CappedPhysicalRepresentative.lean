module

public import Erdos1017.SelectedModel.Capped.CappedDeterministicTests
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# Physical scalar representatives of decorated models

Symmetrizing both orientations makes adjacency and charge pointwise symmetric,
while the original model requires symmetry only almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.CappedModel.PhysicalRepresentative

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Retain a pair precisely when both oriented shifted moments are positive. -/
def adjacency (W : Model Ω μ) (m : ℝ) (x y : Ω) : Bool :=
  positiveAdjacency W m x y && positiveAdjacency W m y x

/-- Symmetrize the actual charge moment and set absent pairs to zero. -/
def charge (W : Model Ω μ) (m : ℝ) (x y : Ω) : ℝ :=
  if adjacency W m x y = true then (chargeKernel W x y + chargeKernel W y x) / 2 else 0

theorem adjacency_symm (W : Model Ω μ) (m : ℝ) (x y : Ω) :
    adjacency W m x y = adjacency W m y x := Bool.and_comm _ _

private theorem measurable_positiveAdjacency (W : Model Ω μ) (m : ℝ) :
    Measurable (Function.uncurry (positiveAdjacency W m)) := by
  classical
  have hm : Measurable (shiftedMoment W m) :=
    (W.stronglyMeasurable_moment (continuous_shiftedColor m).measurable.stronglyMeasurable).measurable
  exact Measurable.ite (measurableSet_lt measurable_const hm) measurable_const measurable_const

theorem measurable_adjacency (W : Model Ω μ) (m : ℝ) :
    Measurable (Function.uncurry (adjacency W m)) := by
  have hp := measurable_positiveAdjacency W m
  exact (measurable_of_finite (fun p : Bool × Bool => p.1 && p.2)).comp
    (hp.prodMk (hp.comp measurable_swap))

theorem measurable_charge (W : Model Ω μ) (m : ℝ) :
    Measurable (Function.uncurry (charge W m)) := by
  have hy : Measurable (Function.uncurry (chargeKernel W)) :=
    (W.stronglyMeasurable_moment CappedColor.continuous_charge.measurable.stronglyMeasurable).measurable
  exact Measurable.ite ((measurable_adjacency W m) (measurableSet_singleton true))
    ((hy.add (hy.comp measurable_swap)).div_const 2) measurable_const

theorem charge_symm (W : Model Ω μ) (m : ℝ) (x y : Ω) :
    charge W m x y = charge W m y x := by
  simp only [charge, adjacency_symm W m x y, add_comm]

theorem charge_zero_of_nonedge (W : Model Ω μ) (m : ℝ) (x y : Ω)
    (h : adjacency W m x y = false) : charge W m x y = 0 := by
  simp only [charge, h, Bool.false_eq_true, ↓reduceIte]

private theorem chargeKernel_mem_Icc (W : Model Ω μ) (x y : Ω) :
    chargeKernel W x y ∈ Icc (-3 : ℝ) 1 := by
  have ha := adjacency_moment_mem W (x, y)
  have hlo := neg_three_adjacency_moment_le_charge W (x, y)
  have hhi := charge_moment_le_adjacency W (x, y)
  change W.moment CappedColor.charge (x, y) ∈ Icc (-3 : ℝ) 1
  constructor <;> linarith [ha.1, ha.2]

/-- The physical representative retains the actual compact charge box
pointwise, including pairs in the original exceptional symmetry set. -/
theorem charge_mem_Icc (W : Model Ω μ) (m : ℝ) (x y : Ω) :
    charge W m x y ∈ Icc (-3 : ℝ) 1 := by
  have hxy := chargeKernel_mem_Icc W x y
  have hyx := chargeKernel_mem_Icc W y x
  unfold charge
  split_ifs <;> constructor <;> linarith [hxy.1, hxy.2, hyx.1, hyx.2]

theorem charge_bound (W : Model Ω μ) (m : ℝ) (x y : Ω) : |charge W m x y| ≤ 3 :=
  abs_le.mpr ⟨(charge_mem_Icc W m x y).1, (charge_mem_Icc W m x y).2.trans (by norm_num)⟩

/-- The symmetric Boolean adjacency agrees almost everywhere with the
original oriented threshold; no pointwise symmetry of that threshold is assumed. -/
theorem adjacency_ae_eq (W : Model Ω μ) (m : ℝ) :
    ∀ᵐ p ∂μ.prod μ, adjacency W m p.1 p.2 = positiveAdjacency W m p.1 p.2 := by
  filter_upwards [positiveAdjacency_symm W m] with p hp
  simp only [adjacency, hp, Bool.and_self]

/-- Strict support identifies the representative's Boolean adjacency with
the actual adjacency moment on one common set of full product measure. -/
theorem adjacency_moment_ae_eq (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if adjacency W m p.1 p.2 = true then 1 else 0 := by
  filter_upwards [hsupport, adjacency_ae_eq W m] with p hp hrep
  rw [hrep]
  exact hp.trans (positiveAdjacency_value W m p).symm

/-- Symmetric averaging and zeroing absent pairs preserve the actual
charge moment almost everywhere under strict support. -/
theorem charge_ae_eq (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    ∀ᵐ p ∂μ.prod μ, charge W m p.1 p.2 = chargeKernel W p.1 p.2 := by
  filter_upwards [adjacency_ae_eq W m, chargeKernel_symm W,
    boolean_missing_charge_zero W m hsupport] with p hrep hsym hzero
  unfold charge
  rw [hrep]
  by_cases h : positiveAdjacency W m p.1 p.2 = true
  · rw [ite_eq_left h, ← hsym]
    ring
  · rw [ite_eq_right h]
    exact (hzero (Bool.eq_false_iff.mpr h)).symm

variable [IsProbabilityMeasure μ]

theorem integrable_charge (W : Model Ω μ) (m : ℝ) :
    Integrable (Function.uncurry (charge W m)) (μ.prod μ) := by
  apply Integrable.of_bound (measurable_charge W m).aestronglyMeasurable 3
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs]
    exact charge_bound W m p.1 p.2)

omit [IsProbabilityMeasure μ] in
/-- Symmetrizing the actual adjacency changes no density. -/
theorem density_eq (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    FiniteCappedSamplingCost.physicalDensity μ (adjacency W m) = density W := by
  unfold FiniteCappedSamplingCost.physicalDensity density
  congr 1
  apply integral_congr_ae
  filter_upwards [adjacency_moment_ae_eq W m hsupport] with p hp
  exact hp.symm

omit [IsProbabilityMeasure μ] in
/-- Symmetric averaging and absent-pair zeroing change no objective. -/
theorem objective_eq (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    FiniteCappedSamplingCost.physicalObjective μ (charge W m) = objective W := by
  unfold FiniteCappedSamplingCost.physicalObjective objective
  congr 1
  exact integral_congr_ae (charge_ae_eq W m hsupport)

/-- The constructed pointwise symmetric representative inherits each
actual imposed colored clique test through pairwise almost-everywhere agreement. -/
theorem feasibleOrder (W : Model Ω μ) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (n : ℕ) (htest : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ᵐ c ∂cliqueLaw W x, violation c = 0) :
    FiniteArity.FeasibleOrder μ (adjacency W m) (charge W m) n := by
  have hold := (sampled_test_iff_feasibleOrder W m hsupport hdet n).mp htest
  have hpairs := FiniteArity.ae_all_pairs μ n _
    ((adjacency_ae_eq W m).and (charge_ae_eq W m hsupport))
  filter_upwards [hold, hpairs] with x hx hpairs hclique
  have hclique' : FiniteArity.TupleClique (positiveAdjacency W m) x := by
    intro i j hij
    rw [← (hpairs i j hij).1]
    exact hclique i j hij
  have hcharge : FiniteArity.tupleCharge (charge W m) x =
      FiniteArity.tupleCharge (chargeKernel W) x := by
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
    · simp only [hij, ↓reduceIte, (hpairs i j hij).2]
  rw [hcharge]
  exact hx hclique'

/-- Full actual sampled-color feasibility yields all scalar clique tests
for this constructed physical representative, including orders zero and one. -/
theorem full_feasible (W : Model Ω μ) (hW : FullFeasible W) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ n, FiniteArity.FeasibleOrder μ (adjacency W m) (charge W m) n := by
  intro n
  by_cases hn : 2 ≤ n
  · exact feasibleOrder W m hsupport hdet n (hW n n hn le_rfl)
  · exact Filter.Eventually.of_forall (fun x _ => by
      rw [FiniteArity.tupleCharge_small (by omega) (charge W m) x]
      norm_num)

end Erdos1017.CappedModel.PhysicalRepresentative

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual fully feasible decorated model with strict shifted support
and deterministic sampled shifted color has a bounded measurable physical
representative with pointwise symmetry and the same density and objective. -/
theorem exists_physical_representative (W : Model Ω μ) (hW : FullFeasible W) (m : ℝ)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∃ (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ),
      Measurable (Function.uncurry A) ∧ (∀ x y, A x y = A y x) ∧
      Measurable (Function.uncurry Y) ∧ (∀ x y, Y x y = Y y x) ∧
      (∀ x y, Y x y ∈ Icc (-3 : ℝ) 1) ∧ (∀ x y, A x y = false → Y x y = 0) ∧
      Integrable (Function.uncurry Y) (μ.prod μ) ∧
      (∀ n, FiniteArity.FeasibleOrder μ A Y n) ∧
      FiniteCappedSamplingCost.physicalDensity μ A = density W ∧
      FiniteCappedSamplingCost.physicalObjective μ Y = objective W := by
  exact ⟨PhysicalRepresentative.adjacency W m, PhysicalRepresentative.charge W m,
    PhysicalRepresentative.measurable_adjacency W m, PhysicalRepresentative.adjacency_symm W m,
    PhysicalRepresentative.measurable_charge W m, PhysicalRepresentative.charge_symm W m,
    PhysicalRepresentative.charge_mem_Icc W m, PhysicalRepresentative.charge_zero_of_nonedge W m,
    PhysicalRepresentative.integrable_charge W m, PhysicalRepresentative.full_feasible W hW m hsupport hdet,
    PhysicalRepresentative.density_eq W m hsupport, PhysicalRepresentative.objective_eq W m hsupport⟩

end Erdos1017.CappedModel

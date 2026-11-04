module

public import Erdos1017.Exclusions.Common.Physical.PhysicalConditionalAveraging
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalRootLeaves

/-!
# Region counts of physical parents

The count `tupleCount` of coordinates in a measurable region (with repetitions)
is defined, and the first, second, factorial and cross moments of the region
counts are identified with ordered pair occupation masses, without any
independent-sampling interpretation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Count actual coordinates in a measurable physical region, including
repetitions. No independent-sampling interpretation is imposed. -/
def tupleCount {n : ℕ} (R : Set Ω) (v : Fin n → Ω) : ℕ :=
  ∑ i, if v i ∈ R then 1 else 0

omit [MeasurableSpace Ω] in
theorem tupleCount_le {n : ℕ} (R : Set Ω) (v : Fin n → Ω) : tupleCount R v ≤ n := by
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> simp)
    _ = n := by simp

theorem measurable_tupleCount {n : ℕ} (R : Set Ω) (hR : MeasurableSet R) :
    Measurable (tupleCount (n := n) R) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hR.preimage (measurable_pi_apply i)) measurable_const measurable_const

/-- The count law is the finite sum of genuine parent pushforwards at
their original orders. Its mass is not normalized to one. -/
def countMeasure (N : ℕ) (η : Laws Ω) (R E : Set Ω) : Measure (ℕ × ℕ) :=
  ∑ n ∈ Finset.range (N + 1), (η n).map (fun v => (tupleCount R v, tupleCount E v))

instance countMeasure_finite (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)] (R E : Set Ω) :
    IsFiniteMeasure (countMeasure N η R E) := by
  unfold countMeasure
  infer_instance

/-- Every function of the two counts is integrable at a fixed finite
order, because the actual counts lie in a finite square. -/
theorem integrable_count_function {n : ℕ} (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E) (F : ℕ × ℕ → ℝ) :
    Integrable (fun v => F (tupleCount R v, tupleCount E v)) ρ := by
  let B := ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), ‖F (k, l)‖
  have hm : Measurable (fun v : Fin n → Ω => F (tupleCount R v, tupleCount E v)) :=
    (measurable_of_countable F).comp
      ((measurable_tupleCount R hR).prodMk (measurable_tupleCount E hE))
  apply Integrable.of_bound hm.aestronglyMeasurable B
  apply Eventually.of_forall
  intro v
  have hk : tupleCount R v ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by
    have := tupleCount_le R v
    omega)
  have hl : tupleCount E v ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by
    have := tupleCount_le E v
    omega)
  exact (Finset.single_le_sum (fun l _ => norm_nonneg (F (tupleCount R v, l))) hl).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => norm_nonneg (F (k, l)))) hk)

theorem integrable_countMeasure (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E) (F : ℕ × ℕ → ℝ) :
    Integrable F (countMeasure N η R E) := by
  apply integrable_finsetSum_measure.mpr
  intro n _
  apply (integrable_map_measure (measurable_of_countable F).aestronglyMeasurable
    ((measurable_tupleCount R hR).prodMk (measurable_tupleCount E hE)).aemeasurable).mpr
  exact integrable_count_function (η n) R E hR hE F

/-- Integration against the actual count law is exactly integration of
the corresponding count function on each original joint parent law. -/
theorem integral_countMeasure (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E) (F : ℕ × ℕ → ℝ) :
    (∫ z, F z ∂countMeasure N η R E) =
      ∑ n ∈ Finset.range (N + 1), ∫ v, F (tupleCount R v, tupleCount E v) ∂η n := by
  have hi := integrable_finsetSum_measure.mp (integrable_countMeasure N η R E hR hE F)
  rw [countMeasure, integral_finsetSum_measure hi]
  apply Finset.sum_congr rfl
  intro n _
  exact integral_map ((measurable_tupleCount R hR).prodMk
    (measurable_tupleCount E hE)).aemeasurable (measurable_of_countable F).aestronglyMeasurable

/-- A genuine order cap identifies total count mass with the exact
physical primal cost, without a probability normalization. -/
theorem countMeasure_mass (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hcap : ∀ n, N < n → η n = 0) :
    (countMeasure N η R E).real univ = cost η := by
  have hi := integral_countMeasure N η R E hR hE (fun _ => 1)
  simp only [integral_const, smul_eq_mul, mul_one] at hi
  rw [hi, cost, tsum_eq_sum (s := Finset.range (N + 1))]
  intro n hn
  have hN : N < n := by
    simp only [Finset.mem_range] at hn
    omega
  simp [hcap n hN]

omit [MeasurableSpace Ω] in
/-- The literal ordered rectangle count is the product of coordinate
counts minus the actual diagonal intersection count. -/
theorem charge_indicator_rectangle {n : ℕ} (R E : Set Ω) (v : Fin n → Ω) :
    charge ((R ×ˢ E).indicator (fun _ => (1 : ℝ))) v =
      ((tupleCount R v : ℝ) * (tupleCount E v : ℝ) - (tupleCount (R ∩ E) v : ℝ)) / 2 := by
  rw [show (R ×ˢ E).indicator (fun _ => (1 : ℝ)) =
      Function.uncurry (fun x y => if x ∈ R ∧ y ∈ E then (1 : ℝ) else 0) by
    funext p
    simp [Set.indicator, mem_prod, Function.uncurry]]
  rw [charge_uncurry_eq_tupleCharge]
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  congr 1
  have he (i j : Fin n) :
      (if i = j then 0 else if v i ∈ R ∧ v j ∈ E then (1 : ℝ) else 0) =
        (if v i ∈ R then (1 : ℝ) else 0) * (if v j ∈ E then (1 : ℝ) else 0) -
          (if i = j then (if v i ∈ R ∩ E then (1 : ℝ) else 0) else 0) := by
    by_cases hij : i = j <;> by_cases hi : v i ∈ R <;> by_cases hj : v j ∈ E <;>
      simp_all
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  simp only [tupleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

omit [MeasurableSpace Ω] in
theorem charge_indicator_self {n : ℕ} (R : Set Ω) (v : Fin n → Ω) :
    charge ((R ×ˢ R).indicator (fun _ => (1 : ℝ))) v =
      (tupleCount R v : ℝ) * ((tupleCount R v : ℝ) - 1) / 2 := by
  rw [charge_indicator_rectangle, inter_self]
  ring

omit [MeasurableSpace Ω] in
theorem charge_indicator_disjoint {n : ℕ} (R E : Set Ω) (hdis : Disjoint R E) (v : Fin n → Ω) :
    charge ((R ×ˢ E).indicator (fun _ => (1 : ℝ))) v =
      (tupleCount R v : ℝ) * (tupleCount E v : ℝ) / 2 := by
  rw [charge_indicator_rectangle, Set.disjoint_iff_inter_eq_empty.mp hdis]
  simp [tupleCount]

/-- An actual order cap reduces the original occupation, not the joint
laws themselves, to its finite sum. -/
theorem occupation_eq_sum_of_cap (N : ℕ) (η : Laws Ω)
    (hcap : ∀ n, N < n → η n = 0) :
    occupation η = ∑ n ∈ Finset.range (N + 1), orderOccupation n (η n) := by
  ext s hs
  rw [occupation, Measure.sum_apply _ hs, Measure.finsetSum_apply]
  apply tsum_eq_sum
  intro n hn
  have hn' : N < n := by simp only [Finset.mem_range] at hn; omega
  rw [hcap n hn', orderOccupation_zero]
  rfl

/-- The two actual region counts have the exact mixed moment dictated
by ordered pair occupation. Singularity of parents causes no loss. -/
theorem countMeasure_cross_moment (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E) (hdis : Disjoint R E)
    (hcap : ∀ n, N < n → η n = 0) (demand : Measure (Ω × Ω)) [IsFiniteMeasure demand]
    (hbalance : occupation η = demand) :
    (∫ z, (z.1 : ℝ) * (z.2 : ℝ) ∂countMeasure N η R E) = demand.real (R ×ˢ E) := by
  let Y := (R ×ˢ E).indicator (fun _ => (1 : ℝ))
  have hi : Integrable Y demand := (integrable_const 1).indicator (hR.prod hE)
  have hin (n : ℕ) : Integrable Y (orderOccupation n (η n)) := by
    apply hi.mono_measure
    rw [← hbalance]
    exact Measure.le_sum (fun k => orderOccupation k (η k)) n
  have horder (n : ℕ) : (∫ v, (tupleCount R v : ℝ) * (tupleCount E v : ℝ) ∂η n) =
      ∫ p, Y p ∂orderOccupation n (η n) := by
    have he := (integral_charge n (η n) Y (hin n)).2
    simp_rw [show ∀ v : Fin n → Ω, charge Y v =
      (tupleCount R v : ℝ) * (tupleCount E v : ℝ) / 2 from charge_indicator_disjoint R E hdis] at he
    rw [integral_div] at he
    linarith
  rw [integral_countMeasure N η R E hR hE]
  simp_rw [horder]
  rw [← integral_finsetSum_measure (fun n _ => hin n), ← occupation_eq_sum_of_cap N η hcap,
    hbalance]
  simp [Y, integral_indicator (hR.prod hE)]

/-- The factorial second moment counts exactly the distinct ordered
pairs in the first region. It is not an ordinary second moment. -/
theorem countMeasure_factorial_moment (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hcap : ∀ n, N < n → η n = 0) (demand : Measure (Ω × Ω)) [IsFiniteMeasure demand]
    (hbalance : occupation η = demand) :
    (∫ z, (z.1 : ℝ) * ((z.1 : ℝ) - 1) ∂countMeasure N η R E) = demand.real (R ×ˢ R) := by
  let Y := (R ×ˢ R).indicator (fun _ => (1 : ℝ))
  have hi : Integrable Y demand := (integrable_const 1).indicator (hR.prod hR)
  have hin (n : ℕ) : Integrable Y (orderOccupation n (η n)) := by
    apply hi.mono_measure
    rw [← hbalance]
    exact Measure.le_sum (fun k => orderOccupation k (η k)) n
  have horder (n : ℕ) : (∫ v, (tupleCount R v : ℝ) * ((tupleCount R v : ℝ) - 1) ∂η n) =
      ∫ p, Y p ∂orderOccupation n (η n) := by
    have he := (integral_charge n (η n) Y (hin n)).2
    simp_rw [show ∀ v : Fin n → Ω, charge Y v =
      (tupleCount R v : ℝ) * ((tupleCount R v : ℝ) - 1) / 2 from charge_indicator_self R] at he
    rw [integral_div] at he
    linarith
  rw [integral_countMeasure N η R E hR hE]
  simp_rw [horder]
  rw [← integral_finsetSum_measure (fun n _ => hin n), ← occupation_eq_sum_of_cap N η hcap,
    hbalance]
  simp [Y, integral_indicator (hR.prod hR)]

omit [MeasurableSpace Ω] in
theorem tupleCount_eq_one_of_unique {n : ℕ} (I : Set Ω) (v : Fin n → Ω)
    (hroot : ∃! i, v i ∈ I) : tupleCount I v = 1 := by
  obtain ⟨i, hi, hu⟩ := hroot
  unfold tupleCount
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hj : v j ∉ I := fun h => hji (hu j h)
    simp [hj]
  · simp

/-- A unique actual root makes the first count moment equal to the
root-to-region ordered pair mass, with no root-parent normalization. -/
theorem countMeasure_first_moment (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (I R E : Set Ω) (hI : MeasurableSet I) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hdis : Disjoint I R) (hroot : ∀ n, ∀ᵐ v ∂η n, ∃! i, v i ∈ I)
    (hcap : ∀ n, N < n → η n = 0) (demand : Measure (Ω × Ω)) [IsFiniteMeasure demand]
    (hbalance : occupation η = demand) :
    (∫ z, (z.1 : ℝ) ∂countMeasure N η R E) = demand.real (I ×ˢ R) := by
  let Y := (I ×ˢ R).indicator (fun _ => (1 : ℝ))
  have hi : Integrable Y demand := (integrable_const 1).indicator (hI.prod hR)
  have hin (n : ℕ) : Integrable Y (orderOccupation n (η n)) := by
    apply hi.mono_measure
    rw [← hbalance]
    exact Measure.le_sum (fun k => orderOccupation k (η k)) n
  have horder (n : ℕ) : (∫ v, (tupleCount R v : ℝ) ∂η n) =
      ∫ p, Y p ∂orderOccupation n (η n) := by
    have he := (integral_charge n (η n) Y (hin n)).2
    have heq : ∀ᵐ v ∂η n, charge Y v = (tupleCount R v : ℝ) / 2 := by
      filter_upwards [hroot n] with v hv
      rw [charge_indicator_disjoint I R hdis, tupleCount_eq_one_of_unique I v hv]
      simp
    rw [integral_congr_ae heq, integral_div] at he
    linarith
  rw [integral_countMeasure N η R E hR hE]
  simp_rw [horder]
  rw [← integral_finsetSum_measure (fun n _ => hin n), ← occupation_eq_sum_of_cap N η hcap,
    hbalance]
  simp [Y, integral_indicator (hI.prod hR)]

theorem countMeasure_second_moment (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (I R E : Set Ω) (hI : MeasurableSet I) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hdis : Disjoint I E) (hroot : ∀ n, ∀ᵐ v ∂η n, ∃! i, v i ∈ I)
    (hcap : ∀ n, N < n → η n = 0) (demand : Measure (Ω × Ω)) [IsFiniteMeasure demand]
    (hbalance : occupation η = demand) :
    (∫ z, (z.2 : ℝ) ∂countMeasure N η R E) = demand.real (I ×ˢ E) := by
  have he : (∫ z, (z.2 : ℝ) ∂countMeasure N η R E) =
      ∫ z, (z.1 : ℝ) ∂countMeasure N η E R := by
    rw [integral_countMeasure N η R E hR hE, integral_countMeasure N η E R hE hR]
  rw [he]
  exact countMeasure_first_moment N η I E R hI hE hR hdis hroot hcap demand hbalance

theorem countMeasure_second_factorial_moment (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hcap : ∀ n, N < n → η n = 0) (demand : Measure (Ω × Ω)) [IsFiniteMeasure demand]
    (hbalance : occupation η = demand) :
    (∫ z, (z.2 : ℝ) * ((z.2 : ℝ) - 1) ∂countMeasure N η R E) = demand.real (E ×ˢ E) := by
  have he : (∫ z, (z.2 : ℝ) * ((z.2 : ℝ) - 1) ∂countMeasure N η R E) =
      ∫ z, (z.1 : ℝ) * ((z.1 : ℝ) - 1) ∂countMeasure N η E R := by
    rw [integral_countMeasure N η R E hR hE, integral_countMeasure N η E R hE hR]
  rw [he]
  exact countMeasure_factorial_moment N η E R hE hR hcap demand hbalance

/-- On an actual complete rectangle, graph demand has exactly the
original product mass, with the ordered-pair normalization unchanged. -/
theorem graphDemand_real_rectangle (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Set (Ω × Ω)) (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hedge : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ E → p ∈ G) :
    (graphDemand μ G).real (R ×ˢ E) = μ.real R * μ.real E := by
  have heq : ((R ×ˢ E) ∩ G : Set (Ω × Ω)) =ᵐ[μ.prod μ] R ×ˢ E := by
    filter_upwards [hedge] with p hp
    exact propext ⟨fun h => h.1, fun h => ⟨h, hp h.1 h.2⟩⟩
  simp only [measureReal_def, graphDemand, Measure.restrict_apply (hR.prod hE),
    measure_congr heq, Measure.prod_prod, ENNReal.toReal_mul]

end Erdos1017.PhysicalPrimal

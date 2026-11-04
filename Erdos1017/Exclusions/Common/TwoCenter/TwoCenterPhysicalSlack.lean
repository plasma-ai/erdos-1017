module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalCliqueRepresentative
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalOccupation
public import Erdos1017.Multipartite.MultipartiteLowDensity
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Physical law paying the two-head bare slack

This module constructs a physical law from independent heads, joined exterior
blocks and the singleton residual left after paying internal pairs, shows it
feasible for the whole graph demand with the bare-head parent as a dominated
order-two component, and proves it pays the signed original-dual bare-head
slack.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace Erdos1017.TwoCenterPhysicalSlack

open PhysicalPrimal PhysicalCliqueRepresentative

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite subprobability remainder has enough singleton mass to pay the
first marginal of all its genuine internal graph edges. -/
theorem graphDemand_fst_le_of_mass_le_one (η : Measure Ω) [IsFiniteMeasure η]
    (hη : η univ ≤ 1) (E : Set (Ω × Ω)) : (graphDemand η E).fst ≤ η := by
  calc
    (graphDemand η E).fst ≤ (η.prod η).fst := Measure.fst_mono Measure.restrict_le_self
    _ = η univ • η := Measure.map_fst_prod
    _ ≤ η := by
      intro A
      change η univ * η A ≤ η A
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hη (show (0 : ℝ≥0∞) ≤ η A from zero_le)

/-- The actual nonnegative one-vertex remainder law after all internal
pairs have been paid by the two-vertex law. -/
def singletonResidual (η : Measure Ω) (E : Set (Ω × Ω)) : Measure Ω :=
  η - (graphDemand η E).fst

/-- The singleton residual and paid pair marginal add exactly to the
original remainder measure, including a null remainder. -/
theorem singletonResidual_add_fst (η : Measure Ω) [IsFiniteMeasure η]
    (hη : η univ ≤ 1) (E : Set (Ω × Ω)) :
    singletonResidual η E + (graphDemand η E).fst = η := by
  have : IsFiniteMeasure (graphDemand η E) := inferInstanceAs (IsFiniteMeasure ((η.prod η).restrict E))
  have : IsFiniteMeasure (graphDemand η E).fst :=
    inferInstanceAs (IsFiniteMeasure ((graphDemand η E).map Prod.fst))
  exact Measure.sub_add_cancel_of_le (graphDemand_fst_le_of_mass_le_one η hη E)

/-- The actual singleton residual remains finite. -/
instance singletonResidual_finite (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω)) :
    IsFiniteMeasure (singletonResidual η E) := inferInstanceAs (IsFiniteMeasure (η - _))

/-- The singleton residual is absolutely continuous to the original
remainder law; its positivity follows from measure subtraction. -/
theorem singletonResidual_absolutelyContinuous (η : Measure Ω) (E : Set (Ω × Ω)) :
    singletonResidual η E ≪ η := Measure.absolutelyContinuous_of_le Measure.sub_le

/-- The bare-head probability of the explicit pair-compensated experiment. -/
def bareProbability (η : Measure Ω) (E : Set (Ω × Ω)) : ℝ :=
  1 - η.real univ + (graphDemand η E).real univ / 2

/-- The actual bare-head mass has the required Markov lower bound. -/
theorem bareProbability_lower_bound (η : Measure Ω) (E : Set (Ω × Ω)) :
    1 - η.real univ ≤ bareProbability η E := by
  dsimp only [bareProbability]
  linarith [measureReal_nonneg (μ := graphDemand η E) (s := univ)]

/-- Subprobability remainder mass makes the bare-head weight nonnegative. -/
theorem bareProbability_nonnegative (η : Measure Ω) [IsFiniteMeasure η]
    (hη : η univ ≤ 1) (E : Set (Ω × Ω)) : 0 ≤ bareProbability η E := by
  have hr : η.real univ ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top η _) (by norm_num)).mpr hη
  exact (sub_nonneg.mpr hr).trans (bareProbability_lower_bound η E)

/-- Adding an independently sampled head preserves the original finite
parent mass, even when the old law is not a probability. -/
theorem freshLaw_mass {n : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] : (freshLaw ν ρ).real univ = ρ.real univ := by
  simp only [freshLaw, measureReal_def, Measure.map_apply measurable_cons MeasurableSet.univ, preimage_univ]
  rw [← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]

/-- The new head's coordinate law is the entire old parent mass times its
actual independent sampling law. -/
theorem freshLaw_coordinate_zero {n : ℕ} (ν : Measure Ω)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] :
    (freshLaw ν ρ).map (fun v => v 0) = ρ univ • ν := by
  rw [freshLaw, Measure.map_map (measurable_pi_apply (0 : Fin (n + 1))) measurable_cons]
  change (ν.prod ρ).map Prod.fst = _
  exact Measure.map_fst_prod

/-- Old coordinate laws survive the independent probability head exactly. -/
theorem freshLaw_coordinate_succ {n : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i : Fin n) :
    (freshLaw ν ρ).map (fun v => v i.succ) = ρ.map (fun v => v i) := by
  rw [freshLaw, Measure.map_map (measurable_pi_apply i.succ) measurable_cons]
  change (ν.prod ρ).map ((fun v : Fin n → Ω => v i) ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_pi_apply i) measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul]

/-- First occupation records one fresh head for every original parent and
all the original vertices, without changing their original laws. -/
theorem firstOccupation_freshLaw {n : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] :
    orderFirstOccupation (n + 1) (freshLaw ν ρ) = ρ univ • ν + orderFirstOccupation n ρ := by
  rw [orderFirstOccupation, Fin.sum_univ_succ, freshLaw_coordinate_zero]
  simp_rw [freshLaw_coordinate_succ]
  rfl

private theorem prod_finsetSum {ι : Type*} [Fintype ι]
    (ν : Measure Ω) [SFinite ν] (η : ι → Measure Ω) [∀ i, SFinite (η i)] :
    ν.prod (∑ i, η i) = ∑ i, ν.prod (η i) := by
  rw [← Measure.sum_fintype, Measure.prod_sum_right, Measure.sum_fintype]

/-- Exact pair occupation of one independently adjoined head retains all
old pairs and both orientations of its actual first occupation. -/
theorem occupation_freshLaw {n : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] :
    orderOccupation (n + 1) (freshLaw ν ρ) = orderOccupation n ρ +
      ν.prod (orderFirstOccupation n ρ) + (ν.prod (orderFirstOccupation n ρ)).map Prod.swap := by
  have hreverse (j : Fin n) :
      (freshLaw ν ρ).map (fun v => (v j.succ, v 0)) =
        (ν.prod (ρ.map (fun v => v j))).map Prod.swap := by
    rw [← freshLaw_pair_zero_succ ν ρ j]
    exact (Measure.map_map measurable_swap
      ((measurable_pi_apply (0 : Fin (n + 1))).prodMk (measurable_pi_apply j.succ))).symm
  have hz (j : Fin n) : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  rw [orderOccupation_eq_sum]
  simp only [Fin.sum_univ_succ, ne_eq, not_true_eq_false, ite_false,
    hz, Fin.succ_ne_zero, not_false_eq_true, ite_true, zero_add,
    Fin.succ_inj, freshLaw_pair_succ_succ, freshLaw_pair_zero_succ, hreverse,
    Finset.sum_add_distrib]
  rw [← prod_finsetSum ν (fun j => ρ.map (fun v => v j))]
  rw [← Measure.map_finset_sum measurable_swap.aemeasurable,
    ← prod_finsetSum ν (fun j => ρ.map (fun v => v j))]
  rw [orderOccupation_eq_sum, orderFirstOccupation]
  ac_rfl


/-- The finite actual remainder graph demand. -/
instance graphDemand_finite (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω)) :
    IsFiniteMeasure (graphDemand η E) := inferInstanceAs (IsFiniteMeasure ((η.prod η).restrict E))

/-- Its actual first marginal is finite as well. -/
instance graphDemand_fst_finite (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω)) :
    IsFiniteMeasure (graphDemand η E).fst :=
  inferInstanceAs (IsFiniteMeasure ((graphDemand η E).map Prod.fst))

/-- Actual symmetry of the remainder edge relation preserves the complete
ordered graph demand, not merely its mass. -/
theorem graphDemand_swap (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω))
    (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E) :
    (graphDemand η E).map Prod.swap = graphDemand η E := by
  unfold graphDemand
  rw [← hsym, ← Measure.restrict_map measurable_swap hE, Measure.prod_swap]
  rw [hsym]

/-- A genuine singleton tuple retains its original one-point law. -/
def singletonLaw (η : Measure Ω) : Measure (Fin 1 → Ω) :=
  η.map (fun x _ => x)

private theorem measurable_singletonTuple : Measurable (fun x : Ω => (fun _ : Fin 1 => x)) :=
  Measurable.of_eval (fun _ => measurable_id')

instance singletonLaw_finite (η : Measure Ω) [IsFiniteMeasure η] : IsFiniteMeasure (singletonLaw η) :=
  Measure.isFiniteMeasure_map _ _

theorem singletonLaw_mass (η : Measure Ω) : (singletonLaw η).real univ = η.real univ := by
  simp only [singletonLaw, measureReal_def, Measure.map_apply measurable_singletonTuple MeasurableSet.univ,
    preimage_univ]

theorem singletonLaw_firstOccupation (η : Measure Ω) :
    orderFirstOccupation 1 (singletonLaw η) = η := by
  rw [orderFirstOccupation, Fin.sum_univ_one, singletonLaw,
    Measure.map_map (measurable_pi_apply (0 : Fin 1)) measurable_singletonTuple]
  exact Measure.map_id

theorem singletonLaw_occupation (η : Measure Ω) : orderOccupation 1 (singletonLaw η) = 0 := by
  simp only [orderOccupation_eq_sum, Fin.sum_univ_one, ne_eq, not_true_eq_false, ite_false]

/-- Half the actual directed internal graph demand is the two-point body law. -/
def pairLaw (η : Measure Ω) (E : Set (Ω × Ω)) : Measure (Fin 2 → Ω) :=
  edgeLaw ((2 : ℝ≥0∞)⁻¹ • graphDemand η E)

instance pairLaw_finite (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω)) :
    IsFiniteMeasure (pairLaw η E) := by
  have : IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • graphDemand η E) := Measure.smul_finite _ (by norm_num)
  exact Measure.isFiniteMeasure_map _ _

/-- Both orientations of the genuine two-vertex law cover the entire
internal graph demand exactly. -/
theorem pairLaw_occupation (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω))
    (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E) :
    orderOccupation 2 (pairLaw η E) = graphDemand η E := by
  rw [pairLaw, edgeLaw_occupation, Measure.map_smul _ measurable_swap.aemeasurable,
    graphDemand_swap η E hE hsym, ← add_smul]
  have hhalf : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [hhalf, one_smul]

/-- The two-point law uses exactly the directed demand's first marginal
as its summed vertex marginal, with no factor-of-two loss. -/
theorem pairLaw_firstOccupation (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω))
    (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E) :
    orderFirstOccupation 2 (pairLaw η E) = (graphDemand η E).fst := by
  have h := fst_orderOccupation 2 (pairLaw η E)
  rw [pairLaw_occupation η E hE hsym] at h
  simpa only [Nat.reduceSub, one_nsmul] using h.symm

/-- The two-vertex parent mass is half the actual directed edge mass. -/
theorem pairLaw_mass (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω)) :
    (pairLaw η E).real univ = (graphDemand η E).real univ / 2 := by
  rw [pairLaw, edgeLaw_mass]
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  ring

/-- The singleton residual's mass is the remaining first occupation. -/
theorem singletonResidual_mass (η : Measure Ω) [IsFiniteMeasure η] (hη : η univ ≤ 1)
    (E : Set (Ω × Ω)) :
    (singletonResidual η E).real univ = η.real univ - (graphDemand η E).real univ := by
  have h := congrArg (fun ν : Measure Ω => ν.real univ) (singletonResidual_add_fst η hη E)
  rw [measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)] at h
  have hfst : (graphDemand η E).fst.real univ = (graphDemand η E).real univ := by
    simp only [Measure.fst, measureReal_def, Measure.map_apply measurable_fst MeasurableSet.univ,
      preimage_univ]
  rw [hfst] at h
  linarith

/-- An actual empty remainder tuple supplies only bare-head parent mass. -/
def emptyLaw (η : Measure Ω) (E : Set (Ω × Ω)) : Measure (Fin 0 → Ω) :=
  ENNReal.ofReal (bareProbability η E) • Measure.dirac (fun i => Fin.elim0 i)

instance emptyLaw_finite (η : Measure Ω) (E : Set (Ω × Ω)) : IsFiniteMeasure (emptyLaw η E) :=
  Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem emptyLaw_mass (η : Measure Ω) [IsFiniteMeasure η] (hη : η univ ≤ 1)
    (E : Set (Ω × Ω)) : (emptyLaw η E).real univ = bareProbability η E := by
  simp only [emptyLaw, measureReal_def, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
    smul_eq_mul, mul_one, ENNReal.toReal_ofReal (bareProbability_nonnegative η hη E)]

theorem emptyLaw_firstOccupation (η : Measure Ω) (E : Set (Ω × Ω)) :
    orderFirstOccupation 0 (emptyLaw η E) = 0 := by simp [orderFirstOccupation]

theorem emptyLaw_occupation (η : Measure Ω) (E : Set (Ω × Ω)) :
    orderOccupation 0 (emptyLaw η E) = 0 := by simp [orderOccupation_eq_sum]

/-- The three genuine body laws have orders zero, one and two. -/
def bodyLaw (η : Measure Ω) (E : Set (Ω × Ω)) : (j : Fin 3) → Measure (Fin j.val → Ω) :=
  Fin.cases (emptyLaw η E) (Fin.cases (singletonLaw (singletonResidual η E))
    (Fin.cases (pairLaw η E) (fun i => Fin.elim0 i)))

instance bodyLaw_finite (η : Measure Ω) [IsFiniteMeasure η] (E : Set (Ω × Ω)) (j : Fin 3) :
    IsFiniteMeasure (bodyLaw η E j) := by
  fin_cases j
  · exact inferInstanceAs (IsFiniteMeasure (emptyLaw η E))
  · exact inferInstanceAs (IsFiniteMeasure (singletonLaw (singletonResidual η E)))
  · exact inferInstanceAs (IsFiniteMeasure (pairLaw η E))

/-- Actual zero/one/two body parent masses sum to exactly one. -/
theorem bodyLaw_mass (η : Measure Ω) [IsFiniteMeasure η] (hη : η univ ≤ 1) (E : Set (Ω × Ω)) :
    (∑ j : Fin 3, (bodyLaw η E j).real univ) = 1 := by
  rw [Fin.sum_univ_three]
  change (emptyLaw η E).real univ + (singletonLaw (singletonResidual η E)).real univ +
    (pairLaw η E).real univ = 1
  rw [emptyLaw_mass η hη E, singletonLaw_mass, singletonResidual_mass η hη E, pairLaw_mass]
  dsimp only [bareProbability]
  ring

/-- The actual summed body vertex law is precisely the original remainder. -/
theorem bodyLaw_firstOccupation (η : Measure Ω) [IsFiniteMeasure η] (hη : η univ ≤ 1)
    (E : Set (Ω × Ω)) (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E) :
    (∑ j : Fin 3, orderFirstOccupation j.val (bodyLaw η E j)) = η := by
  rw [Fin.sum_univ_three]
  change orderFirstOccupation 0 (emptyLaw η E) +
    orderFirstOccupation 1 (singletonLaw (singletonResidual η E)) + orderFirstOccupation 2 (pairLaw η E) = η
  rw [emptyLaw_firstOccupation, singletonLaw_firstOccupation, pairLaw_firstOccupation η E hE hsym,
    zero_add, singletonResidual_add_fst η hη E]

/-- All actual body edges have exactly their original directed demand. -/
theorem bodyLaw_occupation (η : Measure Ω) [IsFiniteMeasure η]
    (E : Set (Ω × Ω)) (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E) :
    (∑ j : Fin 3, orderOccupation j.val (bodyLaw η E j)) = graphDemand η E := by
  rw [Fin.sum_univ_three]
  change orderOccupation 0 (emptyLaw η E) +
    orderOccupation 1 (singletonLaw (singletonResidual η E)) + orderOccupation 2 (pairLaw η E) = _
  rw [emptyLaw_occupation, singletonLaw_occupation, pairLaw_occupation η E hE hsym, zero_add, zero_add]


/-- The total genuine body-parent mass is one also before taking real parts. -/
theorem bodyLaw_mass_ennreal (η : Measure Ω) [IsFiniteMeasure η] (hη : η univ ≤ 1)
    (E : Set (Ω × Ω)) : (∑ j : Fin 3, bodyLaw η E j univ) = 1 := by
  have hfinite : (∑ j : Fin 3, bodyLaw η E j univ) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top (bodyLaw η E j) univ)
  apply (ENNReal.toReal_eq_toReal_iff' hfinite (by norm_num)).mp
  rw [ENNReal.toReal_sum (fun j _ => measure_ne_top (bodyLaw η E j) _), ENNReal.toReal_one]
  exact bodyLaw_mass η hη E

/-- Actual first occupations add under independent head augmentation of a
finite family, with the true parent masses retained. -/
theorem firstOccupation_fresh_family {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (ρ : ∀ j, Measure (Fin (k j) → Ω)) [∀ j, IsFiniteMeasure (ρ j)]
    (ν : Measure Ω) [IsProbabilityMeasure ν] :
    (∑ j, orderFirstOccupation (k j + 1) (freshLaw ν (ρ j))) =
      (∑ j, ρ j univ) • ν + ∑ j, orderFirstOccupation (k j) (ρ j) := by
  simp only [firstOccupation_freshLaw, Finset.sum_add_distrib, ← Finset.sum_smul]

/-- Finite parents have finite actual first occupation. -/
instance orderFirstOccupation_finite {n : ℕ} (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (orderFirstOccupation n ρ) := by
  unfold orderFirstOccupation
  infer_instance

/-- Pair occupations add under actual independent head augmentation of a
finite family, preserving both fresh-old orientations. -/
theorem occupation_fresh_family {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (ρ : ∀ j, Measure (Fin (k j) → Ω)) [∀ j, IsFiniteMeasure (ρ j)]
    (ν : Measure Ω) [IsProbabilityMeasure ν] :
    (∑ j, orderOccupation (k j + 1) (freshLaw ν (ρ j))) =
      (∑ j, orderOccupation (k j) (ρ j)) + ν.prod (∑ j, orderFirstOccupation (k j) (ρ j)) +
        (ν.prod (∑ j, orderFirstOccupation (k j) (ρ j))).map Prod.swap := by
  simp only [occupation_freshLaw, Finset.sum_add_distrib]
  rw [← prod_finsetSum ν (fun j => orderFirstOccupation (k j) (ρ j)),
    ← Measure.map_finset_sum measurable_swap.aemeasurable,
    ← prod_finsetSum ν (fun j => orderFirstOccupation (k j) (ρ j))]

/-- Every physical parent always receives one independent sample from each
actual head, in addition to zero, one or two remainder vertices. -/
def headParent (σ₁ σ₂ η : Measure Ω) (E : Set (Ω × Ω)) (j : Fin 3) :
    Measure (Fin (j.val + 2) → Ω) := freshLaw σ₁ (freshLaw σ₂ (bodyLaw η E j))

instance headParent_finite (σ₁ σ₂ η : Measure Ω) [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    [IsFiniteMeasure η] (E : Set (Ω × Ω)) (j : Fin 3) : IsFiniteMeasure (headParent σ₁ σ₂ η E j) :=
  inferInstanceAs (IsFiniteMeasure (freshLaw σ₁ (freshLaw σ₂ (bodyLaw η E j))))

/-- The actual finite all-orders family has parents only at orders two,
three and four. -/
def laws (σ₁ σ₂ η : Measure Ω) (E : Set (Ω × Ω)) : Laws Ω :=
  assemble (fun j : Fin 3 => j.val + 2) (headParent σ₁ σ₂ η E)

instance laws_finite (σ₁ σ₂ η : Measure Ω) [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    [IsFiniteMeasure η] (E : Set (Ω × Ω)) (n : ℕ) : IsFiniteMeasure (laws σ₁ σ₂ η E n) :=
  assemble_finite _ _ n

/-- Independent head samples do not change any actual body-parent mass. -/
theorem headParent_mass (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁]
    [IsProbabilityMeasure σ₂] [IsFiniteMeasure η] (E : Set (Ω × Ω)) (j : Fin 3) :
    (headParent σ₁ σ₂ η E j).real univ = (bodyLaw η E j).real univ := by
  rw [headParent, freshLaw_mass, freshLaw_mass]

/-- The pair-compensated two-head law has exactly unit conic cost. -/
theorem laws_cost (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁] [IsProbabilityMeasure σ₂]
    [IsFiniteMeasure η] (hη : η univ ≤ 1) (E : Set (Ω × Ω)) : cost (laws σ₁ σ₂ η E) = 1 := by
  rw [laws, cost_assemble]
  simp_rw [headParent_mass]
  exact bodyLaw_mass η hη E

/-- No empty clique is introduced by the two-head construction. -/
theorem laws_zero (σ₁ σ₂ η : Measure Ω) (E : Set (Ω × Ω)) : laws σ₁ σ₂ η E 0 = 0 := by
  unfold laws assemble
  apply Finset.sum_eq_zero
  intro j _
  exact singleOrder_ne (j.val + 2) 0 _ (by omega)

/-- No singleton clique is introduced by the two-head construction. -/
theorem laws_one (σ₁ σ₂ η : Measure Ω) (E : Set (Ω × Ω)) : laws σ₁ σ₂ η E 1 = 0 := by
  unfold laws assemble
  apply Finset.sum_eq_zero
  intro j _
  exact singleOrder_ne (j.val + 2) 1 _ (by omega)

/-- The actual ordered demand includes all body edges, both head-body
orientations and both orientations of the two-head edge. -/
def demand (σ₁ σ₂ η : Measure Ω) (E : Set (Ω × Ω)) : Measure (Ω × Ω) :=
  graphDemand η E + σ₁.prod σ₂ + σ₂.prod σ₁ + σ₁.prod η + η.prod σ₁ + σ₂.prod η + η.prod σ₂

/-- Exact full pair balance of the constructed finite physical law. The
remainder is an arbitrary measurable symmetric graph, including clique dust. -/
theorem laws_occupation (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁]
    [IsProbabilityMeasure σ₂] [IsFiniteMeasure η] (hη : η univ ≤ 1)
    (E : Set (Ω × Ω)) (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E) :
    occupation (laws σ₁ σ₂ η E) = demand σ₁ σ₂ η E := by
  have hf : (∑ j : Fin 3, orderFirstOccupation (j.val + 1) (freshLaw σ₂ (bodyLaw η E j))) =
      σ₂ + η := by
    rw [firstOccupation_fresh_family (fun j : Fin 3 => j.val) (bodyLaw η E) σ₂,
      bodyLaw_mass_ennreal η hη E, one_smul, bodyLaw_firstOccupation η hη E hE hsym]
  have ho : (∑ j : Fin 3, orderOccupation (j.val + 1) (freshLaw σ₂ (bodyLaw η E j))) =
      graphDemand η E + σ₂.prod η + (σ₂.prod η).map Prod.swap := by
    rw [occupation_fresh_family (fun j : Fin 3 => j.val) (bodyLaw η E) σ₂,
      bodyLaw_occupation η E hE hsym, bodyLaw_firstOccupation η hη E hE hsym]
  rw [laws, occupation_assemble]
  change (∑ j : Fin 3, orderOccupation (j.val + 1 + 1)
    (freshLaw σ₁ (freshLaw σ₂ (bodyLaw η E j)))) = _
  rw [occupation_fresh_family (fun j : Fin 3 => j.val + 1)
    (fun j => freshLaw σ₂ (bodyLaw η E j)) σ₁, ho, hf,
    Measure.prod_add, Measure.map_add _ _ measurable_swap, Measure.prod_swap, Measure.prod_swap,
    Measure.prod_swap]
  unfold demand
  ac_rfl

/-- The genuine bare-head parent is a dominated order-two component of the
actual physical partition, before any clique-test comparison. -/
theorem bareParent_le (σ₁ σ₂ η : Measure Ω) (E : Set (Ω × Ω)) :
    headParent σ₁ σ₂ η E 0 ≤ laws σ₁ σ₂ η E 2 := by
  change headParent σ₁ σ₂ η E 0 ≤ ∑ j : Fin 3,
    singleOrder (j.val + 2) (headParent σ₁ σ₂ η E j) 2
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => singleOrder (j.val + 2) (headParent σ₁ σ₂ η E j) 2)
    (fun _ _ => by intro A; exact zero_le) (Finset.mem_univ (0 : Fin 3))
  simpa only [Fin.val_zero, Nat.zero_add, singleOrder_self] using h

/-- The bare parent's full ordered pair law is exactly its scalar mass
times the two true conditional-head product orientations. -/
theorem bareParent_occupation (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁]
    [IsProbabilityMeasure σ₂] [IsFiniteMeasure η] (E : Set (Ω × Ω)) :
    orderOccupation 2 (headParent σ₁ σ₂ η E 0) =
      ENNReal.ofReal (bareProbability η E) • (σ₁.prod σ₂ + σ₂.prod σ₁) := by
  change orderOccupation (0 + 1 + 1) (freshLaw σ₁ (freshLaw σ₂ (emptyLaw η E))) = _
  rw [occupation_freshLaw, occupation_freshLaw, firstOccupation_freshLaw,
    emptyLaw_firstOccupation, emptyLaw_occupation]
  simp only [Measure.prod_zero, Measure.map_zero, add_zero, zero_add]
  have he : emptyLaw η E univ = ENNReal.ofReal (bareProbability η E) := by simp [emptyLaw]
  rw [he, Measure.prod_smul_right, Measure.map_smul _ measurable_swap.aemeasurable,
    Measure.prod_swap, smul_add]

/-- The bare-parent mass is its actual displayed probability. -/
theorem bareParent_mass (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁]
    [IsProbabilityMeasure σ₂] [IsFiniteMeasure η] (hη : η univ ≤ 1) (E : Set (Ω × Ω)) :
    (headParent σ₁ σ₂ η E 0).real univ = bareProbability η E := by
  rw [headParent_mass]
  exact emptyLaw_mass η hη E


private theorem restrict_prod_reverse {σ τ : Measure Ω} [SFinite σ] [SFinite τ]
    {E : Set (Ω × Ω)} (hsym : Prod.swap ⁻¹' E = E) (h : ∀ᵐ p ∂σ.prod τ, p ∈ E) :
    ∀ᵐ p ∂τ.prod σ, p ∈ E := by
  have hswap := (Measure.measurePreserving_swap (μ := τ) (ν := σ)).quasiMeasurePreserving.ae h
  simpa only [← mem_preimage, hsym] using hswap

/-- Independent heads and actual joined exterior blocks identify the exact
full graph demand of the normalized three-component vertex measure. -/
theorem graphDemand_two_heads (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁]
    [IsProbabilityMeasure σ₂] [IsFiniteMeasure η] (E : Set (Ω × Ω))
    (hsym : Prod.swap ⁻¹' E = E)
    (h₁₁ : ∀ᵐ p ∂σ₁.prod σ₁, p ∉ E) (h₂₂ : ∀ᵐ p ∂σ₂.prod σ₂, p ∉ E)
    (h₁₂ : ∀ᵐ p ∂σ₁.prod σ₂, p ∈ E) (h₁R : ∀ᵐ p ∂σ₁.prod η, p ∈ E)
    (h₂R : ∀ᵐ p ∂σ₂.prod η, p ∈ E) :
    graphDemand (σ₁ + σ₂ + η) E = demand σ₁ σ₂ η E := by
  have hzero₁ : (σ₁.prod σ₁).restrict E = 0 :=
    Measure.restrict_eq_zero.mpr (compl_mem_ae_iff.mp h₁₁)
  have hzero₂ : (σ₂.prod σ₂).restrict E = 0 :=
    Measure.restrict_eq_zero.mpr (compl_mem_ae_iff.mp h₂₂)
  have h₂₁ := restrict_prod_reverse hsym h₁₂
  have hR₁ := restrict_prod_reverse hsym h₁R
  have hR₂ := restrict_prod_reverse hsym h₂R
  unfold graphDemand
  simp only [Measure.add_prod, Measure.prod_add, Measure.restrict_add]
  rw [hzero₁, hzero₂, Measure.restrict_eq_self_of_ae_mem h₁₂,
    Measure.restrict_eq_self_of_ae_mem h₂₁, Measure.restrict_eq_self_of_ae_mem h₁R,
    Measure.restrict_eq_self_of_ae_mem h₂R, Measure.restrict_eq_self_of_ae_mem hR₁,
    Measure.restrict_eq_self_of_ae_mem hR₂]
  unfold demand graphDemand
  ac_rfl

/-- The constructed law is genuinely feasible for the entire graph demand
under the concrete independent-head and joined-block hypotheses. -/
theorem laws_feasible (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁]
    [IsProbabilityMeasure σ₂] [IsFiniteMeasure η] (hη : η univ ≤ 1)
    (E : Set (Ω × Ω)) (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E)
    (h₁₁ : ∀ᵐ p ∂σ₁.prod σ₁, p ∉ E) (h₂₂ : ∀ᵐ p ∂σ₂.prod σ₂, p ∉ E)
    (h₁₂ : ∀ᵐ p ∂σ₁.prod σ₂, p ∈ E) (h₁R : ∀ᵐ p ∂σ₁.prod η, p ∈ E)
    (h₂R : ∀ᵐ p ∂σ₂.prod η, p ∈ E) :
    Feasible (fun x y => (x, y) ∈ E) (graphDemand (σ₁ + σ₂ + η) E) (laws σ₁ σ₂ η E) := by
  have hb : occupation (laws σ₁ σ₂ η E) = graphDemand (σ₁ + σ₂ + η) E := by
    rw [laws_occupation σ₁ σ₂ η hη E hE hsym,
      graphDemand_two_heads σ₁ σ₂ η E hsym h₁₁ h₂₂ h₁₂ h₁R h₂R]
  exact ⟨laws_zero σ₁ σ₂ η E, laws_one σ₁ σ₂ η E,
    fun n => ae_all_pairs_of_balance _ _ hb (fun p => p ∈ E) (ae_restrict_mem hE) n, hb⟩

/-- The conditional two-head charge, retaining both actual pair orientations. -/
def headPairMean (σ₁ σ₂ : Measure Ω) (Y : Ω × Ω → ℝ) : ℝ :=
  ((∫ p, Y p ∂σ₁.prod σ₂) + ∫ p, Y p ∂σ₂.prod σ₁) / 2

/-- The constructed physical law pays the signed old-dual bare-head
slack. Every charge test is required under these actual parents. -/
theorem objective_le_bare_slack (σ₁ σ₂ η : Measure Ω) [IsProbabilityMeasure σ₁]
    [IsProbabilityMeasure σ₂] [IsFiniteMeasure η] (hη : η univ ≤ 1)
    (E : Set (Ω × Ω)) (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E)
    (Y : Ω × Ω → ℝ) (hY : Integrable Y (demand σ₁ σ₂ η E))
    (hY₁₂ : Integrable Y (σ₁.prod σ₂)) (hY₂₁ : Integrable Y (σ₂.prod σ₁))
    (htest : ∀ n, ∀ᵐ v ∂laws σ₁ σ₂ η E n, charge Y v ≤ 1) :
    (∫ p, Y p ∂demand σ₁ σ₂ η E) / 2 ≤
      1 - bareProbability η E * (1 - headPairMean σ₁ σ₂ Y) := by
  let ρ := laws σ₁ σ₂ η E
  let β : Measure (Fin 2 → Ω) := headParent σ₁ σ₂ η E 0
  have hb := laws_occupation σ₁ σ₂ η hη E hE hsym
  have : IsFiniteMeasure (demand σ₁ σ₂ η E) := by unfold demand; infer_instance
  have htotal : Integrable Y (occupation ρ) := by rw [hb]; exact hY
  have hi₂ := htotal.mono_measure (Measure.le_sum (fun n => orderOccupation n (ρ n)) 2)
  have hcharge₂ := integral_charge 2 (ρ 2) Y hi₂
  have hiβ : Integrable Y (orderOccupation 2 β) := by
    rw [bareParent_occupation σ₁ σ₂ η E]
    exact (hY₁₂.add_measure hY₂₁).smul_measure ENNReal.ofReal_ne_top
  have hchargeβ := integral_charge 2 β Y hiβ
  have hbare : (∫ v, 1 - charge Y v ∂β) =
      bareProbability η E * (1 - headPairMean σ₁ σ₂ Y) := by
    rw [integral_sub (integrable_const 1) hchargeβ.1, integral_const, smul_eq_mul, mul_one,
      hchargeβ.2, bareParent_mass σ₁ σ₂ η hη E, bareParent_occupation σ₁ σ₂ η E,
      integral_smul_measure, integral_add_measure hY₁₂ hY₂₁,
      ENNReal.toReal_ofReal (bareProbability_nonnegative η hη E)]
    dsimp only [headPairMean]
    ring
  have hnonneg : ∀ᵐ v ∂ρ 2, 0 ≤ 1 - charge Y v := (htest 2).mono (fun _ hv => sub_nonneg.mpr hv)
  have hle : β ≤ ρ 2 := bareParent_le σ₁ σ₂ η E
  have hmono := integral_mono_measure hle hnonneg
    ((integrable_const 1).sub hcharge₂.1)
  have hgap := integral_slack_le_gap ρ (demand σ₁ σ₂ η E) Y
    (laws_zero σ₁ σ₂ η E) (laws_one σ₁ σ₂ η E) hb hY htest 2
  have horder : (∫ v, 1 - charge Y v ∂ρ 2) =
      (ρ 2).real univ - (∫ p, Y p ∂orderOccupation 2 (ρ 2)) / 2 := by
    rw [integral_sub (integrable_const 1) hcharge₂.1, integral_const, smul_eq_mul, mul_one, hcharge₂.2]
  rw [hbare, horder] at hmono
  rw [laws_cost σ₁ σ₂ η hη E] at hgap
  linarith

end Erdos1017.TwoCenterPhysicalSlack

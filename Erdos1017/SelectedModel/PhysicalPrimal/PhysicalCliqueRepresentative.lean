module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPartitionAverages
public import Erdos1017.Multipartite.Physical.PhysicalPrimalDuality
public import Erdos1017.Multipartite.Physical.PhysicalCellLift
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Common pair-null exception for physical clique orders

The exception is derived from finite-cell averaging, rather than assumed as a
certificate or obtained from physical-primal attainment.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalCliqueRepresentative

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalized restriction used for an independent sample inside one cell. -/
def cellLaw (μ : Measure Ω) (s : Set Ω) : Measure Ω := (μ s)⁻¹ • μ.restrict s

theorem cellLaw_probability (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω)
    (hs : μ s ≠ 0) : IsProbabilityMeasure (cellLaw μ s) := by
  constructor
  simp only [cellLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hs (measure_ne_top _ _)

theorem cellLaw_absolutelyContinuous (μ : Measure Ω) (s : Set Ω) : cellLaw μ s ≪ μ :=
  Measure.absolutelyContinuous_restrict.smul_left _

/-- Absolute continuity holds for independent coordinates with different laws. -/
theorem pi_absolutelyContinuous (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∀ {n : ℕ} (ν : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)],
      (∀ i, ν i ≪ μ) → Measure.pi ν ≪ Measure.pi (fun _ : Fin n => μ) := by
  intro n
  induction n with
  | zero =>
    intro ν _ hν
    rw [Measure.pi_of_empty _ (fun i : Fin 0 => Fin.elim0 i),
      Measure.pi_of_empty _ (fun i : Fin 0 => Fin.elim0 i)]
  | succ n ih =>
    intro ν _ hν
    have htail := ih (fun i => ν i.succ) (fun i => hν i.succ)
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0).symm
    have h := e.measurableEmbedding.absolutelyContinuous_map ((hν 0).prod htail)
    have hbase := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hsample := (measurePreserving_piFinSuccAbove ν 0).symm
    rw [← hbase.map_eq, ← hsample.map_eq]
    exact h

/-- Product sampling in two cells has exactly the literal product-cell average. -/
theorem integral_cellLaw_prod (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s t : Set Ω) (hs0 : μ s ≠ 0) (ht0 : μ t ≠ 0) (f : Ω × Ω → ℝ) :
    (∫ z, f z ∂(cellLaw μ s).prod (cellLaw μ t)) = ⨍ z in s ×ˢ t, f z ∂μ.prod μ := by
  unfold cellLaw average
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict]
  simp only [Measure.restrict_apply_univ, Measure.prod_prod]
  rw [ENNReal.mul_inv (Or.inl hs0) (Or.inr ht0)]

/-- The Boolean edge kernel as an actual bounded real function. -/
def edgeIndicator (G : Ω × Ω → Bool) (z : Ω × Ω) : ℝ := if G z then 1 else 0

theorem measurable_edgeIndicator {G : Ω × Ω → Bool} (hG : Measurable G) :
    Measurable (edgeIndicator G) :=
  (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp hG

omit [MeasurableSpace Ω] in
theorem edgeIndicator_bounds (G : Ω × Ω → Bool) (z : Ω × Ω) :
    edgeIndicator G z ∈ Icc (0 : ℝ) 1 := by
  unfold edgeIndicator
  split <;> norm_num

/-- Actual clique membership uses every distinct ordered coordinate pair. -/
def Clique (G : Ω × Ω → Bool) {n : ℕ} (v : Fin n → Ω) : Prop :=
  ∀ i j, i ≠ j → G (v i, v j) = true

/-- A finite ordered nonedge count controls the entire nonclique event. -/
def missingPairs (G : Ω × Ω → Bool) {n : ℕ} (v : Fin n → Ω) : ℝ :=
  ∑ ij : PhysicalPrimal.PairIndex n, (1 - edgeIndicator G (v ij.val.1, v ij.val.2))

omit [MeasurableSpace Ω] in
theorem missingPairs_nonneg (G : Ω × Ω → Bool) {n : ℕ} (v : Fin n → Ω) :
    0 ≤ missingPairs G v := by
  unfold missingPairs
  exact Finset.sum_nonneg (fun ij _ => sub_nonneg.mpr (edgeIndicator_bounds G _).2)

omit [MeasurableSpace Ω] in
theorem one_le_missingPairs_of_not_clique (G : Ω × Ω → Bool) {n : ℕ}
    (v : Fin n → Ω) (hv : ¬Clique G v) : 1 ≤ missingPairs G v := by
  classical
  simp only [Clique, not_forall] at hv
  obtain ⟨i, j, hij, hG⟩ := hv
  have hfalse : G (v i, v j) = false := Bool.eq_false_iff.mpr hG
  have hle := Finset.single_le_sum
    (s := (Finset.univ : Finset (PhysicalPrimal.PairIndex n)))
    (f := fun ij => 1 - edgeIndicator G (v ij.val.1, v ij.val.2))
    (fun ij _ => sub_nonneg.mpr (edgeIndicator_bounds G _).2)
    (Finset.mem_univ (⟨(i, j), hij⟩ : PhysicalPrimal.PairIndex n))
  simpa only [missingPairs, edgeIndicator, hfalse, Bool.false_eq_true, ↓reduceIte, sub_zero] using hle

omit [MeasurableSpace Ω] in
/-- Bounded charges and the actual clique test imply an integrable
pointwise penalty for every missing pair. -/
theorem charge_le_missing_penalty (G : Ω × Ω → Bool) (Y : Ω × Ω → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hY : ∀ z, |Y z| ≤ b) {n : ℕ}
    (v : Fin n → Ω) (hclique : Clique G v → PhysicalPrimal.charge Y v ≤ 1) :
    PhysicalPrimal.charge Y v ≤ 1 +
      ((Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b + 1) * missingPairs G v := by
  have hcharge : PhysicalPrimal.charge Y v ≤
      (Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b := by
    have hsum : (∑ ij : PhysicalPrimal.PairIndex n, Y (v ij.val.1, v ij.val.2)) ≤
        (Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b := by
      simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (PhysicalPrimal.PairIndex n)))
        (f := fun ij => Y (v ij.val.1, v ij.val.2)) (g := fun _ => b)
        (fun ij _ => (le_abs_self _).trans (hY _))
    unfold PhysicalPrimal.charge
    have hnonneg : 0 ≤ (Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b := by positivity
    linarith
  by_cases hv : Clique G v
  · have hprod := mul_nonneg
      (show 0 ≤ (Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b + 1 by positivity)
      (missingPairs_nonneg G v)
    linarith [hclique hv]
  · have hmissing := one_le_missingPairs_of_not_clique G v hv
    have hprod := mul_nonneg
      (show 0 ≤ (Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b + 1 by positivity)
      (show 0 ≤ missingPairs G v - 1 by linarith)
    linarith

/-- Bounded measurable real functions are integrable under any probability law. -/
theorem integrable_of_bounded (ν : Measure Ω) [IsProbabilityMeasure ν]
    {f : Ω → ℝ} (hf : Measurable f) (b : ℝ) (hbound : ∀ x, |f x| ≤ b) :
    Integrable f ν := by
  apply Integrable.of_bound hf.aestronglyMeasurable b
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x)

/-- Each distinct sampled coordinate pair has its full product marginal. -/
theorem integral_pair_coordinates {n : ℕ} (ν : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (ν i)] {f : Ω × Ω → ℝ} (hf : Measurable f)
    (ij : PhysicalPrimal.PairIndex n) :
    (∫ v, f (v ij.val.1, v ij.val.2) ∂Measure.pi ν) =
      ∫ z, f z ∂(ν ij.val.1).prod (ν ij.val.2) := by
  have hmap := PhysicalCellLift.pair_map ν ij.val.1 ij.val.2 ij.prop
  rw [← hmap]
  exact (integral_map ((measurable_pi_apply _).prodMk
    (measurable_pi_apply _)).aemeasurable hf.aestronglyMeasurable).symm

/-- The expected actual charge is the sum of its true product pair integrals. -/
theorem integral_charge_pi {n : ℕ} (ν : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (ν i)] {Y : Ω × Ω → ℝ} (hY : Measurable Y)
    (b : ℝ) (hbound : ∀ z, |Y z| ≤ b) :
    (∫ v, PhysicalPrimal.charge Y v ∂Measure.pi ν) =
      (∑ ij : PhysicalPrimal.PairIndex n, ∫ z, Y z ∂(ν ij.val.1).prod (ν ij.val.2)) / 2 := by
  have hint (ij : PhysicalPrimal.PairIndex n) :
      Integrable (fun v : Fin n → Ω => Y (v ij.val.1, v ij.val.2)) (Measure.pi ν) :=
    integrable_of_bounded _ (hY.comp ((measurable_pi_apply _).prodMk
      (measurable_pi_apply _))) b (fun v => hbound _)
  unfold PhysicalPrimal.charge
  rw [integral_div, integral_finsetSum _ (fun ij _ => hint ij)]
  congr 1
  exact Finset.sum_congr rfl (fun ij _ => integral_pair_coordinates ν hY ij)

/-- The expected ordered nonedge count is the sum of the product-cell deficits. -/
theorem integral_missingPairs_pi {n : ℕ} (ν : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (ν i)] {G : Ω × Ω → Bool} (hG : Measurable G) :
    (∫ v, missingPairs G v ∂Measure.pi ν) =
      ∑ ij : PhysicalPrimal.PairIndex n,
        (1 - ∫ z, edgeIndicator G z ∂(ν ij.val.1).prod (ν ij.val.2)) := by
  have hbound (z : Ω × Ω) : |edgeIndicator G z| ≤ 1 := by
    rw [abs_of_nonneg (edgeIndicator_bounds G z).1]
    exact (edgeIndicator_bounds G z).2
  have hint (ij : PhysicalPrimal.PairIndex n) :
      Integrable (fun v : Fin n → Ω => edgeIndicator G (v ij.val.1, v ij.val.2)) (Measure.pi ν) :=
    integrable_of_bounded _ ((measurable_edgeIndicator hG).comp
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))) 1 (fun v => hbound _)
  unfold missingPairs
  have hshift (ij : PhysicalPrimal.PairIndex n) :
      Integrable (fun v : Fin n → Ω => 1 - edgeIndicator G (v ij.val.1, v ij.val.2))
        (Measure.pi ν) := (integrable_const 1).sub (hint ij)
  rw [integral_finsetSum _ (fun ij _ => hshift ij)]
  apply Finset.sum_congr rfl
  intro ij _
  rw [integral_sub (integrable_const 1) (hint ij), integral_pair_coordinates ν (measurable_edgeIndicator hG)]
  simp

section PartitionSampling

variable [CountablyGenerated Ω]

/-- Independent sampling in the containing positive-measure cells turns
product-almost-everywhere clique tests into a bound on literal averages. -/
theorem cell_average_charge_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Ω × Ω → Bool} {Y : Ω × Ω → ℝ} (hG : Measurable G) (hY : Measurable Y)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Y z| ≤ b)
    {n : ℕ} (htest : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    (v : Fin n → Ω) (m : ℕ)
    (hcell : ∀ i, μ (countablePartitionSet m (v i)) ≠ 0) :
    (∑ ij : PhysicalPrimal.PairIndex n,
      PhysicalPartitionAverages.cellAverage μ m Y (v ij.val.1, v ij.val.2)) / 2 ≤
      1 + ((Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b + 1) *
        ∑ ij : PhysicalPrimal.PairIndex n,
          (1 - PhysicalPartitionAverages.cellAverage μ m (edgeIndicator G)
            (v ij.val.1, v ij.val.2)) := by
  let ν : Fin n → Measure Ω := fun i => cellLaw μ (countablePartitionSet m (v i))
  have hν (i : Fin n) : IsProbabilityMeasure (ν i) := cellLaw_probability μ _ (hcell i)
  have hac : Measure.pi ν ≪ Measure.pi (fun _ : Fin n => μ) :=
    pi_absolutelyContinuous μ ν (fun i => cellLaw_absolutelyContinuous μ _)
  have hpoint : ∀ᵐ w ∂Measure.pi ν, PhysicalPrimal.charge Y w ≤ 1 +
      ((Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b + 1) * missingPairs G w := by
    filter_upwards [hac.ae_le htest] with w hw
    exact charge_le_missing_penalty G Y b hb hbound w hw
  have hYint : Integrable (PhysicalPrimal.charge Y) (Measure.pi ν) := by
    unfold PhysicalPrimal.charge
    apply Integrable.div_const
    apply integrable_finsetSum
    intro ij _
    exact integrable_of_bounded _ (hY.comp ((measurable_pi_apply _).prodMk
      (measurable_pi_apply _))) b (fun _ => hbound _)
  have hmissing : Integrable (missingPairs G) (Measure.pi ν) := by
    unfold missingPairs
    apply integrable_finsetSum
    intro ij _
    apply (integrable_const 1).sub
    apply integrable_of_bounded _ ((measurable_edgeIndicator hG).comp
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))) 1
    intro w
    change |edgeIndicator G (w ij.val.1, w ij.val.2)| ≤ 1
    rw [abs_of_nonneg (edgeIndicator_bounds G _).1]
    exact (edgeIndicator_bounds G _).2
  have hle := integral_mono_ae hYint ((integrable_const 1).add
    (hmissing.const_mul _)) hpoint
  dsimp only [Pi.add_apply] at hle
  rw [integral_add (integrable_const 1) (hmissing.const_mul _),
    integral_const_mul, integral_charge_pi ν hY b hbound, integral_missingPairs_pi ν hG] at hle
  have havg (f : Ω × Ω → ℝ) (ij : PhysicalPrimal.PairIndex n) :
      (∫ z, f z ∂(ν ij.val.1).prod (ν ij.val.2)) =
        PhysicalPartitionAverages.cellAverage μ m f (v ij.val.1, v ij.val.2) :=
    integral_cellLaw_prod μ _ _ (hcell _) (hcell _) f
  simp_rw [havg] at hle
  simpa using hle

/-- Pairwise regularity is built from the actual containing cells and
convergence of their two literal pair-function averages. -/
def PairRegular (μ : Measure Ω) (G : Ω × Ω → Bool) (Y : Ω × Ω → ℝ)
    (z : Ω × Ω) : Prop :=
  (∀ m, μ (countablePartitionSet m z.1) ≠ 0) ∧
    (∀ m, μ (countablePartitionSet m z.2) ≠ 0) ∧
    Tendsto (fun m => PhysicalPartitionAverages.cellAverage μ m (edgeIndicator G) z)
      atTop (nhds (edgeIndicator G z)) ∧
    Tendsto (fun m => PhysicalPartitionAverages.cellAverage μ m Y z) atTop (nhds (Y z))

/-- Martingale convergence and positive cell masses derive pair regularity. -/
theorem ae_pairRegular (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Ω × Ω → Bool} {Y : Ω × Ω → ℝ} (hG : Measurable G) (hY : Measurable Y)
    (b : ℝ) (hbound : ∀ z, |Y z| ≤ b) : ∀ᵐ z ∂μ.prod μ, PairRegular μ G Y z := by
  have hpos := PhysicalPartitionAverages.ae_positive_cells μ
  have hfst : ∀ᵐ z ∂μ.prod μ, ∀ m, μ (countablePartitionSet m z.1) ≠ 0 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hpos
  have hsnd : ∀ᵐ z ∂μ.prod μ, ∀ m, μ (countablePartitionSet m z.2) ≠ 0 :=
    measurePreserving_snd.quasiMeasurePreserving.ae hpos
  have hGbound (z : Ω × Ω) : |edgeIndicator G z| ≤ 1 := by
    rw [abs_of_nonneg (edgeIndicator_bounds G z).1]
    exact (edgeIndicator_bounds G z).2
  have hg := PhysicalPartitionAverages.ae_tendsto_cellAverage μ
    (integrable_of_bounded _ (measurable_edgeIndicator hG) 1 hGbound)
    (measurable_edgeIndicator hG).stronglyMeasurable
  have hy := PhysicalPartitionAverages.ae_tendsto_cellAverage μ
    (integrable_of_bounded _ hY b hbound) hY.stronglyMeasurable
  filter_upwards [hfst, hsnd, hg, hy] with z hz1 hz2 hzg hzy
  exact ⟨hz1, hz2, hzg, hzy⟩

/-- Product-almost-everywhere clique feasibility implies pointwise feasibility
at every finite tuple whose coordinate pairs are regular. -/
theorem charge_le_of_pairRegular (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Ω × Ω → Bool} {Y : Ω × Ω → ℝ} (hG : Measurable G) (hY : Measurable Y)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Y z| ≤ b)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    (n : ℕ) (v : Fin n → Ω) (hv : Clique G v)
    (hregular : ∀ i j, i ≠ j → PairRegular μ G Y (v i, v j)) :
    PhysicalPrimal.charge Y v ≤ 1 := by
  classical
  by_cases hn : 2 ≤ n
  · have hcell (m : ℕ) (i : Fin n) : μ (countablePartitionSet m (v i)) ≠ 0 := by
      by_cases hi : i = ⟨0, by omega⟩
      · exact (hregular i ⟨1, by omega⟩ (by
          intro heq
          have hval := congrArg Fin.val heq
          rw [hi] at hval
          norm_num at hval)).1 m
      · exact (hregular i ⟨0, by omega⟩ hi).1 m
    have hleft : Tendsto (fun m =>
        (∑ ij : PhysicalPrimal.PairIndex n,
          PhysicalPartitionAverages.cellAverage μ m Y (v ij.val.1, v ij.val.2)) / 2)
        atTop (nhds (PhysicalPrimal.charge Y v)) := by
      exact (tendsto_finsetSum Finset.univ (fun ij _ =>
        (hregular ij.val.1 ij.val.2 ij.prop).2.2.2)).div_const 2
    have hdeficit (ij : PhysicalPrimal.PairIndex n) :
        Tendsto (fun m => 1 - PhysicalPartitionAverages.cellAverage μ m (edgeIndicator G)
          (v ij.val.1, v ij.val.2)) atTop (nhds (0 : ℝ)) := by
      have ht := (hregular ij.val.1 ij.val.2 ij.prop).2.2.1
      have heq : edgeIndicator G (v ij.val.1, v ij.val.2) = 1 := by
        simp only [edgeIndicator, hv _ _ ij.prop, ↓reduceIte]
      rw [heq] at ht
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub ht
    have hsum := tendsto_finsetSum Finset.univ (fun ij _ => hdeficit ij)
    have hright : Tendsto (fun m => 1 +
        ((Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * b + 1) *
          ∑ ij : PhysicalPrimal.PairIndex n,
            (1 - PhysicalPartitionAverages.cellAverage μ m (edgeIndicator G)
              (v ij.val.1, v ij.val.2))) atTop (nhds (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hsum)
    exact le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall
      (fun m => cell_average_charge_bound μ hG hY b hb hbound (htest n hn) v m (hcell m)))
  · have hpair : IsEmpty (PhysicalPrimal.PairIndex n) := ⟨fun ij => by
      apply ij.prop
      apply Fin.ext
      have hi := ij.val.1.isLt
      have hj := ij.val.2.isLt
      omega⟩
    simp [PhysicalPrimal.charge]

/-- A single symmetric measurable pair-null set licenses every finite order.
It is constructed from the actual partition martingales, not supplied. -/
theorem exists_common_pair_null [MeasurableEq Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {G : Ω × Ω → Bool} {Y : Ω × Ω → ℝ} (hG : Measurable G) (hY : Measurable Y)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Y z| ≤ b)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      Clique G v → PhysicalPrimal.charge Y v ≤ 1) :
    ∃ Z : Set (Ω × Ω), MeasurableSet Z ∧ (μ.prod μ) Z = 0 ∧
      (∀ z, z ∈ Z ↔ z.swap ∈ Z) ∧ diagonal Ω ⊆ Z ∧
      ∀ n (v : Fin n → Ω), Clique G v →
        (∀ i j, i ≠ j → (v i, v j) ∉ Z) → PhysicalPrimal.charge Y v ≤ 1 := by
  let B := toMeasurable (μ.prod μ) {z | ¬PairRegular μ G Y z}
  have hB : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : (μ.prod μ) B = 0 := by
    rw [measure_toMeasurable]
    exact (ae_iff.mp (ae_pairRegular μ hG hY b hbound))
  let Z := (B ∪ Prod.swap ⁻¹' B) ∪ diagonal Ω
  have hZ : MeasurableSet Z := (hB.union (hB.preimage measurable_swap)).union measurableSet_diagonal
  have hswap0 : (μ.prod μ) (Prod.swap ⁻¹' B) = 0 := by
    rw [← Measure.map_apply measurable_swap hB, Measure.prod_swap]
    exact hB0
  have hZ0 : (μ.prod μ) Z = 0 :=
    measure_union_null (measure_union_null hB0 hswap0) (PhysicalCellLift.product_diagonal_null μ)
  refine ⟨Z, hZ, hZ0, ?_, ?_, ?_⟩
  · intro z
    simp only [Z, mem_union, mem_preimage, Prod.swap_swap, mem_diagonal_iff]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h.symm
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h.symm
  · exact subset_union_right
  · intro n v hv havoid
    apply charge_le_of_pairRegular μ hG hY b hb hbound htest n v hv
    intro i j hij
    by_contra hbad
    apply havoid i j hij
    apply Or.inl
    apply Or.inl
    exact subset_toMeasurable (μ.prod μ) _ hbad

/-- The actual representatives obtained by deleting the one common exception. -/
def removeExceptionEdges (G : Ω × Ω → Bool) (Z : Set (Ω × Ω)) (z : Ω × Ω) : Bool := by
  classical
  exact if z ∈ Z then false else G z

def removeExceptionColor (Y : Ω × Ω → ℝ) (Z : Set (Ω × Ω)) (z : Ω × Ω) : ℝ := by
  classical
  exact if z ∈ Z then 0 else Y z

/-- Actual symmetric measurable representatives satisfy all finite clique
tests everywhere, with their original bounds and support retained. -/
theorem exists_everywhere_representative [MeasurableEq Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {G : Ω × Ω → Bool} {Y : Ω × Ω → ℝ} (hG : Measurable G) (hY : Measurable Y)
    (hGsym : ∀ z, G z.swap = G z) (hYsym : ∀ z, Y z.swap = Y z)
    (hsupport : ∀ z, G z = false → Y z = 0)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Y z| ≤ b)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      Clique G v → PhysicalPrimal.charge Y v ≤ 1) :
    ∃ (G' : Ω × Ω → Bool) (Y' : Ω × Ω → ℝ),
      Measurable G' ∧ Measurable Y' ∧ G' =ᵐ[μ.prod μ] G ∧ Y' =ᵐ[μ.prod μ] Y ∧
      (∀ z, G' z.swap = G' z) ∧ (∀ z, Y' z.swap = Y' z) ∧
      (∀ x, G' (x, x) = false) ∧ (∀ z, G' z = false → Y' z = 0) ∧
      (∀ z, |Y' z| ≤ b) ∧ ∀ n (v : Fin n → Ω), Clique G' v → PhysicalPrimal.charge Y' v ≤ 1 := by
  classical
  obtain ⟨Z, hZ, hZ0, hZsym, hdiag, hlicense⟩ :=
    exists_common_pair_null μ hG hY b hb hbound htest
  let G' := removeExceptionEdges G Z
  let Y' := removeExceptionColor Y Z
  have havoid : ∀ᵐ z ∂μ.prod μ, z ∉ Z := compl_mem_ae_iff.mpr hZ0
  refine ⟨G', Y', measurable_const.ite hZ hG, measurable_const.ite hZ hY, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [havoid] with z hz
    exact ite_eq_right hz
  · filter_upwards [havoid] with z hz
    exact ite_eq_right hz
  · intro z
    by_cases hz : z ∈ Z
    · have hzs := (hZsym z).mp hz
      simp only [G', removeExceptionEdges, hz, hzs, ite_true]
    · have hzs : z.swap ∉ Z := fun h => hz ((hZsym z).mpr h)
      simp only [G', removeExceptionEdges, hz, hzs, ite_false, hGsym]
  · intro z
    by_cases hz : z ∈ Z
    · have hzs := (hZsym z).mp hz
      simp only [Y', removeExceptionColor, hz, hzs, ite_true]
    · have hzs : z.swap ∉ Z := fun h => hz ((hZsym z).mpr h)
      simp only [Y', removeExceptionColor, hz, hzs, ite_false, hYsym]
  · intro x
    exact ite_eq_left (hdiag (by simp [diagonal]))
  · intro z hz
    by_cases hmem : z ∈ Z
    · exact ite_eq_left hmem
    · have hGfalse : G z = false := by simpa only [G', removeExceptionEdges, ite_eq_right hmem] using hz
      simpa only [Y', removeExceptionColor, ite_eq_right hmem] using hsupport z hGfalse
  · intro z
    by_cases hz : z ∈ Z
    · simpa only [Y', removeExceptionColor, ite_eq_left hz, abs_zero] using hb
    · simpa only [Y', removeExceptionColor, ite_eq_right hz] using hbound z
  · intro n v hv
    have hpair : ∀ i j, i ≠ j → (v i, v j) ∉ Z := by
      intro i j hij hmem
      have h := hv i j hij
      simp only [G', removeExceptionEdges, ite_eq_left hmem, Bool.false_eq_true] at h
    have hclique : Clique G v := by
      intro i j hij
      simpa only [G', removeExceptionEdges, ite_eq_right (hpair i j hij)] using hv i j hij
    have hcharge : PhysicalPrimal.charge Y' v = PhysicalPrimal.charge Y v := by
      unfold PhysicalPrimal.charge
      congr 1
      apply Finset.sum_congr rfl
      intro ij _
      exact ite_eq_right (hpair ij.val.1 ij.val.2 ij.prop)
    rw [hcharge]
    exact hlicense n v hclique hpair

omit [CountablyGenerated Ω] in
/-- Marginal absolute continuity removes one pair-null exception under an
arbitrary joint tuple law, including singular parent laws. -/
theorem ae_pairs_avoid_null (μ : Measure Ω) {n : ℕ} (ρ : Measure (Fin n → Ω))
    (hpair : ∀ i j, i ≠ j →
      ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (Z : Set (Ω × Ω)) (hZ0 : (μ.prod μ) Z = 0) :
    ∀ᵐ v ∂ρ, ∀ i j, i ≠ j → (v i, v j) ∉ Z := by
  simp only [ae_all_iff]
  intro i j hij
  have hmap : ∀ᵐ z ∂ρ.map (fun v => (v i, v j)), z ∉ Z :=
    (hpair i j hij).ae_le (compl_mem_ae_iff.mpr hZ0)
  exact ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable hmap

/-- Product-almost-everywhere clique tests license actual arbitrary parent
laws using pair marginal absolute continuity, with no joint density premise. -/
theorem ae_charge_le_of_pair_marginals [MeasurableEq Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {G : Ω × Ω → Bool} {Y : Ω × Ω → ℝ} (hG : Measurable G) (hY : Measurable Y)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Y z| ≤ b)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    {n : ℕ} (ρ : Measure (Fin n → Ω))
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ) :
    ∀ᵐ v ∂ρ, Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
  obtain ⟨Z, _, hZ0, _, _, hlicense⟩ := exists_common_pair_null μ hG hY b hb hbound htest
  filter_upwards [ae_pairs_avoid_null μ ρ hpair Z hZ0] with v hv hclique
  exact hlicense n v hclique hv

end PartitionSampling

/-- The first marginal of an actual pair-absolute-continuous parent law is
absolutely continuous; no joint product density is needed. -/
theorem coordinate_absolutelyContinuous_of_pairs (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (ρ : Measure (Fin n → Ω))
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ) (i : Fin n) :
    ρ.map (fun v => v i) ≪ μ := by
  have hj : ∃ j : Fin n, i ≠ j := by
    by_cases hi : i = ⟨0, by omega⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have hval := congrArg Fin.val h
      rw [hi] at hval
      norm_num at hval
    · exact ⟨⟨0, by omega⟩, hi⟩
  obtain ⟨j, hij⟩ := hj
  have h := (hpair i j hij).map measurable_fst
  rw [Measure.map_map (μ := ρ) measurable_fst ((measurable_pi_apply i).prodMk
    (measurable_pi_apply j)), measurePreserving_fst.map_eq] at h
  exact h

/-- Add one independent fresh physical point to an arbitrary old parent law. -/
def freshLaw {n : ℕ} (ν : Measure Ω) (ρ : Measure (Fin n → Ω)) :
    Measure (Fin (n + 1) → Ω) :=
  (ν.prod ρ).map (fun p => Fin.cons p.1 p.2)

theorem measurable_cons {n : ℕ} :
    Measurable (fun p : Ω × (Fin n → Ω) => (Fin.cons p.1 p.2 : Fin (n + 1) → Ω)) := by
  apply measurable_pi_iff.mpr
  intro i
  cases i using Fin.cases with
  | zero => simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : Ω × (Fin n → Ω) → Ω))
  | succ i => simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd

instance freshLaw_finite {n : ℕ} (ν : Measure Ω) [IsFiniteMeasure ν]
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] : IsFiniteMeasure (freshLaw ν ρ) := by
  unfold freshLaw
  infer_instance

/-- A fresh-old pair has its genuine independent product marginal. -/
theorem freshLaw_pair_zero_succ {n : ℕ} (ν : Measure Ω) (ρ : Measure (Fin n → Ω))
    [IsFiniteMeasure ρ] (j : Fin n) :
    (freshLaw ν ρ).map (fun v => (v 0, v j.succ)) = ν.prod (ρ.map (fun v => v j)) := by
  rw [freshLaw, Measure.map_map ((measurable_pi_apply (0 : Fin (n + 1))).prodMk
    (measurable_pi_apply j.succ)) measurable_cons]
  have h := Measure.map_prod_map ν ρ measurable_id (measurable_pi_apply j)
  have heq : Prod.map (id : Ω → Ω) (fun v : Fin n → Ω => v j) =
      (fun p : Ω × (Fin n → Ω) => (p.1, p.2 j)) := by
    funext p
    rfl
  rw [heq] at h
  simpa only [Measure.map_id, Function.comp_def, Fin.cons_zero, Fin.cons_succ] using h.symm

/-- Old-old pair marginals are unchanged by an independent probability sample. -/
theorem freshLaw_pair_succ_succ {n : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i j : Fin n) :
    (freshLaw ν ρ).map (fun v => (v i.succ, v j.succ)) = ρ.map (fun v => (v i, v j)) := by
  rw [freshLaw, Measure.map_map ((measurable_pi_apply i.succ).prodMk
    (measurable_pi_apply j.succ)) measurable_cons]
  change (ν.prod ρ).map ((fun v : Fin n → Ω => (v i, v j)) ∘ Prod.snd) = _
  rw [← Measure.map_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) measurable_snd,
    measurePreserving_snd.map_eq]

/-- Independence derives every pair marginal of the enlarged law, including
old-new pairs, from the original pair marginals and the fresh sampling law. -/
theorem freshLaw_pairs_absolutelyContinuous (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hν : ν ≪ μ) :
    ∀ i j, i ≠ j → (freshLaw ν ρ).map (fun v => (v i, v j)) ≪ μ.prod μ := by
  have hzero (j : Fin n) :
      (freshLaw ν ρ).map (fun v => (v 0, v j.succ)) ≪ μ.prod μ := by
    rw [freshLaw_pair_zero_succ]
    exact hν.prod (coordinate_absolutelyContinuous_of_pairs μ hn ρ hpair j)
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => exact hzero j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have h := (hzero i).map measurable_swap
      rw [Measure.map_map (μ := freshLaw ν ρ) measurable_swap ((measurable_pi_apply (0 : Fin (n + 1))).prodMk
        (measurable_pi_apply i.succ)),
        Measure.prod_swap] at h
      exact h
    | succ j =>
      rw [freshLaw_pair_succ_succ]
      exact hpair i j (fun h => hij (congrArg Fin.succ h))

/-- Any finite number of fresh independent points is added explicitly. -/
def freshSamples {n : ℕ} (ν : Measure Ω) (ρ : Measure (Fin n → Ω)) :
    (m : ℕ) → Measure (Fin (n + m) → Ω)
  | 0 => ρ
  | m + 1 => freshLaw ν (freshSamples ν ρ m)

instance freshSamples_finite {n : ℕ} (ν : Measure Ω) [IsFiniteMeasure ν]
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (m : ℕ) :
    IsFiniteMeasure (freshSamples ν ρ m) := by
  induction m with
  | zero => exact inferInstanceAs (IsFiniteMeasure ρ)
  | succ m ih => exact inferInstanceAs (IsFiniteMeasure (freshLaw ν (freshSamples ν ρ m)))

/-- Every pair of the finite fresh-sample extension is absolutely continuous,
with the old coordinate marginals derived rather than supplied. -/
theorem freshSamples_pairs_absolutelyContinuous (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hν : ν ≪ μ) (m : ℕ) :
    ∀ i j, i ≠ j → (freshSamples ν ρ m).map (fun v => (v i, v j)) ≪ μ.prod μ := by
  induction m with
  | zero => exact hpair
  | succ m ih =>
    exact freshLaw_pairs_absolutelyContinuous μ (by omega : 2 ≤ n + m)
      (freshSamples ν ρ m) ih ν hν

/-- The actual common representative licenses singular parents together with
any finite number of independent fresh samples absolutely continuous to μ. -/
theorem ae_charge_le_freshSamples [CountablyGenerated Ω] [MeasurableEq Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {G : Ω × Ω → Bool} {Y : Ω × Ω → ℝ} (hG : Measurable G) (hY : Measurable Y)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ z, |Y z| ≤ b)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hν : ν ≪ μ) (m : ℕ) :
    ∀ᵐ v ∂freshSamples ν ρ m, Clique G v → PhysicalPrimal.charge Y v ≤ 1 :=
  ae_charge_le_of_pair_marginals μ hG hY b hb hbound htest _
    (freshSamples_pairs_absolutelyContinuous μ hn ρ hpair ν hν m)

end Erdos1017.PhysicalCliqueRepresentative

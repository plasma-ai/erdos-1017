module

public import Mathlib.Probability.Process.PartitionFiltration
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Product-cell averages on finite vertex partitions

Product-cell averages on a constructed sequence of finite generating vertex
partitions. The averaging functions are related to conditional expectation
internally; their almost-everywhere convergence is a theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open scoped ENNReal

namespace Erdos1017.PhysicalPartitionAverages

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- Measurability with respect to a label records no distinctions inside a fiber. -/
theorem eq_of_label_eq {ι : Type*} [MeasurableSpace ι] {f : Ω → ℝ} {q : Ω → ι}
    (hf : Measurable[(inferInstance : MeasurableSpace ι).comap q] f)
    {x y : Ω} (hxy : q x = q y) : f x = f y := by
  obtain ⟨s, hs, heq⟩ := hf (measurableSet_singleton (f x))
  have hx : x ∈ q ⁻¹' s := by
    rw [heq]
    simp
  have hy : y ∈ q ⁻¹' s := by simpa only [mem_preimage, ← hxy] using hx
  rw [heq] at hy
  exact (Set.mem_singleton_iff.mp hy).symm

/-- On every positive-measure label fiber, the literal average is the
actual conditional expectation at every point of that fiber. -/
theorem fiberAverage_eq_condExp {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : Ω → ι) (hq : Measurable q) {f : Ω → ℝ} (hf : Integrable f μ)
    (x : Ω) (hx : μ (q ⁻¹' {q x}) ≠ 0) :
    (⨍ y in q ⁻¹' {q x}, f y ∂μ) =
      (μ[f | (inferInstance : MeasurableSpace ι).comap q]) x := by
  let m := (inferInstance : MeasurableSpace ι).comap q
  have hm : m ≤ mΩ := hq.comap_le
  have hs : MeasurableSet[m] (q ⁻¹' {q x}) := comap_measurable q (measurableSet_singleton _)
  have hconst : ∀ y ∈ q ⁻¹' {q x}, (μ[f | m]) y = (μ[f | m]) x := by
    intro y hy
    exact eq_of_label_eq stronglyMeasurable_condExp.measurable hy
  have heq := setIntegral_condExp hm hf hs
  have hi : (∫ y in q ⁻¹' {q x}, (μ[f | m]) y ∂μ) =
      μ.real (q ⁻¹' {q x}) * (μ[f | m]) x := by
    rw [setIntegral_congr_fun (hm _ hs) hconst, setIntegral_const, smul_eq_mul]
  rw [setAverage_eq, ← heq, hi]
  have hreal : μ.real (q ⁻¹' {q x}) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hx, measure_ne_top _ _⟩
  simp only [smul_eq_mul]
  exact inv_mul_cancel_left₀ hreal _

/-- A finite labeling has positive-measure fibers at almost every point. -/
theorem ae_positive_fiber {ι : Type*} [Finite ι] (μ : Measure Ω) (q : Ω → ι) :
    ∀ᵐ x ∂μ, μ (q ⁻¹' {q x}) ≠ 0 := by
  have h : ∀ i : ι, ∀ᵐ x ∂μ, μ (q ⁻¹' {i}) = 0 → q x ≠ i := by
    intro i
    by_cases hi : μ (q ⁻¹' {i}) = 0
    · have hnot : ∀ᵐ x ∂μ, x ∉ q ⁻¹' {i} := by
        rw [ae_iff]
        simpa only [Set.preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, not_not] using hi
      filter_upwards [hnot] with x hx _
      simpa using hx
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact fun hzero => hx (q x) hzero rfl

section Partitions

variable [CountablyGenerated Ω]

/-- The actual finite labels of the constructed vertex partition. -/
abbrev Cell (Ω : Type*) [MeasurableSpace Ω] [CountablyGenerated Ω] (n : ℕ) :=
  countablePartition Ω n

instance cellMeasurableSpace (n : ℕ) : MeasurableSpace (Cell Ω n) := ⊤
instance cellMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Cell Ω n) :=
  ⟨fun _ => trivial⟩

/-- The cell containing a given physical vertex. -/
def cellIndex (n : ℕ) (x : Ω) : Cell Ω n :=
  ⟨countablePartitionSet n x, countablePartitionSet_mem n x⟩

theorem measurable_cellIndex (n : ℕ) : Measurable (cellIndex (Ω := Ω) n) :=
  (measurable_countablePartitionSet_subtype n ⊤).mono (countableFiltration Ω |>.le n) le_rfl

/-- The finite label sigma algebra is exactly the partition filtration. -/
theorem cellIndex_comap (n : ℕ) :
    (⊤ : MeasurableSpace (Cell Ω n)).comap (cellIndex n) = countableFiltration Ω n := by
  apply le_antisymm
  · exact (measurable_countablePartitionSet_subtype n ⊤).comap_le
  · apply generateFrom_le
    intro s hs
    have heq : cellIndex n ⁻¹' {⟨s, hs⟩} = s := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, cellIndex, Subtype.mk.injEq]
      exact countablePartitionSet_eq_iff x hs
    rw [← heq]
    exact comap_measurable (cellIndex n) (measurableSet_singleton _)

/-- Every containing cell in the constructed sequence has positive measure
at almost every vertex. -/
theorem ae_positive_cells (μ : Measure Ω) :
    ∀ᵐ x ∂μ, ∀ n, μ (countablePartitionSet n x) ≠ 0 := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [ae_positive_fiber μ (cellIndex (Ω := Ω) n)] with x hx
  have heq : cellIndex n ⁻¹' {cellIndex n x} = countablePartitionSet n x := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, cellIndex, Subtype.mk.injEq]
    exact countablePartitionSet_eq_iff y (countablePartitionSet_mem n x)
  rwa [heq] at hx

/-- Both coordinates are averaged over the same finite vertex partition. -/
def pairFiltration : Filtration ℕ (inferInstance : MeasurableSpace (Ω × Ω)) where
  seq n := (countableFiltration Ω n).prod (countableFiltration Ω n)
  mono' i j hij := by
    dsimp only [MeasurableSpace.prod]
    exact sup_le_sup (comap_mono (countableFiltration Ω |>.mono hij))
      (comap_mono (countableFiltration Ω |>.mono hij))
  le' n := by
    dsimp only [MeasurableSpace.prod]
    exact sup_le_sup (comap_mono (countableFiltration Ω |>.le n))
      (comap_mono (countableFiltration Ω |>.le n))

theorem iSup_pairFiltration :
    ⨆ n, pairFiltration (Ω := Ω) n = (inferInstance : MeasurableSpace (Ω × Ω)) := by
  change (⨆ n, ((countableFiltration Ω n).comap Prod.fst) ⊔
    ((countableFiltration Ω n).comap Prod.snd)) = _
  rw [iSup_sup_eq, ← MeasurableSpace.comap_iSup, ← MeasurableSpace.comap_iSup, iSup_countableFiltration]
  rfl

/-- Literal averages over the actual product of the two containing cells. -/
def cellAverage (μ : Measure Ω) (n : ℕ) (f : Ω × Ω → ℝ) (z : Ω × Ω) : ℝ :=
  ⨍ w in countablePartitionSet n z.1 ×ˢ countablePartitionSet n z.2, f w ∂μ.prod μ

theorem cellAverage_ae_eq_condExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) {f : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ)) :
    cellAverage μ n f =ᵐ[μ.prod μ] (μ.prod μ)[f | pairFiltration n] := by
  let q : Ω × Ω → Cell Ω n × Cell Ω n := fun z => (cellIndex n z.1, cellIndex n z.2)
  have hq : Measurable q := ((measurable_cellIndex n).comp measurable_fst).prodMk
    ((measurable_cellIndex n).comp measurable_snd)
  have hcomap : (inferInstance : MeasurableSpace (Cell Ω n × Cell Ω n)).comap q =
      pairFiltration (Ω := Ω) n := by
    change ((⊤ : MeasurableSpace (Cell Ω n)).prod ⊤).comap
      (Prod.map (cellIndex n) (cellIndex n)) = _
    rw [MeasurableSpace.comap_prodMap, cellIndex_comap]
    rfl
  have hfiber (z : Ω × Ω) : q ⁻¹' {q z} =
      countablePartitionSet n z.1 ×ˢ countablePartitionSet n z.2 := by
    ext w
    simp only [q, mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_prod,
      cellIndex, Subtype.mk.injEq]
    rw [countablePartitionSet_eq_iff _ (countablePartitionSet_mem n z.1),
      countablePartitionSet_eq_iff _ (countablePartitionSet_mem n z.2)]
  filter_upwards [ae_positive_fiber (μ.prod μ) q] with z hz
  have heq := fiberAverage_eq_condExp (μ.prod μ) q hq hf z hz
  rw [hcomap, hfiber] at heq
  exact heq

/-- The constructed literal cell averages converge almost everywhere to
every integrable measurable pair function. No convergence premise occurs. -/
theorem ae_tendsto_cellAverage (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ)) (hfm : StronglyMeasurable f) :
    ∀ᵐ z ∂μ.prod μ, Tendsto (fun n => cellAverage μ n f z) atTop (nhds (f z)) := by
  have hmeas : StronglyMeasurable[⨆ n, pairFiltration (Ω := Ω) n] f := by
    rw [iSup_pairFiltration]
    exact hfm
  have ht := hf.tendsto_ae_condExp (ℱ := pairFiltration (Ω := Ω)) hmeas
  have heq : ∀ᵐ z ∂μ.prod μ, ∀ n, cellAverage μ n f z =
      ((μ.prod μ)[f | pairFiltration n]) z :=
    ae_all_iff.mpr (fun n => cellAverage_ae_eq_condExp μ n hf)
  filter_upwards [ht, heq] with z hz heq
  simpa only [heq] using hz

end Partitions

end Erdos1017.PhysicalPartitionAverages

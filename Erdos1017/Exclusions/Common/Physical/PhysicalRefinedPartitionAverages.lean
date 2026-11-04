module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPartitionAverages

/-!
# Averages over refined partition cells

Containing-cell averages for a finite partition refined by one measurable set.
The finite labels and the generating filtration are constructed here, so their
almost-everywhere convergence is a theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open scoped ENNReal Classical

namespace Erdos1017.PhysicalRefinedPartitionAverages

variable {Ω : Type*} [MeasurableSpace Ω] [CountablyGenerated Ω]

private def sideLabel (D : Set Ω) (x : Ω) : Bool := decide (x ∈ D)

omit [CountablyGenerated Ω] in
private theorem measurable_sideLabel (D : Set Ω) (hD : MeasurableSet D) :
    Measurable (sideLabel D : Ω → Bool) := by
  classical
  have heq : sideLabel D = fun x => if x ∈ D then true else false := by
    funext x
    by_cases hx : x ∈ D <;> simp [sideLabel, hx]
  rw [heq]
  exact Measurable.ite hD measurable_const measurable_const

private def refinedLabel (D : Set Ω) (n : ℕ) (x : Ω) :
    Erdos1017.PhysicalPartitionAverages.Cell Ω n × Bool :=
  (Erdos1017.PhysicalPartitionAverages.cellIndex n x, sideLabel D x)

private theorem measurable_refinedLabel (D : Set Ω) (hD : MeasurableSet D) (n : ℕ) :
    Measurable (refinedLabel D n : Ω → Erdos1017.PhysicalPartitionAverages.Cell Ω n × Bool) :=
  (Erdos1017.PhysicalPartitionAverages.measurable_cellIndex n).prodMk
    (measurable_sideLabel D hD)

/-- The finite containing cell refined by a measurable side. -/
def refinedCell (D : Set Ω) (n : ℕ) (x : Ω) : Set Ω :=
  countablePartitionSet n x ∩ if x ∈ D then D else Dᶜ

/-- Every refined containing cell is measurable. -/
theorem measurableSet_refinedCell (D : Set Ω) (hD : MeasurableSet D)
    (n : ℕ) (x : Ω) : MeasurableSet (refinedCell D n x) := by
  have hc : MeasurableSet (countablePartitionSet n x) :=
    ((countableFiltration Ω).le n) _
      (measurableSet_countableFiltration_countablePartitionSet n x)
  by_cases hx : x ∈ D
  · simpa [refinedCell, hx] using hc.inter hD
  · simpa [refinedCell, hx] using hc.inter hD.compl

/-- A refined cell centered in `D` lies entirely in `D`. -/
theorem refinedCell_subset_of_mem (D : Set Ω) (n : ℕ) (x : Ω)
    (hx : x ∈ D) : refinedCell D n x ⊆ D := by
  simp [refinedCell, hx]

private theorem label_fiber (D : Set Ω) (n : ℕ) (x : Ω) :
    refinedLabel D n ⁻¹' {refinedLabel D n x} = refinedCell D n x := by
  classical
  ext y
  simp only [refinedLabel, refinedCell, mem_preimage, mem_singleton_iff,
    Prod.mk.injEq, Erdos1017.PhysicalPartitionAverages.cellIndex,
    Subtype.mk.injEq, mem_inter_iff]
  rw [countablePartitionSet_eq_iff _ (countablePartitionSet_mem n x)]
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D <;> simp [sideLabel, hx, hy]

/-- All finite refined containing cells have positive measure at almost
every vertex. The finite label carries the measurable side explicitly. -/
theorem ae_positive_refinedCells (μ : Measure Ω) (D : Set Ω) :
    ∀ᵐ x ∂μ, ∀ n, μ (refinedCell D n x) ≠ 0 := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [Erdos1017.PhysicalPartitionAverages.ae_positive_fiber μ
    (refinedLabel D n)] with x hx
  rwa [label_fiber] at hx

private def refinedFiltration (D : Set Ω) (hD : MeasurableSet D) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq n := countableFiltration Ω n ⊔ (⊤ : MeasurableSpace Bool).comap (sideLabel D)
  mono' i j hij := sup_le_sup (countableFiltration Ω |>.mono hij) le_rfl
  le' n := sup_le (countableFiltration Ω |>.le n) (by
    exact (measurable_sideLabel D hD).comap_le)

private theorem refinedLabel_comap (D : Set Ω) (hD : MeasurableSet D) (n : ℕ) :
    (inferInstance : MeasurableSpace (Erdos1017.PhysicalPartitionAverages.Cell Ω n × Bool)).comap
      (refinedLabel D n) = refinedFiltration D hD n := by
  change ((⊤ : MeasurableSpace (Erdos1017.PhysicalPartitionAverages.Cell Ω n)).prod
    (inferInstance : MeasurableSpace Bool)).comap (refinedLabel D n) = _
  rw [show (inferInstance : MeasurableSpace Bool) = ⊤ from rfl]
  rw [MeasurableSpace.comap_prodMk]
  change (⊤ : MeasurableSpace (Erdos1017.PhysicalPartitionAverages.Cell Ω n)).comap
    (Erdos1017.PhysicalPartitionAverages.cellIndex n) ⊔
    (⊤ : MeasurableSpace Bool).comap (sideLabel D) = _
  rw [Erdos1017.PhysicalPartitionAverages.cellIndex_comap]
  rfl

private theorem iSup_refinedFiltration (D : Set Ω) (hD : MeasurableSet D) :
    ⨆ n, refinedFiltration D hD n = (inferInstance : MeasurableSpace Ω) := by
  apply le_antisymm
  · exact iSup_le (fun n => (refinedFiltration D hD).le n)
  · calc
      (inferInstance : MeasurableSpace Ω) = ⨆ n, countableFiltration Ω n :=
        (iSup_countableFiltration Ω).symm
      _ ≤ ⨆ n, refinedFiltration D hD n := iSup_mono (fun n => le_sup_left)

private def refinedPairFiltration (D : Set Ω) (hD : MeasurableSet D) :
    Filtration ℕ (inferInstance : MeasurableSpace (Ω × Ω)) where
  seq n := (refinedFiltration D hD n).prod (refinedFiltration D hD n)
  mono' i j hij := by
    dsimp only [MeasurableSpace.prod]
    exact sup_le_sup (comap_mono ((refinedFiltration D hD).mono hij))
      (comap_mono ((refinedFiltration D hD).mono hij))
  le' n := by
    dsimp only [MeasurableSpace.prod]
    exact sup_le_sup (comap_mono ((refinedFiltration D hD).le n))
      (comap_mono ((refinedFiltration D hD).le n))

private theorem iSup_refinedPairFiltration (D : Set Ω) (hD : MeasurableSet D) :
    ⨆ n, refinedPairFiltration D hD n = (inferInstance : MeasurableSpace (Ω × Ω)) := by
  change (⨆ n, ((refinedFiltration D hD n).comap Prod.fst) ⊔
    ((refinedFiltration D hD n).comap Prod.snd)) = _
  rw [iSup_sup_eq, ← MeasurableSpace.comap_iSup, ← MeasurableSpace.comap_iSup,
    iSup_refinedFiltration D hD]
  rfl

/-- Literal product average over the two refined containing cells. -/
def refinedCellAverage (μ : Measure Ω) (D : Set Ω) (n : ℕ)
    (f : Ω × Ω → ℝ) (z : Ω × Ω) : ℝ :=
  ⨍ w in refinedCell D n z.1 ×ˢ refinedCell D n z.2, f w ∂μ.prod μ

private theorem refinedCellAverage_ae_eq_condExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Set Ω) (hD : MeasurableSet D) (n : ℕ)
    {f : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ)) :
    refinedCellAverage μ D n f =ᵐ[μ.prod μ]
      (μ.prod μ)[f | refinedPairFiltration D hD n] := by
  let q : Ω × Ω →
      (Erdos1017.PhysicalPartitionAverages.Cell Ω n × Bool) ×
        (Erdos1017.PhysicalPartitionAverages.Cell Ω n × Bool) :=
    fun z => (refinedLabel D n z.1, refinedLabel D n z.2)
  have hq : Measurable q :=
    ((measurable_refinedLabel D hD n).comp measurable_fst).prodMk
      ((measurable_refinedLabel D hD n).comp measurable_snd)
  have hcomap : (inferInstance : MeasurableSpace _).comap q =
      refinedPairFiltration D hD n := by
    change ((inferInstance : MeasurableSpace
      (Erdos1017.PhysicalPartitionAverages.Cell Ω n × Bool)).prod inferInstance).comap
        (Prod.map (refinedLabel D n) (refinedLabel D n)) = _
    rw [MeasurableSpace.comap_prodMap, refinedLabel_comap D hD]
    rfl
  have hfiber (z : Ω × Ω) : q ⁻¹' {q z} =
      refinedCell D n z.1 ×ˢ refinedCell D n z.2 := by
    ext w
    simp only [q, mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_prod]
    rw [← label_fiber D n z.1, ← label_fiber D n z.2]
    simp only [mem_preimage, mem_singleton_iff]
  filter_upwards [Erdos1017.PhysicalPartitionAverages.ae_positive_fiber (μ.prod μ) q]
    with z hz
  have heq := Erdos1017.PhysicalPartitionAverages.fiberAverage_eq_condExp
    (μ.prod μ) q hq hf z hz
  rw [hcomap, hfiber] at heq
  exact heq

/-- The constructed refined product-cell averages converge almost everywhere
to every integrable strongly measurable pair function. -/
theorem ae_tendsto_refinedCellAverage (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Set Ω) (hD : MeasurableSet D)
    {f : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ)) (hfm : StronglyMeasurable f) :
    ∀ᵐ z ∂μ.prod μ,
      Tendsto (fun n => refinedCellAverage μ D n f z) atTop (nhds (f z)) := by
  have hmeas : StronglyMeasurable[⨆ n, refinedPairFiltration D hD n] f := by
    rw [iSup_refinedPairFiltration D hD]
    exact hfm
  have ht := hf.tendsto_ae_condExp (ℱ := refinedPairFiltration D hD) hmeas
  have heq : ∀ᵐ z ∂μ.prod μ, ∀ n,
      refinedCellAverage μ D n f z =
        ((μ.prod μ)[f | refinedPairFiltration D hD n]) z :=
    ae_all_iff.mpr (fun n => refinedCellAverage_ae_eq_condExp μ D hD n hf)
  filter_upwards [ht, heq] with z hz heq
  simpa only [heq] using hz

end Erdos1017.PhysicalRefinedPartitionAverages

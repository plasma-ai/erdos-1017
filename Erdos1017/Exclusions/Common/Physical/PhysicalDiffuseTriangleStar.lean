module

public import Erdos1017.Exclusions.Common.Physical.PhysicalRefinedPartitionAverages
public import Erdos1017.Exclusions.Common.Physical.PhysicalTriangleExposure

/-!
# Diffuse star bound on tight triangles

Independent product samples inside refined cells give the diffuse tight-triangle
star bound, including for singular pair-AC parent laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.PhysicalDiffuseTriangleStar

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem sample_charge_bound
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ p, |Y p| ≤ B)
    {n : ℕ} (htest : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    (ν : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i ≪ μ) :
    (∑ ij : PhysicalPrimal.PairIndex n,
      ∫ z, Y z ∂(ν ij.val.1).prod (ν ij.val.2)) / 2 ≤
      1 + ((Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * B + 1) *
        ∑ ij : PhysicalPrimal.PairIndex n,
          (1 - ∫ z, PhysicalCliqueRepresentative.edgeIndicator G z
            ∂(ν ij.val.1).prod (ν ij.val.2)) := by
  have hac := PhysicalCliqueRepresentative.pi_absolutelyContinuous μ ν hν
  have hp : ∀ᵐ w ∂Measure.pi ν, PhysicalPrimal.charge Y w ≤ 1 +
      ((Fintype.card (PhysicalPrimal.PairIndex n) : ℝ) * B + 1) *
        PhysicalCliqueRepresentative.missingPairs G w := by
    filter_upwards [hac.ae_le htest] with w hw
    exact PhysicalCliqueRepresentative.charge_le_missing_penalty G Y B hB hbound w hw
  have hint : Integrable (PhysicalPrimal.charge Y) (Measure.pi ν) := by
    unfold PhysicalPrimal.charge
    apply Integrable.div_const
    apply integrable_finsetSum
    intro ij _
    exact PhysicalCliqueRepresentative.integrable_of_bounded _
      (hY.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))) B
      (fun _ => hbound _)
  have hm : Integrable (PhysicalCliqueRepresentative.missingPairs G) (Measure.pi ν) := by
    unfold PhysicalCliqueRepresentative.missingPairs
    apply integrable_finsetSum
    intro ij _
    apply (integrable_const 1).sub
    apply PhysicalCliqueRepresentative.integrable_of_bounded _
      ((PhysicalCliqueRepresentative.measurable_edgeIndicator hG).comp
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _))) 1
    intro w
    change |PhysicalCliqueRepresentative.edgeIndicator G (w ij.val.1, w ij.val.2)| ≤ 1
    rw [abs_of_nonneg (PhysicalCliqueRepresentative.edgeIndicator_bounds G _).1]
    exact (PhysicalCliqueRepresentative.edgeIndicator_bounds G _).2
  have hle := integral_mono_ae hint ((integrable_const 1).add (hm.const_mul _)) hp
  dsimp only [Pi.add_apply] at hle
  rw [integral_add (integrable_const 1) (hm.const_mul _), integral_const_mul,
    PhysicalCliqueRepresentative.integral_charge_pi ν hY B hbound,
    PhysicalCliqueRepresentative.integral_missingPairs_pi ν hG] at hle
  simpa using hle

private theorem ordered_four {α : Type*} (F : α × α → ℝ) (x y z : α) :
    (∑ ij : PhysicalPrimal.PairIndex 4,
      F ((![x, x, y, z] : Fin 4 → α) ij.val.1, ![x, x, y, z] ij.val.2)) / 2 =
      F (x, x) + F (x, y) + F (y, x) + F (x, z) + F (z, x) +
        (F (y, z) + F (z, y)) / 2 := by
  change PhysicalPrimal.charge F (![x, x, y, z] : Fin 4 → α) = _
  have he := MultipartiteHeadPrice.physicalCharge_eq_tupleCharge
    (fun a b => F (a, b)) (![x, x, y, z] : Fin 4 → α)
  change PhysicalPrimal.charge F _ = _ at he
  rw [he]
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
    Fin.sum_univ_succ]
  ring

private theorem repeat_cell_limit {Y : Fin 3 × Fin 3 → ℝ}
    (F H : ℕ → Fin 3 × Fin 3 → ℝ) (ell C : ℝ)
    (hF : ∀ i j : Fin 3, i ≠ j →
      Tendsto (fun n => F n (i, j)) atTop (nhds (Y (i, j))))
    (hH : ∀ i j : Fin 3, i ≠ j →
      Tendsto (fun n => H n (i, j)) atTop (nhds (1 : ℝ)))
    (hfloor : ∀ n, -ell ≤ F n (0, 0))
    (hdiag : ∀ n, H n (0, 0) = 1)
    (hsym : ∀ i j : Fin 3, Y (i, j) = Y (j, i))
    (htight : Y (0, 1) + Y (0, 2) + Y (1, 2) = 1)
    (hbound : ∀ n,
      (∑ ij : PhysicalPrimal.PairIndex 4,
        F n ((![(0 : Fin 3), 0, 1, 2] : Fin 4 → Fin 3) ij.val.1,
          ![(0 : Fin 3), 0, 1, 2] ij.val.2)) / 2 ≤
      1 + C * ∑ ij : PhysicalPrimal.PairIndex 4,
        (1 - H n ((![(0 : Fin 3), 0, 1, 2] : Fin 4 → Fin 3) ij.val.1,
          ![(0 : Fin 3), 0, 1, 2] ij.val.2))) :
    Y (0, 1) + Y (0, 2) ≤ ell := by
  let L (n : ℕ) := -ell + F n (0, 1) + F n (1, 0) + F n (0, 2) + F n (2, 0) +
    (F n (1, 2) + F n (2, 1)) / 2
  let R (n : ℕ) := 1 + C * (2 * ((1 - H n (0, 1)) + (1 - H n (1, 0)) +
    (1 - H n (0, 2)) + (1 - H n (2, 0)) +
    ((1 - H n (1, 2)) + (1 - H n (2, 1))) / 2))
  have hle : ∀ n, L n ≤ R n := by
    intro n
    have hb := hbound n
    rw [ordered_four] at hb
    have hm := ordered_four (fun p => 1 - H n p) (0 : Fin 3) 1 2
    have he : (∑ ij : PhysicalPrimal.PairIndex 4,
        (1 - H n ((![(0 : Fin 3), 0, 1, 2] : Fin 4 → Fin 3) ij.val.1,
          ![(0 : Fin 3), 0, 1, 2] ij.val.2))) =
      2 * ((1 - H n (0, 1)) + (1 - H n (1, 0)) +
        (1 - H n (0, 2)) + (1 - H n (2, 0)) +
        ((1 - H n (1, 2)) + (1 - H n (2, 1))) / 2) := by
      rw [hdiag] at hm
      linarith only [hm]
    rw [he] at hb
    dsimp only [L, R]
    linarith only [hb, hfloor n]
  have hleft : Tendsto L atTop (nhds (-ell + 1 + (Y (0, 1) + Y (0, 2)))) := by
    have hc : Tendsto (fun _ : ℕ => -ell) atTop (nhds (-ell)) := tendsto_const_nhds
    have ht := (((((hc.add (hF 0 1 (by decide))).add
      (hF 1 0 (by decide))).add (hF 0 2 (by decide))).add
      (hF 2 0 (by decide))).add
      (((hF 1 2 (by decide)).add (hF 2 1 (by decide))).div_const 2))
    have heq : -ell + Y (0, 1) + Y (1, 0) + Y (0, 2) + Y (2, 0) +
        (Y (1, 2) + Y (2, 1)) / 2 = -ell + 1 + (Y (0, 1) + Y (0, 2)) := by
      rw [hsym 1 0, hsym 2 0, hsym 2 1]
      linarith only [htight]
    rw [heq] at ht
    exact ht
  have hright : Tendsto R atTop (nhds (1 : ℝ)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hh (i j : Fin 3) (hij : i ≠ j) := hone.sub (hH i j hij)
    have ht := (((((hh 0 1 (by decide)).add (hh 1 0 (by decide))).add
      (hh 0 2 (by decide))).add (hh 2 0 (by decide))).add
      (((hh 1 2 (by decide)).add (hh 2 1 (by decide))).div_const 2))
    have hc : Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
    have hr := hone.add (hc.mul (htwo.mul ht))
    simpa only [R, sub_self, add_zero, zero_add, zero_div, mul_zero] using hr
  have hlim := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hle)
  linarith only [hlim]

private theorem self_sample_bounds
    (G : Ω × Ω → Bool) (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (B : ℝ) (hbound : ∀ p, |Y p| ≤ B) (D : Set Ω) (ell : ℝ)
    (hfloor : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      G p = true ∧ -ell ≤ Y p)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνD : ∀ᵐ x ∂ν, x ∈ D) :
    -ell ≤ (∫ z, Y z ∂ν.prod ν) ∧
      (∫ z, PhysicalCliqueRepresentative.edgeIndicator G z ∂ν.prod ν) = 1 := by
  have hp : ∀ᵐ p ∂ν.prod ν, G p = true ∧ -ell ≤ Y p := by
    filter_upwards [(hν.prod hν).ae_le hfloor,
      Measure.quasiMeasurePreserving_fst.ae hνD,
      Measure.quasiMeasurePreserving_snd.ae hνD] with p hf hx hy
    exact hf hx hy
  constructor
  · have hi := PhysicalCliqueRepresentative.integrable_of_bounded (ν.prod ν) hY B hbound
    have hm := integral_mono_ae (integrable_const (-ell)) hi (hp.mono (fun _ h => h.2))
    simpa using hm
  · have he : PhysicalCliqueRepresentative.edgeIndicator G =ᵐ[ν.prod ν]
        (fun _ => (1 : ℝ)) := hp.mono (fun p h => by
      simp only [PhysicalCliqueRepresentative.edgeIndicator, h.1, ↓reduceIte])
    rw [integral_congr_ae he]
    simp

variable [MeasurableSpace.CountablyGenerated Ω]

private theorem star_le_of_refined_cells
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hYsym : ∀ x y, Y (x, y) = Y (y, x))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ p, |Y p| ≤ B)
    (D : Set Ω) (hD : MeasurableSet D) (ell : ℝ)
    (hfloor : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      G p = true ∧ -ell ≤ Y p)
    (htest : ∀ᵐ w ∂Measure.pi (fun _ : Fin 4 => μ),
      PhysicalCliqueRepresentative.Clique G w → PhysicalPrimal.charge Y w ≤ 1)
    (v : Fin 3 → Ω) (hv : PhysicalCliqueRepresentative.Clique G v)
    (htight : PhysicalPrimal.charge Y v = 1) (hvD : v 0 ∈ D)
    (hcell : ∀ i n, μ (PhysicalRefinedPartitionAverages.refinedCell D n (v i)) ≠ 0)
    (hYlim : ∀ i j : Fin 3, i ≠ j →
      Tendsto (fun n => PhysicalRefinedPartitionAverages.refinedCellAverage μ D n Y
        (v i, v j)) atTop (nhds (Y (v i, v j))))
    (hGlim : ∀ i j : Fin 3, i ≠ j →
      Tendsto (fun n => PhysicalRefinedPartitionAverages.refinedCellAverage μ D n
        (PhysicalCliqueRepresentative.edgeIndicator G) (v i, v j)) atTop
          (nhds (PhysicalCliqueRepresentative.edgeIndicator G (v i, v j)))) :
    Y (v 0, v 1) + Y (v 0, v 2) ≤ ell := by
  let ν (n : ℕ) (i : Fin 3) := PhysicalCliqueRepresentative.cellLaw μ
    (PhysicalRefinedPartitionAverages.refinedCell D n (v i))
  let : ∀ n i, IsProbabilityMeasure (ν n i) := fun n i =>
    PhysicalCliqueRepresentative.cellLaw_probability μ _ (hcell i n)
  let F (n : ℕ) (p : Fin 3 × Fin 3) := ∫ z, Y z ∂(ν n p.1).prod (ν n p.2)
  let H (n : ℕ) (p : Fin 3 × Fin 3) := ∫ z,
    PhysicalCliqueRepresentative.edgeIndicator G z ∂(ν n p.1).prod (ν n p.2)
  have havg (f : Ω × Ω → ℝ) (n : ℕ) (i j : Fin 3) :
      (∫ z, f z ∂(ν n i).prod (ν n j)) =
        PhysicalRefinedPartitionAverages.refinedCellAverage μ D n f (v i, v j) :=
    PhysicalCliqueRepresentative.integral_cellLaw_prod μ _ _ (hcell i n) (hcell j n) f
  have hFlim (i j : Fin 3) (hij : i ≠ j) :
      Tendsto (fun n => F n (i, j)) atTop (nhds (Y (v i, v j))) := by
    simpa only [F, havg] using hYlim i j hij
  have hHlim (i j : Fin 3) (hij : i ≠ j) :
      Tendsto (fun n => H n (i, j)) atTop (nhds (1 : ℝ)) := by
    have hg := hGlim i j hij
    have he : PhysicalCliqueRepresentative.edgeIndicator G (v i, v j) = 1 := by
      simp only [PhysicalCliqueRepresentative.edgeIndicator, hv i j hij, ↓reduceIte]
    rw [he] at hg
    simpa only [H, havg] using hg
  have hself (n : ℕ) : -ell ≤ F n (0, 0) ∧ H n (0, 0) = 1 := by
    have hνD : ∀ᵐ x ∂ν n 0, x ∈ D := by
      change ∀ᵐ x ∂(μ (PhysicalRefinedPartitionAverages.refinedCell D n (v 0)))⁻¹ •
        μ.restrict (PhysicalRefinedPartitionAverages.refinedCell D n (v 0)), x ∈ D
      apply Measure.ae_smul_measure
      exact (ae_restrict_mem
        (PhysicalRefinedPartitionAverages.measurableSet_refinedCell D hD n (v 0))).mono
          (fun x hx => PhysicalRefinedPartitionAverages.refinedCell_subset_of_mem
            D n (v 0) hvD hx)
    exact self_sample_bounds G Y hY B hbound D ell hfloor (ν n 0)
      (PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous μ _) hνD
  have htest' (n : ℕ) := sample_charge_bound G hG Y hY B hB hbound htest
    (fun j : Fin 4 => ν n ((![(0 : Fin 3), 0, 1, 2] : Fin 4 → Fin 3) j))
    (fun _ => PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous μ _)
  have htight' : Y (v 0, v 1) + Y (v 0, v 2) + Y (v 1, v 2) = 1 := by
    have he : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
    rw [he, PhysicalTriangleExposure.charge_three Y hYsym] at htight
    exact htight
  exact repeat_cell_limit (Y := fun p : Fin 3 × Fin 3 => Y (v p.1, v p.2)) F H ell
    ((Fintype.card (PhysicalPrimal.PairIndex 4) : ℝ) * B + 1)
    hFlim hHlim (fun n => (hself n).1) (fun n => (hself n).2)
    (fun i j => hYsym (v i) (v j)) htight' htest'

/-- Genuine independent sampling from refined diffuse cells bounds every
ordered diffuse star on a pair-AC tight physical triangle law. -/
theorem ae_permuted_triangle_star_le
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hYsym : ∀ x y, Y (x, y) = Y (y, x))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ p, |Y p| ≤ B)
    (D : Set Ω) (hD : MeasurableSet D) (ell : ℝ)
    (hfloor : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      G p = true ∧ -ell ≤ Y p)
    (htest : ∀ᵐ w ∂Measure.pi (fun _ : Fin 4 => μ),
      PhysicalCliqueRepresentative.Clique G w → PhysicalPrimal.charge Y w ≤ 1)
    (ρ : Measure (Fin 3 → Ω))
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique G v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge Y v = 1) :
    ∀ᵐ v ∂ρ, ∀ e : Equiv.Perm (Fin 3), v (e 0) ∈ D →
      Y (v (e 0), v (e 1)) + Y (v (e 0), v (e 2)) ≤ ell := by
  have hYconv := PhysicalRefinedPartitionAverages.ae_tendsto_refinedCellAverage μ D hD
    (PhysicalCliqueRepresentative.integrable_of_bounded (μ.prod μ) hY B hbound)
    hY.stronglyMeasurable
  have hE := PhysicalCliqueRepresentative.measurable_edgeIndicator hG
  have hGbound (p : Ω × Ω) : |PhysicalCliqueRepresentative.edgeIndicator G p| ≤ 1 := by
    rw [abs_of_nonneg (PhysicalCliqueRepresentative.edgeIndicator_bounds G _).1]
    exact (PhysicalCliqueRepresentative.edgeIndicator_bounds G _).2
  have hGconv := PhysicalRefinedPartitionAverages.ae_tendsto_refinedCellAverage μ D hD
    (PhysicalCliqueRepresentative.integrable_of_bounded (μ.prod μ) hE 1 hGbound)
    hE.stronglyMeasurable
  have hpairY : ∀ᵐ v ∂ρ, ∀ i j : Fin 3, i ≠ j →
      Tendsto (fun n => PhysicalRefinedPartitionAverages.refinedCellAverage μ D n Y
        (v i, v j)) atTop (nhds (Y (v i, v j))) := by
    simp only [ae_all_iff]
    intro i j hij
    exact ae_of_ae_map ((measurable_pi_apply i).prodMk
      (measurable_pi_apply j)).aemeasurable ((hpairs i j hij).ae_le hYconv)
  have hpairG : ∀ᵐ v ∂ρ, ∀ i j : Fin 3, i ≠ j →
      Tendsto (fun n => PhysicalRefinedPartitionAverages.refinedCellAverage μ D n
        (PhysicalCliqueRepresentative.edgeIndicator G) (v i, v j)) atTop
          (nhds (PhysicalCliqueRepresentative.edgeIndicator G (v i, v j))) := by
    simp only [ae_all_iff]
    intro i j hij
    exact ae_of_ae_map ((measurable_pi_apply i).prodMk
      (measurable_pi_apply j)).aemeasurable ((hpairs i j hij).ae_le hGconv)
  have hcells : ∀ᵐ v ∂ρ, ∀ i n,
      μ (PhysicalRefinedPartitionAverages.refinedCell D n (v i)) ≠ 0 := by
    simp only [ae_all_iff]
    intro i n
    exact (ae_of_ae_map (measurable_pi_apply i).aemeasurable
      ((PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs μ
        (by norm_num : 2 ≤ 3) ρ hpairs i).ae_le
          (PhysicalRefinedPartitionAverages.ae_positive_refinedCells μ D))).mono
            (fun _ hx => hx n)
  filter_upwards [hpairY, hpairG, hcells, hclique, htight] with v hy hg hc hcl ht e hvD
  have hperm : ∀ i j : Fin 3, i ≠ j → e i ≠ e j :=
    fun _ _ hij he => hij (e.injective he)
  exact star_le_of_refined_cells G hG Y hY hYsym B hB hbound D hD ell hfloor htest
    (fun i => v (e i)) (fun i j hij => hcl _ _ (hperm i j hij))
    ((PhysicalTriangleExposure.charge_comp_equiv Y v e).trans ht) hvD
    (fun i n => hc (e i) n) (fun i j hij => hy _ _ (hperm i j hij))
    (fun i j hij => hg _ _ (hperm i j hij))

end Erdos1017.PhysicalDiffuseTriangleStar

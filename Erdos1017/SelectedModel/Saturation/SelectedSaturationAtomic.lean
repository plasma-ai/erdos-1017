module

public import Erdos1017.SelectedModel.Structure.SelectedHighLowClassification
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.Models.Decorated.DecoratedAbsoluteContinuity
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalCliqueRepresentative
public import Erdos1017.Exclusions.Common.ProductRectangleLocalization
public import Erdos1017.Exclusions.Common.SelectedAtomDiffuseCharge

/-!
# Saturated pairs join distinct original atoms

Independent product sampling in the complete diffuse remainder bounds every
charge there by the negative selected multiplier, so at a selected strict-gap
optimum with multiplier above minus one, every saturated pair joins distinct
original independent whole fibers.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem tupleCharge_two_blocks {Ω : Type*} (k : ℕ) (Y : Ω → Ω → ℝ)
    (v : Fin (k + k) → Ω) (hsym : ∀ i j, Y (v i) (v j) = Y (v j) (v i)) :
    FiniteArity.tupleCharge Y v =
      FiniteArity.tupleCharge Y (fun i : Fin k => v (Fin.castAdd k i)) +
      FiniteArity.tupleCharge Y (fun j : Fin k => v (Fin.natAdd k j)) +
      ∑ i : Fin k, ∑ j : Fin k, Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j)) := by
  have hcross (i j : Fin k) : Fin.castAdd k i ≠ Fin.natAdd k j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hcrosssym (i j : Fin k) :
      Y (v (Fin.natAdd k i)) (v (Fin.castAdd k j)) =
        Y (v (Fin.castAdd k j)) (v (Fin.natAdd k i)) := hsym _ _
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  simp only [Fin.sum_univ_add, Fin.castAdd_inj, Fin.natAdd_inj]
  simp only [hcross, Ne.symm (hcross _ _), ↓reduceIte]
  simp only [Finset.sum_add_distrib]
  simp_rw [hcrosssym]
  rw [Finset.sum_comm (f := fun i j : Fin k => Y (v (Fin.castAdd k j)) (v (Fin.natAdd k i)))]
  ring

private theorem tupleCharge_ge_choose {Ω : Type*} (k : ℕ) (Y : Ω → Ω → ℝ)
    (v : Fin k → Ω) (m : ℝ) (hlower : ∀ i j, i ≠ j → m ≤ Y (v i) (v j)) :
    (k.choose 2 : ℝ) * m ≤ FiniteArity.tupleCharge Y v := by
  let y : Fin k → Fin k → ℝ := fun i j => if i = j then 0 else Y (v i) (v j)
  have hy (i : Fin k) : y i i = 0 := by simp [y]
  change (k.choose 2 : ℝ) * m ≤ FiniteArity.pairCharge Finset.univ y
  rw [FiniteArity.pairCharge_eq_sum_pairs Finset.univ y hy]
  calc
    (k.choose 2 : ℝ) * m = ∑ _ ∈ (Finset.univ : Finset (Fin k)).powersetCard 2, m := by
      simp [Finset.card_powersetCard, mul_comm]
    _ ≤ ∑ t ∈ (Finset.univ : Finset (Fin k)).powersetCard 2,
        FiniteArity.pairCharge t y := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨i, j, hij, heq⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp ht).2
      subst t
      rw [FiniteArity.pairCharge_pair i j hij y hy]
      have h1 := hlower i j hij
      have h2 := hlower j i hij.symm
      simp only [y, hij, hij.symm, ↓reduceIte]
      linarith

private theorem measurePreserving_pair_pi {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (fun v : Fin n → Ω => (v i, v j))
      (Measure.pi ν) ((ν i).prod (ν j)) := by
  have hind : iIndepFun (fun i (v : Fin n → Ω) => v i) (Measure.pi ν) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval ν i).map_eq, (measurePreserving_eval ν j).map_eq]

private theorem integral_two_block_cross {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (ν : Fin (k + k) → Measure Ω)
    [∀ i, IsProbabilityMeasure (ν i)] (νU νV : Measure Ω)
    (hU : ∀ i : Fin k, ν (Fin.castAdd k i) = νU)
    (hV : ∀ j : Fin k, ν (Fin.natAdd k j) = νV)
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B) :
    (∫ v, (∑ i : Fin k, ∑ j : Fin k,
        Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j))) ∂Measure.pi ν) =
      (k : ℝ) ^ 2 * ∫ p, Y p.1 p.2 ∂νU.prod νV := by
  have hpair (i j : Fin k) :
      (∫ v, Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j)) ∂Measure.pi ν) =
        ∫ p, Y p.1 p.2 ∂νU.prod νV := by
    have hij : Fin.castAdd k i ≠ Fin.natAdd k j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have hp := measurePreserving_pair_pi ν _ _ hij
    have hm : (∫ p, Y p.1 p.2
        ∂Measure.map (fun v : Fin (k + k) → Ω =>
          (v (Fin.castAdd k i), v (Fin.natAdd k j))) (Measure.pi ν)) =
        ∫ v, Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j)) ∂Measure.pi ν :=
      integral_map hp.measurable.aemeasurable hY.aestronglyMeasurable
    rw [hp.map_eq, hU i, hV j] at hm
    exact hm.symm
  have hint (i j : Fin k) : Integrable
      (fun v : Fin (k + k) → Ω => Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j)))
      (Measure.pi ν) := by
    have hpairmeas : Measurable (fun v : Fin (k + k) → Ω =>
        (v (Fin.castAdd k i), v (Fin.natAdd k j))) :=
      (measurable_pi_apply (Fin.castAdd k i)).prodMk
        (measurable_pi_apply (Fin.natAdd k j))
    have hmeas := hY.comp hpairmeas
    change Measurable (fun v : Fin (k + k) → Ω =>
      Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j))) at hmeas
    apply Integrable.of_bound hmeas.aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun v => hB
      (v (Fin.castAdd k i), v (Fin.natAdd k j)))
  have hintsum (i : Fin k) : Integrable
      (fun v : Fin (k + k) → Ω => ∑ j : Fin k,
        Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j))) (Measure.pi ν) :=
    integrable_finsetSum _ (fun j _ => hint i j)
  rw [integral_finsetSum Finset.univ (fun i _ => hintsum i)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hint _ j), hpair]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring

private theorem two_block_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (D U V : Set Ω) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUD : U ⊆ D) (hVD : V ⊆ D) (hUpos : 0 < μ U) (hVpos : 0 < μ V)
    (m : ℝ)
    (hclique : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = true)
    (hlower : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → m ≤ Y p.1 p.2)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (k : ℕ) :
    (k : ℝ) ^ 2 *
      (∫ p, Y p.1 p.2
        ∂(ProbabilityTheory.cond μ U).prod (ProbabilityTheory.cond μ V)) ≤
      1 - 2 * (k.choose 2 : ℝ) * m := by
  let ν : Fin (k + k) → Measure Ω := fun i =>
    if i.val < k then ProbabilityTheory.cond μ U else ProbabilityTheory.cond μ V
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ U) :=
    ProbabilityTheory.cond_isProbabilityMeasure hUpos.ne'
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ V) :=
    ProbabilityTheory.cond_isProbabilityMeasure hVpos.ne'
  have : ∀ i, IsProbabilityMeasure (ν i) := by
    intro i
    dsimp [ν]
    split_ifs <;> infer_instance
  have hνU (i : Fin k) : ν (Fin.castAdd k i) = ProbabilityTheory.cond μ U := by
    simp only [ν, Fin.val_castAdd, i.isLt, ↓reduceIte]
  have hνV (j : Fin k) : ν (Fin.natAdd k j) = ProbabilityTheory.cond μ V := by
    have hj : ¬(Fin.natAdd k j).val < k := by simp only [Fin.val_natAdd]; omega
    simp only [ν, hj, ↓reduceIte]
  have hac : Measure.pi ν ≪ Measure.pi (fun _ : Fin (k + k) => μ) :=
    Erdos1017.PhysicalCliqueRepresentative.pi_absolutelyContinuous μ ν (fun i => by
      dsimp [ν]
      split_ifs <;> exact ProbabilityTheory.cond_absolutelyContinuous)
  have hinside : ∀ᵐ v ∂Measure.pi ν, ∀ i : Fin (k + k), v i ∈ D := by
    apply ae_all_iff.mpr
    intro i
    have hi : ∀ᵐ x ∂ν i, x ∈ D := by
      dsimp [ν]
      split_ifs with h
      · exact (ProbabilityTheory.ae_cond_mem hU).mono (fun _ hx => hUD hx)
      · exact (ProbabilityTheory.ae_cond_mem hV).mono (fun _ hx => hVD hx)
    exact (measurePreserving_eval ν i).quasiMeasurePreserving.ae hi
  have hpairs : ∀ᵐ v ∂Measure.pi ν, ∀ i j : Fin (k + k), i ≠ j →
      (A (v i) (v j) = true ∧ m ≤ Y (v i) (v j)) := by
    have hbase := FiniteArity.ae_all_pairs μ (k + k) _ (hclique.and hlower)
    filter_upwards [hac.ae_le hbase, hinside] with v hv hmem i j hij
    have hp := hv i j hij
    exact ⟨hp.1 (hmem i) (hmem j), hp.2 (hmem i) (hmem j)⟩
  have htest := hac.ae_le (hfull (k + k))
  have hcross : ∀ᵐ v ∂Measure.pi ν,
      (∑ i : Fin k, ∑ j : Fin k,
        Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j))) ≤
      1 - 2 * (k.choose 2 : ℝ) * m := by
    filter_upwards [hpairs, htest] with v hp ht
    have hclq : FiniteArity.TupleClique A v := fun i j hij => (hp i j hij).1
    have hleft : (k.choose 2 : ℝ) * m ≤
        FiniteArity.tupleCharge Y (fun i : Fin k => v (Fin.castAdd k i)) := by
      apply tupleCharge_ge_choose
      intro i j hij
      exact (hp _ _ (fun heq => hij ((Fin.castAdd_injective k k) heq))).2
    have hright : (k.choose 2 : ℝ) * m ≤
        FiniteArity.tupleCharge Y (fun j : Fin k => v (Fin.natAdd k j)) := by
      apply tupleCharge_ge_choose
      intro i j hij
      exact (hp _ _ (fun heq => hij ((Fin.natAdd_injective k k) heq))).2
    have hcharge := ht hclq
    rw [tupleCharge_two_blocks k Y v (fun i j => hYsym _ _)] at hcharge
    linarith
  have hint : Integrable (fun v : Fin (k + k) → Ω =>
      ∑ i : Fin k, ∑ j : Fin k,
        Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j))) (Measure.pi ν) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    have hmeas : Measurable (fun v : Fin (k + k) → Ω =>
        Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j))) := by
      have hpairmeas : Measurable (fun v : Fin (k + k) → Ω =>
          (v (Fin.castAdd k i), v (Fin.natAdd k j))) :=
        (measurable_pi_apply (Fin.castAdd k i)).prodMk
          (measurable_pi_apply (Fin.natAdd k j))
      have h := hY.comp hpairmeas
      change Measurable (fun v : Fin (k + k) → Ω =>
        Y (v (Fin.castAdd k i)) (v (Fin.natAdd k j))) at h
      exact h
    apply Integrable.of_bound hmeas.aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun v => hB
      (v (Fin.castAdd k i), v (Fin.natAdd k j)))
  have hbound := integral_mono_ae hint (integrable_const _)
    hcross
  rw [integral_two_block_cross k ν _ _ hνU hνV Y hY B hB] at hbound
  simpa using hbound

private theorem two_block_cond_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (D U V : Set Ω) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUD : U ⊆ D) (hVD : V ⊆ D) (hUpos : 0 < μ U) (hVpos : 0 < μ V)
    (m : ℝ)
    (hclique : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = true)
    (hlower : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → m ≤ Y p.1 p.2)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    (∫ p, Y p.1 p.2
      ∂(ProbabilityTheory.cond μ U).prod (ProbabilityTheory.cond μ V)) ≤ -m := by
  let I : ℝ := ∫ p, Y p.1 p.2
    ∂(ProbabilityTheory.cond μ U).prod (ProbabilityTheory.cond μ V)
  have hseq (n : ℕ) :
      I ≤ -m + m / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hk : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h := two_block_integral_bound μ A Y hY hYsym B hB D U V hU hV
      hUD hVD hUpos hVpos m hclique hlower hfull (n + 1)
    rw [Nat.cast_choose_two ℝ] at h
    change ((↑(n + 1) : ℝ) ^ 2) * I ≤
      1 - 2 * (((↑(n + 1) : ℝ) * (↑(n + 1) - 1)) / 2) * m at h
    have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := hk.ne'
    have heq :
        (-m + m / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) ^ 2) *
          ((n + 1 : ℕ) : ℝ) ^ 2 =
          1 - 2 * (((↑(n + 1) : ℝ) * (↑(n + 1) - 1)) / 2) * m := by
      field_simp
      ring
    rw [← heq] at h
    exact le_of_mul_le_mul_right (by simpa only [mul_comm] using h)
      (sq_pos_of_pos hk)
  have ht : Filter.Tendsto
      (fun n : ℕ => -m + m / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds (-m)) := by
    have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_nhds.add (hzero.const_mul m)).add (hzero.pow 2)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Filter.Eventually.of_forall hseq)

private theorem two_block_rectangle_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (D U V : Set Ω) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUD : U ⊆ D) (hVD : V ⊆ D) (hUpos : 0 < μ U) (hVpos : 0 < μ V)
    (m : ℝ)
    (hclique : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = true)
    (hlower : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → m ≤ Y p.1 p.2)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    (∫ p in U ×ˢ V, Y p.1 p.2 ∂μ.prod μ) ≤
      (-m) * μ.real U * μ.real V := by
  have h := two_block_cond_bound μ A Y hY hYsym B hB D U V hU hV
    hUD hVD hUpos hVpos m hclique hlower hfull
  change (∫ p, Y p.1 p.2
      ∂(Erdos1017.PhysicalCliqueRepresentative.cellLaw μ U).prod
        (Erdos1017.PhysicalCliqueRepresentative.cellLaw μ V)) ≤ -m at h
  rw [Erdos1017.PhysicalCliqueRepresentative.integral_cellLaw_prod μ U V
    hUpos.ne' hVpos.ne'] at h
  have hmass : (μ.prod μ).real (U ×ˢ V) = μ.real U * μ.real V := by
    change ((μ.prod μ) (U ×ˢ V)).toReal = (μ U).toReal * (μ V).toReal
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hscale := measure_smul_average ((μ.prod μ).restrict (U ×ˢ V))
    (fun p : Ω × Ω => Y p.1 p.2)
  simp only [smul_eq_mul] at hscale
  have hreal : ((μ.prod μ).restrict (U ×ˢ V)).real univ =
      (μ.prod μ).real (U ×ˢ V) := by
    change (((μ.prod μ).restrict (U ×ˢ V)) univ).toReal =
      ((μ.prod μ) (U ×ˢ V)).toReal
    simp
  rw [← hscale, hreal, hmass]
  have hnonneg : 0 ≤ μ.real U * μ.real V :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h hnonneg]

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

variable {W : Model Ω μ} {m : ℝ}

/-- Independent product sampling inside the original complete diffuse remainder
bounds every original charge there by the negative selected multiplier. -/
theorem charge_le_neg_multiplier_on_diffuse_sq
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
      chargeKernel W p.1 p.2 ≤ -m := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := hW.strict_gap_structure hd hgap
  have hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n :=
    PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic
  have hclique : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
      A p.1 p.2 = true := by
    filter_upwards [S.hDcomplete,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support]
      with p hc ha hx hy
    have h := hc hx hy
    rw [ha] at h
    split_ifs at h with hA
    · exact hA
    · norm_num at h
  have hlower : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
      m ≤ Y p.1 p.2 := by
    filter_upwards [S.hDcomplete, hW.moment_mem,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support]
      with p hc hk hy hx hz
    have hA := hc hx hz
    have hK := hk.1
    rw [shiftedMoment_eq] at hK
    change 0 ≤ chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2 at hK
    change adjacencyKernel W p.1 p.2 = 1 at hA
    rw [hA] at hK
    dsimp [Y]
    rw [hy]
    linarith
  by_cases hDpos : 0 < μ S.D
  · let ν := ProbabilityTheory.cond μ S.D
    have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hDpos.ne'
    have hνac : ν ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
    have hνmem : ∀ᵐ x ∂ν, x ∈ S.D := ProbabilityTheory.ae_cond_mem S.hD
    have hνpair : ∀ᵐ p ∂ν.prod ν, p.1 ∈ S.D ∧ p.2 ∈ S.D :=
      (Measure.quasiMeasurePreserving_fst.ae hνmem).and
        (Measure.quasiMeasurePreserving_snd.ae hνmem)
    have hcliqueν : ∀ᵐ p ∂ν.prod ν, p.1 ∈ univ → p.2 ∈ univ →
        A p.1 p.2 = true := by
      filter_upwards [(hνac.prod hνac).ae_le hclique, hνpair]
        with p hp hD _ _
      exact hp hD.1 hD.2
    have hlowerν : ∀ᵐ p ∂ν.prod ν, p.1 ∈ univ → p.2 ∈ univ →
        m ≤ Y p.1 p.2 := by
      filter_upwards [(hνac.prod hνac).ae_le hlower, hνpair]
        with p hp hD _ _
      exact hp hD.1 hD.2
    have hfullν : ∀ n, FiniteArity.FeasibleOrder ν A Y n := by
      intro n
      exact (DecoratedKernel.pi_absolutelyContinuous hνac n).ae_le (hfull n)
    have hrect : ∀ U V, MeasurableSet U → MeasurableSet V →
        (∫ p in U ×ˢ V, Y p.1 p.2 ∂ν.prod ν) ≤
          (-m) * ν.real U * ν.real V := by
      intro U V hU hV
      by_cases hUpos : 0 < ν U
      · by_cases hVpos : 0 < ν V
        · exact two_block_rectangle_bound ν A Y
            (PhysicalRepresentative.measurable_charge W m)
            (PhysicalRepresentative.charge_symm W m) 3
            (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
            univ U V hU hV (subset_univ _) (subset_univ _) hUpos hVpos
            m hcliqueν hlowerν hfullν
        · have hVzero : ν V = 0 := le_antisymm (le_of_not_gt hVpos) bot_le
          have hVreal : ν.real V = 0 := by change (ν V).toReal = 0; simp [hVzero]
          have hrectzero : (ν.prod ν) (U ×ˢ V) = 0 := by
            rw [Measure.prod_prod, hVzero]
            simp
          rw [setIntegral_measure_zero (fun p : Ω × Ω => Y p.1 p.2) hrectzero,
            hVreal]
          norm_num
      · have hUzero : ν U = 0 := le_antisymm (le_of_not_gt hUpos) bot_le
        have hUreal : ν.real U = 0 := by change (ν U).toReal = 0; simp [hUzero]
        have hrectzero : (ν.prod ν) (U ×ˢ V) = 0 := by
          rw [Measure.prod_prod, hUzero]
          simp
        rw [setIntegral_measure_zero (fun p : Ω × Ω => Y p.1 p.2) hrectzero,
          hUreal]
        norm_num
    have hYν : ∀ᵐ p ∂ν.prod ν, Y p.1 p.2 ≤ -m :=
      ProductRectangleLocalization.ae_le_of_forall_rectangle_integral_le
        (Function.uncurry Y) (PhysicalRepresentative.measurable_charge W m)
        3 (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2) (-m) hrect
    have hνD : μ.restrict S.D ≪ ν := by
      change μ.restrict S.D ≪ ProbabilityTheory.cond μ S.D
      rw [ProbabilityTheory.cond]
      exact Measure.absolutelyContinuous_smul (by simp [measure_ne_top])
    have hrestricted : ∀ᵐ p ∂(μ.restrict S.D).prod (μ.restrict S.D),
        chargeKernel W p.1 p.2 ≤ -m := by
      filter_upwards [(hνD.prod hνD).ae_le hYν,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          (PhysicalRepresentative.charge_ae_eq W m hs.strict_support)]
        with p hp heq
      rw [← heq]
      exact hp
    rw [Measure.prod_restrict] at hrestricted
    have hraw := (ae_restrict_iff' (S.hD.prod S.hD)).mp hrestricted
    filter_upwards [hraw] with p hp hx hy
    exact hp ⟨hx, hy⟩
  · have hDzero : μ S.D = 0 := le_antisymm (le_of_not_gt hDpos) bot_le
    have hrect : (μ.prod μ) (S.D ×ˢ S.D) = 0 := by
      rw [Measure.prod_prod, hDzero]
      simp
    have hzero : (μ.prod μ).restrict (S.D ×ˢ S.D) = 0 :=
      Measure.restrict_eq_zero.mpr hrect
    have hraw : ∀ᵐ p ∂μ.prod μ, p ∈ S.D ×ˢ S.D →
        chargeKernel W p.1 p.2 ≤ -m := by
      apply (ae_restrict_iff' (S.hD.prod S.hD)).mp
      rw [hzero]
      simp
    filter_upwards [hraw] with p hp hx hy
    exact hp ⟨hx, hy⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace ↥(Lp ℝ 2 μ)] in
private theorem saturation_atoms_of_caps (S : SelectedHighLowStructure W m)
    (a b : ℝ) (ha : a < 1) (hb : b < 1)
    (hDD : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
      chargeKernel W p.1 p.2 ≤ a)
    (hID : ∀ r : S.I, ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∈ S.D →
      chargeKernel W p.1 p.2 ≤ b) :
    ∀ᵐ p ∂μ.prod μ, chargeKernel W p.1 p.2 = 1 →
      ∃ r s : S.I, r ≠ s ∧ S.ρ p.1 = r.val ∧ S.ρ p.2 = s.val := by
  let : Countable S.I := S.hI.to_subtype
  have hII (r : S.I) : ∀ᵐ p ∂μ.prod μ,
      S.ρ p.1 = r.val → S.ρ p.2 = r.val → chargeKernel W p.1 p.2 = 0 := by
    have h := (S.hfibers r.val r.property).2.2.1
    rw [Measure.prod_restrict] at h
    have hg := (ae_restrict_iff' ((S.hfibers r.val r.property).1.prod
      (S.hfibers r.val r.property).1)).mp h
    filter_upwards [hg] with p hp hx hy
    have he := hp ⟨hx, hy⟩
    have hlo := neg_three_adjacency_moment_le_charge W p
    have hhi := charge_moment_le_adjacency W p
    change W.moment CappedColor.adjacency p = 0 at he
    change W.moment CappedColor.charge p = 0
    rw [he] at hlo hhi
    linarith
  have hIIs : ∀ᵐ p ∂μ.prod μ, ∀ r : S.I,
      S.ρ p.1 = r.val → S.ρ p.2 = r.val → chargeKernel W p.1 p.2 = 0 :=
    ae_all_iff.mpr hII
  have hIDs : ∀ᵐ p ∂μ.prod μ, ∀ r : S.I,
      S.ρ p.1 = r.val → p.2 ∈ S.D → chargeKernel W p.1 p.2 ≤ b :=
    ae_all_iff.mpr hID
  have hDIs := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hIDs
  have hAtomOfNotD (x : Ω) (hx : x ∉ S.D) : ∃ r : S.I, S.ρ x = r.val := by
    have hu : x ∈ ⋃ r ∈ S.I, {x | S.ρ x = r} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hx
    obtain ⟨r, hr⟩ := mem_iUnion.mp hu
    obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
    exact ⟨⟨r, hrI⟩, hxr⟩
  filter_upwards [hDD, hIDs, hDIs, hIIs, chargeKernel_symm W] with p hdd hid hdi hii hsym hsat
  have hx : p.1 ∉ S.D := by
    intro hx
    by_cases hy : p.2 ∈ S.D
    · have hc := hdd hx hy
      rw [hsat] at hc
      linarith
    · obtain ⟨s, hs⟩ := hAtomOfNotD p.2 hy
      have hc := hdi s hs hx
      change chargeKernel W p.2 p.1 ≤ b at hc
      rw [← hsym, hsat] at hc
      linarith
  obtain ⟨r, hr⟩ := hAtomOfNotD p.1 hx
  have hy : p.2 ∉ S.D := by
    intro hy
    have hc := hid r hr hy
    rw [hsat] at hc
    linarith
  obtain ⟨s, hs⟩ := hAtomOfNotD p.2 hy
  refine ⟨r, s, ?_, hr, hs⟩
  intro heq
  have hz := hii r hr (heq ▸ hs)
  rw [hsat] at hz
  norm_num at hz

/-- At a selected strict-gap optimum with multiplier above minus one, every
actual saturated pair joins distinct original independent whole fibers. -/
theorem ae_saturated_pair_between_distinct_original_atoms
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ p ∂μ.prod μ, chargeKernel W p.1 p.2 = 1 →
      ∃ r s : S.I, r ≠ s ∧ S.ρ p.1 = r.val ∧ S.ρ p.2 = s.val := by
  apply S.saturation_atoms_of_caps (-m) ((1 - m) / 2) hell (by linarith)
  · exact S.charge_le_neg_multiplier_on_diffuse_sq hW hd hgap
  · intro r
    exact S.charge_le_half_one_sub_multiplier_on_atom_diffuse hW hd hgap r

end Erdos1017.CappedModel.SelectedHighLowStructure

module

public import Erdos1017.Models.Capped.CappedModel
public import Erdos1017.Models.Decorated.DecoratedCountingIntegration
public import Graphon.CutDistance
public import Graphon.HomDensity

/-!
# Colored counting with one graphon per pair

A clipped pointwise representative of a graphon (`eval01`) leaves colored
densities and sampled vertex-pair values unchanged, and the colored density with
one graphon per unordered clique pair differs between two families by at most
the sum of the pairwise cut-norm differences.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.DecoratedCounting

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A pointwise `[0,1]` representative of a graphon, equal to it almost everywhere. -/
def eval01 (U : Graphon Ω μ) (p : Ω × Ω) : ℝ :=
  max 0 (min 1 (U.toAEEqFun p))

theorem measurable_eval01 (U : Graphon Ω μ) : Measurable (eval01 U) :=
  measurable_const.max (measurable_const.min U.toAEEqFun.measurable)

theorem eval01_mem_Icc (U : Graphon Ω μ) (p : Ω × Ω) : eval01 U p ∈ Set.Icc 0 1 := by
  unfold eval01
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem eval01_ae_eq (U : Graphon Ω μ) :
    ∀ᵐ p ∂μ.prod μ, eval01 U p = U.toAEEqFun p := by
  filter_upwards [U.ae_mem_Icc] with p hp
  simp [eval01, min_eq_right hp.2, max_eq_right hp.1]

/-- Product of pair-specific graphons evaluated on independently sampled vertices. -/
def coloredDensity (n : ℕ) (U : CliquePair n → Graphon Ω μ) : ℝ :=
  ∫ x : Fin n → Ω,
    ∏ e, eval01 (U e) (x e.val.1, x e.val.2)
      ∂Measure.pi (fun _ : Fin n => μ)

variable [IsProbabilityMeasure μ]

/-- Clipping does not change a graphon value at a sampled distinct vertex pair. -/
theorem eval01_vertex_ae_eq (n : ℕ) (U : Graphon Ω μ) (e : CliquePair n) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      eval01 U (x e.val.1, x e.val.2) = U.toAEEqFun (x e.val.1, x e.val.2) := by
  filter_upwards [Graphon.graphonEval_mem_Icc_ae U (ne_of_lt e.property)] with x hx
  simp [eval01, min_eq_right hx.2, max_eq_right hx.1]

/-- The clipped colored density equals the integral of the original AEEqFun moments. -/
theorem coloredDensity_eq_integral (n : ℕ) (U : CliquePair n → Graphon Ω μ) :
    coloredDensity n U =
      ∫ x : Fin n → Ω, ∏ e, (U e).toAEEqFun (x e.val.1, x e.val.2)
        ∂Measure.pi (fun _ : Fin n => μ) := by
  unfold coloredDensity
  apply integral_congr_ae
  have h : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ e : CliquePair n,
      eval01 (U e) (x e.val.1, x e.val.2) =
        (U e).toAEEqFun (x e.val.1, x e.val.2) :=
    (ae_all_iff).mpr (fun e => eval01_vertex_ae_eq n (U e) e)
  filter_upwards [h] with x hx
  exact Finset.prod_congr rfl (fun e _ => hx e)

omit [IsProbabilityMeasure μ] in
/-- The clipped colored integrand is measurable and bounded in `[0,1]`. -/
theorem coloredIntegrand_measurable (n : ℕ) (U : CliquePair n → Graphon Ω μ) :
    Measurable (fun x : Fin n → Ω =>
      ∏ e, eval01 (U e) (x e.val.1, x e.val.2)) := by
  apply Finset.measurable_prod
  intro e _
  exact (measurable_eval01 (U e)).comp
    ((measurable_pi_apply e.val.1).prodMk (measurable_pi_apply e.val.2))

omit [IsProbabilityMeasure μ] in
theorem coloredIntegrand_mem_Icc (n : ℕ) (U : CliquePair n → Graphon Ω μ)
    (x : Fin n → Ω) :
    (∏ e, eval01 (U e) (x e.val.1, x e.val.2)) ∈ Set.Icc 0 1 := by
  refine ⟨Finset.prod_nonneg (fun e _ => (eval01_mem_Icc (U e) _).1), ?_⟩
  apply Finset.prod_le_one₀
  · intro e _
    exact (eval01_mem_Icc (U e) _).1
  · intro e _
    exact (eval01_mem_Icc (U e) _).2

theorem coloredIntegrand_integrable (n : ℕ) (U : CliquePair n → Graphon Ω μ) :
    Integrable (fun x : Fin n → Ω =>
      ∏ e, eval01 (U e) (x e.val.1, x e.val.2))
      (Measure.pi (fun _ : Fin n => μ)) :=
  Integrable.of_mem_Icc 0 1 (coloredIntegrand_measurable n U).aemeasurable
    (Filter.Eventually.of_forall (coloredIntegrand_mem_Icc n U))

/-- Whether an unordered clique pair meets a vertex. -/
def touches {n : ℕ} (e : CliquePair n) (v : Fin n) : Prop :=
  e.val.1 = v ∨ e.val.2 = v

theorem touches_both_eq {n : ℕ} (e j : CliquePair n)
    (hja : touches j e.val.1) (hjb : touches j e.val.2) : j = e := by
  apply Subtype.ext
  rcases hja with hja | hja <;> rcases hjb with hjb | hjb
  · exfalso
    have : e.val.1 = e.val.2 := hja.symm.trans hjb
    exact (ne_of_lt e.property) this
  · exact Prod.ext hja hjb
  · exfalso
    have hj : j.val.1 < j.val.2 := j.property
    have he : e.val.1 < e.val.2 := e.property
    omega
  · exfalso
    have : e.val.1 = e.val.2 := hja.symm.trans hjb
    exact (ne_of_lt e.property) this

private def indexedProduct {n m : ℕ} (E : Fin m → CliquePair n)
    (U : Fin m → Graphon Ω μ) (s : Finset (Fin m)) (x : Fin n → Ω) : ℝ :=
  ∏ j ∈ s, eval01 (U j) (x (E j).val.1, x (E j).val.2)

omit [IsProbabilityMeasure μ] in
private theorem indexedProduct_measurable {n m : ℕ} (E : Fin m → CliquePair n)
    (U : Fin m → Graphon Ω μ) (s : Finset (Fin m)) :
    Measurable (indexedProduct E U s) := by
  apply Finset.measurable_prod
  intro j _
  exact (measurable_eval01 (U j)).comp
    ((measurable_pi_apply (E j).val.1).prodMk
      (measurable_pi_apply (E j).val.2))

omit [IsProbabilityMeasure μ] in
private theorem indexedProduct_mem_Icc {n m : ℕ} (E : Fin m → CliquePair n)
    (U : Fin m → Graphon Ω μ) (s : Finset (Fin m)) (x : Fin n → Ω) :
    indexedProduct E U s x ∈ Set.Icc 0 1 := by
  refine ⟨Finset.prod_nonneg (fun j _ => (eval01_mem_Icc (U j) _).1), ?_⟩
  apply Finset.prod_le_one₀
  · intro j _
    exact (eval01_mem_Icc (U j) _).1
  · intro j _
    exact (eval01_mem_Icc (U j) _).2

private theorem indexedProduct_integrable {n m : ℕ} (E : Fin m → CliquePair n)
    (U : Fin m → Graphon Ω μ) (s : Finset (Fin m)) :
    Integrable (indexedProduct E U s) (Measure.pi (fun _ : Fin n => μ)) :=
  Integrable.of_mem_Icc 0 1 (indexedProduct_measurable E U s).aemeasurable
    (Filter.Eventually.of_forall (indexedProduct_mem_Icc E U s))

omit [IsProbabilityMeasure μ] in
private theorem indexedProduct_update {n m : ℕ} (E : Fin m → CliquePair n)
    (U : Fin m → Graphon Ω μ) (s : Finset (Fin m)) (v : Fin n)
    (hs : ∀ j ∈ s, ¬touches (E j) v) (x : Fin n → Ω) (y : Ω) :
    indexedProduct E U s (Function.update x v y) = indexedProduct E U s x := by
  unfold indexedProduct
  apply Finset.prod_congr rfl
  intro j hj
  have h1 : (E j).val.1 ≠ v := by
    intro h
    exact hs j hj (Or.inl h)
  have h2 : (E j).val.2 ≠ v := by
    intro h
    exact hs j hj (Or.inr h)
  simp [Function.update_of_ne h1, Function.update_of_ne h2]

private def hybridKernel {m : ℕ} (U V : Fin m → Graphon Ω μ)
    (i j : Fin m) : Graphon Ω μ :=
  if j < i then U j else V j

private def hybridWeight {n m : ℕ} (E : Fin m → CliquePair n)
    (U V : Fin m → Graphon Ω μ) (i : Fin m)
    (s : Finset (Fin m)) (x : Fin n → Ω) : ℝ :=
  indexedProduct E (hybridKernel U V i) s x

omit [IsProbabilityMeasure μ] in
open scoped Classical in
private theorem hybridWeight_split {n m : ℕ} (E : Fin m → CliquePair n)
    (U V : Fin m → Graphon Ω μ) (i : Fin m)
    (s : Finset (Fin m)) (x : Fin n → Ω) :
    hybridWeight E U V i s x =
      (∏ j ∈ s with j < i, eval01 (U j) (x (E j).val.1, x (E j).val.2)) *
      (∏ j ∈ s with i ≤ j, eval01 (V j) (x (E j).val.1, x (E j).val.2)) := by
  classical
  unfold hybridWeight indexedProduct hybridKernel
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun j : Fin m => j < i)]
  simp only [not_lt]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro j hj
  · simp [(Finset.mem_filter.mp hj).2]
  · have hji : ¬j < i := not_lt.mpr (Finset.mem_filter.mp hj).2
    simp [hji]

omit [IsProbabilityMeasure μ] in
private theorem hybridWeight_erase_eq {n m : ℕ} (E : Fin m → CliquePair n)
    (U V : Fin m → Graphon Ω μ) (i : Fin m) (x : Fin n → Ω) :
    hybridWeight E U V i (Finset.univ.erase i) x =
      (∏ j ∈ Finset.univ with j < i,
        eval01 (U j) (x (E j).val.1, x (E j).val.2)) *
      (∏ j ∈ Finset.univ with i < j,
        eval01 (V j) (x (E j).val.1, x (E j).val.2)) := by
  classical
  rw [hybridWeight_split]
  congr 1
  · apply Finset.prod_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨⟨ne_of_lt h, trivial⟩, h⟩
    · intro j _
      rfl
  · apply Finset.prod_congr
    · ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hneq, -⟩, hle⟩
        exact lt_of_le_of_ne hle hneq.symm
      · intro h
        exact ⟨⟨(ne_of_gt h), trivial⟩, h.le⟩
    · intro j _
      rfl

/-- Replacing one indexed pair factor changes the colored integral by at most
that pair's cut-norm difference. -/
private theorem abs_integral_hybrid_edge_le {n m : ℕ} (E : Fin m ≃ CliquePair n)
    (U V : Fin m → Graphon Ω μ) (i : Fin m) :
    |∫ z : Fin n → Ω,
      hybridWeight E U V i (Finset.univ.erase i) z *
        (eval01 (U i) (z (E i).val.1, z (E i).val.2) -
          eval01 (V i) (z (E i).val.1, z (E i).val.2))
        ∂Measure.pi (fun _ : Fin n => μ)| ≤ Graphon.cutNormDiff (U i) (V i) := by
  classical
  let a := (E i).val.1
  let b := (E i).val.2
  have hab : a ≠ b := ne_of_lt (E i).property
  let s : Finset (Fin m) := Finset.univ.erase i
  let K : Fin m → Graphon Ω μ := hybridKernel U V i
  let sA := s.filter (fun j => touches (E j) a)
  let sNotA := s.filter (fun j => ¬touches (E j) a)
  let sB := sNotA.filter (fun j => touches (E j) b)
  let sR := sNotA.filter (fun j => ¬touches (E j) b)
  let f : (Fin n → Ω) → ℝ := indexedProduct E K sA
  let g : (Fin n → Ω) → ℝ := indexedProduct E K sB
  let r : (Fin n → Ω) → ℝ := indexedProduct E K sR
  have hsAavoidB : ∀ j ∈ sA, ¬touches (E j) b := by
    intro j hj hjb
    have hja : touches (E j) a := (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
    exact hji (E.injective (touches_both_eq (E i) (E j) hja hjb))
  have hsBavoidA : ∀ j ∈ sB, ¬touches (E j) a := by
    intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have hsRavoidA : ∀ j ∈ sR, ¬touches (E j) a := by
    intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  have hsRavoidB : ∀ j ∈ sR, ¬touches (E j) b := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hfactor (z : Fin n → Ω) :
      hybridWeight E U V i s z = r z * f z * g z := by
    have hsplit1 := Finset.prod_filter_mul_prod_filter_not s
      (fun j => touches (E j) a)
      (fun j => eval01 (K j) (z (E j).val.1, z (E j).val.2))
    have hsplit2 := Finset.prod_filter_mul_prod_filter_not sNotA
      (fun j => touches (E j) b)
      (fun j => eval01 (K j) (z (E j).val.1, z (E j).val.2))
    change f z * (indexedProduct E K sNotA z) = hybridWeight E U V i s z at hsplit1
    change g z * r z = indexedProduct E K sNotA z at hsplit2
    rw [← hsplit1, ← hsplit2]
    ring
  have hpair := measurePreserving_pairProjection (μ := μ) a b hab
  have hclipU : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),
      eval01 (U i) (z a, z b) = (U i).toAEEqFun (z a, z b) :=
    hpair.quasiMeasurePreserving.ae (eval01_ae_eq (U i))
  have hclipV : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => μ),
      eval01 (V i) (z a, z b) = (V i).toAEEqFun (z a, z b) :=
    hpair.quasiMeasurePreserving.ae (eval01_ae_eq (V i))
  have hint :
      (∫ z : Fin n → Ω,
        hybridWeight E U V i s z *
          (eval01 (U i) (z a, z b) - eval01 (V i) (z a, z b))
          ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z : Fin n → Ω, r z * f z * g z *
        ((U i).toAEEqFun (z a, z b) - (V i).toAEEqFun (z a, z b))
          ∂Measure.pi (fun _ : Fin n => μ) := by
    apply integral_congr_ae
    filter_upwards [hclipU, hclipV] with z hzU hzV
    rw [hfactor, hzU, hzV]
  change |∫ z : Fin n → Ω,
      hybridWeight E U V i s z *
        (eval01 (U i) (z a, z b) - eval01 (V i) (z a, z b))
        ∂Measure.pi (fun _ : Fin n => μ)| ≤ _
  rw [hint]
  exact abs_integral_changed_edge_le a b hab (U i) (V i) r f g
    (indexedProduct_measurable E K sR) (indexedProduct_measurable E K sA)
    (indexedProduct_measurable E K sB)
    (indexedProduct_mem_Icc E K sR) (indexedProduct_mem_Icc E K sA)
    (indexedProduct_mem_Icc E K sB)
    (fun z x => indexedProduct_update E K sR a hsRavoidA z x)
    (fun z y => indexedProduct_update E K sR b hsRavoidB z y)
    (fun z y => indexedProduct_update E K sA b hsAavoidB z y)
    (fun z x => indexedProduct_update E K sB a hsBavoidA z x)

omit [IsProbabilityMeasure μ] in
private theorem coloredDensity_eq_indexed {n m : ℕ} (E : Fin m ≃ CliquePair n)
    (U : CliquePair n → Graphon Ω μ) :
    coloredDensity n U =
      ∫ z : Fin n → Ω,
        ∏ i : Fin m, eval01 (U (E i)) (z (E i).val.1, z (E i).val.2)
          ∂Measure.pi (fun _ : Fin n => μ) := by
  unfold coloredDensity
  congr 1
  funext z
  exact (Fintype.prod_equiv E
    (fun i : Fin m => eval01 (U (E i)) (z (E i).val.1, z (E i).val.2))
    (fun e : CliquePair n => eval01 (U e) (z e.val.1, z e.val.2))
    (fun i => rfl)).symm

private theorem integrable_hybrid_edge {n m : ℕ} (E : Fin m ≃ CliquePair n)
    (U V : Fin m → Graphon Ω μ) (i : Fin m) :
    Integrable (fun z : Fin n → Ω =>
      hybridWeight E U V i (Finset.univ.erase i) z *
        (eval01 (U i) (z (E i).val.1, z (E i).val.2) -
          eval01 (V i) (z (E i).val.1, z (E i).val.2)))
      (Measure.pi (fun _ : Fin n => μ)) := by
  let s := Finset.univ.erase i
  let K := hybridKernel U V i
  have hm : Measurable (fun z : Fin n → Ω =>
      hybridWeight E U V i s z *
        (eval01 (U i) (z (E i).val.1, z (E i).val.2) -
          eval01 (V i) (z (E i).val.1, z (E i).val.2))) := by
    exact (indexedProduct_measurable E K s).mul
      (((measurable_eval01 (U i)).comp
        ((measurable_pi_apply (E i).val.1).prodMk
          (measurable_pi_apply (E i).val.2))).sub
        ((measurable_eval01 (V i)).comp
          ((measurable_pi_apply (E i).val.1).prodMk
            (measurable_pi_apply (E i).val.2))))
  apply Integrable.of_mem_Icc (-1) 1 hm.aemeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hw := indexedProduct_mem_Icc E K s z
  have hU := eval01_mem_Icc (U i) (z (E i).val.1, z (E i).val.2)
  have hV := eval01_mem_Icc (V i) (z (E i).val.1, z (E i).val.2)
  change hybridWeight E U V i s z ∈ Set.Icc 0 1 at hw
  have hlow : -1 ≤ eval01 (U i) (z (E i).val.1, z (E i).val.2) -
      eval01 (V i) (z (E i).val.1, z (E i).val.2) := by
    linarith [hU.1, hV.2]
  have hupp : eval01 (U i) (z (E i).val.1, z (E i).val.2) -
      eval01 (V i) (z (E i).val.1, z (E i).val.2) ≤ 1 := by
    linarith [hU.2, hV.1]
  rcases hw with ⟨hwlo, hwup⟩
  have hmul₁ := mul_le_mul_of_nonneg_left hlow hwlo
  have hmul₂ := mul_le_mul_of_nonneg_left hupp hwlo
  constructor <;> nlinarith

/-- Colored counting: one graphon per unordered pair, with a bound by the
sum of the pairwise cut-norm differences. -/
theorem abs_coloredDensity_sub_le (n : ℕ)
    (U V : CliquePair n → Graphon Ω μ) :
    |coloredDensity n U - coloredDensity n V| ≤
      ∑ e : CliquePair n, Graphon.cutNormDiff (U e) (V e) := by
  classical
  let m := Fintype.card (CliquePair n)
  let E : Fin m ≃ CliquePair n := (Fintype.equivFin (CliquePair n)).symm
  let A : Fin m → Graphon Ω μ := U ∘ E
  let B : Fin m → Graphon Ω μ := V ∘ E
  let a : Fin m → (Fin n → Ω) → ℝ :=
    fun j z => eval01 (A j) (z (E j).val.1, z (E j).val.2)
  let b : Fin m → (Fin n → Ω) → ℝ :=
    fun j z => eval01 (B j) (z (E j).val.1, z (E j).val.2)
  have hpoint (z : Fin n → Ω) :
      (∏ j : Fin m, a j z) - (∏ j : Fin m, b j z) =
        ∑ i : Fin m, hybridWeight E A B i (Finset.univ.erase i) z *
          (a i z - b i z) := by
    have h := Finset.prod_add_ordered (Finset.univ : Finset (Fin m))
      (fun j => b j z) (fun j => a j z - b j z)
    simp_rw [show ∀ j : Fin m, b j z + (a j z - b j z) = a j z from
      fun j => by ring] at h
    have h' : (∏ j : Fin m, a j z) - (∏ j : Fin m, b j z) =
        ∑ i : Fin m, (a i z - b i z) *
          (∏ j ∈ Finset.univ with j < i, a j z) *
          (∏ j ∈ Finset.univ with i < j, b j z) :=
      sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)
    calc
      _ = ∑ i : Fin m, (a i z - b i z) *
          (∏ j ∈ Finset.univ with j < i, a j z) *
          (∏ j ∈ Finset.univ with i < j, b j z) := h'
      _ = ∑ i : Fin m, hybridWeight E A B i (Finset.univ.erase i) z *
          (a i z - b i z) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hybridWeight_erase_eq]
        ring
  have hA : Integrable (fun z : Fin n → Ω => ∏ j : Fin m, a j z)
      (Measure.pi (fun _ : Fin n => μ)) := indexedProduct_integrable E A Finset.univ
  have hB : Integrable (fun z : Fin n → Ω => ∏ j : Fin m, b j z)
      (Measure.pi (fun _ : Fin n => μ)) := indexedProduct_integrable E B Finset.univ
  calc
    |coloredDensity n U - coloredDensity n V|
        = |∫ z : Fin n → Ω, (∏ j : Fin m, a j z) - (∏ j : Fin m, b j z)
            ∂Measure.pi (fun _ : Fin n => μ)| := by
          rw [coloredDensity_eq_indexed E U, coloredDensity_eq_indexed E V]
          exact congrArg abs (integral_sub hA hB).symm
    _ = |∫ z : Fin n → Ω,
          ∑ i : Fin m, hybridWeight E A B i (Finset.univ.erase i) z *
            (a i z - b i z) ∂Measure.pi (fun _ : Fin n => μ)| := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = |∑ i : Fin m, ∫ z : Fin n → Ω,
          hybridWeight E A B i (Finset.univ.erase i) z * (a i z - b i z)
            ∂Measure.pi (fun _ : Fin n => μ)| := by
          rw [integral_finsetSum]
          intro i _
          exact integrable_hybrid_edge E A B i
    _ ≤ ∑ i : Fin m, |∫ z : Fin n → Ω,
          hybridWeight E A B i (Finset.univ.erase i) z * (a i z - b i z)
            ∂Measure.pi (fun _ : Fin n => μ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, Graphon.cutNormDiff (A i) (B i) := by
          apply Finset.sum_le_sum
          intro i _
          exact abs_integral_hybrid_edge_le E A B i
    _ = ∑ e : CliquePair n, Graphon.cutNormDiff (U e) (V e) := by
          exact Fintype.sum_equiv E
            (fun i : Fin m => Graphon.cutNormDiff (A i) (B i))
            (fun e : CliquePair n => Graphon.cutNormDiff (U e) (V e)) (fun i => rfl)

end Erdos1017.DecoratedCounting

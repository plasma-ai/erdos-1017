module

public import Erdos1017.Exclusions.Common.Physical.IndependentCoordinateResampling
public import Erdos1017.Models.PhysicalPrimal.TupleSampling
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Atomizing the dust class of a multipartite model

The atomized scalar kernel averages the charge over an independently resampled
`C` vertex, passes every clique test implied by the old product tests, vanishes
on new nonedges, and its total charge integral changes only by deleting the
internal `C` block.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.MultipartiteDustAtomization

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]

local instance atomizationOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance atomizationNewOptionMeasurable : MeasurableSpace (Option (ι ⊕ Unit)) := ⊤
local instance atomizationDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Independent labels are unequal on edges, while none is genuine clique dust. -/
def adjacency (labels : Ω → Option ι) (x y : Ω) : Bool :=
  if labels x ≠ labels y ∨ labels x = none then true else false

omit [Countable ι] [MeasurableSpace Ω] in
theorem adjacency_eq_true_iff (labels : Ω → Option ι) (x y : Ω) :
    adjacency labels x y = true ↔ labels x ≠ labels y ∨ labels x = none := by
  classical
  unfold adjacency
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun he => False.elim he, fun hp => False.elim (h hp)⟩

omit [Countable ι] [MeasurableSpace Ω] in
theorem adjacency_symm (labels : Ω → Option ι) (x y : Ω) :
    adjacency labels x y = adjacency labels y x := by
  classical
  cases h₁ : labels x <;> cases h₂ : labels y <;>
    simp [adjacency, h₁, h₂, ne_comm]

theorem measurable_adjacency (labels : Ω → Option ι) (hlabels : Measurable labels) :
    Measurable (Function.uncurry (adjacency labels)) :=
  Measurable.ite
    ((measurableSet_eq_fun (hlabels.comp measurable_fst) (hlabels.comp measurable_snd)).compl.union
      ((hlabels.comp measurable_fst) (measurableSet_singleton none)))
    measurable_const measurable_const

/-- Atomization keeps every old independent class, makes C one new class,
and retains the rest of the old none fiber as genuine clique dust. -/
def atomizedLabels (labels : Ω → Option ι) (C : Set Ω) (x : Ω) : Option (ι ⊕ Unit) := by
  classical
  exact if x ∈ C then some (.inr ()) else (labels x).map Sum.inl

theorem measurable_atomizedLabels (labels : Ω → Option ι) (hlabels : Measurable labels)
    (C : Set Ω) (hC : MeasurableSet C) : Measurable (atomizedLabels labels C) :=
  Measurable.ite hC measurable_const ((measurable_of_countable (Option.map Sum.inl)).comp hlabels)

omit [Countable ι] [MeasurableSpace Ω] in
theorem atomized_old_fiber (labels : Ω → Option ι) (C : Set Ω)
    (hCdust : C ⊆ labels ⁻¹' {none}) (i : ι) :
    atomizedLabels labels C ⁻¹' {some (.inl i)} = labels ⁻¹' {some i} := by
  classical
  ext x
  by_cases hx : x ∈ C
  · have hlabel : labels x = none := hCdust hx
    simp [atomizedLabels, hx, hlabel]
  · cases hl : labels x <;> simp [atomizedLabels, hx, hl]

omit [Countable ι] [MeasurableSpace Ω] in
theorem atomized_new_fiber (labels : Ω → Option ι) (C : Set Ω) :
    atomizedLabels labels C ⁻¹' {some (.inr ())} = C := by
  classical
  ext x
  by_cases hx : x ∈ C <;> cases hl : labels x <;> simp [atomizedLabels, hx, hl]

omit [Countable ι] [MeasurableSpace Ω] in
theorem atomized_dust_fiber (labels : Ω → Option ι) (C : Set Ω) :
    atomizedLabels labels C ⁻¹' {none} = labels ⁻¹' {none} \ C := by
  classical
  ext x
  by_cases hx : x ∈ C <;> cases hl : labels x <;> simp [atomizedLabels, hx, hl]

omit [Countable ι] [MeasurableSpace Ω] in
theorem adjacency_outside (labels : Ω → Option ι) (C : Set Ω) {x y : Ω}
    (hx : x ∉ C) (hy : y ∉ C) :
    adjacency (atomizedLabels labels C) x y = adjacency labels x y := by
  classical
  cases h₁ : labels x <;> cases h₂ : labels y <;>
    simp [adjacency, atomizedLabels, hx, hy, h₁, h₂]

omit [Countable ι] [MeasurableSpace Ω] in
theorem clique_at_most_one {n : ℕ} (labels : Ω → Option ι) (C : Set Ω)
    (v : Fin n → Ω) (hv : FiniteArity.TupleClique (adjacency (atomizedLabels labels C)) v)
    (i j : Fin n) (hij : i ≠ j) (hi : v i ∈ C) : v j ∉ C := by
  classical
  intro hj
  have h := hv i j hij
  simp only [adjacency, atomizedLabels, hi, hj, ↓reduceIte, ne_eq,
    not_true_eq_false, Option.some_ne_none, or_self, Bool.false_eq_true] at h

omit [Countable ι] [MeasurableSpace Ω] in
theorem clique_outside_old {n : ℕ} (labels : Ω → Option ι) (C : Set Ω)
    (v : Fin n → Ω) (hv : FiniteArity.TupleClique (adjacency (atomizedLabels labels C)) v)
    (hout : ∀ i, v i ∉ C) : FiniteArity.TupleClique (adjacency labels) v := by
  intro i j hij
  rw [← adjacency_outside labels C (hout i) (hout j)]
  exact hv i j hij

omit [Countable ι] [MeasurableSpace Ω] in
/-- Resampling the unique new-class vertex at any current dust point gives
an actual old multipartite clique. No old charge sign is used. -/
theorem clique_update_old {n : ℕ} (labels : Ω → Option ι) (C : Set Ω)
    (hCdust : C ⊆ labels ⁻¹' {none}) (v : Fin n → Ω)
    (hv : FiniteArity.TupleClique (adjacency (atomizedLabels labels C)) v)
    (i : Fin n) (hi : v i ∈ C) (z : Ω) (hz : z ∈ C) :
    FiniteArity.TupleClique (adjacency labels) (Function.update v i z) := by
  classical
  have hlabel : labels z = none := hCdust hz
  intro a b hab
  by_cases ha : a = i
  · subst a
    have hb : b ≠ i := Ne.symm hab
    rw [Function.update_self, Function.update_of_ne hb]
    apply (adjacency_eq_true_iff labels z (v b)).mpr
    exact Or.inr hlabel
  · by_cases hb : b = i
    · subst b
      rw [Function.update_of_ne ha, Function.update_self]
      by_cases hl : labels (v a) = none <;> simp [adjacency, hlabel, hl]
    · rw [Function.update_of_ne ha, Function.update_of_ne hb,
        ← adjacency_outside labels C (clique_at_most_one labels C v hv i a (Ne.symm ha) hi)
          (clique_at_most_one labels C v hv i b (Ne.symm hb) hi)]
      exact hv a b hab

omit [Countable ι] [MeasurableSpace Ω] in
/-- The only adjacency block changed by the literal new labels is C×C. -/
theorem adjacency_atomized (labels : Ω → Option ι) (C : Set Ω)
    (hCdust : C ⊆ labels ⁻¹' {none}) (x y : Ω) :
    adjacency (atomizedLabels labels C) x y =
      if x ∈ C ∧ y ∈ C then false else adjacency labels x y := by
  classical
  by_cases hx : x ∈ C
  · by_cases hy : y ∈ C
    · simp [adjacency, atomizedLabels, hx, hy]
    · have hl : labels x = none := hCdust hx
      cases hr : labels y <;> simp [adjacency, atomizedLabels, hx, hy, hl, hr]
  · by_cases hy : y ∈ C
    · have hr : labels y = none := hCdust hy
      cases hl : labels x <;> simp [adjacency, atomizedLabels, hx, hy, hl, hr]
    · simp only [hx, false_and, ↓reduceIte]
      exact adjacency_outside labels C hx hy

omit [Countable ι] [MeasurableSpace Ω] in
theorem adjacency_atomized_cross (labels : Ω → Option ι) (C : Set Ω) {x y : Ω}
    (hx : x ∈ C) (hy : y ∉ C) : adjacency (atomizedLabels labels C) x y = true := by
  classical
  cases hl : labels y <;> simp [adjacency, atomizedLabels, hx, hy, hl]

variable {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- The external row is averaged against the normalized current law on C. -/
def averagedRow (C : Set Ω) (Y : Ω × Ω → ℝ) (y : Ω) : ℝ :=
  ∫ x, Y (x, y) ∂ProbabilityTheory.cond ν C

/-- The new scalar charge deletes C's internal block and makes its two
external orientations equal to the same actual current-law row average. -/
def atomizedCharge (C : Set Ω) (Y : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ := by
  classical
  exact if p.1 ∈ C then (if p.2 ∈ C then 0 else averagedRow (ν := ν) C Y p.2)
    else if p.2 ∈ C then averagedRow (ν := ν) C Y p.1 else Y p

theorem measurable_averagedRow (C : Set Ω) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) : Measurable (averagedRow (ν := ν) C Y) := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond ν C) := cond_isProbabilityMeasure hCpos.ne'
  exact hY.stronglyMeasurable.integral_prod_left'.measurable

theorem averagedRow_mem_Icc (C : Set Ω) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1) (y : Ω) :
    averagedRow (ν := ν) C Y y ∈ Icc (-3 : ℝ) 1 := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond ν C) := cond_isProbabilityMeasure hCpos.ne'
  have hi : Integrable (fun x => Y (x, y)) (ProbabilityTheory.cond ν C) :=
    Integrable.of_bound (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 3
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(hbound (x, y)).1, (hbound (x, y)).2.trans (by norm_num)⟩))
  constructor
  · simpa [averagedRow] using integral_mono_ae (integrable_const (-3 : ℝ)) hi
      (Eventually.of_forall (fun x => (hbound (x, y)).1))
  · simpa [averagedRow] using integral_mono_ae hi (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun x => (hbound (x, y)).2))

theorem measurable_atomizedCharge (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) : Measurable (atomizedCharge (ν := ν) C Y) := by
  have hr := measurable_averagedRow C hCpos Y hY
  exact Measurable.ite (hC.preimage measurable_fst)
    (Measurable.ite (hC.preimage measurable_snd) measurable_const (hr.comp measurable_snd))
    (Measurable.ite (hC.preimage measurable_snd) (hr.comp measurable_fst) hY)

omit [IsProbabilityMeasure ν] in
theorem atomizedCharge_symm (C : Set Ω) (Y : Ω × Ω → ℝ)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) (x y : Ω) :
    atomizedCharge (ν := ν) C Y (x, y) = atomizedCharge (ν := ν) C Y (y, x) := by
  classical
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;>
    simp only [atomizedCharge, hx, hy, ↓reduceIte, hsym x y]

theorem atomizedCharge_mem_Icc (C : Set Ω) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
    (p : Ω × Ω) : atomizedCharge (ν := ν) C Y p ∈ Icc (-3 : ℝ) 1 := by
  classical
  unfold atomizedCharge
  split_ifs
  · constructor <;> norm_num
  · exact averagedRow_mem_Icc C hCpos Y hY hbound p.2
  · exact averagedRow_mem_Icc C hCpos Y hY hbound p.1
  · exact hbound p

omit [IsProbabilityMeasure ν] in
theorem atomizedCharge_outside (C : Set Ω) (Y : Ω × Ω → ℝ) {x y : Ω}
    (hx : x ∉ C) (hy : y ∉ C) : atomizedCharge (ν := ν) C Y (x, y) = Y (x, y) := by
  classical
  simp only [atomizedCharge, hx, hy, ↓reduceIte]

omit [IsProbabilityMeasure ν] in
theorem atomizedCharge_internal (C : Set Ω) (Y : Ω × Ω → ℝ) {x y : Ω}
    (hx : x ∈ C) (hy : y ∈ C) : atomizedCharge (ν := ν) C Y (x, y) = 0 := by
  classical
  simp only [atomizedCharge, hx, hy, ↓reduceIte]

omit [IsProbabilityMeasure ν] in
theorem atomizedCharge_cross (C : Set Ω) (Y : Ω × Ω → ℝ) {x y : Ω}
    (hx : x ∈ C) (hy : y ∉ C) :
    atomizedCharge (ν := ν) C Y (x, y) = averagedRow (ν := ν) C Y y := by
  classical
  simp only [atomizedCharge, hx, hy, ↓reduceIte]

/-- Current-law normalization is exact on every external row. -/
theorem mass_mul_averagedRow (C : Set Ω) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (y : Ω) :
    ν.real C * averagedRow (ν := ν) C Y y = ∫ x in C, Y (x, y) ∂ν := by
  have hb : ν.real C ≠ 0 := (ENNReal.toReal_pos hCpos.ne' (measure_ne_top ν C)).ne'
  rw [averagedRow, ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  change ν.real C * ((ν.real C)⁻¹ * ∫ x in C, Y (x, y) ∂ν) = _
  rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]

omit [Countable ι] in
/-- A new clique with one C vertex has exactly the average signed charge
of the old cliques obtained by independently resampling that one vertex. -/
theorem tupleCharge_average {n : ℕ} (labels : Ω → Option ι) (C : Set Ω)
    (hCpos : 0 < ν C) (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) (v : Fin n → Ω)
    (hv : FiniteArity.TupleClique (adjacency (atomizedLabels labels C)) v)
    (i : Fin n) (hi : v i ∈ C) :
    Integrable (fun z => FiniteArity.tupleCharge (fun x y => Y (x, y))
      (Function.update v i z)) (ProbabilityTheory.cond ν C) ∧
    (∫ z, FiniteArity.tupleCharge (fun x y => Y (x, y)) (Function.update v i z)
      ∂ProbabilityTheory.cond ν C) =
        FiniteArity.tupleCharge (fun x y => atomizedCharge (ν := ν) C Y (x, y)) v := by
  classical
  let σ := ProbabilityTheory.cond ν C
  have : IsProbabilityMeasure σ := cond_isProbabilityMeasure hCpos.ne'
  have hout (a : Fin n) (ha : a ≠ i) : v a ∉ C :=
    clique_at_most_one labels C v hv i a (Ne.symm ha) hi
  have hm (a : Fin n) : Measurable (fun z => Function.update v i z a) := by
    by_cases ha : a = i
    · subst a
      simpa only [Function.update_self] using (measurable_id' : Measurable (fun z : Ω => z))
    · have heq : (fun z => Function.update v i z a) = fun _ : Ω => v a :=
        funext (fun _ => Function.update_of_ne ha _ _)
      rw [heq]
      exact measurable_const
  have hpair (a b : Fin n) :
      Integrable (fun z => Y (Function.update v i z a, Function.update v i z b)) σ :=
    Integrable.of_bound (hY.comp ((hm a).prodMk (hm b))).aestronglyMeasurable 3
      (Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(hbound _).1, (hbound _).2.trans (by norm_num)⟩))
  have havg (a b : Fin n) (hab : a ≠ b) :
      (∫ z, Y (Function.update v i z a, Function.update v i z b) ∂σ) =
        atomizedCharge (ν := ν) C Y (v a, v b) := by
    by_cases ha : a = i
    · subst a
      have hb : b ≠ i := Ne.symm hab
      simp_rw [Function.update_self, Function.update_of_ne hb]
      rw [atomizedCharge_cross C Y hi (hout b hb)]
      rfl
    · by_cases hb : b = i
      · subst b
        simp_rw [Function.update_of_ne ha, Function.update_self]
        rw [atomizedCharge_symm C Y hsym (v a) (v i),
          atomizedCharge_cross C Y hi (hout a ha)]
        exact integral_congr_ae (Eventually.of_forall (fun z => hsym (v a) z))
      · simp_rw [Function.update_of_ne ha, Function.update_of_ne hb]
        rw [atomizedCharge_outside C Y (hout a ha) (hout b hb)]
        simp
  have hf (a b : Fin n) : Integrable (fun z =>
      if a = b then (0 : ℝ) else Y (Function.update v i z a, Function.update v i z b)) σ := by
    by_cases hab : a = b
    · simp only [hab, ↓reduceIte]
      exact integrable_const 0
    · simpa only [hab, ↓reduceIte] using hpair a b
  have hsum (a : Fin n) := integrable_finsetSum Finset.univ (fun b _ => hf a b)
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  refine ⟨(integrable_finsetSum Finset.univ (fun a _ => hsum a)).div_const 2, ?_⟩
  rw [integral_div, integral_finsetSum Finset.univ (fun a _ => hsum a)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum Finset.univ (fun b _ => hf a b)]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte, integral_zero]
  · simp only [hab, ↓reduceIte]
    exact havg a b hab

omit [Countable ι] in
/-- All actual old product clique tests imply all tests for this atomized
scalar kernel. The one-C case averages an independently resampled common
current C point, rather than assuming any edited feasibility. -/
theorem feasibleOrder (labels : Ω → Option ι) (C : Set Ω) (hC : MeasurableSet C)
    (hCpos : 0 < ν C) (hCdust : C ⊆ labels ⁻¹' {none})
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) (n : ℕ)
    (htest : FiniteArity.FeasibleOrder ν (adjacency labels) (fun x y => Y (x, y)) n) :
    FiniteArity.FeasibleOrder ν (adjacency (atomizedLabels labels C))
      (fun x y => atomizedCharge (ν := ν) C Y (x, y)) n := by
  classical
  let σ := ProbabilityTheory.cond ν C
  have : IsProbabilityMeasure σ := cond_isProbabilityMeasure hCpos.ne'
  have hmem : ∀ᵐ z ∂σ, z ∈ C :=
    (show σ ≪ ν.restrict C from Measure.smul_absolutelyContinuous).ae_le (ae_restrict_mem hC)
  cases n with
  | zero =>
    exact Eventually.of_forall (fun v _ => by
      rw [FiniteArity.tupleCharge_small (by omega)]
      norm_num)
  | succ n =>
    have hresample : ∀ᵐ v ∂Measure.pi (fun _ : Fin (n + 1) => ν),
        ∀ i : Fin (n + 1), ∀ᵐ z ∂σ,
          FiniteArity.TupleClique (adjacency labels) (Function.update v i z) →
            FiniteArity.tupleCharge (fun x y => Y (x, y)) (Function.update v i z) ≤ 1 := by
      apply ae_all_iff.mpr
      intro i
      exact IndependentCoordinateResampling.ae_update_pi σ cond_absolutelyContinuous i _ htest
    filter_upwards [htest, hresample] with v ht hr hc
    by_cases hhas : ∃ i, v i ∈ C
    · obtain ⟨i, hi⟩ := hhas
      have havg := tupleCharge_average labels C hCpos Y hY hbound hsym v hc i hi
      have hle : ∀ᵐ z ∂σ, FiniteArity.tupleCharge (fun x y => Y (x, y))
          (Function.update v i z) ≤ 1 := by
        filter_upwards [hr i, hmem] with z hz hzin
        exact hz (clique_update_old labels C hCdust v hc i hi z hzin)
      have h := integral_mono_ae havg.1 (integrable_const (1 : ℝ)) hle
      rw [havg.2] at h
      simpa using h
    · have hout : ∀ i, v i ∉ C := fun i hi => hhas ⟨i, hi⟩
      have heq : FiniteArity.tupleCharge
          (fun x y => atomizedCharge (ν := ν) C Y (x, y)) v =
          FiniteArity.tupleCharge (fun x y => Y (x, y)) v := by
        unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        by_cases hab : a = b
        · simp only [hab, ↓reduceIte]
        · simp only [hab, ↓reduceIte, atomizedCharge_outside C Y (hout a) (hout b)]
      rw [heq]
      exact ht (clique_outside_old labels C v hc hout)

omit [Countable ι] [IsProbabilityMeasure ν] in
/-- The atomized charge is exactly zero on the actual new nonedges. -/
theorem atomizedCharge_zero_of_nonedge (labels : Ω → Option ι) (C : Set Ω)
    (Y : Ω × Ω → ℝ) (hzero : ∀ x y, adjacency labels x y = false → Y (x, y) = 0)
    (x y : Ω) (hxy : adjacency (atomizedLabels labels C) x y = false) :
    atomizedCharge (ν := ν) C Y (x, y) = 0 := by
  classical
  by_cases hx : x ∈ C
  · by_cases hy : y ∈ C
    · exact atomizedCharge_internal C Y hx hy
    · have h := adjacency_atomized_cross labels C hx hy
      rw [h] at hxy
      cases hxy
  · by_cases hy : y ∈ C
    · have h := (adjacency_symm (atomizedLabels labels C) x y).trans
        (adjacency_atomized_cross labels C hy hx)
      rw [h] at hxy
      cases hxy
    · rw [adjacency_outside labels C hx hy] at hxy
      rw [atomizedCharge_outside C Y hx hy]
      exact hzero x y hxy

/-- Current-law almost-everywhere changes of the old charge do not change
the atomized charge almost everywhere, including its averaged external row. -/
theorem atomizedCharge_congr_ae (C : Set Ω) (hCpos : 0 < ν C)
    (Y Y' : Ω × Ω → ℝ) (hYY' : Y =ᵐ[ν.prod ν] Y') :
    atomizedCharge (ν := ν) C Y =ᵐ[ν.prod ν] atomizedCharge (ν := ν) C Y' := by
  let σ := ProbabilityTheory.cond ν C
  have : IsProbabilityMeasure σ := cond_isProbabilityMeasure hCpos.ne'
  have hac : σ.prod ν ≪ ν.prod ν := cond_absolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
  have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := σ)).quasiMeasurePreserving.ae
    (hac.ae_le hYY')
  have hrow : averagedRow (ν := ν) C Y =ᵐ[ν] averagedRow (ν := ν) C Y' :=
    (Measure.ae_ae_of_ae_prod hswap).mono (fun _ hy => integral_congr_ae hy)
  filter_upwards [hYY', Measure.quasiMeasurePreserving_fst.ae hrow,
    Measure.quasiMeasurePreserving_snd.ae hrow] with p hp hx hy
  classical
  by_cases h₁ : p.1 ∈ C <;> by_cases h₂ : p.2 ∈ C <;>
    simp only [atomizedCharge, h₁, h₂, ↓reduceIte, hp, hx, hy]

/-- Averaging preserves both signed external blocks exactly; deleting the
internal C block is the entire change in the actual total charge integral. -/
theorem integral_atomizedCharge (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) :
    (∫ p, atomizedCharge (ν := ν) C Y p ∂ν.prod ν) =
      (∫ p, Y p ∂ν.prod ν) - ∫ p in C ×ˢ C, Y p ∂ν.prod ν := by
  let α := ν.restrict C
  let β := ν.restrict Cᶜ
  have : IsFiniteMeasure α := by dsimp [α]; infer_instance
  have : IsFiniteMeasure β := by dsimp [β]; infer_instance
  have hold (ρ : Measure (Ω × Ω)) [IsFiniteMeasure ρ] : Integrable Y ρ :=
    Integrable.of_bound hY.aestronglyMeasurable 3 (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(hbound p).1, (hbound p).2.trans (by norm_num)⟩))
  have hnew (ρ : Measure (Ω × Ω)) [IsFiniteMeasure ρ] :
      Integrable (atomizedCharge (ν := ν) C Y) ρ :=
    Integrable.of_bound (measurable_atomizedCharge C hC hCpos Y hY).aestronglyMeasurable 3
      (Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs]
        have hp := atomizedCharge_mem_Icc C hCpos Y hY hbound p
        exact abs_le.mpr ⟨hp.1, hp.2.trans (by norm_num)⟩))
  have hinside : ∀ᵐ x ∂α, x ∈ C := ae_restrict_mem hC
  have houtside : ∀ᵐ x ∂β, x ∉ C := ae_restrict_mem hC.compl
  have hcc : (∫ p, atomizedCharge (ν := ν) C Y p ∂α.prod α) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hinside,
      Measure.quasiMeasurePreserving_snd.ae hinside] with p hx hy
    exact atomizedCharge_internal C Y hx hy
  have hdd : (∫ p, atomizedCharge (ν := ν) C Y p ∂β.prod β) = ∫ p, Y p ∂β.prod β := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae houtside,
      Measure.quasiMeasurePreserving_snd.ae houtside] with p hx hy
    exact atomizedCharge_outside C Y hx hy
  have hcross : (∫ p, atomizedCharge (ν := ν) C Y p ∂α.prod β) = ∫ p, Y p ∂α.prod β := by
    have heq : atomizedCharge (ν := ν) C Y =ᵐ[α.prod β]
        (fun p => averagedRow (ν := ν) C Y p.2) := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hinside,
        Measure.quasiMeasurePreserving_snd.ae houtside] with p hx hy
      exact atomizedCharge_cross C Y hx hy
    rw [integral_congr_ae heq, integral_prod_symm _ ((hnew _).congr heq),
      integral_prod_symm Y (hold _)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      change (∫ _ : Ω, averagedRow (ν := ν) C Y y ∂α) = ∫ x, Y (x, y) ∂α
      rw [integral_const, smul_eq_mul]
      simp only [α, measureReal_def, Measure.restrict_apply_univ]
      exact mass_mul_averagedRow C hCpos Y y)
  have hswap (f : Ω × Ω → ℝ) (hf : Measurable f) (hs : ∀ x y, f (x, y) = f (y, x)) :
      (∫ p, f p ∂β.prod α) = ∫ p, f p ∂α.prod β := by
    rw [← Measure.prod_swap (μ := α) (ν := β),
      integral_map measurable_swap.aemeasurable hf.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall (fun p => hs p.2 p.1))
  have hreverse : (∫ p, atomizedCharge (ν := ν) C Y p ∂β.prod α) = ∫ p, Y p ∂β.prod α := by
    rw [hswap _ (measurable_atomizedCharge C hC hCpos Y hY) (atomizedCharge_symm C Y hsym),
      hcross, hswap Y hY hsym]
  have hsum : ν = α + β := (Measure.restrict_add_restrict_compl hC).symm
  have hprod : ν.prod ν = (α.prod α + α.prod β) + (β.prod α + β.prod β) := by
    rw [hsum, Measure.add_prod, Measure.prod_add, Measure.prod_add]
  have hexpand (f : Ω × Ω → ℝ)
      (hf : ∀ ρ : Measure (Ω × Ω), [IsFiniteMeasure ρ] → Integrable f ρ) :
      (∫ p, f p ∂ν.prod ν) = (∫ p, f p ∂α.prod α) + (∫ p, f p ∂α.prod β) +
        (∫ p, f p ∂β.prod α) + ∫ p, f p ∂β.prod β := by
    rw [hprod, integral_add_measure (hf _) (hf _),
      integral_add_measure (hf _) (hf _), integral_add_measure (hf _) (hf _)]
    ring
  have hinternal : (∫ p, Y p ∂α.prod α) = ∫ p in C ×ˢ C, Y p ∂ν.prod ν := by
    dsimp only [α]
    rw [Measure.prod_restrict]
  rw [hexpand _ hnew, hexpand Y hold, hcc, hdd, hcross, hreverse, ← hinternal]
  ring

end Erdos1017.MultipartiteDustAtomization

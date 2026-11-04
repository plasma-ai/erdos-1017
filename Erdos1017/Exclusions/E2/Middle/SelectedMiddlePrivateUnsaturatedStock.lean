module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateUnsaturatedInsertion
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerQuota
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedCount

/-!
# First-root parent stock of a bounded row

The first-root parent event `firstRootEvent` is measurable, unique roots make
the first-root count its indicator, and the exact first-root parent stock is
computed for a bounded row `φ` constant on the first fiber and null on the
second (`first_root_stock`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.PrivatePhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  {i p : S.I} {c d : ℝ}

/-- The first-root parent event. -/
def firstRootEvent (S : SelectedHighLowStructure W m) (i : S.I) (n : ℕ) : Set (Fin n → Ω) :=
  {v | ∃ j, S.ρ (v j) = i.val}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_firstRootEvent (S : SelectedHighLowStructure W m) (i : S.I) (n : ℕ) :
    MeasurableSet (firstRootEvent S i n) := by
  have h := MeasurableSet.iUnion (fun j : Fin n =>
    (S.hfibers i.val i.property).1.preimage (measurable_pi_apply j))
  convert h using 1
  ext v
  simp [firstRootEvent]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Unique roots make the first-root count the event indicator. -/
theorem ae_tupleCount_eq_indicator (P : S.PrivatePhysicalPrimal i p c) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, (PhysicalPrimal.tupleCount {x | S.ρ x = i.val} v : ℝ) =
      (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v := by
  filter_upwards [P.unique_roots n] with v hu
  by_cases h : ∃ j, S.ρ (v j) = i.val
  · obtain ⟨j, hj⟩ := h
    rw [PhysicalPrimal.tupleCount_eq_one_of_unique _ v
      ⟨j, hj, fun k hk => hu k j (Or.inl hk) (Or.inl hj)⟩,
      indicator_of_mem (show v ∈ firstRootEvent S i n from ⟨j, hj⟩)]
    simp
  · rw [indicator_of_notMem (show v ∉ firstRootEvent S i n from h)]
    simp only [not_exists] at h
    simp [PhysicalPrimal.tupleCount, h]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A μ-a.e. vertex property holds at every coordinate of almost every parent. -/
theorem ae_coordinates (P : S.PrivatePhysicalPrimal i p c) (n : ℕ)
    (Q : Ω → Prop) (hQ : ∀ᵐ y ∂μ, Q y) : ∀ᵐ v ∂P.laws n, ∀ j, Q (v j) := by
  by_cases hn : 2 ≤ n
  · have hdemand : PhysicalPrimal.graphDemand μ
        {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true} ≪ μ.prod μ :=
      Measure.absolutelyContinuous_restrict
    have hpairs : ∀ a b : Fin n, a ≠ b →
        (P.laws n).map (fun v => (v a, v b)) ≪ μ.prod μ := fun a b hab =>
      (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
        P.feasible.2.2.2 n ⟨(a, b), hab⟩).trans hdemand
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable
      ((PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs
        μ hn _ hpairs j).ae_le hQ)
  · have hz : P.laws n = 0 := by
      interval_cases n
      · exact P.feasible.1
      · exact P.feasible.2.1
    rw [hz, ae_zero]
    exact Filter.eventually_bot

omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
private theorem integrable_bounded {n : ℕ} (τ : Measure (Fin n → Ω)) [IsFiniteMeasure τ]
    (g : (Fin n → Ω) → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ v, |g v| ≤ B) :
    Integrable g τ :=
  Integrable.of_bound hg.aestronglyMeasurable B
    (Eventually.of_forall (fun v => by simpa [Real.norm_eq_abs] using hB v))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The exact first-root parent stock of an arbitrary bounded row `φ`
that is constant `cI` on the first fiber and null on the second. -/
theorem first_root_stock (P : S.PrivatePhysicalPrimal i p c)
    (φ : Ω → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : ∀ y, |φ y| ≤ B) (cI : ℝ)
    (hI : ∀ᵐ y ∂μ, S.ρ y = i.val → φ y = cI)
    (hP : ∀ᵐ y ∂μ, S.ρ y = p.val → φ y = 0) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v * ∑ j, φ (v j) ∂P.laws n) =
      cI * (∑ n ∈ Finset.range (P.orderCap + 1), (P.laws n).real (firstRootEvent S i n)) +
        μ.real {x | S.ρ x = i.val} * ((∫ y, φ y ∂μ) - μ.real {x | S.ρ x = i.val} * cI) := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  let J := (I ∪ Pset)ᶜ
  have hIm : MeasurableSet I := (S.hfibers i.val i.property).1
  have hPm : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hdis : Disjoint I Pset := disjoint_left.mpr (fun _ hx hy =>
    P.distinct_roots (Subtype.ext (hx.symm.trans hy)))
  let f := Iᶜ.indicator φ
  have hf : Measurable f := hφ.indicator hIm.compl
  have hfB (y : Ω) : |f y| ≤ B := by
    by_cases hy : y ∈ Iᶜ
    · rw [show f y = φ y from indicator_of_mem hy φ]
      exact hB y
    · rw [show f y = 0 from indicator_of_notMem hy φ, abs_zero]
      exact (abs_nonneg _).trans (hB y)
  have hK : Integrable (fun z : Ω × Ω => if z.1 ∈ I then f z.2 else 0)
      (PhysicalPrimal.occupation P.laws) := by
    have hKm : Measurable (fun z : Ω × Ω => if z.1 ∈ I then f z.2 else 0) :=
      Measurable.ite (hIm.preimage measurable_fst) (hf.comp measurable_snd) measurable_const
    have hKi : Integrable (fun z : Ω × Ω => if z.1 ∈ I then f z.2 else 0) (μ.prod μ) :=
      Integrable.of_bound hKm.aestronglyMeasurable B (Eventually.of_forall (fun z => by
        split_ifs
        · simpa [Real.norm_eq_abs] using hfB z.2
        · simpa using (abs_nonneg _).trans (hB z.2)))
    rw [P.feasible.2.2.2]
    exact hKi.mono_measure Measure.restrict_le_self
  have hstock : (∫ x, f x ∂PhysicalPrimal.rootLeaves P.laws I) =
      ∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
        (PhysicalPrimal.tupleCount I v : ℝ) * ∑ j, f (v j) ∂P.laws n := by
    rw [PhysicalPrimal.integral_rootLeaves_eq_sum_of_cap P.orderCap P.laws
      (fun n hn => P.capped n (Or.inr hn)) I hIm f hf (by convert hK)]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    funext v
    rw [sub_eq_self]
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hj
    · simp [f, hj]
    · rfl
  rw [P.leaves_first, integral_smul_measure] at hstock
  -- The leaf side.
  have hJf : (∫ y in J, f y ∂μ) = ∫ y in J, φ y ∂μ := by
    apply setIntegral_congr_fun (hIm.union hPm).compl
    intro y hy
    exact indicator_of_mem (show y ∈ Iᶜ from fun h => hy (Or.inl h)) φ
  have hφi : Integrable φ μ := Integrable.of_bound hφ.aestronglyMeasurable B
    (Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs] using hB y))
  have hIint : (∫ y in I, φ y ∂μ) = μ.real I * cI := by
    rw [setIntegral_congr_ae hIm (hI.mono (fun y hy hyI => hy hyI)), setIntegral_const,
      smul_eq_mul]
  have hPint : (∫ y in Pset, φ y ∂μ) = 0 := by
    rw [setIntegral_congr_ae hPm (hP.mono (fun y hy hyP => hy hyP))]
    simp
  have hsplit : (∫ y, φ y ∂μ) = (∫ y in I, φ y ∂μ) + (∫ y in Pset, φ y ∂μ) +
      ∫ y in J, φ y ∂μ := by
    rw [← integral_add_compl (hIm.union hPm) hφi, setIntegral_union hdis hPm
      hφi.integrableOn hφi.integrableOn]
  have hleaf : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (PhysicalPrimal.tupleCount I v : ℝ) * ∑ j, f (v j) ∂P.laws n) =
      μ.real I * ((∫ y, φ y ∂μ) - μ.real I * cI) := by
    rw [← hstock, hJf, smul_eq_mul]
    change (μ I).toReal * _ = _
    rw [← measureReal_def]
    have hJ : (∫ y in J, φ y ∂μ) = (∫ y, φ y ∂μ) - μ.real I * cI := by linarith
    rw [hJ]
  -- Each order splits into the leaf stock and the constant root row.
  have horder (n : ℕ) : (∫ v, (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
      ∑ j, φ (v j) ∂P.laws n) =
      (∫ v, (PhysicalPrimal.tupleCount I v : ℝ) * ∑ j, f (v j) ∂P.laws n) +
        cI * (P.laws n).real (firstRootEvent S i n) := by
    have hcoord := ae_coordinates P n _ hI
    have hcount := ae_tupleCount_eq_indicator P n
    have hEm := measurableSet_firstRootEvent S i n
    have heq : (fun v => (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ∑ j, φ (v j)) =ᵐ[P.laws n]
        fun v => (PhysicalPrimal.tupleCount I v : ℝ) * ∑ j, f (v j) +
          (firstRootEvent S i n).indicator (fun _ => cI) v := by
      filter_upwards [hcoord, hcount] with v hv hc
      have hsum : (∑ j, φ (v j)) = (∑ j, f (v j)) +
          (PhysicalPrimal.tupleCount I v : ℝ) * cI := by
        rw [PhysicalPrimal.tupleCount, Nat.cast_sum, Finset.sum_mul,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : v j ∈ I
        · simp [f, hj, hv j hj]
        · simp [f, hj]
      rw [hsum, hc]
      by_cases hE : v ∈ firstRootEvent S i n
      · simp [indicator_of_mem hE]
      · simp [indicator_of_notMem hE]
    have hmeasf : Measurable (fun v : Fin n → Ω => ∑ j, f (v j)) :=
      Finset.measurable_sum _ (fun j _ => hf.comp (measurable_pi_apply j))
    have h1 : Integrable (fun v : Fin n → Ω =>
        (PhysicalPrimal.tupleCount I v : ℝ) * ∑ j, f (v j)) (P.laws n) :=
      integrable_bounded _ _ ((measurable_tupleCount_real n I hIm).mul hmeasf) (n * (n * B))
        (fun v => by
          rw [abs_mul]
          have hc : |(PhysicalPrimal.tupleCount I v : ℝ)| ≤ n := by
            rw [abs_of_nonneg (Nat.cast_nonneg _)]
            exact_mod_cast PhysicalPrimal.tupleCount_le I v
          have hs : |∑ j, f (v j)| ≤ n * B := by
            calc
              _ ≤ ∑ j, |f (v j)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _j : Fin n, B := Finset.sum_le_sum (fun j _ => hfB (v j))
              _ = n * B := by simp
          exact mul_le_mul hc hs (abs_nonneg _) (Nat.cast_nonneg _))
    have h2 : Integrable ((firstRootEvent S i n).indicator (fun _ => cI)) (P.laws n) :=
      (integrable_const cI).indicator hEm
    rw [integral_congr_ae heq, integral_add h1 h2, integral_indicator hEm, setIntegral_const,
      smul_eq_mul, mul_comm]
  simp_rw [horder]
  rw [Finset.sum_add_distrib, hleaf, ← Finset.mul_sum]
  ring
where
  measurable_tupleCount_real (n : ℕ) (I : Set Ω) (hI : MeasurableSet I) :
      Measurable (fun v : Fin n → Ω => (PhysicalPrimal.tupleCount I v : ℝ)) :=
    measurable_from_nat.comp (PhysicalPrimal.measurable_tupleCount I hI)

end Erdos1017.CappedModel.SelectedHighLowStructure.PrivatePhysicalPrimal

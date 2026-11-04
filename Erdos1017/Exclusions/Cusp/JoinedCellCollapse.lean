module

public import Erdos1017.Exclusions.Common.CappedDustAtomization

/-!
# Collapsing a joined cell

Collapsing a cell removes precisely its internal edges. The collapsed `model`
uses the current conditional J law, inherits all original tests by the
resampled-cell argument, and changes the objective by deletion of the current J
square; it is used to build the whole-source child.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.JoinedCellCollapse

open MultipartiteDustAtomization

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Collapsing a cell removes precisely its internal edges. -/
def adjacency (A : Ω → Ω → Bool) (J : Set Ω) (x y : Ω) : Bool :=
  if x ∈ J ∧ y ∈ J then false else A x y

theorem measurable_adjacency (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (J : Set Ω) (hJ : MeasurableSet J) :
    Measurable (Function.uncurry (adjacency A J)) :=
  Measurable.ite ((hJ.preimage measurable_fst).inter (hJ.preimage measurable_snd))
    measurable_const hA

omit [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem adjacency_symm (A : Ω → Ω → Bool) (J : Set Ω)
    (hsym : ∀ x y, A x y = A y x) (x y : Ω) :
    adjacency A J x y = adjacency A J y x := by
  simp only [adjacency, and_comm, hsym x y]

omit [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem clique_at_most_one {n : ℕ} (A : Ω → Ω → Bool) (J : Set Ω)
    (v : Fin n → Ω) (hv : FiniteArity.TupleClique (adjacency A J) v)
    (i j : Fin n) (hij : i ≠ j) (hi : v i ∈ J) : v j ∉ J := by
  intro hj
  have h := hv i j hij
  simp only [adjacency, hi, hj, and_self, ↓reduceIte, Bool.false_eq_true] at h

omit [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
private theorem clique_dummy {n : ℕ} (A : Ω → Ω → Bool) (J : Set Ω)
    (v : Fin n → Ω) (hv : FiniteArity.TupleClique (adjacency A J) v) :
    FiniteArity.TupleClique
      (MultipartiteDustAtomization.adjacency
        (atomizedLabels (fun _ : Ω => (none : Option Unit)) J)) v := by
  intro i j hij
  by_cases hi : v i ∈ J
  · exact adjacency_atomized_cross _ J hi (clique_at_most_one A J v hv i j hij hi)
  · by_cases hj : v j ∈ J
    · rw [MultipartiteDustAtomization.adjacency_symm]
      exact adjacency_atomized_cross _ J hj hi
    · rw [adjacency_outside _ J hi hj]
      simp [MultipartiteDustAtomization.adjacency]

/-- Old product tests and actual externally joined sections license the
collapsed cell. The new common cell point is independently resampled. -/
theorem feasibleOrder (A : Ω → Ω → Bool) (J : Set Ω) (hJ : MeasurableSet J)
    (hJpos : 0 < ν J)
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J →
      A p.1 p.2 = true ∧ A p.2 p.1 = true)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) (n : ℕ)
    (htest : FiniteArity.FeasibleOrder ν A (fun x y => Y (x, y)) n) :
    FiniteArity.FeasibleOrder ν (adjacency A J)
      (fun x y => atomizedCharge (ν := ν) J Y (x, y)) n := by
  classical
  let σ := ProbabilityTheory.cond ν J
  have : IsProbabilityMeasure σ := cond_isProbabilityMeasure hJpos.ne'
  have hmem : ∀ᵐ z ∂σ, z ∈ J :=
    (show σ ≪ ν.restrict J from Measure.smul_absolutelyContinuous).ae_le (ae_restrict_mem hJ)
  have hsections : ∀ᵐ y ∂ν, ∀ᵐ z ∂σ, z ∈ J → y ∉ J →
      A z y = true ∧ A y z = true := by
    have hac : σ.prod ν ≪ ν.prod ν :=
      cond_absolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
    have hs := (Measure.measurePreserving_swap (μ := ν) (ν := σ)).quasiMeasurePreserving.ae
      (hac.ae_le hjoin)
    exact Measure.ae_ae_of_ae_prod hs
  cases n with
  | zero =>
    exact Eventually.of_forall (fun v _ => by
      rw [FiniteArity.tupleCharge_small (by omega)]
      norm_num)
  | succ n =>
    have hresample : ∀ᵐ v ∂Measure.pi (fun _ : Fin (n + 1) => ν),
        ∀ i : Fin (n + 1), ∀ᵐ z ∂σ,
          FiniteArity.TupleClique A (Function.update v i z) →
            FiniteArity.tupleCharge (fun x y => Y (x, y)) (Function.update v i z) ≤ 1 := by
      apply ae_all_iff.mpr
      intro i
      exact IndependentCoordinateResampling.ae_update_pi σ cond_absolutelyContinuous i _ htest
    have hrows : ∀ᵐ v ∂Measure.pi (fun _ : Fin (n + 1) => ν),
        ∀ j : Fin (n + 1), ∀ᵐ z ∂σ, z ∈ J → v j ∉ J →
          A z (v j) = true ∧ A (v j) z = true := by
      apply ae_all_iff.mpr
      intro j
      exact (measurePreserving_eval (fun _ : Fin (n + 1) => ν) j).quasiMeasurePreserving.ae hsections
    filter_upwards [htest, hresample, hrows] with v ht hr hrow hc
    by_cases hhas : ∃ i, v i ∈ J
    · obtain ⟨i, hi⟩ := hhas
      have havg := tupleCharge_average (fun _ : Ω => (none : Option Unit)) J hJpos Y hY
        hbound hsym v (clique_dummy A J v hc) i hi
      have hall : ∀ᵐ z ∂σ, ∀ j : Fin (n + 1), z ∈ J → v j ∉ J →
          A z (v j) = true ∧ A (v j) z = true := ae_all_iff.mpr hrow
      have hle : ∀ᵐ z ∂σ, FiniteArity.tupleCharge (fun x y => Y (x, y))
          (Function.update v i z) ≤ 1 := by
        filter_upwards [hr i, hmem, hall] with z hz hzin hj
        apply hz
        intro a b hab
        by_cases ha : a = i
        · subst a
          have hb : b ≠ i := Ne.symm hab
          rw [Function.update_self, Function.update_of_ne hb]
          exact (hj b hzin (clique_at_most_one A J v hc i b hab hi)).1
        · by_cases hb : b = i
          · subst b
            rw [Function.update_of_ne ha, Function.update_self]
            exact (hj a hzin (clique_at_most_one A J v hc i a (Ne.symm ha) hi)).2
          · rw [Function.update_of_ne ha, Function.update_of_ne hb]
            have hout := clique_at_most_one A J v hc i a (Ne.symm ha) hi
            simpa only [adjacency, hout, false_and, ↓reduceIte] using hc a b hab
      have h := integral_mono_ae havg.1 (integrable_const (1 : ℝ)) hle
      rw [havg.2] at h
      simpa using h
    · have hout : ∀ i, v i ∉ J := fun i hi => hhas ⟨i, hi⟩
      have heq : FiniteArity.tupleCharge
          (fun x y => atomizedCharge (ν := ν) J Y (x, y)) v =
          FiniteArity.tupleCharge (fun x y => Y (x, y)) v := by
        unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        by_cases hab : a = b
        · simp only [hab, ↓reduceIte]
        · simp only [hab, ↓reduceIte, atomizedCharge_outside J Y (hout a) (hout b)]
      rw [heq]
      apply ht
      intro a b hab
      simpa only [adjacency, hout a, false_and, ↓reduceIte] using hc a b hab

/-- The collapsed support is a genuine deterministic Bernoulli parameter. -/
def probability (A : Ω → Ω → Bool) (J : Set Ω) (p : Ω × Ω) : unitInterval :=
  if adjacency A J p.1 p.2 = true then 1 else 0

theorem measurable_probability (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (J : Set Ω) (hJ : MeasurableSet J) :
    Measurable (probability A J) :=
  Measurable.ite ((measurable_adjacency A hA J hJ) (measurableSet_singleton true))
    measurable_const measurable_const

/-- The collapsed bounded model uses the current conditional J law. -/
def model (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hAsym : ∀ x y, A x y = A y x) (J : Set Ω) (hJ : MeasurableSet J)
    (hJpos : 0 < ν J) (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1) (hsym : ∀ x y, Y (x, y) = Y (y, x)) :
    Model Ω ν :=
  ScalarModel.model (probability A J) (DustAtomization.charge J hJpos Y hY hbound)
    (measurable_probability A hA J hJ) (DustAtomization.measurable_charge J hJ hJpos Y hY hbound)
    (Eventually.of_forall (fun p => by
      simp only [probability, Prod.swap, adjacency_symm A J hAsym p.2 p.1]))
    (Eventually.of_forall (DustAtomization.charge_symm J hJpos Y hY hbound hsym))

section ScalarModel

variable (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
  (hAsym : ∀ x y, A x y = A y x) (J : Set Ω) (hJ : MeasurableSet J)
  (hJpos : 0 < ν J) (Y : Ω × Ω → ℝ) (hY : Measurable Y)
  (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1) (hsym : ∀ x y, Y (x, y) = Y (y, x))

theorem adjacency_moment (p : Ω × Ω) :
    (model A hA hAsym J hJ hJpos Y hY hbound hsym).moment CappedColor.adjacency p =
      if adjacency A J p.1 p.2 = true then 1 else 0 := by
  rw [model, CappedModel.ScalarModel.adjacency_moment]
  simp only [probability]
  split_ifs <;> rfl

theorem charge_moment_ae
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J →
      A p.1 p.2 = true ∧ A p.2 p.1 = true)
    (hzero : ∀ p, A p.1 p.2 = false → Y p = 0) :
    ∀ᵐ p ∂ν.prod ν,
      (model A hA hAsym J hJ hJpos Y hY hbound hsym).moment CappedColor.charge p =
        atomizedCharge (ν := ν) J Y p := by
  have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hjoin
  filter_upwards [hjoin, hswap] with p hp hps
  rw [model, CappedModel.ScalarModel.charge_moment]
  change (probability A J p : ℝ) * atomizedCharge (ν := ν) J Y p = _
  by_cases hx : p.1 ∈ J
  · by_cases hy : p.2 ∈ J
    · simp only [atomizedCharge, hx, hy, ↓reduceIte, mul_zero]
    · have ha := (hp hx hy).1
      simp [probability, adjacency, hx, hy, ha]
  · by_cases hy : p.2 ∈ J
    · have ha : A p.1 p.2 = true := (hps hy hx).2
      simp [probability, adjacency, hx, ha]
    · by_cases ha : A p.1 p.2 = true
      · simp [probability, adjacency, hx, ha]
      · have hz := hzero p (Bool.eq_false_iff.mpr ha)
        simp only [atomizedCharge, hx, hy, ↓reduceIte, hz, mul_zero]

/-- The actual colored model inherits all old tests by the independently
resampled cell argument, without an edited-feasibility premise. -/
theorem fullFeasible_model
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J →
      A p.1 p.2 = true ∧ A p.2 p.1 = true)
    (htests : ∀ n, FiniteArity.FeasibleOrder ν A (fun x y => Y (x, y)) n) :
    FullFeasible (model A hA hAsym J hJ hJpos Y hY hbound hsym) := by
  apply CappedModel.ScalarModel.fullFeasible_model
    (probability A J) (DustAtomization.charge J hJpos Y hY hbound)
    (measurable_probability A hA J hJ) (DustAtomization.measurable_charge J hJ hJpos Y hY hbound)
    (Eventually.of_forall (fun p => by
      simp only [probability, Prod.swap, adjacency_symm A J hAsym p.2 p.1]))
    (Eventually.of_forall (DustAtomization.charge_symm J hJpos Y hY hbound hsym))
    (adjacency A J)
  · exact Eventually.of_forall (fun p hp => by simp [probability, hp])
  · intro n _
    exact feasibleOrder A J hJ hJpos hjoin Y hY hbound hsym n (htests n)

/-- The entire signed change in objective is deletion of the current J square. -/
theorem objective_model
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J →
      A p.1 p.2 = true ∧ A p.2 p.1 = true)
    (hzero : ∀ p, A p.1 p.2 = false → Y p = 0) :
    objective (model A hA hAsym J hJ hJpos Y hY hbound hsym) =
      (∫ p, Y p ∂ν.prod ν) / 2 - (∫ p in J ×ˢ J, Y p ∂ν.prod ν) / 2 := by
  unfold objective
  rw [integral_congr_ae (charge_moment_ae A hA hAsym J hJ hJpos Y hY hbound hsym hjoin hzero),
    integral_atomizedCharge J hJ hJpos Y hY hbound hsym]
  ring

/-- No external edge is changed by collapse; the current internal edge
integral, including a nonclique old cell, is removed exactly. -/
theorem density_model (W : Model Ω ν)
    (hAdj : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if A p.1 p.2 = true then 1 else 0) :
    density (model A hA hAsym J hJ hJpos Y hY hbound hsym) =
      density W - (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂ν.prod ν) / 2 := by
  let f : Ω × Ω → ℝ := fun p => if A p.1 p.2 = true then 1 else 0
  have hf : Integrable f (ν.prod ν) :=
    Integrable.of_bound
      (Measurable.ite (hA (measurableSet_singleton true)) measurable_const
        measurable_const).aestronglyMeasurable 1 (Eventually.of_forall (fun p => by
          dsimp [f]
          split_ifs <;> norm_num))
  have heq : (fun p => (model A hA hAsym J hJ hJpos Y hY hbound hsym).moment
      CappedColor.adjacency p) = fun p => f p - (J ×ˢ J).indicator f p := by
    funext p
    rw [adjacency_moment]
    by_cases hx : p.1 ∈ J <;> by_cases hy : p.2 ∈ J <;>
      simp [adjacency, hx, hy, f]
  unfold density
  rw [heq, integral_sub hf (hf.indicator (hJ.prod hJ)), integral_indicator (hJ.prod hJ)]
  have hwhole := integral_congr_ae hAdj
  have hinternal := integral_congr_ae (ae_restrict_of_ae hAdj :
    (fun p => W.moment CappedColor.adjacency p) =ᵐ[(ν.prod ν).restrict (J ×ˢ J)] f)
  rw [← hwhole, ← hinternal]
  simp only [adjacencyKernel]
  change ((_ : ℝ) - _) / 2 = _ / 2 - _ / 2
  ring

end ScalarModel

/-- An actual binary-support full model supplies its own scalar tests and
bounded charge. Only the displayed current-law external join is required. -/
theorem exists_model (W : Model Ω ν) (hW : FullFeasible W)
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hAsym : ∀ x y, A x y = A y x)
    (hAdj : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if A p.1 p.2 = true then 1 else 0)
    (J : Set Ω) (hJ : MeasurableSet J) (hJpos : 0 < ν J)
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J →
      A p.1 p.2 = true ∧ A p.2 p.1 = true) :
    ∃ V : Model Ω ν, FullFeasible V ∧
      (∀ p, V.moment CappedColor.adjacency p = if adjacency A J p.1 p.2 = true then 1 else 0) ∧
      (∀ᵐ p ∂ν.prod ν, V.moment CappedColor.charge p =
        atomizedCharge (ν := ν) J (fun p => chargeKernel W p.1 p.2) p) ∧
      density V = density W - (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂ν.prod ν) / 2 ∧
      objective V = objective W - (∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂ν.prod ν) / 2 := by
  obtain ⟨Y, hY, hsym, hbound, hzero, hcharge, htests⟩ :=
    BinaryRepresentative.exists_scalar_representative W hW (Function.uncurry A) hA hAsym hAdj
  let V := model A hA hAsym J hJ hJpos Y hY hbound hsym
  have hwhole : (∫ p, Y p ∂ν.prod ν) / 2 = objective W := by
    unfold objective
    congr 1
    exact integral_congr_ae hcharge
  have hinternal : (∫ p in J ×ˢ J, Y p ∂ν.prod ν) =
      ∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂ν.prod ν :=
    integral_congr_ae (ae_restrict_of_ae hcharge)
  refine ⟨V, fullFeasible_model A hA hAsym J hJ hJpos Y hY hbound hsym hjoin htests,
    adjacency_moment A hA hAsym J hJ hJpos Y hY hbound hsym, ?_,
    density_model A hA hAsym J hJ hJpos Y hY hbound hsym W hAdj, ?_⟩
  · filter_upwards [charge_moment_ae A hA hAsym J hJ hJpos Y hY hbound hsym hjoin hzero,
      atomizedCharge_congr_ae J hJpos Y (fun p => chargeKernel W p.1 p.2) hcharge]
      with p hp hq
    exact hp.trans hq
  · rw [objective_model A hA hAsym J hJ hJpos Y hY hbound hsym hjoin hzero, hwhole, hinternal]

end Erdos1017.CappedModel.JoinedCellCollapse

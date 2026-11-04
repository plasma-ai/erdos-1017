module

public import Erdos1017.Models.Capped.CappedUniversalVertices
public import Erdos1017.Models.Capped.CappedGrowingLimit
public import Erdos1017.Models.Capped.CappedConditionalCharge

/-!
# Turning a measurable set into universal dust

The edit `universalSetEdit` makes every point of a measurable set universal with
zero incident charge while keeping the probability law, and it stays feasible
with computed moments. Turning part of an independent class into universal dust
raises edge density by an explicit amount and loses at most its outside pair
mass in objective.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every point of the displayed measurable set becomes universal with
zero incident charge. The original probability law is retained. -/
def universalSetEdit (C : Set Ω) (z : ((Ω × Ω) × CappedColor)) : CappedColor :=
  if z.1.1 ∈ C ∨ z.1.2 ∈ C then zeroChargePresent else z.2

theorem measurable_universalSetEdit (C : Set Ω) (hC : MeasurableSet C) :
    Measurable (universalSetEdit C) :=
  measurable_const.ite ((hC.preimage (by fun_prop)).union (hC.preimage (by fun_prop)))
    measurable_snd

def universalSet (W : Model Ω μ) (C : Set Ω) (hC : MeasurableSet C) : Model Ω μ :=
  W.edit (universalSetEdit C) (measurable_universalSetEdit C hC)
    (Eventually.of_forall (fun _ _ => by simp [universalSetEdit, or_comm]))

/-- Genuine old subclique tests license all orders of the set edit. -/
theorem feasible_universalSet (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (C : Set Ω) (hC : MeasurableSet C) : Feasible r (universalSet W C hC) := by
  intro n hn hnr
  filter_upwards [ae_all_subclique_tests W hW n] with x hx
  unfold cliqueLaw universalSet
  rw [DecoratedKernel.sampleLaw_edit]
  have hm : Measurable (fun c : CliquePair n → CappedColor =>
      fun p => universalSetEdit C ((x p.val.1, x p.val.2), c p)) :=
    measurable_pi_iff.mpr (fun p =>
      (measurable_universalSetEdit C hC).comp (measurable_const.prodMk (measurable_pi_apply p)))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (continuous_violation n).measurable measurable_const)).2
  filter_upwards [hx] with c hc
  have he : (fun p => universalSetEdit C ((x p.val.1, x p.val.2), c p)) =
      universalConfiguration (fun i => decide (x i ∈ C)) c := by
    funext p
    simp [universalSetEdit, universalConfiguration]
  rw [he]
  exact violation_universalConfiguration _ _ (fun k hk hkn e => hc k hk (hkn.trans hnr) e)

theorem fullFeasible_universalSet (W : Model Ω μ) (hW : FullFeasible W)
    (C : Set Ω) (hC : MeasurableSet C) : FullFeasible (universalSet W C hC) :=
  fun r => feasible_universalSet W (hW r) C hC

omit [IsProbabilityMeasure μ] in
theorem moment_universalSet (W : Model Ω μ) (C : Set Ω) (hC : MeasurableSet C)
    (p : Ω × Ω) (h : CappedColor → ℝ) (hh : StronglyMeasurable h) :
    (universalSet W C hC).moment h p =
      if p.1 ∈ C ∨ p.2 ∈ C then h zeroChargePresent else W.moment h p := by
  change (∫ c, h c ∂W.editKernel (universalSetEdit C) p) = _
  rw [DecoratedKernel.editKernel_apply _ _ (measurable_universalSetEdit C hC),
    integral_map_of_stronglyMeasurable (φ := fun c => universalSetEdit C (p, c))
      ((measurable_universalSetEdit C hC).comp measurable_prodMk_left) hh]
  by_cases hp : p.1 ∈ C ∨ p.2 ∈ C
  · simp only [universalSetEdit, hp, ↓reduceIte]
    simp
  · simp only [universalSetEdit, hp, ↓reduceIte]
    rfl

omit [IsProbabilityMeasure μ] in
theorem adjacency_moment_universalSet (W : Model Ω μ) (C : Set Ω) (hC : MeasurableSet C)
    (p : Ω × Ω) :
    (universalSet W C hC).moment CappedColor.adjacency p =
      if p.1 ∈ C ∨ p.2 ∈ C then 1 else W.moment CappedColor.adjacency p := by
  rw [moment_universalSet W C hC p _
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable, adjacency_zeroChargePresent]

omit [IsProbabilityMeasure μ] in
theorem charge_moment_universalSet (W : Model Ω μ) (C : Set Ω) (hC : MeasurableSet C)
    (p : Ω × Ω) :
    (universalSet W C hC).moment CappedColor.charge p =
      if p.1 ∈ C ∨ p.2 ∈ C then 0 else W.moment CappedColor.charge p := by
  rw [moment_universalSet W C hC p _
    CappedColor.continuous_charge.measurable.stronglyMeasurable, charge_zeroChargePresent]

/-- Turning a subset of an independent class into universal dust increases
edge density by the displayed amount and loses at most its full
outside pair mass in objective. No constant charge row is required. -/
theorem universalSet_independent_comparison (W : Model Ω μ) (P C : Set Ω)
    (hP : MeasurableSet P) (hC : MeasurableSet C) (hCP : C ⊆ P)
    (hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ P →
      W.moment CappedColor.adjacency p = 0) :
    density W + μ.real C * μ.real P - (μ.real C) ^ 2 / 2 ≤
        density (universalSet W C hC) ∧
      objective W - μ.real C * (1 - μ.real P) ≤ objective (universalSet W C hC) := by
  let U := universalSet W C hC
  let Z := C ×ˢ P ∪ (P \ C) ×ˢ C
  let F := C ×ˢ Pᶜ ∪ Pᶜ ×ˢ C
  have hZ : MeasurableSet Z := (hC.prod hP).union ((hP.diff hC).prod hC)
  have hF : MeasurableSet F := (hC.prod hP.compl).union (hP.compl.prod hC)
  have hDZ : Disjoint (C ×ˢ P) ((P \ C) ×ˢ C) := Set.disjoint_left.mpr
    (fun _ hp hq => hq.1.2 hp.1)
  have hDF : Disjoint (C ×ˢ Pᶜ) (Pᶜ ×ˢ C) := Set.disjoint_left.mpr
    (fun _ hp hq => hq.1 (hCP hp.1))
  have hZm : (μ.prod μ).real Z = 2 * μ.real C * μ.real P - (μ.real C) ^ 2 := by
    rw [measureReal_union hDZ ((hP.diff hC).prod hC),
      measureReal_prod_prod, measureReal_prod_prod,
      measureReal_sdiff (μ := μ) hCP hC]
    ring
  have hFm : (μ.prod μ).real F = 2 * μ.real C * (1 - μ.real P) := by
    rw [measureReal_union hDF (hP.compl.prod hC),
      measureReal_prod_prod, measureReal_prod_prod, measureReal_compl hP]
    simp only [probReal_univ]
    ring
  have hA (V : Model Ω μ) : Integrable (V.moment CappedColor.adjacency) (μ.prod μ) :=
    integrable_bounded_moment V CappedColor.adjacency
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2)
  have hY (V : Model Ω μ) : Integrable (V.moment CappedColor.charge) (μ.prod μ) :=
    integrable_bounded_moment V CappedColor.charge
      CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
          (CappedColor.charge_mem c).2.trans (by norm_num)⟩)
  have hAle : ∀ᵐ p ∂μ.prod μ,
      Z.indicator (fun _ => (1 : ℝ)) p ≤
        U.moment CappedColor.adjacency p - W.moment CappedColor.adjacency p := by
    filter_upwards [hind] with p hp
    rw [adjacency_moment_universalSet]
    by_cases hz : p ∈ Z
    · rw [indicator_of_mem hz]
      rcases hz with hz | hz
      · rw [ite_eq_left (Or.inl hz.1), hp (hCP hz.1) hz.2]
        norm_num
      · rw [ite_eq_left (Or.inr hz.2), hp hz.1.1 (hCP hz.2)]
        norm_num
    · rw [indicator_of_notMem hz]
      split_ifs
      · exact sub_nonneg.mpr (adjacency_moment_mem W p).2
      · simp
  have hYle : ∀ᵐ p ∂μ.prod μ,
      W.moment CappedColor.charge p - U.moment CappedColor.charge p ≤
        F.indicator (fun _ => (1 : ℝ)) p := by
    filter_upwards [hind] with p hp
    rw [charge_moment_universalSet]
    by_cases hc : p.1 ∈ C ∨ p.2 ∈ C
    · rw [ite_eq_left hc, sub_zero]
      by_cases hf : p ∈ F
      · rw [indicator_of_mem hf]
        exact (charge_moment_le_adjacency W p).trans (adjacency_moment_mem W p).2
      · rw [indicator_of_notMem hf]
        have hpp : p.1 ∈ P ∧ p.2 ∈ P := by
          rcases hc with hx | hy
          · exact ⟨hCP hx, by by_contra hn; exact hf (Or.inl ⟨hx, hn⟩)⟩
          · exact ⟨by by_contra hn; exact hf (Or.inr ⟨hn, hy⟩), hCP hy⟩
        rw [charge_moment_of_adjacency_zero W p (hp hpp.1 hpp.2)]
    · rw [ite_eq_right hc, sub_self]
      exact indicator_nonneg (fun _ _ => by norm_num) p
  have ha := integral_mono_ae ((integrable_const 1).indicator hZ) ((hA U).sub (hA W)) hAle
  have hy := integral_mono_ae ((hY W).sub (hY U)) ((integrable_const 1).indicator hF) hYle
  simp only [Pi.sub_apply] at ha hy
  rw [integral_indicator hZ, setIntegral_const, smul_eq_mul, mul_one,
    integral_sub (hA U) (hA W), hZm] at ha
  rw [integral_indicator hF, setIntegral_const, smul_eq_mul, mul_one,
    integral_sub (hY W) (hY U), hFm] at hy
  constructor <;> simp only [density, objective] <;> dsimp [U] at ha hy <;>
    linarith only [ha, hy]

end Erdos1017.CappedModel

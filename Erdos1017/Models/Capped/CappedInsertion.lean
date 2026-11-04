module

public import Erdos1017.Models.Capped.CappedConfigurationInsertion
public import Erdos1017.Models.Capped.CappedRandomDeletion

/-!
# Insertion into absent outcomes of capped models

Inserting every absent outcome at charge `-3` (`insertAbsent`) gives a feasible
decorated kernel by the finite cost-four repair, randomized and
endpoint-dependent insertion preserves every imposed test, and sprinkling
(`sprinkle`) inserts a fraction `t` of absent outcomes independently at each
pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measurable_insertColor : Measurable insertColor := by
  exact measurable_id.ite
    (measurableSet_eq_fun CappedColor.continuous_adjacency.measurable measurable_const)
    measurable_const

theorem violation_insertColor {n : ℕ} (c : CliquePair n → CappedColor) (hn : 2 ≤ n)
    (htests : ∀ k, 2 ≤ k → k ≤ n → ∀ e : Fin k ↪o Fin n,
      violation (fun p => c (pairEmbedding e p)) = 0) :
    violation (fun p => insertColor (c p)) = 0 := by
  have hsum := sum_insertColor_le_one c hn htests
  simp only [violation, max_eq_right (sub_nonpos.mpr hsum), zero_mul]

/-- Insert every absent outcome at charge `-3` as an actual decorated
kernel. Feasibility is proved from the finite cost-four repair. -/
def insertAbsent (W : Model Ω μ) : Model Ω μ := W.map insertColor measurable_insertColor

theorem feasible_insertAbsent (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) :
    Feasible r (insertAbsent W) := by
  intro n hn hnr
  filter_upwards [ae_all_subclique_tests W hW n] with x hx
  unfold cliqueLaw insertAbsent
  rw [DecoratedKernel.sampleLaw_map]
  have hm : Measurable (fun c : CliquePair n → CappedColor => fun p => insertColor (c p)) :=
    measurable_pi_iff.mpr (fun p => measurable_insertColor.comp (measurable_pi_apply p))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (continuous_violation n).measurable measurable_const)).2
  filter_upwards [hx] with c hc
  exact violation_insertColor c hn (fun k hk hkn e => hc k hk (hkn.trans hnr) e)

/-- Independently randomized and endpoint-dependent insertion into absent
outcomes preserves every imposed test. Present outcomes retain their old
charges, and new outcomes receive exactly the repair charge `-3`. -/
theorem feasible_random_insertion (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (η : Measure U) [IsProbabilityMeasure η]
    (f : (Ω × Ω) × (CappedColor × U) → CappedColor) (hf : Measurable f)
    (hsym : ∀ᵐ p ∂μ.prod μ, ∀ c, f (p.swap, c) = f (p, c))
    (hinsert : ∀ p c u, f (p, (c, u)) = c ∨
      (CappedColor.adjacency c ≠ 1 ∧ f (p, (c, u)) = negativeThree)) :
    Feasible r ((W.couple η).edit f hf hsym) := by
  intro n hn hnr
  filter_upwards [ae_all_subclique_tests W hW n] with x hx
  let pairs : CliquePair n → Ω × Ω := fun p => (x p.val.1, x p.val.2)
  have hproj : ∀ᵐ c ∂(W.couple η).sampleLaw pairs,
      ∀ k, 2 ≤ k → k ≤ r → ∀ e : Fin k ↪o Fin n,
        violation (fun p => (c (pairEmbedding e p)).1) = 0 := by
    have hm : Measurable (fun c : CliquePair n → CappedColor × U => fun p => (c p).1) :=
      measurable_pi_iff.mpr (fun p => measurable_fst.comp (measurable_pi_apply p))
    change ∀ᵐ c ∂W.sampleLaw pairs, _ at hx
    rw [← DecoratedKernel.sampleLaw_couple_fst W η pairs] at hx
    exact ae_of_ae_map hm.aemeasurable hx
  unfold cliqueLaw
  rw [DecoratedKernel.sampleLaw_edit]
  have hm : Measurable (fun c : CliquePair n → CappedColor × U =>
      fun p => f (pairs p, c p)) :=
    measurable_pi_iff.mpr (fun p =>
      hf.comp (measurable_const.prodMk (measurable_pi_apply p)))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (continuous_violation n).measurable measurable_const)).2
  filter_upwards [hproj] with c hc
  classical
  by_cases hz : ∃ p, CappedColor.adjacency (f (pairs p, c p)) = 0
  · obtain ⟨p, hp⟩ := hz
    have hp' : (∏ q, CappedColor.adjacency (f (pairs q, c q))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) hp
    simp only [violation, hp', mul_zero]
  · have heq (p : CliquePair n) : f (pairs p, c p) = insertColor (c p).1 := by
      rcases hinsert (pairs p) (c p).1 (c p).2 with hkeep | ⟨habs, hnew⟩
      · have hold : CappedColor.adjacency (c p).1 = 1 := by
          rcases CappedColor.adjacency_eq_zero_or_one (c p).1 with hzero | hone
          · exact False.elim (hz ⟨p, hkeep ▸ hzero⟩)
          · exact hone
        simp only [insertColor, hold, ↓reduceIte, hkeep]
      · simp only [insertColor, habs, ↓reduceIte, hnew]
    simp only [heq]
    exact violation_insertColor (fun p => (c p).1) hn
      (fun k hk hkn e => hc k hk (hkn.trans hnr) e)

/-- An independent coin inserts an absent outcome and retains every old
present outcome. -/
def insertCoin (z : (Ω × Ω) × (CappedColor × Bool)) : CappedColor :=
  if CappedColor.adjacency z.2.1 = 1 then z.2.1
  else if z.2.2 = true then negativeThree else z.2.1

theorem measurable_insertCoin : Measurable (insertCoin (Ω := Ω)) := by
  have hp : Measurable (fun z : (Ω × Ω) × (CappedColor × Bool) =>
      CappedColor.adjacency z.2.1) :=
    CappedColor.continuous_adjacency.measurable.comp (measurable_fst.comp measurable_snd)
  have hcoin : MeasurableSet {z : (Ω × Ω) × (CappedColor × Bool) | z.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  exact (measurable_fst.comp measurable_snd).ite (measurableSet_eq_fun hp measurable_const)
    (measurable_const.ite hcoin (measurable_fst.comp measurable_snd))

/-- Insert fraction `t` of absent outcomes independently at each pair. -/
def sprinkle (W : Model Ω μ) (t : unitInterval) : Model Ω μ :=
  (W.couple (bernoulliMeasure true false t)).edit insertCoin measurable_insertCoin
    (Filter.Eventually.of_forall (fun _ _ => rfl))

theorem feasible_sprinkle (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) (t : unitInterval) :
    Feasible r (sprinkle W t) := by
  apply feasible_random_insertion W hW
  intro p c u
  by_cases hc : CappedColor.adjacency c = 1
  · simp [insertCoin, hc]
  · cases u <;> simp [insertCoin, hc]

end Erdos1017.CappedModel

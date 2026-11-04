module

public import Erdos1017.SelectedModel.Structure.FeatureCountSampling

/-!
# Feasibility of completing a two-clique-covered set

Completing the pairs inside a measurable set `D` with charge `-ell` keeps
adjacency and charge measurable, and when `D` is covered by two cliques it
preserves each fixed-order physical clique test
(`feasibleOrder_complete_of_two_clique_cover`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.FiniteArity

/-- Support sampling and zero-pair transfers prove the completed test for
one finite feature tuple. Outside types stay at count one; only the diffuse
types are repeated, and their total count is unchanged. -/
theorem mixed_feature_tuple_test_le
    {Ω E ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (F : Ω → E) (hF : Measurable F) (J : E →ₗᵢ[ℝ] E) (ℓ : ℝ)
    (hstrict : ∀ᵐ p ∂μ.prod μ, 0 < ⟪J (F p.1), F p.2⟫ → A p.1 p.2 = true)
    (hcharge : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = true → Y p.1 p.2 = ⟪J (F p.1), F p.2⟫ - ℓ)
    (m n : ℕ) (hn : Fintype.card ι + m = n) (htest : FeasibleOrder μ A Y n)
    (C : Fin m → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hclique : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C i → p.2 ∈ C i → A p.1 p.2 = true)
    (w : ι ⊕ Fin m → E)
    (hout : ∀ i, w (Sum.inl i) ∈ (μ.map F).support)
    (hin : ∀ i, w (Sum.inr i) ∈ ((μ.restrict (C i)).map F).support)
    (hsym : ∀ a b, ⟪J (w a), w b⟫ = ⟪J (w b), w a⟫)
    (hdiag : ∀ i, 0 ≤ ⟪J (w (Sum.inr i)), w (Sum.inr i)⟫)
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ ⟪J (w (Sum.inr i)), w (Sum.inr j)⟫)
    (houtside : ∀ i b, Sum.inl i ≠ b → 0 < ⟪J (w (Sum.inl i)), w b⟫) :
    multiplicityCharge (fun a b => ⟪J (w a), w b⟫ - ℓ) (fun _ => 1) ≤ 1 := by
  classical
  let K : ι ⊕ Fin m → ι ⊕ Fin m → ℝ := fun a b => ⟪J (w a), w b⟫ - ℓ
  let M : Fin m → Fin m → ℝ := fun i j => ⟪J (w (Sum.inr i)), w (Sum.inr j)⟫
  let h := multiplicityCharge (fun i j => K (Sum.inl i) (Sum.inl j)) (fun _ => 1)
  let x : Fin m → ℝ := fun j => ∑ i, K (Sum.inl i) (Sum.inr j)
  have hMsym : ∀ i j, M i j = M j i := fun i j => hsym (Sum.inr i) (Sum.inr j)
  have hsplit (k : Fin m → ℕ) :
      multiplicityCharge K (Sum.elim (fun _ => 1) k) =
        ZeroPairCount.countCharge h ℓ x (fun i => M i i) M k := by
    rw [multiplicityCharge_sum_one K k (fun i j => by
      dsimp only [K]
      rw [hsym])]
    exact (countCharge_eq_multiplicityCharge h ℓ x M hMsym k).symm
  have hbound (k : Fin m → ℕ) (hk : ∑ i, k i = m)
      (hpositive : ZeroPairCount.strictSupport M k) :
      ZeroPairCount.countCharge h ℓ x (fun i => M i i) M k ≤ 1 := by
    rw [← hsplit]
    apply multiplicity_test_le_of_feature_support μ A Y F hF J ℓ
      (Sum.elim (fun _ => univ) C)
      (by intro a; cases a with | inl i => exact MeasurableSet.univ | inr i => exact hC i)
      hstrict hcharge n htest (Sum.elim (fun _ => 1) k)
    · simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hk] using hn
    · intro a ha
      cases a with
      | inl i => simp only [Sum.elim_inl] at ha; omega
      | inr i => exact hclique i
    · intro a _
      cases a with
      | inl i => simpa only [Sum.elim_inl, Measure.restrict_univ] using hout i
      | inr i => exact hin i
    · intro a b hab ha hb
      cases a with
      | inl i => exact houtside i b hab
      | inr i =>
        cases b with
        | inl j => rw [hsym]; exact houtside j (Sum.inr i) (by simp)
        | inr j => exact hpositive i j (fun hij => hab (congrArg Sum.inr hij)) ha hb
  have hall := ZeroPairCount.countCharge_le_of_strictSupport h ℓ x (fun i => M i i) M
    hdiag hMsym hnonneg m hbound (fun _ => 1) (by simp)
  have heq : (Sum.elim (fun _ : ι => 1) (fun _ : Fin m => 1)) = fun _ => 1 := by
    funext a
    cases a <;> rfl
  rw [← hsplit, heq] at hall
  exact hall

/-- Complete only pairs inside D, retaining every incidence involving its
complement. -/
def completeAdjacency {Ω : Type*} (A : Ω → Ω → Bool) (D : Set Ω)
    [DecidablePred (· ∈ D)] (x y : Ω) : Bool :=
  if x ∈ D ∧ y ∈ D then true else A x y

/-- New edges inside D receive charge -ell; every old charge is retained. -/
def completeCharge {Ω : Type*} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (D : Set Ω) [DecidablePred (· ∈ D)] (ℓ : ℝ) (x y : Ω) : ℝ :=
  if x ∈ D ∧ y ∈ D ∧ A x y = false then -ℓ else Y x y

/-- A measurable completion set gives a measurable completed adjacency. -/
theorem measurable_completeAdjacency {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (D : Set Ω) [DecidablePred (· ∈ D)] (hD : MeasurableSet D) :
    Measurable (Function.uncurry (completeAdjacency A D)) :=
  measurable_const.ite ((hD.preimage measurable_fst).inter (hD.preimage measurable_snd)) hA

/-- New constant charges on the measurable missing-pair region preserve
measurability of the original charge kernel. -/
theorem measurable_completeCharge {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (D : Set Ω) [DecidablePred (· ∈ D)] (hD : MeasurableSet D) (ℓ : ℝ) :
    Measurable (Function.uncurry (completeCharge A Y D ℓ)) :=
  measurable_const.ite ((hD.preimage measurable_fst).inter
    ((hD.preimage measurable_snd).inter (measurableSet_eq_fun hA measurable_const))) hY

/-- Completing a two-clique-covered set with charge -ell preserves
an actual fixed-order physical clique test. No other orders, homogeneous atoms,
or completed-test premises are used. -/
theorem feasibleOrder_complete_of_two_clique_cover
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (F : Ω → E) (hF : Measurable F) (J : E →ₗᵢ[ℝ] E)
    (hsym : ∀ x y : E, ⟪J x, y⟫ = ⟪J y, x⟫) (ℓ : ℝ)
    (hpair : ∀ᵐ p ∂μ.prod μ,
      0 ≤ ⟪J (F p.1), F p.2⟫ ∧
        (A p.1 p.2 = true ↔ 0 < ⟪J (F p.1), F p.2⟫) ∧
        (A p.1 p.2 = true → Y p.1 p.2 = ⟪J (F p.1), F p.2⟫ - ℓ))
    (hdiag : ∀ᵐ x ∂μ, 0 ≤ ⟪J (F x), F x⟫)
    (D : Set Ω) [DecidablePred (· ∈ D)]
    (C : Bool → Set Ω) (hC : ∀ b, MeasurableSet (C b))
    (hcover : ∀ᵐ x ∂μ, x ∈ D → x ∈ C false ∨ x ∈ C true)
    (hclique : ∀ b, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C b → p.2 ∈ C b → A p.1 p.2 = true)
    (n : ℕ) (htest : FeasibleOrder μ A Y n) :
    FeasibleOrder μ (completeAdjacency A D) (completeCharge A Y D ℓ) n := by
  classical
  have hglobal : ∀ᵐ x ∂μ, F x ∈ (μ.map F).support :=
    ae_of_ae_map hF.aemeasurable Measure.support_mem_ae
  have hcells : ∀ᵐ x ∂μ, ∀ b, x ∈ C b → F x ∈ ((μ.restrict (C b)).map F).support := by
    apply ae_all_iff.mpr
    intro b
    apply (ae_restrict_iff' (hC b)).mp
    exact ae_of_ae_map hF.aemeasurable Measure.support_mem_ae
  have hpoint : ∀ᵐ x ∂μ,
      F x ∈ (μ.map F).support ∧
        (∀ b, x ∈ C b → F x ∈ ((μ.restrict (C b)).map F).support) ∧
        0 ≤ ⟪J (F x), F x⟫ ∧ (x ∈ D → x ∈ C false ∨ x ∈ C true) := by
    filter_upwards [hglobal, hcells, hdiag, hcover] with x hg hc hd hv
    exact ⟨hg, hc, hd, hv⟩
  have hcoords : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), ∀ i,
      F (v i) ∈ (μ.map F).support ∧
        (∀ b, v i ∈ C b → F (v i) ∈ ((μ.restrict (C b)).map F).support) ∧
        0 ≤ ⟪J (F (v i)), F (v i)⟫ ∧
          (v i ∈ D → v i ∈ C false ∨ v i ∈ C true) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => μ) i).quasiMeasurePreserving.ae hpoint
  have hpairs := ae_all_pairs μ n _ hpair
  filter_upwards [hcoords, hpairs] with v hv hp
  intro hvclique
  let S : Set (Fin n) := {i | v i ∈ D}
  let eD : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let e : ↥(Sᶜ) ⊕ Fin (Fintype.card S) ≃ Fin n :=
    ((Equiv.sumCongr (Equiv.refl ↥(Sᶜ)) eD).trans (Equiv.sumComm _ _)).trans
      (Equiv.Set.sumCompl S)
  let w : ↥(Sᶜ) ⊕ Fin (Fintype.card S) → E := fun a => F (v (e a))
  have hn : Fintype.card ↥(Sᶜ) + Fintype.card S = n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  have hinD (i : Fin (Fintype.card S)) : v (e (Sum.inr i)) ∈ D := (eD i).property
  have houtD (i : ↥(Sᶜ)) : v (e (Sum.inl i)) ∉ D := i.property
  let side : Fin (Fintype.card S) → Bool := fun i =>
    if v (e (Sum.inr i)) ∈ C false then false else true
  have hside (i : Fin (Fintype.card S)) : v (e (Sum.inr i)) ∈ C (side i) := by
    dsimp only [side]
    split_ifs with hi
    · exact hi
    · exact ((hv (e (Sum.inr i))).2.2.2 (hinD i)).resolve_left hi
  have hmixed := mixed_feature_tuple_test_le μ A Y F hF J ℓ
    (hpair.mono (fun _ h => h.2.1.mpr)) (hpair.mono (fun _ h => h.2.2))
    (Fintype.card S) n hn htest (fun i => C (side i)) (fun i => hC (side i))
    (fun i => hclique (side i)) w
    (fun i => (hv (e (Sum.inl i))).1)
    (fun i => (hv (e (Sum.inr i))).2.1 (side i) (hside i))
    (fun a b => hsym (w a) (w b))
    (fun i => (hv (e (Sum.inr i))).2.2.1)
    (fun i j hij => (hp (e (Sum.inr i)) (e (Sum.inr j)) (fun heq =>
      hij (Sum.inr.inj (e.injective heq)))).1)
    (by
      intro i b hib
      have hij : e (Sum.inl i) ≠ e b := fun heq => hib (e.injective heq)
      have ha := hvclique (e (Sum.inl i)) (e b) hij
      simp only [completeAdjacency, houtD i, false_and, ite_false] at ha
      exact (hp _ _ hij).2.1.mp ha)
  have hcharge (i j : Fin n) (hij : i ≠ j) :
      completeCharge A Y D ℓ (v i) (v j) = ⟪J (F (v i)), F (v j)⟫ - ℓ := by
    cases ha : A (v i) (v j) with
    | true =>
      simp only [completeCharge, ha, Bool.true_eq_false, and_false, ite_false]
      exact (hp i j hij).2.2 ha
    | false =>
      have hD : v i ∈ D ∧ v j ∈ D := by
        have h := hvclique i j hij
        by_contra hnot
        simp only [completeAdjacency, hnot, ite_false, ha, Bool.false_eq_true] at h
      have hz : ⟪J (F (v i)), F (v j)⟫ = 0 := by
        have hnot : ¬ 0 < ⟪J (F (v i)), F (v j)⟫ := by
          intro hpos
          have h := (hp i j hij).2.1.mpr hpos
          rw [ha] at h
          contradiction
        exact le_antisymm (le_of_not_gt hnot) (hp i j hij).1
      simp only [completeCharge, hD.1, hD.2, ha, and_self, ite_true, hz, zero_sub]
  have hchargeTuple : tupleCharge (completeCharge A Y D ℓ) v =
      tupleCharge (fun x y : E => ⟪J x, y⟫ - ℓ) (fun i => F (v i)) := by
    unfold tupleCharge
    congr 1
    funext i j
    by_cases hij : i = j
    · simp only [hij, ite_true]
    · simp only [hij, ite_false, hcharge i j hij]
  rw [hchargeTuple, tupleCharge_eq_multiplicityCharge_one]
  have heq := multiplicityCharge_equiv e
    (fun i j => ⟪J (F (v i)), F (v j)⟫ - ℓ) (fun _ => 1)
  exact heq ▸ hmixed

end Erdos1017.FiniteArity

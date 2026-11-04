module

public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Finite arity from bounded features

Bounded Hilbert features and a positive stationary gap reduce all physical
clique tests to an explicit finite budget, by constructing hubs
(`bounded_feature_arity`), also in the shifted-kernel form.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.FiniteArity

/-- The pairwise support, symmetry, and color bounds used in the arity proof. -/
structure PairRegular {Ω : Type*} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (x y : Ω) : Prop where
  adjacency_symm : A x y = A y x
  charge_symm : Y x y = Y y x
  charge_le_one : Y x y ≤ 1
  missing_zero : A x y = false → Y x y = 0
  charge_ge_neg_three : A x y = true → -3 ≤ Y x y

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Ordinary product-null tests license the actual finite certificate at every
larger sampled order. No singular joint tuple law is used in this lemma. -/
theorem omitted_feasible_of_hubs (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (R g : ℝ) (hR : 0 < R) (hg : 0 < g)
    (hreg : ∀ᵐ z ∂μ.prod μ, PairRegular A Y z.1 z.2)
    (hcap : ∀ r, 2 ≤ r → r ≤ Certificate.testBudget R g → FeasibleOrder μ A Y r)
    (hubs : Fin (Certificate.hubCount R g) → Ω)
    (hcover : ∀ᵐ x ∂μ, Certificate.hubGap g ≤
      (Certificate.hubCount R g : ℝ)⁻¹ * ∑ i, Y (hubs i) x)
    (hhubreg : ∀ i, ∀ᵐ x ∂μ, PairRegular A Y (hubs i) x)
    (hroot : ∀ i, ∀ᵐ v ∂Measure.pi (fun _ : Fin (Certificate.testOrder g) => μ),
      TupleClique A (Fin.cons (hubs i) v) → tupleCharge Y (Fin.cons (hubs i) v) ≤ 1)
    (n : ℕ) (hn : Certificate.testBudget R g < n) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), TupleClique A v → tupleCharge Y v < 0 := by
  have hpairs := ae_all_pairs μ n (fun z => PairRegular A Y z.1 z.2) hreg
  have hrows : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), ∀ j,
      Certificate.hubGap g ≤ (Certificate.hubCount R g : ℝ)⁻¹ * ∑ i, Y (hubs i) (v j) := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (fun _ : Fin n => μ) j).quasiMeasurePreserving.ae hcover
  have hhubs : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), ∀ i j, PairRegular A Y (hubs i) (v j) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (fun _ : Fin n => μ) j).quasiMeasurePreserving.ae (hhubreg i)
  have hroots : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), ∀ i,
      ∀ e : Fin (Certificate.testOrder g) ↪ Fin n,
      TupleClique A (Fin.cons (hubs i) (fun j => v (e j))) →
        tupleCharge Y (Fin.cons (hubs i) (fun j => v (e j))) ≤ 1 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro e
    exact (measurePreserving_subtuple μ e).quasiMeasurePreserving.ae (hroot i)
  have hsmall := ae_small_subsets μ A Y (Certificate.testBudget R g) n hcap
  filter_upwards [hpairs, hrows, hhubs, hroots, hsmall] with v hv hrow hhub hrootv hsmallv
  intro hclique
  change pairCharge Finset.univ (fun i j => if i = j then 0 else Y (v i) (v j)) < 0
  apply Certificate.finite_omitted_negative R g hR hg Finset.univ
    (fun j i => A (hubs i) (v j)) (fun i j => Y (hubs i) (v j))
    (fun i j => if i = j then 0 else Y (v i) (v j))
  · intro i
    simp
  · intro i j
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using (hv i j hij).charge_le_one
  · intro i _ j _ hij
    simpa [hij] using (hv i j hij).charge_ge_neg_three (hclique i j hij)
  · intro j _
    exact hrow j
  · intro j _ i hi
    exact (hhub i j).missing_zero hi
  · intro i S _ hS hadj
    let e := (S.orderEmbOfFin hS).toEmbedding
    have heMem (j : Fin (Certificate.testOrder g)) : e j ∈ S := S.orderEmbOfFin_mem hS j
    have hl (j : Fin (Certificate.testOrder g)) : A (hubs i) (v (e j)) = true := hadj (e j) (heMem j)
    have hr (j : Fin (Certificate.testOrder g)) : A (v (e j)) (hubs i) = true :=
      (hhub i (e j)).adjacency_symm.symm.trans (hl j)
    have hc := (hclique.subtuple e).cons (hubs i) hl hr
    have ht := hrootv i e hc
    rw [tupleCharge_cons Y (hubs i) _ (fun j => (hhub i (e j)).charge_symm.symm),
      tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ S hS] at ht
    have hsum : (∑ j, Y (hubs i) (v (e j))) = ∑ a ∈ S, Y (hubs i) (v a) := by
      rw [← Finset.map_orderEmbOfFin_univ S hS, Finset.sum_map]
    rw [hsum] at ht
    exact ht
  · intro S _ hS
    exact hsmallv hclique S hS
  · simpa using hn

/-- Bounded Hilbert features and a positive stationary gap reduce all physical
clique tests to the explicit finite budget. The proof constructs the hubs. -/
theorem bounded_feature_arity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) (J : E →ₗᵢ[ℝ] E)
    (R g ν ℓ : ℝ) (hR : 0 < R) (hg : 0 < g) (hgap : g ≤ ν - ℓ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R)
    (hrow : ∀ᵐ x ∂μ, ⟪J (∫ y, f y ∂μ), f x⟫ = ν)
    (hfeature : ∀ᵐ z ∂μ.prod μ, ⟪J (f z.1), f z.2⟫ - ℓ ≤ Y z.1 z.2)
    (hreg : ∀ᵐ z ∂μ.prod μ, PairRegular A Y z.1 z.2)
    (hcap : ∀ r, 2 ≤ r → r ≤ Certificate.testBudget R g → FeasibleOrder μ A Y r) :
    (∀ n, FeasibleOrder μ A Y n) ∧
      ∀ n, Certificate.testBudget R g < n →
        ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), TupleClique A v → tupleCharge Y v < 0 := by
  let k := Certificate.testOrder g
  have hk : 2 ≤ k := Certificate.testOrder_ge_two g
  have hbudget : k + 1 ≤ Certificate.testBudget R g := le_max_left _ _
  have hroot := ae_root_sections μ k
    (fun v => TupleClique A v → tupleCharge Y v ≤ 1)
    (hcap (k + 1) (by omega) hbudget)
  have hregular := Measure.ae_ae_of_ae_prod hreg
  let Good : (Fin (Certificate.hubCount R g) → Ω) → Prop := fun ω =>
    ∀ i, (∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
      TupleClique A (Fin.cons (ω i) v) → tupleCharge Y (Fin.cons (ω i) v) ≤ 1) ∧
      ∀ᵐ x ∂μ, PairRegular A Y (ω i) x
  have hGood : ∀ᵐ ω ∂Measure.pi (fun _ : Fin (Certificate.hubCount R g) => μ), Good ω := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin (Certificate.hubCount R g) => μ) i).quasiMeasurePreserving.ae
      (hroot.and hregular)
  obtain ⟨hubs, hhub, hcover⟩ := Certificate.exists_hub_cover_at_gap μ f hf J Y R g ν ℓ hR hg hgap
    hbound hrow (Measure.ae_ae_of_ae_prod hfeature) Good hGood
  have hneg (n : ℕ) (hn : Certificate.testBudget R g < n) :
      ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), TupleClique A v → tupleCharge Y v < 0 :=
    omitted_feasible_of_hubs μ A Y R g hR hg hreg hcap hubs hcover
      (fun i => (hhub i).2) (fun i => (hhub i).1) n hn
  refine ⟨?_, hneg⟩
  intro n
  by_cases hsmall : n ≤ 1
  · exact Filter.Eventually.of_forall (fun v _ => by
      rw [tupleCharge_small hsmall Y v]
      norm_num)
  · by_cases hn : n ≤ Certificate.testBudget R g
    · exact hcap n (by omega) hn
    · exact (hneg n (Nat.lt_of_not_ge hn)).mono (fun v hv hc => (hv hc).le.trans zero_le_one)

/-- The bounded-feature finite-arity theorem in the shifted-kernel form of the
source: sections 1–4 require no spectral theorem and no global extremality. -/
theorem bounded_feature_arity_of_shifted_kernel {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) (J : E →ₗᵢ[ℝ] E)
    (hself : ∀ u v : E, ⟪J u, v⟫ = ⟪u, J v⟫)
    (R g ν ℓ : ℝ) (hR : 0 < R) (hg : 0 < g) (hℓ : 0 < ℓ ∧ ℓ ≤ 3)
    (hgap : g ≤ ν - ℓ) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R)
    (hsym : ∀ᵐ z ∂μ.prod μ, A z.1 z.2 = A z.2 z.1 ∧ Y z.1 z.2 = Y z.2 z.1)
    (hupper : ∀ᵐ z ∂μ.prod μ, Y z.1 z.2 ≤ 1)
    (hsupport : ∀ᵐ z ∂μ.prod μ, A z.1 z.2 = false → Y z.1 z.2 = 0)
    (hnonneg : ∀ᵐ z ∂μ.prod μ, 0 ≤ Y z.1 z.2 + ℓ * (if A z.1 z.2 then 1 else 0))
    (hrepresentation : ∀ᵐ z ∂μ.prod μ,
      Y z.1 z.2 + ℓ * (if A z.1 z.2 then 1 else 0) = ⟪J (f z.1), f z.2⟫)
    (hstationary : ∀ᵐ x ∂μ, (∫ y, Y x y + ℓ * (if A x y then 1 else 0) ∂μ) = ν)
    (hcap : ∀ r, 2 ≤ r → r ≤ Certificate.testBudget R g → FeasibleOrder μ A Y r) :
    (∀ n, FeasibleOrder μ A Y n) ∧
      ∀ n, Certificate.testBudget R g < n →
        ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), TupleClique A v → tupleCharge Y v < 0 := by
  have hregular : ∀ᵐ z ∂μ.prod μ, PairRegular A Y z.1 z.2 := by
    filter_upwards [hsym, hupper, hsupport, hnonneg] with z hz hu hs hn
    refine ⟨hz.1, hz.2, hu, hs, ?_⟩
    intro hA
    simp only [hA, ite_true, mul_one] at hn
    linarith [hℓ.2]
  have hfeature : ∀ᵐ z ∂μ.prod μ, ⟪J (f z.1), f z.2⟫ - ℓ ≤ Y z.1 z.2 := by
    filter_upwards [hrepresentation] with z hz
    cases hA : A z.1 z.2
    · simp only [hA, Bool.false_eq_true, ite_false, mul_zero, add_zero] at hz
      rw [← hz]
      linarith [hℓ.1]
    · simp only [hA, ite_true, mul_one] at hz
      rw [← hz]
      linarith
  have hfi : Integrable f μ :=
    (show MemLp f 1 μ from MemLp.of_bound hf R hbound).integrable le_rfl
  have hrow : ∀ᵐ x ∂μ, ⟪J (∫ y, f y ∂μ), f x⟫ = ν := by
    filter_upwards [hstationary, Measure.ae_ae_of_ae_prod hrepresentation] with x hx hr
    have heq : (∫ y, Y x y + ℓ * (if A x y then 1 else 0) ∂μ) =
        ⟪J (f x), ∫ y, f y ∂μ⟫ := by
      rw [integral_congr_ae hr, integral_inner hfi]
    calc
      ⟪J (∫ y, f y ∂μ), f x⟫ = ⟪∫ y, f y ∂μ, J (f x)⟫ := hself _ _
      _ = ⟪J (f x), ∫ y, f y ∂μ⟫ := real_inner_comm _ _
      _ = ν := heq.symm.trans hx
  exact bounded_feature_arity μ A Y f hf J R g ν ℓ hR hg hgap hbound hrow hfeature hregular hcap

end Erdos1017.FiniteArity

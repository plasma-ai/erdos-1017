module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2PrivateStars

/-!
# Averaged fresh insertion into the private parents

Averaging a fresh insertion over a measurable vertex set `X` joined to every
vertex outside `X'` and the second fiber gives the averaged insertion inequality
for the original private parents (`ae_averaged_insertion`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.PrivatePhysicalPrimal

private theorem cons_pairs {Ω : Type*} {n : ℕ} (Q : Ω × Ω → Prop) (x : Ω) (v : Fin n → Ω)
    (hx : ∀ j, Q (x, v j) ∧ Q (v j, x)) (hv : ∀ a b, a ≠ b → Q (v a, v b)) :
    ∀ a b : Fin (n + 1), a ≠ b →
      Q ((Fin.cons x v : Fin (n + 1) → Ω) a, (Fin.cons x v : Fin (n + 1) → Ω) b) := by
  intro a b hab
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => exact (hab rfl).elim
    | succ b => simpa using (hx b).1
  | succ a =>
    cases b using Fin.cases with
    | zero => simpa using (hx a).2
    | succ b => simpa using hv a b (fun h => hab (by rw [h]))

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  {i p : S.I} {c d : ℝ}

/-- Averaged fresh insertion into the original private parents. Let `X` be
a measurable vertex set joined to every vertex outside `X'` and the second
fiber. Averaging a fresh point over `X` and inserting it into almost every
first-root parent avoiding `X'` gives a nonpositive averaged star. Pair
regularity of the same original model licenses every enlarged clique; the
parent laws may be singular. -/
theorem ae_averaged_insertion (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (X X' : Set Ω) (hX : MeasurableSet X)
    (hjoin : ∀ᵐ z ∂μ.prod μ, z.1 ∈ X → z.2 ∉ X' → S.ρ z.2 ≠ p.val →
      PhysicalRepresentative.adjacency W m z.1 z.2 = true) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, (∃ j, S.ρ (v j) = i.val) → (∀ j, v j ∉ X') →
      (∑ j, ∫ x in X, PhysicalRepresentative.charge W m x (v j) ∂μ) ≤ 0 := by
  let G : Ω × Ω → Bool := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let Y : Ω × Ω → ℝ := Function.uncurry (PhysicalRepresentative.charge W m)
  have hG : Measurable G := PhysicalRepresentative.measurable_adjacency W m
  have hY : Measurable Y := PhysicalRepresentative.measurable_charge W m
  have hYb : ∀ z, |Y z| ≤ 3 := fun z => PhysicalRepresentative.charge_bound W m z.1 z.2
  have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    intro k _
    filter_upwards [PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic k] with v hv hc
    change PhysicalPrimal.charge (Function.uncurry
      (PhysicalRepresentative.charge W m)) v ≤ 1
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    exact hv hc
  by_cases hn : 2 ≤ n
  swap
  · have hz : P.laws n = 0 := by
      interval_cases n
      · exact P.feasible.1
      · exact P.feasible.2.1
    rw [hz, ae_zero]
    exact Filter.eventually_bot
  have : IsFiniteMeasure (P.laws n) := P.finite n
  have hdemand : PhysicalPrimal.graphDemand μ
      {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true} ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict
  have hpairs : ∀ a b : Fin n, a ≠ b →
      (P.laws n).map (fun v => (v a, v b)) ≪ μ.prod μ := fun a b hab =>
    (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
      P.feasible.2.2.2 n ⟨(a, b), hab⟩).trans hdemand
  let Reg : Set (Ω × Ω) := {z | PhysicalCliqueRepresentative.PairRegular μ G Y z}
  have hReg : ∀ᵐ z ∂μ.prod μ, z ∈ Reg :=
    PhysicalCliqueRepresentative.ae_pairRegular μ hG hY 3 hYb
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hgood : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, (x, y) ∈ Reg ∧ (y, x) ∈ Reg ∧
      (x ∈ X → y ∉ X' → S.ρ y ≠ p.val → G (x, y) = true) := by
    have h1 : ∀ᵐ z ∂μ.prod μ, (z.2, z.1) ∈ Reg ∧ z ∈ Reg ∧
        (z.2 ∈ X → z.1 ∉ X' → S.ρ z.1 ≠ p.val → G (z.2, z.1) = true) := by
      filter_upwards [hswap.ae hReg, hReg, hswap.ae hjoin] with z h1 h2 h3
      exact ⟨h1, h2, h3⟩
    exact Measure.ae_ae_of_ae_prod h1
  have hcoord : ∀ᵐ v ∂P.laws n, ∀ j, ∀ᵐ x ∂μ, (x, v j) ∈ Reg ∧ (v j, x) ∈ Reg ∧
      (x ∈ X → v j ∉ X' → S.ρ (v j) ≠ p.val → G (x, v j) = true) := by
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable
      ((PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs
        μ hn _ hpairs j).ae_le hgood)
  have hpr : ∀ᵐ v ∂P.laws n, ∀ a b, a ≠ b → (v a, v b) ∈ Reg := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    by_cases hab : a = b
    · exact Eventually.of_forall (fun _ h => (h hab).elim)
    · exact (ae_of_ae_map ((measurable_pi_apply a).prodMk
        (measurable_pi_apply b)).aemeasurable ((hpairs a b hab).ae_le hReg)).mono
          (fun _ h _ => h)
  filter_upwards [hcoord, hpr, P.feasible.2.2.1 n, P.tight_physical n, P.unique_roots n]
    with v hc hr hcl ht hu hroot havoid
  obtain ⟨k, hk⟩ := hroot
  have hnoP : ∀ j, S.ρ (v j) ≠ p.val := by
    intro j hj
    have hjk := hu j k (Or.inr hj) (Or.inl hk)
    subst hjk
    exact P.distinct_roots (Subtype.ext (hk.symm.trans hj))
  have hx : ∀ᵐ x ∂μ.restrict X,
      (∑ j, PhysicalRepresentative.charge W m x (v j)) ≤ 0 := by
    have hall := ae_all_iff.mpr hc
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem hX] with x hxj hxX
    have hadj (j : Fin n) : G (x, v j) = true := (hxj j).2.2 hxX (havoid j) (hnoP j)
    have hcl' : PhysicalCliqueRepresentative.Clique G (Fin.cons x v : Fin (n + 1) → Ω) :=
      cons_pairs (fun z => G z = true) x v
        (fun j => ⟨hadj j, by
          change PhysicalRepresentative.adjacency W m (v j) x = true
          rw [PhysicalRepresentative.adjacency_symm]
          exact hadj j⟩) hcl
    have hreg := cons_pairs (· ∈ Reg) x v (fun j => ⟨(hxj j).1, (hxj j).2.1⟩) hr
    have hle := PhysicalCliqueRepresentative.charge_le_of_pairRegular μ hG hY 3
      (by norm_num) hYb htest (n + 1) _ hcl' hreg
    rw [PhysicalTriangleExposure.charge_cons Y (PhysicalRepresentative.charge_symm W m) v x,
      ht] at hle
    change (∑ j, Y (x, v j)) ≤ 0
    linarith
  have hint (j : Fin n) :
      Integrable (fun x => PhysicalRepresentative.charge W m x (v j)) (μ.restrict X) :=
    Integrable.of_bound ((PhysicalRepresentative.measurable_charge W m).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable 3
      (Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x (v j)))
  rw [← integral_finsetSum _ (fun j _ => hint j)]
  exact integral_nonpos_of_ae hx

end Erdos1017.CappedModel.SelectedHighLowStructure.PrivatePhysicalPrimal

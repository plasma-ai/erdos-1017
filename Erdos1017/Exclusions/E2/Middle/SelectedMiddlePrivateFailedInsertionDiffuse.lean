module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateFailedInsertion

/-!
# Failed insertion of a fresh diffuse point

`diffuseExtraHole` is the set of nonneighbors of a fresh point outside the
second private fiber; the missing row of a point missing the second neighborhood
is that fiber plus this region, and the quantitative failed insertion holds for
such a fresh point (`failed_insertion_diffuse`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  {i p : S.I} {c d : ℝ}

/-- The actual nonneighbors of a fresh point outside the second private
fiber. At an atomic point its own fiber is included. -/
def diffuseExtraHole (S : SelectedHighLowStructure W m) (p : S.I) (x : Ω) : Set Ω :=
  {y | PhysicalRepresentative.adjacency W m x y = false} \ {y | S.ρ y = p.val}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_diffuseExtraHole (S : SelectedHighLowStructure W m)
    (p : S.I) (x : Ω) : MeasurableSet (S.diffuseExtraHole p x) :=
  (((PhysicalRepresentative.measurable_adjacency W m).comp
    (measurable_const.prodMk measurable_id)) (measurableSet_singleton false)).diff
      (S.hfibers p.val p.property).1

/-- Missing the literal second neighborhood makes its whole fiber part
of the fresh point's missing row. The remaining part is exactly the
variable forbidden region. -/
theorem ae_missing_mass_eq_second_add_diffuseExtraHole
    (S : SelectedHighLowStructure W m) (p : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∉ S.rootNeighborhood p →
      μ.real {y | PhysicalRepresentative.adjacency W m x y = false} =
        μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) := by
  filter_upwards [Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_root_adjacency p hW hd hgap))] with x hx hxp
  let M := {y | PhysicalRepresentative.adjacency W m x y = false}
  let Pset := {y | S.ρ y = p.val}
  have hM : MeasurableSet M := ((PhysicalRepresentative.measurable_adjacency W m).comp
    (measurable_const.prodMk measurable_id)) (measurableSet_singleton false)
  have hP : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hsub : Pset ≤ᵐ[μ] M := by
    filter_upwards [hx] with y hy hyp
    have hn : PhysicalRepresentative.adjacency W m y x ≠ true :=
      fun h => hxp ((hy hyp).mp h)
    change PhysicalRepresentative.adjacency W m x y = false
    rw [PhysicalRepresentative.adjacency_symm]
    cases hh : PhysicalRepresentative.adjacency W m y x
    · rfl
    · exact (hn hh).elim
  have hMP : μ.real (M ∩ Pset) = μ.real Pset := by
    apply measureReal_congr
    filter_upwards [hsub] with y hy
    simp only [mem_inter_iff]
    exact propext ⟨And.right, fun h => ⟨hy h, h⟩⟩
  have hdis : Disjoint (M \ Pset) (M ∩ Pset) := disjoint_left.mpr
    (fun _ h1 h2 => h1.2 h2.2)
  have hsplit := measureReal_union (μ := μ) hdis (hM.inter hP)
  rw [sdiff_union_inter, hMP] at hsplit
  change μ.real M = μ.real Pset + μ.real (M \ Pset)
  linarith

/-- The same missing-row identity in the original model's moment kernel. -/
theorem ae_missing_row_eq_second_add_diffuseExtraHole
    (S : SelectedHighLowStructure W m) (p : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∉ S.rootNeighborhood p →
      (∫ y, 1 - adjacencyKernel W x y ∂μ) =
        μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) := by
  filter_upwards [Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support),
    S.ae_missing_mass_eq_second_add_diffuseExtraHole p hW hd hgap]
    with x hx hm hxN
  rw [← hm hxN]
  let M := {y | PhysicalRepresentative.adjacency W m x y = false}
  have hM : MeasurableSet M := ((PhysicalRepresentative.measurable_adjacency W m).comp
    (measurable_const.prodMk measurable_id)) (measurableSet_singleton false)
  have heq : (fun y => 1 - adjacencyKernel W x y) =ᵐ[μ]
      M.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hx] with y hy
    change adjacencyKernel W x y =
      (if PhysicalRepresentative.adjacency W m x y = true then 1 else 0) at hy
    rw [hy]
    cases hb : PhysicalRepresentative.adjacency W m x y <;> simp [M, hb]
  rw [integral_congr_ae heq, integral_indicator hM, setIntegral_const, smul_eq_mul, mul_one]

namespace PrivatePhysicalPrimal

private theorem cons_pairs {α : Type*} {n : ℕ} (Q : α × α → Prop) (x : α) (v : Fin n → α)
    (hx : ∀ j, Q (x, v j) ∧ Q (v j, x)) (hv : ∀ a b, a ≠ b → Q (v a, v b)) :
    ∀ a b : Fin (n + 1), a ≠ b →
      Q ((Fin.cons x v : Fin (n + 1) → α) a, (Fin.cons x v : Fin (n + 1) → α) b) := by
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

/-- A fresh regular point can be inserted into every original tight
parent it joins. Coordinate absolute continuity, rather than absolute
continuity of the parent law, supplies its common exceptional set. -/
private theorem ae_fresh_insertion (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (n : ℕ) :
    ∀ᵐ x ∂μ, ∀ᵐ v ∂P.laws n,
      (∀ j, PhysicalRepresentative.adjacency W m x (v j) = true) →
        (∑ j, PhysicalRepresentative.charge W m x (v j)) ≤ 0 := by
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
    exact Eventually.of_forall (fun _ => Filter.eventually_bot)
  have hdemand : PhysicalPrimal.graphDemand μ
      {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true} ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict
  have hpairs : ∀ a b : Fin n, a ≠ b →
      (P.laws n).map (fun v => (v a, v b)) ≪ μ.prod μ := fun a b hab =>
    (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
      P.feasible.2.2.2 n ⟨(a, b), hab⟩).trans hdemand
  let Reg := {z | PhysicalCliqueRepresentative.PairRegular μ G Y z}
  have hReg : ∀ᵐ z ∂μ.prod μ, z ∈ Reg :=
    PhysicalCliqueRepresentative.ae_pairRegular μ hG hY 3 hYb
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
  have hboth : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (x, y) ∈ Reg ∧ (y, x) ∈ Reg := by
    have h : ∀ᵐ z ∂μ.prod μ, z ∈ Reg ∧ z.swap ∈ Reg := by
      filter_upwards [hReg,
        (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hReg]
        with z h1 h2
      exact ⟨h1, h2⟩
    exact Measure.ae_ae_of_ae_prod h
  filter_upwards [hboth] with x hx
  filter_upwards [P.ae_coordinates n _ hx, hpr, P.feasible.2.2.1 n, P.tight_physical n]
    with v hc hr hcl ht hjoin
  have hcl' : PhysicalCliqueRepresentative.Clique G (Fin.cons x v : Fin (n + 1) → Ω) :=
    cons_pairs (fun z => G z = true) x v
      (fun j => ⟨hjoin j, by
        change PhysicalRepresentative.adjacency W m (v j) x = true
        rw [PhysicalRepresentative.adjacency_symm]
        exact hjoin j⟩) hcl
  have hreg := cons_pairs (· ∈ Reg) x v hc hr
  have hle := PhysicalCliqueRepresentative.charge_le_of_pairRegular μ hG hY 3
    (by norm_num) hYb htest (n + 1) _ hcl' hreg
  rw [PhysicalTriangleExposure.charge_cons Y (PhysicalRepresentative.charge_symm W m) v x,
    ht] at hle
  change (∑ j, Y (x, v j)) ≤ 0
  linarith

/-- Quantitative failed insertion for an actual fresh point missing the
second private root. The forbidden region is its entire extra hole, and
all orders use the same original private primal. Atomic points are also
allowed: their own fiber remains in the forbidden region. -/
theorem failed_insertion_diffuse (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m ≤ 1)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ, S.ρ x ≠ i.val → S.ρ x ≠ p.val → x ∉ S.rootNeighborhood p →
      (μ.real {y | S.ρ y = i.val} ^ 2 -
          (∑ n ∈ Finset.range (P.orderCap + 1), (P.laws n).real (firstRootEvent S i n)) +
          μ.real {y | S.ρ y = i.val} * μ.real (S.diffuseExtraHole p x)) *
          S.rootChargeRow i x ≥
        μ.real {y | S.ρ y = i.val} *
          (2 * (c - m * d) + m + (-m) *
            (μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x))) -
          μ.real {y | S.ρ y = i.val} * μ.real (S.diffuseExtraHole p x) -
          P.positiveRootExcess := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hs := hW.strict_gap_structure hd hgap
  have hroot : ∀ᵐ z ∂μ.prod μ, S.ρ z.2 = i.val →
      PhysicalRepresentative.charge W m z.1 z.2 = S.rootChargeRow i z.1 ∧
      (S.ρ z.1 ≠ i.val → S.ρ z.1 ≠ p.val →
        PhysicalRepresentative.adjacency W m z.1 z.2 = true) := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
    filter_upwards [hswap.ae (S.ae_root_charge i hW hd hgap), hswap.ae hprivate,
      hswap.ae (PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support)]
      with z hy hp hg hi
    refine ⟨?_, ?_⟩
    · rw [PhysicalRepresentative.charge_symm]
      exact hy hi
    · intro hxi hxp
      have he := hp hi
      change adjacencyKernel W z.2 z.1 =
        (if S.ρ z.1 = i.val ∨ S.ρ z.1 = p.val then 0 else 1) at he
      simp only [hxi, hxp, or_self, ↓reduceIte] at he
      change adjacencyKernel W z.2 z.1 =
        (if PhysicalRepresentative.adjacency W m z.2 z.1 = true then 1 else 0) at hg
      cases hb : PhysicalRepresentative.adjacency W m z.2 z.1
      · rw [hb] at hg
        simp only [Bool.false_eq_true, ↓reduceIte] at hg
        exact (by linarith : False).elim
      · rw [PhysicalRepresentative.adjacency_symm]
        exact hb
  have hsecond := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency p hW hd hgap)
  filter_upwards [Measure.ae_ae_of_ae_prod hroot, Measure.ae_ae_of_ae_prod hsecond,
    ae_rootChargeRow_ge S i hW hd hgap hs.multiplier_neg.le,
    S.ae_physical_shifted_stationary hW hd hgap,
    S.ae_missing_mass_eq_second_add_diffuseExtraHole p hW hd hgap,
    ae_all_iff.mpr (fun n => P.ae_fresh_insertion hW hd hgap n)]
    with x hxI hxP hxβ hxstation hmass hins hxi hxp hxN
  let Λ := S.diffuseExtraHole p x
  let β := S.rootChargeRow i x
  let φ := PhysicalRepresentative.charge W m x
  have hΛm : MeasurableSet Λ := S.measurableSet_diffuseExtraHole p x
  have hφm : Measurable φ := (PhysicalRepresentative.measurable_charge W m).comp
    (measurable_const.prodMk measurable_id)
  have hφb (y : Ω) : |φ y| ≤ 3 := PhysicalRepresentative.charge_bound W m x y
  have hφI : ∀ᵐ y ∂μ, S.ρ y = i.val → φ y = β :=
    hxI.mono (fun _ hy hi => (hy hi).1)
  have hrootΛ : ∀ᵐ y ∂μ, S.ρ y = i.val → y ∉ Λ := by
    filter_upwards [hxI] with y hy hi hΛ
    have ht := (hy hi).2 hxi hxp
    have hf := hΛ.1
    change PhysicalRepresentative.adjacency W m x y = false at hf
    rw [ht] at hf
    exact Bool.noConfusion hf
  have hφP : ∀ᵐ y ∂μ, S.ρ y = p.val → φ y = 0 := by
    filter_upwards [hxP] with y hy hyp
    apply PhysicalRepresentative.charge_zero_of_nonedge
    rw [PhysicalRepresentative.adjacency_symm]
    cases hb : PhysicalRepresentative.adjacency W m y x
    · rfl
    · exact (hxN ((hy hyp).mp hb)).elim
  have hφΛ (y : Ω) (hy : y ∈ Λ) : φ y = 0 :=
    PhysicalRepresentative.charge_zero_of_nonedge W m x y hy.1
  have hβ : 0 ≤ 1 + β := by dsimp only [β]; linarith
  have hpoint (n : ℕ) : ∀ᵐ v ∂P.laws n,
      (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v * ∑ k, φ (v k) ≤
        (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}).indicator (fun _ => 1 + β) v +
          (firstRootEvent S i n).indicator (fun _ => max ((n : ℝ) - 3) 0) v := by
    filter_upwards [hins n, P.ae_coordinates n _ hφI, P.ae_coordinates n _ hrootΛ,
      P.unique_roots n] with v hv hI hr hu
    by_cases hE : v ∈ firstRootEvent S i n
    swap
    · have hnot : v ∉ firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ} := fun h => hE h.1
      simp [indicator_of_notMem hE, indicator_of_notMem hnot]
    simp only [indicator_of_mem hE, one_mul]
    obtain ⟨k, hk⟩ := hE
    have hnoP : ∀ l, S.ρ (v l) ≠ p.val := by
      intro l hl
      have he := hu l k (Or.inr hl) (Or.inl hk)
      subst he
      exact P.distinct_roots (Subtype.ext (hk.symm.trans hl))
    by_cases hB : ∃ l, v l ∈ Λ
    · rw [indicator_of_mem (show v ∈ firstRootEvent S i n ∩ {v | ∃ l, v l ∈ Λ}
        from ⟨⟨k, hk⟩, hB⟩)]
      obtain ⟨k0, hk0⟩ := hB
      have hne : k ≠ k0 := by
        rintro rfl
        exact hr k hk hk0
      have hle : ∑ l, φ (v l) ≤
          ∑ l, ((1 : ℝ) + (if l = k then β - 1 else 0) +
            (if l = k0 then -1 else 0)) := by
        apply Finset.sum_le_sum
        intro l _
        by_cases hlk : l = k
        · subst hlk
          simp only [hne, ↓reduceIte, hI l hk]
          linarith
        · by_cases hlk0 : l = k0
          · subst hlk0
            simp only [hlk, ↓reduceIte, hφΛ _ hk0]
            linarith
          · simp only [hlk, hlk0, ↓reduceIte]
            simpa only [add_zero] using (PhysicalRepresentative.charge_mem_Icc W m x (v l)).2
      have hsum : (∑ l : Fin n, ((1 : ℝ) + (if l = k then β - 1 else 0) +
          (if l = k0 then -1 else 0))) = n + (β - 1) - 1 := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
      linarith [le_max_left ((n : ℝ) - 3) 0]
    · rw [indicator_of_notMem (show v ∉ firstRootEvent S i n ∩ {v | ∃ l, v l ∈ Λ}
        from fun h => hB h.2)]
      have hjoin (l : Fin n) : PhysicalRepresentative.adjacency W m x (v l) = true := by
        cases hb : PhysicalRepresentative.adjacency W m x (v l)
        · exact (hB ⟨l, hb, hnoP l⟩).elim
        · rfl
      exact (hv hjoin).trans (by simp only [zero_add]; exact le_max_right _ _)
  have horder (n : ℕ) : (∫ v, (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
      ∑ k, φ (v k) ∂P.laws n) ≤
        (1 + β) * (P.laws n).real (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}) +
          max ((n : ℝ) - 3) 0 * (P.laws n).real (firstRootEvent S i n) := by
    have hE := measurableSet_firstRootEvent S i n
    have hB : MeasurableSet {v : Fin n → Ω | ∃ k, v k ∈ Λ} := by
      have h := MeasurableSet.iUnion (fun k : Fin n => hΛm.preimage (measurable_pi_apply k))
      convert h using 1
      ext v
      simp
    have hsi : Integrable (fun v : Fin n → Ω => ∑ k, φ (v k)) (P.laws n) := by
      apply Integrable.of_bound (Finset.measurable_sum _
        (fun k _ => hφm.comp (measurable_pi_apply k))).aestronglyMeasurable (n * 3 : ℝ)
      exact Eventually.of_forall (fun v => by
        rw [Real.norm_eq_abs]
        calc
          _ ≤ ∑ k, |φ (v k)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun k _ => hφb (v k))
          _ = _ := by simp)
    have hL : Integrable (fun v => (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ∑ k, φ (v k)) (P.laws n) := by
      convert hsi.indicator hE using 1
      funext v
      by_cases hv : v ∈ firstRootEvent S i n <;> simp [hv]
    have h1 : Integrable ((firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}).indicator
        (fun _ => 1 + β)) (P.laws n) := (integrable_const _).indicator (hE.inter hB)
    have h2 : Integrable ((firstRootEvent S i n).indicator
        (fun _ => max ((n : ℝ) - 3) 0)) (P.laws n) := (integrable_const _).indicator hE
    have h := integral_mono_ae hL (h1.add h2) (hpoint n)
    simp only [Pi.add_apply] at h
    rw [integral_add h1 h2, integral_indicator_const _ (hE.inter hB),
      integral_indicator_const _ hE, smul_eq_mul, smul_eq_mul] at h
    simpa only [mul_comm] using h
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (P.orderCap + 1)) => horder n)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hstock := P.first_root_stock φ hφm 3 hφb β hφI hφP
  have hbad := mul_le_mul_of_nonneg_left (P.bad_parent_mass_le Λ hΛm hrootΛ) hβ
  rw [hstock] at hsum
  have hφi : Integrable φ μ := Integrable.of_bound hφm.aestronglyMeasurable 3
    (Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs] using hφb y))
  let G : Ω → ℝ := fun y => if PhysicalRepresentative.adjacency W m x y = true then 1 else 0
  have hGi : Integrable G μ := Integrable.of_bound (Measurable.ite
    (((PhysicalRepresentative.measurable_adjacency W m).comp
      (measurable_const.prodMk measurable_id)) (measurableSet_singleton true))
    measurable_const measurable_const).aestronglyMeasurable 1
      (Eventually.of_forall (fun y => by dsimp only [G]; split_ifs <;> simp))
  have hGint : (∫ y, G y ∂μ) =
      1 - μ.real {y | PhysicalRepresentative.adjacency W m x y = false} := by
    have hM : MeasurableSet {y | PhysicalRepresentative.adjacency W m x y = false} :=
      ((PhysicalRepresentative.measurable_adjacency W m).comp
        (measurable_const.prodMk measurable_id)) (measurableSet_singleton false)
    have heq : G = {y | PhysicalRepresentative.adjacency W m x y = false}ᶜ.indicator
        (fun _ => (1 : ℝ)) := by
      funext y
      cases hb : PhysicalRepresentative.adjacency W m x y <;> simp [G, hb]
    rw [heq, integral_indicator hM.compl, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_compl hM, probReal_univ]
  have hZ : (∫ y, φ y ∂μ) = 2 * (c - m * d) + m + (-m) *
      (μ.real {y | S.ρ y = p.val} + μ.real Λ) := by
    rw [integral_sub hφi (hGi.const_mul m), integral_const_mul, hGint, hmass hxN]
      at hxstation
    change (∫ y, φ y ∂μ) - m *
      (1 - (μ.real {y | S.ρ y = p.val} + μ.real Λ)) = 2 * (c - m * d) at hxstation
    linarith
  rw [hZ] at hsum
  dsimp only [β, Λ] at hsum hbad
  rw [positiveRootExcess]
  nlinarith only [hsum, hbad]

end PrivatePhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure

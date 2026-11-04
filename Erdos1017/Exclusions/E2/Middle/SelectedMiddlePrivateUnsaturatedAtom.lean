module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateUnsaturatedDust
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpMissingCap
public import Erdos1017.Exclusions.E2.Middle.MiddleE2UniversalSmallHeadScalar

/-!
# Parent stock of a second private-type atom

The parents meeting a second private-type whole atom `F` carry at most `a ∫ φ`
of the averaged `F` row (`atom_stock_le`).
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

namespace PrivatePhysicalPrimal

/-- The parents meeting a second private-type whole atom `F` carry at most
`a ∫ φ` of the averaged `F` row: the `F`-root leaves are `a μ|(F ∪ P)ᶜ` and
every `F`-star of a tight parent is nonnegative by deletion feasibility. -/
theorem atom_stock_le (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (f : S.I)
    (hFrow : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = f.val →
      (PhysicalRepresentative.adjacency W m z.1 z.2 = true ↔
        ¬(S.ρ z.2 = f.val ∨ S.ρ z.2 = p.val))) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ((firstRootEvent S f n).indicator (fun _ => (1 : ℝ)) v *
          ∑ j, (∫ x in {x | S.ρ x = f.val}, PhysicalRepresentative.charge W m x (v j) ∂μ))
          ∂P.laws n) ≤
      μ.real {x | S.ρ x = f.val} *
        ∫ y, (∫ x in {x | S.ρ x = f.val}, PhysicalRepresentative.charge W m x y ∂μ) ∂μ := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let F := {x | S.ρ x = f.val}
  let Pset := {x | S.ρ x = p.val}
  have hFm : MeasurableSet F := (S.hfibers f.val f.property).1
  have hPm : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hFpos : 0 < μ F := (S.hfibers f.val f.property).2.1
  let a := μ.real F
  let φ : Ω → ℝ := fun y => ∫ x in F, PhysicalRepresentative.charge W m x y ∂μ
  have hφm : Measurable φ :=
    (PhysicalRepresentative.measurable_charge W m).stronglyMeasurable.integral_prod_left'.measurable
  have hφB (y : Ω) : |φ y| ≤ 3 := by
    have h := norm_integral_le_of_norm_le_const (μ := μ.restrict F)
      (f := fun x => PhysicalRepresentative.charge W m x y) (C := 3)
      (Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
    rw [Real.norm_eq_abs] at h
    have hX1 : (μ.restrict F).real univ ≤ 1 := by
      rw [measureReal_restrict_apply_univ]
      exact measureReal_le_one
    nlinarith
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  -- `φ` vanishes on `F ∪ P` almost everywhere.
  have hφzero : ∀ᵐ y ∂μ, (S.ρ y = f.val ∨ S.ρ y = p.val) → φ y = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod (hswap.ae hFrow)] with y hy hyFP
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hy, ae_restrict_mem hFm] with x hx hxF
    apply PhysicalRepresentative.charge_zero_of_nonedge
    cases hb : PhysicalRepresentative.adjacency W m x y
    · rfl
    · exact False.elim (((hx hxF).mp hb) hyFP)
  -- The `F`-root leaves.
  have hE : MeasurableSet {z : Ω × Ω | PhysicalRepresentative.adjacency W m z.1 z.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hleaves : PhysicalPrimal.rootLeaves P.laws F = μ F • μ.restrict (F ∪ Pset)ᶜ := by
    apply PhysicalPrimal.rootLeaves_graphDemand_homogeneous P.laws μ _ hE P.feasible.2.2.2
      F _ hFm
    have hle : (μ.restrict F).prod μ ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self le_rfl
    filter_upwards [ae_mono hle hFrow,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hFm)] with z hz hzF
    simpa only [mem_ofPred_eq, mem_compl_iff, mem_union, F, Pset] using hz hzF
  have hK : Integrable (fun z : Ω × Ω => if z.1 ∈ F then φ z.2 else 0)
      (PhysicalPrimal.occupation P.laws) := by
    have hKm : Measurable (fun z : Ω × Ω => if z.1 ∈ F then φ z.2 else 0) :=
      Measurable.ite (hFm.preimage measurable_fst) (hφm.comp measurable_snd) measurable_const
    have hKi : Integrable (fun z : Ω × Ω => if z.1 ∈ F then φ z.2 else 0) (μ.prod μ) :=
      Integrable.of_bound hKm.aestronglyMeasurable 3 (Eventually.of_forall (fun z => by
        split_ifs
        · simpa [Real.norm_eq_abs] using hφB z.2
        · simp))
    rw [P.feasible.2.2.2]
    exact hKi.mono_measure Measure.restrict_le_self
  have hstock := PhysicalPrimal.integral_rootLeaves_eq_sum_of_cap P.orderCap P.laws
    (fun n hn => P.capped n (Or.inr hn)) F hFm φ hφm (by convert hK)
  rw [hleaves, integral_smul_measure] at hstock
  have hφi : Integrable φ μ := Integrable.of_bound hφm.aestronglyMeasurable 3
    (Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs] using hφB y))
  have hFP : (∫ y in (F ∪ Pset)ᶜ, φ y ∂μ) = ∫ y, φ y ∂μ := by
    rw [← integral_add_compl (hFm.union hPm) hφi]
    have h0 : (∫ y in F ∪ Pset, φ y ∂μ) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [hφzero] with y hy hyFP
      exact hy hyFP
    rw [h0, zero_add]
  rw [hFP] at hstock
  -- Pairwise and coordinate facts for the parent laws.
  have hcoordZ := ae_coordinates P
  have hrootF := S.ae_root_charge f hW hd hgap
  have hφrow (y : Ω) : φ y = a * S.rootChargeRow f y := by
    simp only [φ, rootChargeRow, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_inv, a, measureReal_def]
    rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_pos hFpos.ne' (measure_ne_top μ _)).ne',
      one_mul]
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
  have hpairgood : ∀ᵐ z ∂μ.prod μ, PhysicalCliqueRepresentative.PairRegular μ G Y z ∧
      (S.ρ z.1 = f.val → φ z.2 = a * PhysicalRepresentative.charge W m z.1 z.2) ∧
      (S.ρ z.1 = f.val → S.ρ z.2 = f.val → G z = false) := by
    filter_upwards [PhysicalCliqueRepresentative.ae_pairRegular μ hG hY 3 hYb, hrootF,
      hFrow] with z hreg hr hrow
    refine ⟨hreg, fun hz => by rw [hφrow, hr hz], fun hz1 hz2 => ?_⟩
    cases hb : G z
    · rfl
    · exact False.elim ((hrow hz1).mp hb (Or.inl hz2))
  have horder (n : ℕ) : (∫ v, (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
      ((firstRootEvent S f n).indicator (fun _ => (1 : ℝ)) v * ∑ j, φ (v j)) ∂P.laws n) ≤
      ∫ v, (PhysicalPrimal.tupleCount F v : ℝ) * (∑ j, φ (v j)) -
        (∑ j, if v j ∈ F then φ (v j) else 0) ∂P.laws n := by
    by_cases hn : 2 ≤ n
    swap
    · have hz : P.laws n = 0 := by
        interval_cases n
        · exact P.feasible.1
        · exact P.feasible.2.1
      simp [hz]
    have hdemand : PhysicalPrimal.graphDemand μ
        {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true} ≪ μ.prod μ :=
      Measure.absolutelyContinuous_restrict
    have hpairs : ∀ a b : Fin n, a ≠ b →
        (P.laws n).map (fun v => (v a, v b)) ≪ μ.prod μ := fun a b hab =>
      (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
        P.feasible.2.2.2 n ⟨(a, b), hab⟩).trans hdemand
    have hpr : ∀ᵐ v ∂P.laws n, ∀ x y : Fin n, x ≠ y →
        PhysicalCliqueRepresentative.PairRegular μ G Y (v x, v y) ∧
        (S.ρ (v x) = f.val → φ (v y) = a * PhysicalRepresentative.charge W m (v x) (v y)) ∧
        (S.ρ (v x) = f.val → S.ρ (v y) = f.val → G (v x, v y) = false) := by
      apply ae_all_iff.mpr
      intro x
      apply ae_all_iff.mpr
      intro y
      by_cases hxy : x = y
      · exact Eventually.of_forall (fun _ h => (h hxy).elim)
      · exact (ae_of_ae_map ((measurable_pi_apply x).prodMk
          (measurable_pi_apply y)).aemeasurable ((hpairs x y hxy).ae_le hpairgood)).mono
            (fun _ h _ => h)
    have hcz := hcoordZ n _ (hφzero.mono (fun y hy hyF => hy (Or.inl hyF)))
    have hmono : ∀ᵐ v ∂P.laws n,
        (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
          ((firstRootEvent S f n).indicator (fun _ => (1 : ℝ)) v * ∑ j, φ (v j)) ≤
        (PhysicalPrimal.tupleCount F v : ℝ) * (∑ j, φ (v j)) -
          (∑ j, if v j ∈ F then φ (v j) else 0) := by
      filter_upwards [hpr, hcz, P.feasible.2.2.1 n, P.tight_physical n] with v hv hz hcl ht
      have hdiag : (∑ j, if v j ∈ F then φ (v j) else 0) = 0 :=
        Finset.sum_eq_zero (fun j _ => by split_ifs with hj; exacts [hz j hj, rfl])
      rw [hdiag, sub_zero]
      by_cases hEF : v ∈ firstRootEvent S f n
      · obtain ⟨j0, hj0⟩ := hEF
        have hcount : PhysicalPrimal.tupleCount F v = 1 := by
          apply PhysicalPrimal.tupleCount_eq_one_of_unique
          refine ⟨j0, hj0, fun k hk => ?_⟩
          by_contra hkj
          have hfalse := (hv k j0 hkj).2.2 hk hj0
          have htrue : G (v k, v j0) = true := hcl k j0 hkj
          rw [hfalse] at htrue
          contradiction
        -- The `F`-star of the tight parent is nonnegative.
        have hstar : 0 ≤ ∑ j, φ (v j) := by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          let σ := Equiv.swap (0 : Fin (k + 1)) j0
          let w : Fin k → Ω := fun l => v (σ l.succ)
          have hsum : (∑ j, φ (v j)) = φ (v j0) + ∑ l, φ (w l) := by
            rw [← Equiv.sum_comp σ, Fin.sum_univ_succ]
            simp [σ, w]
          have hw (l : Fin k) : φ (w l) = a * PhysicalRepresentative.charge W m (v j0) (w l) := by
            have hne : j0 ≠ σ l.succ := by
              intro h
              have : σ l.succ = σ 0 := by simp [σ, ← h]
              exact Fin.succ_ne_zero l (σ.injective this)
            exact (hv j0 (σ l.succ) hne).2.1 hj0
          have hcons : (fun j => v (σ j)) = (Fin.cons (v j0) w : Fin (k + 1) → Ω) := by
            funext j
            cases j using Fin.cases with
            | zero => simp [σ]
            | succ l => rfl
          have hcharge := PhysicalTriangleExposure.charge_comp_equiv Y v σ
          rw [hcons, PhysicalTriangleExposure.charge_cons Y
            (PhysicalRepresentative.charge_symm W m) w (v j0), ht] at hcharge
          have hσne (x y : Fin k) (hxy : x ≠ y) : σ x.succ ≠ σ y.succ := fun h =>
            hxy (Fin.succ_injective _ (σ.injective h))
          have hwcl : PhysicalCliqueRepresentative.Clique G w := fun x y hxy =>
            hcl (σ x.succ) (σ y.succ) (hσne x y hxy)
          have hwreg : ∀ x y, x ≠ y → PhysicalCliqueRepresentative.PairRegular μ G Y (w x, w y) :=
            fun x y hxy => (hv (σ x.succ) (σ y.succ) (hσne x y hxy)).1
          have hwle := PhysicalCliqueRepresentative.charge_le_of_pairRegular μ hG hY 3
            (by norm_num) hYb htest k w hwcl hwreg
          rw [hsum, hz j0 hj0, zero_add]
          simp_rw [hw]
          rw [← Finset.mul_sum]
          have ha0 : 0 ≤ a := measureReal_nonneg
          change 0 ≤ a * ∑ l, Y (v j0, w l)
          exact mul_nonneg ha0 (by linarith)
        rw [indicator_of_mem (show v ∈ firstRootEvent S f n from ⟨j0, hj0⟩), one_mul,
          hcount, Nat.cast_one, one_mul]
        by_cases hEI : v ∈ firstRootEvent S i n
        · rw [indicator_of_mem hEI, one_mul]
        · rw [indicator_of_notMem hEI, zero_mul]
          exact hstar
      · rw [indicator_of_notMem hEF, zero_mul, mul_zero]
        have hcount : PhysicalPrimal.tupleCount F v = 0 := by
          simp only [firstRootEvent, mem_ofPred_eq, not_exists] at hEF
          simp [PhysicalPrimal.tupleCount, F, hEF]
        simp [hcount]
    have hint1 : Integrable (fun v => (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ((firstRootEvent S f n).indicator (fun _ => (1 : ℝ)) v * ∑ j, φ (v j))) (P.laws n) :=
      Integrable.of_bound (Measurable.aestronglyMeasurable
        ((measurable_const.indicator (measurableSet_firstRootEvent S i n)).mul
          ((measurable_const.indicator (measurableSet_firstRootEvent S f n)).mul
            (Finset.measurable_sum _ (fun j _ => hφm.comp (measurable_pi_apply j))))))
        (n * 3) (Eventually.of_forall (fun v => by
          have hs : |∑ j, φ (v j)| ≤ n * 3 := by
            calc
              _ ≤ ∑ j, |φ (v j)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _j : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun j _ => hφB (v j))
              _ = n * 3 := by simp
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have h1 : |(firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v| ≤ 1 := by
            by_cases h : v ∈ firstRootEvent S i n <;> simp [h]
          have h2 : |(firstRootEvent S f n).indicator (fun _ => (1 : ℝ)) v| ≤ 1 := by
            by_cases h : v ∈ firstRootEvent S f n <;> simp [h]
          have h3 := mul_le_mul h2 hs (abs_nonneg _) zero_le_one
          have h4 := mul_le_mul h1 h3 (by positivity) zero_le_one
          linarith))
    have hint2 : Integrable (fun v => (PhysicalPrimal.tupleCount F v : ℝ) * (∑ j, φ (v j)) -
        (∑ j, if v j ∈ F then φ (v j) else 0)) (P.laws n) := by
      refine Integrable.of_bound (Measurable.aestronglyMeasurable ?_) (n * (n * 3) + n * 3)
        (Eventually.of_forall (fun v => ?_))
      · exact ((measurable_from_nat.comp (PhysicalPrimal.measurable_tupleCount F hFm)).mul
          (Finset.measurable_sum _ (fun j _ => hφm.comp (measurable_pi_apply j)))).sub
          (Finset.measurable_sum _ (fun j _ => Measurable.ite
            (hFm.preimage (measurable_pi_apply j)) (hφm.comp (measurable_pi_apply j))
            measurable_const))
      · have hs : |∑ j, φ (v j)| ≤ n * 3 := by
          calc
            _ ≤ ∑ j, |φ (v j)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun j _ => hφB (v j))
            _ = n * 3 := by simp
        have hs' : |∑ j, if v j ∈ F then φ (v j) else 0| ≤ n * 3 := by
          calc
            _ ≤ ∑ j, |if v j ∈ F then φ (v j) else 0| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun j _ => by
                split_ifs
                · exact hφB (v j)
                · simp)
            _ = n * 3 := by simp
        have hc : |(PhysicalPrimal.tupleCount F v : ℝ)| ≤ n := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast PhysicalPrimal.tupleCount_le F v
        rw [Real.norm_eq_abs]
        calc
          _ ≤ |(PhysicalPrimal.tupleCount F v : ℝ) * (∑ j, φ (v j))| +
              |∑ j, if v j ∈ F then φ (v j) else 0| := abs_sub _ _
          _ ≤ n * (n * 3) + n * 3 := by
            rw [abs_mul]
            gcongr
    exact integral_mono_ae hint1 hint2 hmono
  have hstock' : (μ F).toReal • (∫ y, φ y ∂μ) =
      ∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
        (PhysicalPrimal.tupleCount F v : ℝ) * (∑ j, φ (v j)) -
          (∑ j, if v j ∈ F then φ (v j) else 0) ∂P.laws n := by
    rw [hstock]
    exact Finset.sum_congr rfl (fun n _ => integral_congr_ae (Eventually.of_forall
      (fun v => by
        dsimp only
        congr 1
        exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> rfl))))
  calc
    _ ≤ _ := Finset.sum_le_sum (fun n _ => horder n)
    _ = _ := hstock'.symm
    _ = _ := by
      rw [smul_eq_mul, measureReal_def]

end PrivatePhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure

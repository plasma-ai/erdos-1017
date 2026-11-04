module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateUnsaturatedDust

/-!
# Failed insertion of a whole atom into the private parents

The averaged physical row `atomRow`, the extra missing region `atomExtraHole` of
a whole atom and the nonnegative first-root excess `L_I⁺` are defined, and the
failed-insertion inequality is proved for a whole atom `J ∉ {I, P}` missing the
second private root (`failed_insertion_atom`,
`failed_insertion_atom_normalized`).
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

/-- The unnormalized averaged physical row of a whole original atom `J`:
`atomRow j y = ∫_J Y(x,y) dμ(x) = μ(J) Y(ρ_J, y)`. -/
abbrev atomRow (S : SelectedHighLowStructure W m) (j : S.I) (y : Ω) : ℝ :=
  ∫ x in {x | S.ρ x = j.val}, PhysicalRepresentative.charge W m x y ∂μ

/-- The extra missing region `Λ` of a whole atom `J`: its original
nonneighbors outside its own fiber and the second private root. -/
abbrev atomExtraHole (S : SelectedHighLowStructure W m) (j p : S.I) : Set Ω :=
  (S.rootNeighborhood j)ᶜ \ ({x | S.ρ x = j.val} ∪ {x | S.ρ x = p.val})

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurable_atomRow (S : SelectedHighLowStructure W m) (j : S.I) :
    Measurable (S.atomRow j) :=
  (PhysicalRepresentative.measurable_charge W m).stronglyMeasurable.integral_prod_left'.measurable

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integrable_charge_left (y : Ω) (J : Set Ω) :
    Integrable (fun x => PhysicalRepresentative.charge W m x y) (μ.restrict J) :=
  Integrable.of_bound ((PhysicalRepresentative.measurable_charge W m).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable 3
    (Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem atomRow_abs_le (S : SelectedHighLowStructure W m) (j : S.I) (y : Ω) :
    |S.atomRow j y| ≤ 3 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ.restrict {x | S.ρ x = j.val})
    (f := fun x => PhysicalRepresentative.charge W m x y) (C := 3)
    (Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y))
  rw [Real.norm_eq_abs] at h
  have hX1 : (μ.restrict {x | S.ρ x = j.val}).real univ ≤ 1 := by
    rw [measureReal_restrict_apply_univ]
    exact measureReal_le_one
  nlinarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every edge charge is at most one, so the averaged row is at most `μ(J)`. -/
theorem atomRow_le (S : SelectedHighLowStructure W m) (j : S.I) (y : Ω) :
    S.atomRow j y ≤ μ.real {x | S.ρ x = j.val} := by
  have h := integral_mono_ae (integrable_charge_left (W := W) (m := m) y {x | S.ρ x = j.val})
    (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun x => (PhysicalRepresentative.charge_mem_Icc W m x y).2))
  rw [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at h
  exact h

/-- The averaged row vanishes off the original neighborhood of `J`. -/
theorem ae_atomRow_zero (S : SelectedHighLowStructure W m) (j : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, y ∉ S.rootNeighborhood j → S.atomRow j y = 0 := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  filter_upwards [Measure.ae_ae_of_ae_prod (hswap.ae (S.ae_root_adjacency j hW hd hgap))]
    with y hy hyN
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hy, ae_restrict_mem (S.hfibers j.val j.property).1]
    with x hx hxJ
  apply PhysicalRepresentative.charge_zero_of_nonedge
  cases hb : PhysicalRepresentative.adjacency W m x y
  · rfl
  · exact False.elim (hyN ((hx hxJ).mp hb))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_of_fiber_section (S : SelectedHighLowStructure W m) (j : S.I)
    (T : Ω → Prop) (h : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = j.val → T z.2) : ∀ᵐ y ∂μ, T y := by
  obtain ⟨x, hx, hsec⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j.val j.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod h))
  exact hsec.mono (fun _ hy => hy hx)

/-- The private first root lies in the neighborhood of every other whole
atom distinct from both private roots. -/
theorem ae_private_root_mem_atomNeighborhood (S : SelectedHighLowStructure W m)
    (i p j : S.I) (hji : j ≠ i) (hjp : j ≠ p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ y ∂μ, S.ρ y = i.val → y ∈ S.rootNeighborhood j := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  apply S.ae_of_fiber_section j
  filter_upwards [S.ae_root_adjacency j hW hd hgap, hswap.ae (S.ae_root_adjacency i hW hd hgap),
    Measure.quasiMeasurePreserving_fst.ae
      (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate)] with z hJ hI hN hzj hzi
  have hne : S.ρ z.1 ≠ i.val ∧ S.ρ z.1 ≠ p.val :=
    ⟨fun h => hji (Subtype.ext (hzj.symm.trans h)), fun h => hjp (Subtype.ext (hzj.symm.trans h))⟩
  have hadj : PhysicalRepresentative.adjacency W m z.2 z.1 = true := (hI hzi).mpr (hN.mpr hne)
  rw [PhysicalRepresentative.adjacency_symm] at hadj
  exact (hJ hzj).mp hadj

/-- If the whole atom `J` misses the second root, the second root misses `J`. -/
theorem ae_second_root_not_mem_atomNeighborhood (S : SelectedHighLowStructure W m)
    (p j : S.I) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hJP : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∉ S.rootNeighborhood p) :
    ∀ᵐ y ∂μ, S.ρ y = p.val → y ∉ S.rootNeighborhood j := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  apply S.ae_of_fiber_section j
  filter_upwards [S.ae_root_adjacency j hW hd hgap, hswap.ae (S.ae_root_adjacency p hW hd hgap),
    Measure.quasiMeasurePreserving_fst.ae
      ((ae_restrict_iff' (S.hfibers j.val j.property).1).mp hJP)] with z hJ hP hout hzj hzp hzN
  have hadj := (hJ hzj).mpr hzN
  rw [PhysicalRepresentative.adjacency_symm] at hadj
  exact hout hzj ((hP hzp).mp hadj)

/-- A whole original atom is physically independent. -/
theorem ae_atom_independent (S : SelectedHighLowStructure W m) (j : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = j.val → S.ρ z.2 = j.val →
      PhysicalRepresentative.adjacency W m z.1 z.2 = false := by
  filter_upwards [S.ae_root_adjacency j hW hd hgap] with z h h1 h2
  cases hb : PhysicalRepresentative.adjacency W m z.1 z.2
  · rfl
  · exact False.elim (((h h1).mp hb).1 h2)

namespace PrivatePhysicalPrimal

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integrable_indicator_mul {n : ℕ} (τ : Measure (Fin n → Ω)) [IsFiniteMeasure τ]
    (E : Set (Fin n → Ω)) (hE : MeasurableSet E) (g : (Fin n → Ω) → ℝ) (hg : Measurable g)
    (hgi : Integrable g τ) :
    Integrable (fun v => E.indicator (fun _ => (1 : ℝ)) v * g v) τ :=
  hgi.mono ((measurable_const.indicator hE).mul hg).aestronglyMeasurable
    (Eventually.of_forall (fun v => by by_cases hv : v ∈ E <;> simp [hv]))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integrable_row_sum {n : ℕ} (τ : Measure (Fin n → Ω)) [IsFiniteMeasure τ]
    (j : S.I) : Integrable (fun v : Fin n → Ω => ∑ k, S.atomRow j (v k)) τ :=
  integrable_finsetSum _ (fun k _ => Integrable.of_bound
    ((S.measurable_atomRow j).comp (measurable_pi_apply k)).aestronglyMeasurable 3
    (Eventually.of_forall (fun v => by
      simpa [Real.norm_eq_abs] using S.atomRow_abs_le j (v k))))

/-- The first-root parents meeting an arbitrary whole atom `J` carry at most
`μ(J) ∫ atomRow`. The `J`-root leaves are `μ(J) μ|N(J)` by `J`'s own
homogeneous original row, the row vanishes off `N(J)`, and every `J`-star
of a tight parent is nonnegative by deletion feasibility. -/
theorem atom_parent_stock_le (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (j : S.I) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v *
          ∑ k, S.atomRow j (v k)) ∂P.laws n) ≤
      μ.real {x | S.ρ x = j.val} * ∫ y, S.atomRow j y ∂μ := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let F := {x | S.ρ x = j.val}
  let N := S.rootNeighborhood j
  have hFm : MeasurableSet F := (S.hfibers j.val j.property).1
  have hNm : MeasurableSet N := S.measurableSet_rootNeighborhood j
  have hFpos : 0 < μ F := (S.hfibers j.val j.property).2.1
  let a := μ.real F
  let φ : Ω → ℝ := S.atomRow j
  have hφm : Measurable φ := S.measurable_atomRow j
  have hφB (y : Ω) : |φ y| ≤ 3 := S.atomRow_abs_le j y
  have hφzero := S.ae_atomRow_zero j hW hd hgap
  have hzeroF : ∀ᵐ y ∂μ, y ∈ F → φ y = 0 :=
    hφzero.mono (fun y hy hyF => hy (fun hN => hN.1 hyF))
  have hE : MeasurableSet {z : Ω × Ω | PhysicalRepresentative.adjacency W m z.1 z.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hleaves : PhysicalPrimal.rootLeaves P.laws F = μ F • μ.restrict N := by
    apply PhysicalPrimal.rootLeaves_graphDemand_homogeneous P.laws μ _ hE P.feasible.2.2.2
      F _ hFm
    have hle : (μ.restrict F).prod μ ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self le_rfl
    filter_upwards [ae_mono hle (S.ae_root_adjacency j hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hFm)] with z hz hzF
    exact hz hzF
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
  have hNint : (∫ y in N, φ y ∂μ) = ∫ y, φ y ∂μ := by
    rw [← integral_add_compl hNm hφi]
    have h0 : (∫ y in Nᶜ, φ y ∂μ) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [hφzero] with y hy hyN
      exact hy hyN
    rw [h0, add_zero]
  rw [hNint] at hstock
  have hφrow (y : Ω) : φ y = a * S.rootChargeRow j y := by
    simp only [φ, atomRow, rootChargeRow, ProbabilityTheory.cond, integral_smul_measure,
      smul_eq_mul, ENNReal.toReal_inv, a, measureReal_def]
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
      (S.ρ z.1 = j.val → φ z.2 = a * PhysicalRepresentative.charge W m z.1 z.2) ∧
      (S.ρ z.1 = j.val → S.ρ z.2 = j.val → G z = false) := by
    filter_upwards [PhysicalCliqueRepresentative.ae_pairRegular μ hG hY 3 hYb,
      S.ae_root_charge j hW hd hgap, S.ae_atom_independent j hW hd hgap] with z hreg hr hind
    exact ⟨hreg, fun hz => by rw [hφrow, hr hz], hind⟩
  have horder (n : ℕ) : (∫ v, (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
      ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v * ∑ k, φ (v k)) ∂P.laws n) ≤
      ∫ v, (PhysicalPrimal.tupleCount F v : ℝ) * (∑ k, φ (v k)) -
        (∑ k, if v k ∈ F then φ (v k) else 0) ∂P.laws n := by
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
    have hpairs : ∀ x y : Fin n, x ≠ y →
        (P.laws n).map (fun v => (v x, v y)) ≪ μ.prod μ := fun x y hxy =>
      (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
        P.feasible.2.2.2 n ⟨(x, y), hxy⟩).trans hdemand
    have hpr : ∀ᵐ v ∂P.laws n, ∀ x y : Fin n, x ≠ y →
        PhysicalCliqueRepresentative.PairRegular μ G Y (v x, v y) ∧
        (S.ρ (v x) = j.val → φ (v y) = a * PhysicalRepresentative.charge W m (v x) (v y)) ∧
        (S.ρ (v x) = j.val → S.ρ (v y) = j.val → G (v x, v y) = false) := by
      apply ae_all_iff.mpr
      intro x
      apply ae_all_iff.mpr
      intro y
      by_cases hxy : x = y
      · exact Eventually.of_forall (fun _ h => (h hxy).elim)
      · exact (ae_of_ae_map ((measurable_pi_apply x).prodMk
          (measurable_pi_apply y)).aemeasurable ((hpairs x y hxy).ae_le hpairgood)).mono
            (fun _ h _ => h)
    have hcz := ae_coordinates P n _ hzeroF
    have hmono : ∀ᵐ v ∂P.laws n,
        (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
          ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v * ∑ k, φ (v k)) ≤
        (PhysicalPrimal.tupleCount F v : ℝ) * (∑ k, φ (v k)) -
          (∑ k, if v k ∈ F then φ (v k) else 0) := by
      filter_upwards [hpr, hcz, P.feasible.2.2.1 n, P.tight_physical n] with v hv hz hcl ht
      have hdiag : (∑ k, if v k ∈ F then φ (v k) else 0) = 0 :=
        Finset.sum_eq_zero (fun k _ => by split_ifs with hk; exacts [hz k hk, rfl])
      rw [hdiag, sub_zero]
      by_cases hEF : v ∈ firstRootEvent S j n
      · obtain ⟨j0, hj0⟩ := hEF
        have hcount : PhysicalPrimal.tupleCount F v = 1 := by
          apply PhysicalPrimal.tupleCount_eq_one_of_unique
          refine ⟨j0, hj0, fun k hk => ?_⟩
          by_contra hkj
          have hfalse := (hv k j0 hkj).2.2 hk hj0
          have htrue : G (v k, v j0) = true := hcl k j0 hkj
          rw [hfalse] at htrue
          contradiction
        have hstar : 0 ≤ ∑ k, φ (v k) := by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          let σ := Equiv.swap (0 : Fin (k + 1)) j0
          let w : Fin k → Ω := fun l => v (σ l.succ)
          have hsum : (∑ l, φ (v l)) = φ (v j0) + ∑ l, φ (w l) := by
            rw [← Equiv.sum_comp σ, Fin.sum_univ_succ]
            simp [σ, w]
          have hw (l : Fin k) : φ (w l) = a * PhysicalRepresentative.charge W m (v j0) (w l) := by
            have hne : j0 ≠ σ l.succ := by
              intro h
              have : σ l.succ = σ 0 := by simp [σ, ← h]
              exact Fin.succ_ne_zero l (σ.injective this)
            exact (hv j0 (σ l.succ) hne).2.1 hj0
          have hcons : (fun l => v (σ l)) = (Fin.cons (v j0) w : Fin (k + 1) → Ω) := by
            funext l
            cases l using Fin.cases with
            | zero => simp [σ]
            | succ l => rfl
          have hcharge := PhysicalTriangleExposure.charge_comp_equiv Y v σ
          rw [hcons, PhysicalTriangleExposure.charge_cons Y
            (PhysicalRepresentative.charge_symm W m) w (v j0), ht] at hcharge
          have hσne (x y : Fin k) (hxy : x ≠ y) : σ x.succ ≠ σ y.succ := fun h =>
            hxy (Fin.succ_injective _ (σ.injective h))
          have hwcl : PhysicalCliqueRepresentative.Clique G w := fun x y hxy =>
            hcl (σ x.succ) (σ y.succ) (hσne x y hxy)
          have hwreg : ∀ x y, x ≠ y →
              PhysicalCliqueRepresentative.PairRegular μ G Y (w x, w y) :=
            fun x y hxy => (hv (σ x.succ) (σ y.succ) (hσne x y hxy)).1
          have hwle := PhysicalCliqueRepresentative.charge_le_of_pairRegular μ hG hY 3
            (by norm_num) hYb htest k w hwcl hwreg
          rw [hsum, hz j0 hj0, zero_add]
          simp_rw [hw]
          rw [← Finset.mul_sum]
          have ha0 : 0 ≤ a := measureReal_nonneg
          change 0 ≤ a * ∑ l, Y (v j0, w l)
          exact mul_nonneg ha0 (by linarith)
        rw [indicator_of_mem (show v ∈ firstRootEvent S j n from ⟨j0, hj0⟩), one_mul,
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
        ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v * ∑ k, φ (v k))) (P.laws n) :=
      integrable_indicator_mul _ _ (measurableSet_firstRootEvent S i n) _
        ((measurable_const.indicator (measurableSet_firstRootEvent S j n)).mul
          (Finset.measurable_sum _ (fun k _ => hφm.comp (measurable_pi_apply k))))
        (integrable_indicator_mul _ _ (measurableSet_firstRootEvent S j n) _
          (Finset.measurable_sum _ (fun k _ => hφm.comp (measurable_pi_apply k)))
          (integrable_row_sum _ j))
    have hint2 : Integrable (fun v => (PhysicalPrimal.tupleCount F v : ℝ) * (∑ k, φ (v k)) -
        (∑ k, if v k ∈ F then φ (v k) else 0)) (P.laws n) := by
      refine Integrable.of_bound (Measurable.aestronglyMeasurable ?_) (n * (n * 3) + n * 3)
        (Eventually.of_forall (fun v => ?_))
      · exact ((measurable_from_nat.comp (PhysicalPrimal.measurable_tupleCount F hFm)).mul
          (Finset.measurable_sum _ (fun k _ => hφm.comp (measurable_pi_apply k)))).sub
          (Finset.measurable_sum _ (fun k _ => Measurable.ite
            (hFm.preimage (measurable_pi_apply k)) (hφm.comp (measurable_pi_apply k))
            measurable_const))
      · have hs : |∑ k, φ (v k)| ≤ n * 3 := by
          calc
            _ ≤ ∑ k, |φ (v k)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun k _ => hφB (v k))
            _ = n * 3 := by simp
        have hs' : |∑ k, if v k ∈ F then φ (v k) else 0| ≤ n * 3 := by
          calc
            _ ≤ ∑ k, |if v k ∈ F then φ (v k) else 0| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun k _ => by
                split_ifs
                · exact hφB (v k)
                · simp)
            _ = n * 3 := by simp
        have hc : |(PhysicalPrimal.tupleCount F v : ℝ)| ≤ n := by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast PhysicalPrimal.tupleCount_le F v
        rw [Real.norm_eq_abs]
        calc
          _ ≤ |(PhysicalPrimal.tupleCount F v : ℝ) * (∑ k, φ (v k))| +
              |∑ k, if v k ∈ F then φ (v k) else 0| := abs_sub _ _
          _ ≤ n * (n * 3) + n * 3 := by
            rw [abs_mul]
            gcongr
    exact integral_mono_ae hint1 hint2 hmono
  have hstock' : (μ F).toReal • (∫ y, φ y ∂μ) =
      ∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
        (PhysicalPrimal.tupleCount F v : ℝ) * (∑ k, φ (v k)) -
          (∑ k, if v k ∈ F then φ (v k) else 0) ∂P.laws n := by
    rw [hstock]
    exact Finset.sum_congr rfl (fun n _ => integral_congr_ae (Eventually.of_forall
      (fun v => by
        dsimp only
        congr 1
        exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> rfl))))
  calc
    _ ≤ _ := Finset.sum_le_sum (fun n _ => horder n)
    _ = _ := hstock'.symm
    _ = _ := by
      rw [smul_eq_mul, measureReal_def]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- First-root parents meeting a measurable leaf region `Λ` that avoids the
root fiber have total mass at most `A μ(Λ)`: each such parent supplies at
least one actual first-root leaf in `Λ`, and those leaves are exactly
`A μ|(I ∪ P)ᶜ`. All orders of the same original law are counted. -/
theorem bad_parent_mass_le (P : S.PrivatePhysicalPrimal i p c)
    (Λ : Set Ω) (hΛ : MeasurableSet Λ)
    (hroot : ∀ᵐ y ∂μ, S.ρ y = i.val → y ∉ Λ) :
    (∑ n ∈ Finset.range (P.orderCap + 1),
      (P.laws n).real (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ})) ≤
      μ.real {x | S.ρ x = i.val} * μ.real Λ := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let I := {x | S.ρ x = i.val}
  have hn (n : ℕ) : (P.laws n) (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}) ≤
      PhysicalPrimal.orderRootLeaves n (P.laws n) I Λ := by
    have hcoord := ae_coordinates P n _ hroot
    have hsub : ∀ᵐ v ∂P.laws n, v ∈ firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ} →
        v ∈ ⋃ ab : PhysicalPrimal.PairIndex n,
          (fun v : Fin n → Ω => v ab.val.2) ⁻¹' Λ ∩ {v | v ab.val.1 ∈ I} := by
      filter_upwards [hcoord] with v hv hvE
      obtain ⟨⟨k, hk⟩, k0, hk0⟩ := hvE
      have hne : k ≠ k0 := by
        rintro rfl
        exact hv k hk hk0
      exact mem_iUnion.mpr ⟨⟨(k, k0), hne⟩, hk0, hk⟩
    calc
      _ ≤ _ := measure_mono_ae hsub
      _ ≤ _ := measure_iUnion_fintype_le _ _
      _ = _ := by
        rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
        apply Finset.sum_congr rfl
        intro ab _
        rw [Measure.map_apply (measurable_pi_apply _) hΛ,
          Measure.restrict_apply (hΛ.preimage (measurable_pi_apply _))]
  have hsumE : (∑ n ∈ Finset.range (P.orderCap + 1),
      (P.laws n) (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ})) ≤ μ I * μ Λ := by
    calc
      _ ≤ ∑ n ∈ Finset.range (P.orderCap + 1),
          PhysicalPrimal.orderRootLeaves n (P.laws n) I Λ := Finset.sum_le_sum (fun n _ => hn n)
      _ ≤ ∑' n, PhysicalPrimal.orderRootLeaves n (P.laws n) I Λ := ENNReal.sum_le_tsum _
      _ = PhysicalPrimal.rootLeaves P.laws I Λ := by
        rw [PhysicalPrimal.rootLeaves, Measure.sum_apply _ hΛ]
      _ = μ I * μ.restrict ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ Λ := by
        rw [P.leaves_first, Measure.smul_apply, smul_eq_mul]
      _ ≤ μ I * μ Λ := by
        gcongr
        exact Measure.restrict_le_self
  calc
    _ = (∑ n ∈ Finset.range (P.orderCap + 1),
        (P.laws n) (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ})).toReal := by
      rw [ENNReal.toReal_sum (fun n _ => measure_ne_top _ _)]
      rfl
    _ ≤ (μ I * μ Λ).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hsumE
    _ = _ := by
      rw [ENNReal.toReal_mul]
      rfl

/-- The nonnegative first-root excess `L_I⁺ = ∑ (n-3)⁺ m_n` of the same
original private primal. -/
def positiveRootExcess (P : S.PrivatePhysicalPrimal i p c) : ℝ :=
  ∑ n ∈ Finset.range (P.orderCap + 1),
    max ((n : ℝ) - 3) 0 * (P.laws n).real (firstRootEvent S i n)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The order-two correction: `L_I⁺ = L_I + m_2`, where `m_2` is the mass of
order-two first-root parents. With no order-two first-root parent it is `L_I`. -/
theorem positiveRootExcess_eq (P : S.PrivatePhysicalPrimal i p c) :
    P.positiveRootExcess = P.rootExcess + (P.laws 2).real (firstRootEvent S i 2) := by
  rw [P.rootExcess_eq_sum, positiveRootExcess]
  have h2 : 2 ∈ Finset.range (P.orderCap + 1) :=
    Finset.mem_range.mpr (by have := P.orderCap_ge_two; omega)
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single 2]
  · norm_num
  · intro n _ hn2
    by_cases h3 : 3 ≤ n
    · have h3' : (3 : ℝ) ≤ n := by exact_mod_cast h3
      rw [max_eq_left (by linarith)]
      ring
    · have hz : P.laws n = 0 := by
        interval_cases n
        · exact P.feasible.1
        · exact P.feasible.2.1
        · exact absurd rfl hn2
      simp [hz, measureReal_def]
  · intro h
    exact absurd h2 h

/-- Failed insertion for an arbitrary whole atom `J ∉ {I, P}` that
misses the second private root. With `A = μ(I)`, `a = μ(J)`, the extra hole
`Λ = N(J)ᶜ \ (J ∪ P)` of mass `f`, `R = A² - m_I`, the nonnegative excess
`L⁺`, the averaged row `∫ atomRow` and `c_I = ∫_J Y(ρ_I, ·)`,
`(A-a) ∫ atomRow - a A f - a L⁺ ≤ (R + A f) c_I`.
Every parent count, leaf law, insertion and deletion test is the same
original private physical primal; nothing is supplied. -/
theorem failed_insertion_atom (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m ≤ 1)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (j : S.I) (hji : j ≠ i) (hjp : j ≠ p)
    (hJP : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∉ S.rootNeighborhood p) :
    (μ.real {x | S.ρ x = i.val} - μ.real {x | S.ρ x = j.val}) * (∫ y, S.atomRow j y ∂μ) -
        μ.real {x | S.ρ x = j.val} * μ.real {x | S.ρ x = i.val} *
          μ.real (S.atomExtraHole j p) -
        μ.real {x | S.ρ x = j.val} * P.positiveRootExcess ≤
      (μ.real {x | S.ρ x = i.val} ^ 2 -
          (∑ n ∈ Finset.range (P.orderCap + 1), (P.laws n).real (firstRootEvent S i n)) +
          μ.real {x | S.ρ x = i.val} * μ.real (S.atomExtraHole j p)) *
        ∫ x in {x | S.ρ x = j.val}, S.rootChargeRow i x ∂μ := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let J := {x | S.ρ x = j.val}
  let Λ := S.atomExtraHole j p
  let cI := ∫ x in J, S.rootChargeRow i x ∂μ
  let a := μ.real J
  have hJm : MeasurableSet J := (S.hfibers j.val j.property).1
  have hPm : MeasurableSet {x | S.ρ x = p.val} := (S.hfibers p.val p.property).1
  have hΛm : MeasurableSet Λ :=
    (S.measurableSet_rootNeighborhood j).compl.diff (hJm.union hPm)
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hφm := S.measurable_atomRow j
  have hzero := S.ae_atomRow_zero j hW hd hgap
  have hIN := S.ae_private_root_mem_atomNeighborhood i p j hji hjp hW hd hgap hprivate
  have hPN := S.ae_second_root_not_mem_atomNeighborhood p j hW hd hgap hJP
  have hφI : ∀ᵐ y ∂μ, S.ρ y = i.val → S.atomRow j y = cI := by
    filter_upwards [Measure.ae_ae_of_ae_prod (S.ae_root_charge i hW hd hgap)] with y hy hyi
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hy] with x hx
    rw [PhysicalRepresentative.charge_symm]
    exact hx hyi
  have hφP : ∀ᵐ y ∂μ, S.ρ y = p.val → S.atomRow j y = 0 := by
    filter_upwards [hzero, hPN] with y h1 h2 hy
    exact h1 (h2 hy)
  have hφΛ : ∀ᵐ y ∂μ, y ∈ Λ → S.atomRow j y = 0 := by
    filter_upwards [hzero] with y h hy
    exact h hy.1
  have hrootΛ : ∀ᵐ y ∂μ, S.ρ y = i.val → y ∉ Λ := by
    filter_upwards [hIN] with y h hy hyΛ
    exact hyΛ.1 (h hy)
  have hjoin : ∀ᵐ z ∂μ.prod μ, z.1 ∈ J → z.2 ∉ J ∪ Λ → S.ρ z.2 ≠ p.val →
      PhysicalRepresentative.adjacency W m z.1 z.2 = true := by
    filter_upwards [S.ae_root_adjacency j hW hd hgap] with z h hz1 hz2 hz3
    apply (h hz1).mpr
    by_contra hN
    exact hz2 (Or.inr ⟨hN, fun h' => h'.elim (fun h1 => hz2 (Or.inl h1)) hz3⟩)
  -- `c_I ≥ m a ≥ -a`.
  have hmle : m ≤ 0 := (hW.strict_gap_structure hd hgap).multiplier_neg.le
  have hrcI : Integrable (S.rootChargeRow i) μ :=
    Integrable.of_bound (S.measurable_rootChargeRow i).aestronglyMeasurable 3
      (Eventually.of_forall (fun y => by
        have := S.rootChargeRow_mem_Icc i y
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [this.1, this.2]))
  have hcIlo : m * a ≤ cI := by
    have h := setIntegral_mono_ae (μ := μ) (s := J) (f := fun _ => m)
      (integrable_const _).integrableOn hrcI.integrableOn
      (ae_rootChargeRow_ge S i hW hd hgap hmle)
    simpa [setIntegral_const, a, mul_comm] using h
  have haci : 0 ≤ a + cI := by nlinarith [mul_nonneg (show 0 ≤ m + 1 by linarith) ha0]
  -- Pointwise split of every first-root parent.
  have hpoint (n : ℕ) : ∀ᵐ v ∂P.laws n,
      (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v * ∑ k, S.atomRow j (v k) ≤
        (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
            ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v *
              ∑ k, S.atomRow j (v k)) +
          (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}).indicator (fun _ => a + cI) v +
          (firstRootEvent S i n).indicator (fun _ => a * max ((n : ℝ) - 3) 0) v := by
    filter_upwards [P.ae_averaged_insertion hW hd hgap J (J ∪ Λ) hJm hjoin n,
      ae_coordinates P n _ hφI, ae_coordinates P n _ hφΛ,
      ae_coordinates P n _ hrootΛ] with v hins hI hΛ hr
    have hmax : 0 ≤ a * max ((n : ℝ) - 3) 0 := mul_nonneg ha0 (le_max_right _ _)
    by_cases hEI : v ∈ firstRootEvent S i n
    swap
    · have hnot : v ∉ firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ} := fun h => hEI h.1
      simp [indicator_of_notMem hEI, indicator_of_notMem hnot]
    simp only [indicator_of_mem hEI, one_mul]
    by_cases hEJ : v ∈ firstRootEvent S j n
    · rw [indicator_of_mem hEJ, one_mul]
      have h2 : 0 ≤ (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}).indicator
          (fun _ => a + cI) v := indicator_nonneg (fun _ _ => haci) v
      linarith
    rw [indicator_of_notMem hEJ, zero_mul, zero_add]
    by_cases hB : v ∈ {v : Fin n → Ω | ∃ k, v k ∈ Λ}
    · rw [indicator_of_mem (show v ∈ firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ} from ⟨hEI, hB⟩)]
      obtain ⟨k, hk⟩ := hEI
      obtain ⟨k0, hk0⟩ := hB
      have hne : k ≠ k0 := by
        rintro rfl
        exact hr k hk hk0
      have hle : ∑ l, S.atomRow j (v l) ≤
          ∑ l, (a + (if l = k then cI - a else 0) + (if l = k0 then -a else 0)) := by
        apply Finset.sum_le_sum
        intro l _
        by_cases hlk : l = k
        · subst hlk
          simp only [hne, ↓reduceIte, hI l hk]
          linarith
        · by_cases hlk0 : l = k0
          · subst hlk0
            simp only [hlk, ↓reduceIte, hΛ l hk0]
            linarith
          · simp only [hlk, hlk0, ↓reduceIte]
            linarith [S.atomRow_le j (v l)]
      have hsum : ∑ l : Fin n, (a + (if l = k then cI - a else 0) +
          (if l = k0 then -a else 0)) = n * a + (cI - a) + -a := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hm3 := mul_le_mul_of_nonneg_left (le_max_left ((n : ℝ) - 3) 0) ha0
      linarith
    · have hnot : v ∉ firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ} := fun h => hB h.2
      rw [indicator_of_notMem hnot]
      have hins' : ∑ l, S.atomRow j (v l) ≤ 0 :=
        hins hEI (fun l hl => hl.elim (fun h => hEJ ⟨l, h⟩) (fun h => hB ⟨l, h⟩))
      linarith
  -- Integrate each order.
  have hn (n : ℕ) : (∫ v, (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
      ∑ k, S.atomRow j (v k) ∂P.laws n) ≤
      (∫ v, (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
          ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v *
            ∑ k, S.atomRow j (v k)) ∂P.laws n) +
        (P.laws n).real (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}) • (a + cI) +
        (P.laws n).real (firstRootEvent S i n) • (a * max ((n : ℝ) - 3) 0) := by
    have hEI := measurableSet_firstRootEvent S i n
    have hEJ := measurableSet_firstRootEvent S j n
    have hB : MeasurableSet {v : Fin n → Ω | ∃ k, v k ∈ Λ} := by
      have h := MeasurableSet.iUnion (fun k : Fin n => hΛm.preimage (measurable_pi_apply k))
      convert h using 1
      ext v
      simp
    have hsm : Measurable (fun v : Fin n → Ω => ∑ k, S.atomRow j (v k)) :=
      Finset.measurable_sum _ (fun k _ => hφm.comp (measurable_pi_apply k))
    have hT1 : Integrable (fun v => (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v *
          ∑ k, S.atomRow j (v k))) (P.laws n) :=
      integrable_indicator_mul (P.laws n) _ hEI _
        ((measurable_const.indicator hEJ).mul hsm)
        (integrable_indicator_mul (P.laws n) _ hEJ _ hsm (integrable_row_sum _ j))
    have hT2 : Integrable (fun v => (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}).indicator
        (fun _ => a + cI) v) (P.laws n) := (integrable_const _).indicator (hEI.inter hB)
    have hT3 : Integrable (fun v => (firstRootEvent S i n).indicator
        (fun _ => a * max ((n : ℝ) - 3) 0) v) (P.laws n) := (integrable_const _).indicator hEI
    have hT12 : Integrable (fun v => (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ((firstRootEvent S j n).indicator (fun _ => (1 : ℝ)) v *
          ∑ k, S.atomRow j (v k)) +
        (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}).indicator (fun _ => a + cI) v)
        (P.laws n) := hT1.add hT2
    have hL : Integrable (fun v => (firstRootEvent S i n).indicator (fun _ => (1 : ℝ)) v *
        ∑ k, S.atomRow j (v k)) (P.laws n) :=
      integrable_indicator_mul (P.laws n) _ hEI _ hsm (integrable_row_sum _ j)
    have hmono := integral_mono_ae hL (hT12.add hT3) (hpoint n)
    have hsplit := integral_add hT12 hT3
    have hsplit' := integral_add hT1 hT2
    have h2 := integral_indicator_const (μ := P.laws n) (a + cI) (hEI.inter hB)
    have h3 := integral_indicator_const (μ := P.laws n) (a * max ((n : ℝ) - 3) 0) hEI
    simp only [Pi.add_apply] at hmono hsplit hsplit'
    linarith
  have hle := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (P.orderCap + 1)) => hn n)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hle
  have hsumT2 : (∑ n ∈ Finset.range (P.orderCap + 1),
      (P.laws n).real (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}) • (a + cI)) =
      (a + cI) * ∑ n ∈ Finset.range (P.orderCap + 1),
        (P.laws n).real (firstRootEvent S i n ∩ {v | ∃ k, v k ∈ Λ}) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [smul_eq_mul]; ring)
  have hsumT3 : (∑ n ∈ Finset.range (P.orderCap + 1),
      (P.laws n).real (firstRootEvent S i n) • (a * max ((n : ℝ) - 3) 0)) =
      a * P.positiveRootExcess := by
    rw [positiveRootExcess, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [smul_eq_mul]; ring)
  rw [hsumT2, hsumT3] at hle
  have hstock := P.first_root_stock (S.atomRow j) hφm 3 (S.atomRow_abs_le j) cI hφI hφP
  have hatom := P.atom_parent_stock_le hW hd hgap j
  have hbad := P.bad_parent_mass_le Λ hΛm hrootΛ
  have hbad' := mul_le_mul_of_nonneg_left hbad haci
  rw [hstock] at hle
  change _ ≤ (μ.real {x | S.ρ x = i.val} ^ 2 -
      (∑ n ∈ Finset.range (P.orderCap + 1), (P.laws n).real (firstRootEvent S i n)) +
      μ.real {x | S.ρ x = i.val} * μ.real Λ) * cI
  nlinarith [hle, hatom, hbad']

/-- The same failed insertion in normalized symbols: with `β = c_I / a` and
`Z = ∫ atomRow / a`,
`(R + A f) β ≥ (A - a) Z - A f - L⁺`. -/
theorem failed_insertion_atom_normalized (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m ≤ 1)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (j : S.I) (hji : j ≠ i) (hjp : j ≠ p)
    (hJP : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∉ S.rootNeighborhood p) :
    (μ.real {x | S.ρ x = i.val} - μ.real {x | S.ρ x = j.val}) *
          ((∫ y, S.atomRow j y ∂μ) / μ.real {x | S.ρ x = j.val}) -
        μ.real {x | S.ρ x = i.val} * μ.real (S.atomExtraHole j p) - P.positiveRootExcess ≤
      (μ.real {x | S.ρ x = i.val} ^ 2 -
          (∑ n ∈ Finset.range (P.orderCap + 1), (P.laws n).real (firstRootEvent S i n)) +
          μ.real {x | S.ρ x = i.val} * μ.real (S.atomExtraHole j p)) *
        ((∫ x in {x | S.ρ x = j.val}, S.rootChargeRow i x ∂μ) /
          μ.real {x | S.ρ x = j.val}) := by
  have h := P.failed_insertion_atom hW hd hgap hell hprivate j hji hjp hJP
  have ha : 0 < μ.real {x | S.ρ x = j.val} :=
    ENNReal.toReal_pos (S.hfibers j.val j.property).2.1.ne' (measure_ne_top μ _)
  rw [← mul_div_assoc, ← mul_div_assoc, div_sub' ha.ne', div_sub' ha.ne',
    div_le_div_iff_of_pos_right ha]
  linarith

end PrivatePhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure

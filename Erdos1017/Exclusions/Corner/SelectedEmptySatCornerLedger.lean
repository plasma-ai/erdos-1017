module

public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerCancellation
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerCounts

/-!
# Parent ledger of the empty-source saturated corner

The parent ledger integrates the refunded selector and spends the signed pair
demand and partner stock exactly once.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private def privateRestRegion (S : SelectedHighLowStructure W m) (r p : S.I) : Set Ω :=
  (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
    S.reverseCompulsorySource {p})ᶜ

private theorem measurableSet_privateRestRegion
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] (r p : S.I) :
    MeasurableSet (privateRestRegion S r p) :=
  (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).union
    (S.measurableSet_reverseCompulsorySource {p})).compl

private theorem integrable_bounded_parent_sum {n : ℕ}
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (f : Ω → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ x, ‖f x‖ ≤ B) :
    Integrable (fun v => ∑ i, f (v i)) ρ := by
  apply integrable_finsetSum
  intro i _
  exact Integrable.of_bound (hf.comp (measurable_pi_apply i)).aestronglyMeasurable B
    (Eventually.of_forall (fun v => hb (v i)))

private theorem integrable_bounded_parent_charge {n : ℕ}
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (K : Ω × Ω → ℝ)
    (hK : Measurable K) (B : ℝ) (hb : ∀ z, ‖K z‖ ≤ B) :
    Integrable (PhysicalPrimal.charge K) ρ := by
  unfold PhysicalPrimal.charge
  apply Integrable.div_const
  apply integrable_finsetSum
  intro ij _
  exact Integrable.of_bound
    (hK.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))).aestronglyMeasurable B
    (Eventually.of_forall (fun v => hb (v ij.val.1, v ij.val.2)))

omit [MeasurableSpace Ω] in
private theorem indicator_norm_le (E : Set Ω) (f : Ω → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) (x : Ω) : ‖E.indicator f x‖ ≤ B := by
  by_cases hx : x ∈ E
  · simpa only [indicator_of_mem hx] using hb x
  · simp only [indicator_of_notMem hx, norm_zero]
    exact hB

omit [IsProbabilityMeasure μ] in
private theorem physical_charge_integrable (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] :
    Integrable (Function.uncurry (PhysicalRepresentative.charge W m)) ν := by
  apply Integrable.of_bound (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
  exact Eventually.of_forall (fun z => by
    change ‖PhysicalRepresentative.charge W m z.1 z.2‖ ≤ 3
    simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m z.1 z.2)

private theorem measurable_privateStar (p : S.I) : Measurable (S.emptySatPrivateStar p) :=
  (PhysicalRepresentative.measurable_charge W m).stronglyMeasurable.integral_prod_left'.measurable

private theorem privateStar_norm_le (p : S.I) (x : Ω) : ‖S.emptySatPrivateStar p x‖ ≤ 3 := by
  let J := S.reverseCompulsorySource {p}
  have hY : Integrable (fun z => PhysicalRepresentative.charge W m z x) (μ.restrict J) := by
    apply Integrable.of_bound
      ((PhysicalRepresentative.measurable_charge W m).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable 3
    exact Eventually.of_forall (fun z => by
      change ‖PhysicalRepresentative.charge W m z x‖ ≤ 3
      simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m z x)
  calc
    _ ≤ ∫ z in J, ‖PhysicalRepresentative.charge W m z x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ in J, (3 : ℝ) ∂μ := integral_mono_ae hY.norm (integrable_const 3)
      (Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m z x))
    _ ≤ 3 := by
      simp only [setIntegral_const, smul_eq_mul]
      exact mul_le_of_le_one_left (by norm_num) measureReal_le_one

private theorem root_row_norm_le (r : S.I) (x : Ω) : ‖S.rootChargeRow r x‖ ≤ 3 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(S.rootChargeRow_mem_Icc r x).1,
    (S.rootChargeRow_mem_Icc r x).2.trans (by norm_num)⟩

omit [MeasurableSpace Ω] in
private theorem charge_add (K L : Ω × Ω → ℝ) {n : ℕ} (v : Fin n → Ω) :
    PhysicalPrimal.charge (K + L) v =
      PhysicalPrimal.charge K v + PhysicalPrimal.charge L v := by
  simp only [PhysicalPrimal.charge, Pi.add_apply, Finset.sum_add_distrib]
  ring

omit [MeasurableSpace Ω] in
private theorem charge_congr_parent (K L : Ω × Ω → ℝ) {n : ℕ} (v : Fin n → Ω)
    (h : ∀ i j, i ≠ j → K (v i, v j) = L (v i, v j)) :
    PhysicalPrimal.charge K v = PhysicalPrimal.charge L v := by
  unfold PhysicalPrimal.charge
  congr 1
  exact Finset.sum_congr rfl (fun ij _ => h ij.val.1 ij.val.2 ij.property)

omit [MeasurableSpace Ω] in
private theorem charge_flip (K : Ω × Ω → ℝ) {n : ℕ} (v : Fin n → Ω) :
    PhysicalPrimal.charge (K ∘ Prod.swap) v = PhysicalPrimal.charge K v := by
  unfold PhysicalPrimal.charge
  congr 1
  let e : PhysicalPrimal.PairIndex n ≃ PhysicalPrimal.PairIndex n :=
    { toFun := fun ij => ⟨(ij.val.2, ij.val.1), ij.property.symm⟩
      invFun := fun ij => ⟨(ij.val.2, ij.val.1), ij.property.symm⟩
      left_inv := fun ij => by cases ij; rfl
      right_inv := fun ij => by cases ij; rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

omit [MeasurableSpace Ω] in
private theorem one_root_charge (I : Set Ω) (Y : Ω × Ω → ℝ) (f : Ω → ℝ)
    {n : ℕ} (v : Fin n → Ω) (hroot : ∃! i, v i ∈ I)
    (hsym : ∀ x y, Y (x, y) = Y (y, x))
    (hrow : ∀ i j, i ≠ j → v i ∈ I → Y (v i, v j) = f (v j))
    (hzero : ∀ i, v i ∈ I → f (v i) = 0) :
    PhysicalPrimal.charge Y v =
      PhysicalPrimal.charge ((Iᶜ ×ˢ Iᶜ).indicator Y) v + ∑ i, f (v i) := by
  classical
  let K : Ω × Ω → ℝ := fun z => if z.1 ∈ I then f z.2 else 0
  have hpoint : ∀ i j, i ≠ j → Y (v i, v j) =
      (((Iᶜ ×ˢ Iᶜ).indicator Y + K) + K ∘ Prod.swap) (v i, v j) := by
    intro i j hij
    by_cases hi : v i ∈ I
    · have hj : v j ∉ I := by
        intro hj
        obtain ⟨k, _, hk⟩ := hroot
        exact hij ((hk i hi).trans (hk j hj).symm)
      simp [K, hi, hj, hrow i j hij hi]
    · by_cases hj : v j ∈ I
      · simp [K, hi, hj, hsym (v i) (v j), hrow j i hij.symm hj]
      · simp [K, hi, hj]
  have hcharge := charge_congr_parent Y _ v hpoint
  rw [charge_add, charge_add, charge_flip] at hcharge
  have hw := PhysicalPrimal.charge_weighted_root I f v
  have hc : PhysicalPrimal.tupleCount I v = 1 :=
    PhysicalPrimal.tupleCount_eq_one_of_unique I v hroot
  have hd : (∑ i, if v i ∈ I then f (v i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : v i ∈ I <;> simp [hi, hzero i]
  rw [hc, Nat.cast_one, one_mul] at hw
  have hd' : (∑ i, @ite ℝ (v i ∈ I) (Classical.propDecidable _) (f (v i)) 0) = 0 := hd
  rw [hd', sub_zero] at hw
  change 2 * PhysicalPrimal.charge K v = _ at hw
  linarith only [hcharge, hw]

private def privateSourceKernel (S : SelectedHighLowStructure W m) (r p : S.I) :
    Ω × Ω → ℝ :=
  let J := S.reverseCompulsorySource {p}
  let Q := privateRestRegion S r p
  ((J ×ˢ J) ∪ (J ×ˢ Q) ∪ (Q ×ˢ J)).indicator
    (Function.uncurry (PhysicalRepresentative.charge W m))

private theorem measurable_privateSourceKernel
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] (r p : S.I) :
    Measurable (privateSourceKernel S r p) := by
  have hJ := S.measurableSet_reverseCompulsorySource {p}
  have hQ := measurableSet_privateRestRegion (S := S) r p
  exact (PhysicalRepresentative.measurable_charge W m).indicator
    (((hJ.prod hJ).union (hJ.prod hQ)).union (hQ.prod hJ))

private theorem privateSourceKernel_norm_le (r p : S.I) (z : Ω × Ω) :
    ‖privateSourceKernel S r p z‖ ≤ 3 :=
  indicator_norm_le _ _ _ (by norm_num)
    (fun z => by
      simpa only [Real.norm_eq_abs, Function.uncurry] using
        PhysicalRepresentative.charge_bound W m z.1 z.2) z

private theorem outside_charge_decomposition (r p : S.I) {n : ℕ} (v : Fin n → Ω)
    (hheads : ∀ i, S.ρ (v i) ≠ r.val ∧ S.ρ (v i) ≠ p.val) :
    PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v =
      PhysicalPrimal.charge (privateSourceKernel S r p) v +
        S.emptySatPrivateContextCharge r p n v := by
  have hpoint : ∀ i j, i ≠ j → PhysicalRepresentative.charge W m (v i) (v j) =
      (privateSourceKernel S r p +
        ((privateRestRegion S r p) ×ˢ (privateRestRegion S r p)).indicator
          (Function.uncurry (PhysicalRepresentative.charge W m))) (v i, v j) := by
    intro i j _
    by_cases hi : v i ∈ S.reverseCompulsorySource {p} <;>
      by_cases hj : v j ∈ S.reverseCompulsorySource {p} <;>
      simp [privateSourceKernel, privateRestRegion, Set.indicator, hi, hj,
        (hheads i).1, (hheads i).2, (hheads j).1, (hheads j).2]
  have h := charge_congr_parent (Function.uncurry (PhysicalRepresentative.charge W m)) _ v hpoint
  simpa only [charge_add, emptySatPrivateContextCharge, privateRestRegion] using h

omit [MeasurableSpace Ω] in
private theorem outside_kernel_partition (I J Q : Set Ω) (Y : Ω × Ω → ℝ) (x y : Ω)
    (hxJ : x ∈ J → x ∉ I) (hyJ : y ∈ J → y ∉ I)
    (hxQ : x ∈ Q ↔ x ∉ I ∧ x ∉ J) (hyQ : y ∈ Q ↔ y ∉ I ∧ y ∉ J) :
    ((Iᶜ ×ˢ Iᶜ).indicator Y) (x, y) =
      (((J ×ˢ J) ∪ (J ×ˢ Q) ∪ (Q ×ˢ J)).indicator Y) (x, y) +
        ((Q ×ˢ Q).indicator Y) (x, y) := by
  by_cases hi : x ∈ I <;> by_cases hj : y ∈ I <;>
    by_cases hk : x ∈ J <;> by_cases hl : y ∈ J <;>
    simp_all [Set.indicator]

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

private theorem ae_head_rows (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ,
      (S.ρ x = r.val → S.rootChargeRow r x = 0 ∧ S.rootChargeRow p x = 1) ∧
      (S.ρ x = p.val → S.rootChargeRow r x = 1 ∧ S.rootChargeRow p x = 0) := by
  have hI := (S.hfibers r.val r.property).1
  have hP := (S.hfibers p.val p.property).1
  have hrp := (ae_restrict_iff' hP).mp
    (S.ae_rootChargeRow_on_constant_block r p hW hd hgap 1 hpair.2)
  have hpr := (ae_restrict_iff' hI).mp
    (S.ae_rootChargeRow_on_constant_block p r hW hd hgap 1 hpair.symm.2)
  filter_upwards [hrp, hpr, S.rootChargeRow_zero_off_neighborhood r hW hd hgap,
    S.rootChargeRow_zero_off_neighborhood p hW hd hgap] with x hrp hpr hr hp
  exact ⟨fun hx => ⟨hr (fun hy => hy.1 hx), hpr hx⟩,
    fun hx => ⟨hrp hx, hp (fun hy => hy.1 hx)⟩⟩

namespace UniversalPhysicalPrimal

variable {r : S.I} {c : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem integrable_context_functions (r p : S.I) (n : ℕ)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] :
    Integrable (S.emptySatPrivateContextCharge r p n) ρ ∧
      Integrable (S.emptySatPrivateContextStar r p n) ρ ∧
        Integrable (S.emptySatPrivateRootStar r p n) ρ := by
  let Q := privateRestRegion S r p
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  have hQ : MeasurableSet Q := measurableSet_privateRestRegion r p
  have hcharge : Integrable (PhysicalPrimal.charge ((Q ×ˢ Q).indicator Y)) ρ :=
    integrable_bounded_parent_charge ρ _
      ((PhysicalRepresentative.measurable_charge W m).indicator (hQ.prod hQ)) 3
      (indicator_norm_le _ _ _ (by norm_num) (fun z => by
        simpa only [Real.norm_eq_abs, Y, Function.uncurry] using
          PhysicalRepresentative.charge_bound W m z.1 z.2))
  have hstar := integrable_bounded_parent_sum ρ (Q.indicator (S.emptySatPrivateStar p))
    ((measurable_privateStar p).indicator hQ) 3
    (indicator_norm_le _ _ _ (by norm_num) (privateStar_norm_le p))
  have hroot := integrable_bounded_parent_sum ρ (Q.indicator (S.rootChargeRow r))
    ((S.measurable_rootChargeRow r).indicator hQ) 3
    (indicator_norm_le _ _ _ (by norm_num) (root_row_norm_le r))
  exact ⟨hcharge, hstar, hroot⟩

private theorem integrated_selector (R : S.ReverseRecovery) (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    {d : ℝ} (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0)
    (η : PhysicalPrimal.Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (hη : ∀ n, η n ≤ P.laws n) (hcap : ∀ n, P.orderCap < n → η n = 0) :
    S.emptySatPrivateSelectorCharge r p * PhysicalPrimal.cost η +
      S.originalAtomMass r * (∑ n ∈ Finset.range (P.orderCap + 1),
        ∫ v, S.emptySatPrivateContextStar r p n v ∂η n) ≤
      S.emptySatPrivateSelectorRefund r p * (∑ n ∈ Finset.range (P.orderCap + 1),
        ∫ v, 1 - S.emptySatPrivateContextCharge r p n v -
          S.emptySatPrivateRootStar r p n v ∂η n) := by
  have hcost : PhysicalPrimal.cost η =
      ∑ n ∈ Finset.range (P.orderCap + 1), (η n).real univ := by
    rw [PhysicalPrimal.cost, tsum_eq_sum (s := Finset.range (P.orderCap + 1))]
    intro n hn
    have hn' : P.orderCap < n := by simp only [Finset.mem_range] at hn; omega
    simp [hcap n hn']
  have hpoint (n : ℕ) :
      S.emptySatPrivateSelectorCharge r p * (η n).real univ + S.originalAtomMass r *
        (∫ v, S.emptySatPrivateContextStar r p n v ∂η n) ≤
      S.emptySatPrivateSelectorRefund r p * (∫ v,
        1 - S.emptySatPrivateContextCharge r p n v - S.emptySatPrivateRootStar r p n v ∂η n) := by
    obtain ⟨hcharge, hstar, hroot⟩ := integrable_context_functions r p n (η n)
    have hbracket := ((integrable_const (1 : ℝ)).sub hcharge).sub hroot
    have h := integral_mono_ae ((integrable_const (S.emptySatPrivateSelectorCharge r p)).add
      (hstar.const_mul (S.originalAtomMass r)))
      (hbracket.const_mul (S.emptySatPrivateSelectorRefund r p))
      (ae_mono (hη n) (R.ae_emptySat_context_selector_sum r p hr hpair P hW hd hgap hell hnull n))
    change (∫ v, S.emptySatPrivateSelectorCharge r p +
      S.originalAtomMass r * S.emptySatPrivateContextStar r p n v ∂η n) ≤
      ∫ v, S.emptySatPrivateSelectorRefund r p *
        (1 - S.emptySatPrivateContextCharge r p n v - S.emptySatPrivateRootStar r p n v) ∂η n at h
    rw [integral_add (integrable_const _) (hstar.const_mul _), integral_const,
      integral_const_mul, integral_const_mul, smul_eq_mul] at h
    nlinarith only [h]
  have h := Finset.sum_le_sum (s := Finset.range (P.orderCap + 1)) (fun n _ => hpoint n)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← hcost] at h
  exact h

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem parent_integral_partition (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (F : ∀ n, (Fin n → Ω) → ℝ) (hF : ∀ n, Integrable (F n) (P.laws n)) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, F n v ∂P.laws n) =
      (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, F n v ∂P.emptySatRootPartnerLaws p n) +
      (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, F n v ∂P.emptySatRootNoPartnerLaws p n) +
      (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, F n v ∂P.emptySatPartnerLaws p n) +
      (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, F n v ∂P.emptySatHoleLaws p n) +
      (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, F n v ∂P.emptySatCommonLaws p n) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hIP : Integrable (F n) (P.emptySatRootPartnerLaws p n) :=
    (hF n).mono_measure Measure.restrict_le_self
  have hI : Integrable (F n) (P.emptySatRootNoPartnerLaws p n) :=
    (hF n).mono_measure Measure.restrict_le_self
  have hP : Integrable (F n) (P.emptySatPartnerLaws p n) :=
    (hF n).mono_measure Measure.restrict_le_self
  have hH : Integrable (F n) (P.emptySatHoleLaws p n) :=
    (hF n).mono_measure Measure.restrict_le_self
  have hU : Integrable (F n) (P.emptySatCommonLaws p n) :=
    (hF n).mono_measure Measure.restrict_le_self
  have h := congrArg (fun ν : Measure (Fin n → Ω) => ∫ v, F n v ∂ν)
    (P.emptySat_laws_partition p n)
  rw [integral_add_measure (((hIP.add_measure hI).add_measure hP).add_measure hH) hU,
    integral_add_measure ((hIP.add_measure hI).add_measure hP) hH,
    integral_add_measure (hIP.add_measure hI) hP, integral_add_measure hIP hI] at h
  exact h.symm

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem source_kernel_zero {n : ℕ} (r p : S.I) (v : Fin n → Ω)
    (h : ∀ i, v i ∉ S.reverseCompulsorySource {p}) :
    PhysicalPrimal.charge (privateSourceKernel S r p) v = 0 := by
  simp [PhysicalPrimal.charge, privateSourceKernel, h]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem source_kernel_global_inventory (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      PhysicalPrimal.charge (privateSourceKernel S r p) v ∂P.laws n) =
        S.emptySatPrivateCharge p + S.emptySatPrivateRestCharge r p := by
  let J := S.reverseCompulsorySource {p}
  let Q := privateRestRegion S r p
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let E : Set (Ω × Ω) := {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hQ : MeasurableSet Q := measurableSet_privateRestRegion r p
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hK : Integrable (privateSourceKernel S r p) (μ.prod μ) :=
    Integrable.of_bound (measurable_privateSourceKernel r p).aestronglyMeasurable 3
      (Eventually.of_forall (privateSourceKernel_norm_le r p))
  rw [P.emptySat_sum_integral_charge _ hK]
  have hsupport : (∫ z, privateSourceKernel S r p z ∂PhysicalPrimal.graphDemand μ E) =
      ∫ z, privateSourceKernel S r p z ∂μ.prod μ := by
    rw [PhysicalPrimal.graphDemand, ← integral_indicator hE]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      by_cases he : PhysicalRepresentative.adjacency W m z.1 z.2 = true
      · simp [E, he]
      · have hz := PhysicalRepresentative.charge_zero_of_nonedge W m z.1 z.2
          (Bool.eq_false_iff.mpr he)
        simp [E, he, privateSourceKernel, Set.indicator, Function.uncurry, hz])
  rw [hsupport]
  have hdis : Disjoint J Q := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hy (Or.inr hx)
  have hfun : privateSourceKernel S r p =
      ((J ×ˢ J).indicator Y + (J ×ˢ Q).indicator Y) + (Q ×ˢ J).indicator Y := by
    funext z
    have hnotx : z.1 ∈ J → z.1 ∉ Q := fun h => disjoint_left.mp hdis h
    have hnoty : z.2 ∈ J → z.2 ∉ Q := fun h => disjoint_left.mp hdis h
    by_cases hx : z.1 ∈ J <;> by_cases hy : z.2 ∈ J <;>
      by_cases hxQ : z.1 ∈ Q <;> by_cases hyQ : z.2 ∈ Q <;>
      simp_all [privateSourceKernel, J, Q, Y, Set.indicator]
  have hY : Integrable Y (μ.prod μ) := physical_charge_integrable (μ.prod μ)
  have hJJ := hY.indicator (hJ.prod hJ)
  have hJQ := hY.indicator (hJ.prod hQ)
  have hQJ := hY.indicator (hQ.prod hJ)
  have hiJJ : (∫ z, (J ×ˢ J).indicator Y z ∂μ.prod μ) = 2 * S.emptySatPrivateCharge p := by
    rw [integral_indicator (hJ.prod hJ), ← Measure.prod_restrict]
    change (∫ z, Y z ∂(μ.restrict J).prod (μ.restrict J)) =
      2 * ((∫ z, Y z ∂(μ.restrict J).prod (μ.restrict J)) / 2)
    ring
  have hiJQ : (∫ z, (J ×ˢ Q).indicator Y z ∂μ.prod μ) = S.emptySatPrivateRestCharge r p := by
    rw [integral_indicator (hJ.prod hQ), ← Measure.prod_restrict,
      integral_prod_symm Y (physical_charge_integrable _)]
    rfl
  have hiQJ : (∫ z, (Q ×ˢ J).indicator Y z ∂μ.prod μ) = S.emptySatPrivateRestCharge r p := by
    rw [integral_indicator (hQ.prod hJ), ← Measure.prod_restrict]
    calc
      _ = ∫ z, Y z.swap ∂(μ.restrict Q).prod (μ.restrict J) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => PhysicalRepresentative.charge_symm W m z.1 z.2)
      _ = ∫ z, Y z ∂(μ.restrict J).prod (μ.restrict Q) := integral_prod_swap Y
      _ = _ := by rw [integral_prod_symm Y (physical_charge_integrable _)]; rfl
  rw [hfun]
  simp only [Pi.add_apply]
  have hadd := integral_add (hJJ.add hJQ) hQJ
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hJJ hJQ, hiJJ, hiJQ, hiQJ]
  ring

private theorem source_deletion_identity (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    P.emptySatPrivateDeletionSlack p =
      S.emptySatPrivateCharge p + S.emptySatPrivateRestCharge r p -
        ∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
          PhysicalPrimal.charge (privateSourceKernel S r p) v ∂P.emptySatRootNoPartnerLaws p n := by
  have hglobal := P.source_kernel_global_inventory p
  have hpart := P.parent_integral_partition p
    (fun _ => PhysicalPrimal.charge (privateSourceKernel S r p)) (fun n => by
      have := P.finite n
      exact integrable_bounded_parent_charge _ _ (measurable_privateSourceKernel r p) 3
        (privateSourceKernel_norm_le r p))
  have hIP : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      PhysicalPrimal.charge (privateSourceKernel S r p) v ∂P.emptySatRootPartnerLaws p n) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (P.emptySat_source_parent_facts p hpair hW hd hgap hell n),
      ae_restrict_mem (S.measurableSet_emptySatRootPartnerEvent r p n)] with v hs hv
    exact source_kernel_zero r p v (hs.2.2 hv.2)
  have hP : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      PhysicalPrimal.charge (privateSourceKernel S r p) v ∂P.emptySatPartnerLaws p n) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (P.emptySat_source_parent_facts p hpair hW hd hgap hell n),
      ae_restrict_mem (S.measurableSet_emptySatPartnerEvent r p n)] with v hs hv
    exact source_kernel_zero r p v (hs.2.2 hv.2)
  have hU : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      PhysicalPrimal.charge (privateSourceKernel S r p) v ∂P.emptySatCommonLaws p n) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (P.emptySat_source_parent_facts p hpair hW hd hgap hell n),
      ae_restrict_mem (S.measurableSet_emptySatCommonEvent r p n)] with v hs hv
    apply source_kernel_zero r p v
    intro i hi
    exact disjoint_left.mp (S.universalPartner_regions_disjoint r p) (hs.1 i hi) (hv i)
  have hH : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      PhysicalPrimal.charge (privateSourceKernel S r p) v ∂P.emptySatHoleLaws p n) =
      P.emptySatPrivateDeletionSlack p := by
    apply Finset.sum_congr rfl
    intro n _
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (P.tight_physical n),
      ae_restrict_mem (S.measurableSet_emptySatHoleEvent r p n)] with v ht hv
    have h := outside_charge_decomposition r p v hv.1
    rw [ht] at h
    linarith only [h]
  rw [hIP, hP, hU, hH, hglobal] at hpart
  linarith only [hpart]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem rooted_weighted_stock (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (f : Ω → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B)
    (hzero : ∀ᵐ x ∂μ, S.ρ x = r.val → f x = 0) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, (∑ i, f (v i))
        ∂P.emptySatRootNoPartnerLaws p n) +
      (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, (∑ i, f (v i))
        ∂P.emptySatRootPartnerLaws p n) = S.originalAtomMass r * ∫ x, f x ∂μ := by
  classical
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hK : Integrable (fun z : Ω × Ω => if z.1 ∈ I then f z.2 else 0)
      (PhysicalPrimal.occupation P.laws) := by
    rw [P.feasible.2.2.2]
    apply Integrable.of_bound
      (Measurable.ite (hI.preimage measurable_fst) (hf.comp measurable_snd)
        measurable_const).aestronglyMeasurable B
    exact Eventually.of_forall (fun z => by
      split_ifs
      · exact hb z.2
      · simpa only [norm_zero] using hB)
  have hw := PhysicalPrimal.integral_rootLeaves_eq_sum_of_cap P.orderCap P.laws
    (fun n hn => P.capped n (Or.inr hn)) I hI f hf (by
      convert hK using 1
      funext z
      split_ifs <;> rfl)
  have hfull : (∫ x, f x ∂μ.restrict Iᶜ) = ∫ x, f x ∂μ := by
    rw [← integral_indicator hI.compl]
    apply integral_congr_ae
    filter_upwards [hzero] with x hx
    by_cases hi : x ∈ I
    · simpa [hi] using (hx hi).symm
    · simp [hi]
  have hleft : (∫ x, f x ∂PhysicalPrimal.rootLeaves P.laws I) =
      S.originalAtomMass r * ∫ x, f x ∂μ := by
    rw [P.leaves, integral_smul_measure]
    change μ.real I * (∫ x, f x ∂μ.restrict Iᶜ) = _
    rw [hfull]
    rfl
  rw [hleft] at hw
  rw [← Finset.sum_add_distrib, hw]
  apply Finset.sum_congr rfl
  intro n _
  have hint := integrable_bounded_parent_sum (P.laws n) f hf B hb
  rw [emptySatRootNoPartnerLaws, emptySatRootPartnerLaws,
    ← integral_indicator (S.measurableSet_emptySatRootNoPartnerEvent r p n),
    ← integral_indicator (S.measurableSet_emptySatRootPartnerEvent r p n),
    ← integral_add (hint.indicator (S.measurableSet_emptySatRootNoPartnerEvent r p n))
      (hint.indicator (S.measurableSet_emptySatRootPartnerEvent r p n))]
  apply integral_congr_ae
  filter_upwards [P.unique_root n, P.ae_original_vertices _ hzero n] with v huni hz
  have hd : (∑ i, @ite ℝ (v i ∈ I) (Classical.propDecidable _) (f (v i)) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : v i ∈ I
    · simp only [hi, ite_true]
      exact hz i hi
    · simp [hi]
  rw [hd, sub_zero]
  by_cases hr : ∃ i, S.ρ (v i) = r.val
  · have hc : PhysicalPrimal.tupleCount I v = 1 :=
      PhysicalPrimal.tupleCount_eq_one_of_unique I v (by
        obtain ⟨i, hi⟩ := hr
        exact ⟨i, hi, fun j hj => huni j i hj hi⟩)
    by_cases hp : ∃ i, S.ρ (v i) = p.val <;>
      simp [hc, emptySatRootNoPartnerEvent, emptySatRootPartnerEvent, hr, hp]
  · have hc : PhysicalPrimal.tupleCount I v = 0 := by
      simp only [PhysicalPrimal.tupleCount]
      apply Finset.sum_eq_zero
      intro i _
      have hi : v i ∉ I := fun hi => hr ⟨i, hi⟩
      simp [hi]
    simp [hc, emptySatRootNoPartnerEvent, emptySatRootPartnerEvent, hr]

private theorem ae_rootNoPartner_decomposition (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1) (n : ℕ) :
    ∀ᵐ v ∂P.emptySatRootNoPartnerLaws p n,
      1 - S.emptySatPrivateContextCharge r p n v - S.emptySatPrivateRootStar r p n v =
        PhysicalPrimal.charge (privateSourceKernel S r p) v +
          ∑ i, (S.reverseCompulsorySource {p}).indicator (S.rootChargeRow r) (v i) := by
  classical
  let I := {x | S.ρ x = r.val}
  let J := S.reverseCompulsorySource {p}
  let Q := privateRestRegion S r p
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  filter_upwards [ae_restrict_of_ae (P.emptySat_source_parent_facts p hpair hW hd hgap hell n),
    ae_restrict_of_ae (P.ae_original_vertices _ (ae_head_rows r p hpair hW hd hgap) n),
    ae_restrict_of_ae (P.ae_original_pairs _ (S.ae_root_charge r hW hd hgap) n),
    ae_restrict_of_ae (P.unique_root n), ae_restrict_of_ae (P.tight_physical n),
    ae_restrict_mem (S.measurableSet_emptySatRootNoPartnerEvent r p n)]
    with v hsource hheads hrow huni ht hv
  have hroot : ∃! i, v i ∈ I := by
    obtain ⟨i, hi⟩ := hv.1
    exact ⟨i, hi, fun j hj => huni j i hj hi⟩
  have hcharge := one_root_charge I Y (S.rootChargeRow r) v hroot
    (PhysicalRepresentative.charge_symm W m) hrow (fun i hi => ((hheads i).1 hi).1)
  have hQ (i : Fin n) : v i ∈ Q ↔ v i ∉ I ∧ v i ∉ J := by
    change (¬((S.ρ (v i) = r.val ∨ S.ρ (v i) = p.val) ∨ v i ∈ J)) ↔ _
    have hp := hv.2 i
    change _ ↔ S.ρ (v i) ≠ r.val ∧ v i ∉ J
    tauto
  have houtside : PhysicalPrimal.charge ((Iᶜ ×ˢ Iᶜ).indicator Y) v =
      PhysicalPrimal.charge (privateSourceKernel S r p) v +
        S.emptySatPrivateContextCharge r p n v := by
    have hpoint : ∀ i j, i ≠ j → ((Iᶜ ×ˢ Iᶜ).indicator Y) (v i, v j) =
        (privateSourceKernel S r p + (Q ×ˢ Q).indicator Y) (v i, v j) := by
      intro i j _
      exact outside_kernel_partition I J Q Y (v i) (v j)
        (fun h => (hsource.2.1 i h).1) (fun h => (hsource.2.1 j h).1) (hQ i) (hQ j)
    exact (charge_congr_parent _ _ v hpoint).trans (charge_add _ _ v)
  have hsum : (∑ i, S.rootChargeRow r (v i)) = S.emptySatPrivateRootStar r p n v +
      ∑ i, J.indicator (S.rootChargeRow r) (v i) := by
    change _ = (∑ i, Q.indicator (S.rootChargeRow r) (v i)) + _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : v i ∈ I
    · have hn : v i ∉ J := fun hj => (hsource.2.1 i hj).1 hi
      simp [Set.indicator, hQ i, hi, hn, ((hheads i).1 hi).1]
    · by_cases hj : v i ∈ J <;> simp [Set.indicator, hQ i, hi, hj]
  rw [houtside, hsum, ht] at hcharge
  linarith only [hcharge]

private theorem ae_rootPartner_decomposition (P : S.UniversalPhysicalPrimal r c)
    (p : S.I) (hpair : S.IsSaturatedAtomPair r p) {d : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1) (n : ℕ) :
    ∀ᵐ v ∂P.emptySatRootPartnerLaws p n,
      1 - S.emptySatPrivateContextCharge r p n v - S.emptySatPrivateRootStar r p n v =
        ∑ i, S.rootChargeRow p (v i) := by
  classical
  let I := {x | S.ρ x = r.val}
  let B := {x | S.ρ x = p.val}
  let Q := privateRestRegion S r p
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let L := (Iᶜ ×ˢ Iᶜ).indicator Y
  let g := Iᶜ.indicator (S.rootChargeRow p)
  filter_upwards [ae_restrict_of_ae (P.emptySat_source_parent_facts p hpair hW hd hgap hell n),
    ae_restrict_of_ae (P.ae_original_vertices _ (ae_head_rows r p hpair hW hd hgap) n),
    ae_restrict_of_ae (P.ae_original_pairs _ (S.ae_root_charge r hW hd hgap) n),
    ae_restrict_of_ae (P.ae_original_pairs _ (S.ae_root_charge p hW hd hgap) n),
    ae_restrict_of_ae (P.unique_root n),
    ae_restrict_of_ae (P.partner_unique_root p hW hd hgap n),
    ae_restrict_of_ae (P.tight_physical n),
    ae_restrict_mem (S.measurableSet_emptySatRootPartnerEvent r p n)]
    with v hsource hheads hrowI hrowP huniI huniP ht hv
  have hrootI : ∃! i, v i ∈ I := by
    obtain ⟨i, hi⟩ := hv.1
    exact ⟨i, hi, fun j hj => huniI j i hj hi⟩
  have hrootP : ∃! i, v i ∈ B := by
    obtain ⟨i, hi⟩ := hv.2
    exact ⟨i, hi, fun j hj => huniP j i hj hi⟩
  have hnone := hsource.2.2 hv.2
  have hPi (i : Fin n) (hi : v i ∈ B) : v i ∉ I := by
    intro hj
    exact hpair.1 (Subtype.ext (hj.symm.trans hi))
  have hsymL (x y : Ω) : L (x, y) = L (y, x) := by
    by_cases hx : x ∈ I <;> by_cases hy : y ∈ I <;>
      simp [L, hx, hy, Y, PhysicalRepresentative.charge_symm W m x y]
  have hrowL (i j : Fin n) (hij : i ≠ j) (hi : v i ∈ B) : L (v i, v j) = g (v j) := by
    by_cases hj : v j ∈ I <;>
      simp [L, g, Y, Function.uncurry, hj, hPi i hi, hrowP i j hij hi]
  have hzeroL (i : Fin n) (hi : v i ∈ B) : g (v i) = 0 := by
    simp [g, hPi i hi, ((hheads i).2 hi).2]
  have hchargeI := one_root_charge I Y (S.rootChargeRow r) v hrootI
    (PhysicalRepresentative.charge_symm W m) hrowI (fun i hi => ((hheads i).1 hi).1)
  have hchargeP := one_root_charge B L g v hrootP hsymL hrowL hzeroL
  have hctx : PhysicalPrimal.charge ((Bᶜ ×ˢ Bᶜ).indicator L) v =
      S.emptySatPrivateContextCharge r p n v := by
    apply charge_congr_parent
    intro i j _
    by_cases hi : v i ∈ I <;> by_cases hj : v j ∈ I <;>
      by_cases hk : v i ∈ B <;> by_cases hl : v j ∈ B <;>
      simp [L, I, B, Y, Function.uncurry,
        Set.indicator, hi, hj, hk, hl, hnone i, hnone j]
  have hsumI : (∑ i, S.rootChargeRow r (v i)) = S.emptySatPrivateRootStar r p n v + 1 := by
    have hpoint (i : Fin n) : S.rootChargeRow r (v i) =
        Q.indicator (S.rootChargeRow r) (v i) + if v i ∈ B then 1 else 0 := by
      by_cases hi : v i ∈ I <;> by_cases hp : v i ∈ B
      · exact (hPi i hp hi).elim
      · simp [privateRestRegion, Q, I, B, Set.indicator, hi, hp, hnone i,
          ((hheads i).1 hi).1]
      · simp [privateRestRegion, Q, I, B, Set.indicator, hi, hp, hnone i,
          ((hheads i).2 hp).1]
      · simp [privateRestRegion, Q, I, B, Set.indicator, hi, hp, hnone i]
    simp_rw [hpoint, Finset.sum_add_distrib]
    have hc := PhysicalPrimal.tupleCount_eq_one_of_unique B v hrootP
    have he : (∑ i, if v i ∈ B then (1 : ℝ) else 0) = 1 := by
      simpa only [PhysicalPrimal.tupleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero] using congrArg (fun n : ℕ => (n : ℝ)) hc
    rw [he]
    rfl
  have hsumP : (∑ i, g (v i)) = (∑ i, S.rootChargeRow p (v i)) - 1 := by
    have hpoint (i : Fin n) : g (v i) = S.rootChargeRow p (v i) -
        if v i ∈ I then 1 else 0 := by
      by_cases hi : v i ∈ I
      · simp [g, hi, ((hheads i).1 hi).2]
      · simp [g, hi]
    simp_rw [hpoint, Finset.sum_sub_distrib]
    have hc := PhysicalPrimal.tupleCount_eq_one_of_unique I v hrootI
    have he : (∑ i, if v i ∈ I then (1 : ℝ) else 0) = 1 := by
      simpa only [PhysicalPrimal.tupleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero] using congrArg (fun n : ℕ => (n : ℝ)) hc
    rw [he]
  rw [hctx, hsumP] at hchargeP
  rw [hchargeP, hsumI, ht] at hchargeI
  linarith only [hchargeI]

private theorem partner_weighted_stock (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    {d : ℝ} (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, (∑ i, S.rootChargeRow p (v i))
        ∂P.emptySatRootPartnerLaws p n) +
      (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v, (∑ i, S.rootChargeRow p (v i))
        ∂P.emptySatPartnerLaws p n) = S.originalAtomMass p * ∫ x, S.rootChargeRow p x ∂μ := by
  classical
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let B := {x | S.ρ x = p.val}
  let q := S.rootChargeRow p
  have hB : MeasurableSet B := (S.hfibers p.val p.property).1
  have hq : Measurable q := S.measurable_rootChargeRow p
  have hzero : ∀ᵐ x ∂μ, x ∈ B → q x = 0 := by
    filter_upwards [S.rootChargeRow_zero_off_neighborhood p hW hd hgap] with x hx hp
    exact hx (fun hn => hn.1 hp)
  have hK : Integrable (fun z : Ω × Ω => if z.1 ∈ B then q z.2 else 0)
      (PhysicalPrimal.occupation P.laws) := by
    rw [P.feasible.2.2.2]
    apply Integrable.of_bound
      (Measurable.ite (hB.preimage measurable_fst) (hq.comp measurable_snd)
        measurable_const).aestronglyMeasurable 3
    exact Eventually.of_forall (fun z => by
      split_ifs
      · exact root_row_norm_le p z.2
      · simp)
  have hw := PhysicalPrimal.integral_rootLeaves_eq_sum_of_cap P.orderCap P.laws
    (fun n hn => P.capped n (Or.inr hn)) B hB q hq (by
      convert hK using 1
      funext z
      split_ifs <;> rfl)
  have hfull : (∫ x, q x ∂μ.restrict (S.rootNeighborhood p)) = ∫ x, q x ∂μ := by
    rw [← integral_indicator (S.measurableSet_rootNeighborhood p)]
    apply integral_congr_ae
    filter_upwards [S.rootChargeRow_zero_off_neighborhood p hW hd hgap] with x hx
    by_cases hi : x ∈ S.rootNeighborhood p <;> simp [hi, q, hx]
  have hleft : (∫ x, q x ∂PhysicalPrimal.rootLeaves P.laws B) =
      S.originalAtomMass p * ∫ x, q x ∂μ := by
    rw [P.partner_rootLeaves p hW hd hgap, integral_smul_measure, hfull]
    rfl
  rw [hleft] at hw
  change _ = S.originalAtomMass p * ∫ x, q x ∂μ
  rw [← Finset.sum_add_distrib, hw]
  apply Finset.sum_congr rfl
  intro n _
  have hint := integrable_bounded_parent_sum (P.laws n) q hq 3 (root_row_norm_le p)
  rw [emptySatRootPartnerLaws, emptySatPartnerLaws,
    ← integral_indicator (S.measurableSet_emptySatRootPartnerEvent r p n),
    ← integral_indicator (S.measurableSet_emptySatPartnerEvent r p n),
    ← integral_add (hint.indicator (S.measurableSet_emptySatRootPartnerEvent r p n))
      (hint.indicator (S.measurableSet_emptySatPartnerEvent r p n))]
  apply integral_congr_ae
  filter_upwards [P.partner_unique_root p hW hd hgap n, P.ae_original_vertices _ hzero n]
    with v huni hz
  have hd : (∑ i, @ite ℝ (v i ∈ B) (Classical.propDecidable _) (q (v i)) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : v i ∈ B <;> simp [hi, hz i]
  rw [hd, sub_zero]
  by_cases hp : ∃ i, S.ρ (v i) = p.val
  · have hc : PhysicalPrimal.tupleCount B v = 1 :=
      PhysicalPrimal.tupleCount_eq_one_of_unique B v (by
        obtain ⟨i, hi⟩ := hp
        exact ⟨i, hi, fun j hj => huni j i hj hi⟩)
    by_cases hr : ∃ i, S.ρ (v i) = r.val <;>
      simp [hc, emptySatRootPartnerEvent, emptySatPartnerEvent, hr, hp]
  · have hc : PhysicalPrimal.tupleCount B v = 0 := by
      simp only [PhysicalPrimal.tupleCount]
      apply Finset.sum_eq_zero
      intro i _
      have hi : v i ∉ B := fun hi => hp ⟨i, hi⟩
      simp [hi]
    simp [hc, emptySatRootPartnerEvent, emptySatPartnerEvent, hp]

private theorem partner_load_lower (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    P.emptySatPartnerCost p - P.emptySatPartnerSigmaLoad p ≤
      ∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
        (∑ i, S.rootChargeRow p (v i)) ∂P.emptySatPartnerLaws p n := by
  let U := S.universalPartnerCommonRegion r p
  let σ := U.indicator (fun x => -(S.rootChargeRow r x + S.rootChargeRow p x))
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hσ : Measurable σ :=
    ((S.measurable_rootChargeRow r).add (S.measurable_rootChargeRow p)).neg.indicator hU
  have hbound (x : Ω) : ‖σ x‖ ≤ 6 := by
    apply indicator_norm_le _ _ _ (by norm_num) _ x
    intro y
    rw [norm_neg]
    exact (norm_add_le _ _).trans (by linarith only [root_row_norm_le r y, root_row_norm_le p y])
  have hcost : P.emptySatPartnerCost p =
      ∑ n ∈ Finset.range (P.orderCap + 1), (P.emptySatPartnerLaws p n).real univ := by
    rw [emptySatPartnerCost, PhysicalPrimal.cost, tsum_eq_sum (s := Finset.range (P.orderCap + 1))]
    intro n hn
    have hn' : P.orderCap < n := by simp only [Finset.mem_range] at hn; omega
    simp [emptySatPartnerLaws, P.capped n (Or.inr hn')]
  have hpoint (n : ℕ) : (P.emptySatPartnerLaws p n).real univ -
      (∫ v, S.emptySatSigmaLoad r p n v ∂P.emptySatPartnerLaws p n) ≤
      ∫ v, (∑ i, S.rootChargeRow p (v i)) ∂P.emptySatPartnerLaws p n := by
    have hSigma : Integrable (S.emptySatSigmaLoad r p n) (P.emptySatPartnerLaws p n) :=
      integrable_bounded_parent_sum _ σ hσ 6 hbound
    have hq := integrable_bounded_parent_sum (P.emptySatPartnerLaws p n)
      (S.rootChargeRow p) (S.measurable_rootChargeRow p) 3 (root_row_norm_le p)
    have h := integral_mono_ae ((integrable_const (1 : ℝ)).sub hSigma) hq
      ((P.ae_emptySat_partner_charge_load p hpair hW hd hgap hN n).mono (fun _ hv => hv.2))
    change (∫ v, 1 - S.emptySatSigmaLoad r p n v ∂P.emptySatPartnerLaws p n) ≤ _ at h
    rwa [integral_sub (integrable_const _) hSigma, integral_const, smul_eq_mul, mul_one] at h
  have h := Finset.sum_le_sum (s := Finset.range (P.orderCap + 1)) (fun n _ => hpoint n)
  rw [Finset.sum_sub_distrib, ← hcost] at h
  exact h

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem rooted_context_stock (P : S.UniversalPhysicalPrimal r c) (p : S.I) :
    (∑ n ∈ Finset.range (P.orderCap + 1),
      ∫ v, S.emptySatPrivateContextStar r p n v ∂P.emptySatRootNoPartnerLaws p n) +
      (∑ n ∈ Finset.range (P.orderCap + 1),
        ∫ v, S.emptySatPrivateContextStar r p n v ∂P.emptySatRootPartnerLaws p n) =
      S.originalAtomMass r * S.emptySatPrivateRestCharge r p := by
  let Q := privateRestRegion S r p
  have hQ : MeasurableSet Q := measurableSet_privateRestRegion r p
  have h := P.rooted_weighted_stock p (Q.indicator (S.emptySatPrivateStar p))
    ((measurable_privateStar p).indicator hQ) 3 (by norm_num)
    (indicator_norm_le _ _ _ (by norm_num) (privateStar_norm_le p))
    (Eventually.of_forall (fun x hx => by simp [Q, privateRestRegion, hx]))
  rw [integral_indicator hQ] at h
  exact h

private theorem rooted_source_stock (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (∑ i, (S.reverseCompulsorySource {p}).indicator (S.rootChargeRow r) (v i))
        ∂P.emptySatRootNoPartnerLaws p n) =
      S.emptySatPrivateSelectorCharge r p - S.emptySatPrivateCharge p := by
  let J := S.reverseCompulsorySource {p}
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hzero : ∀ᵐ x ∂μ, S.ρ x = r.val → J.indicator (S.rootChargeRow r) x = 0 := by
    filter_upwards [ae_head_rows r p hpair hW hd hgap] with x hx hr
    by_cases hj : x ∈ J <;> simp [hj, (hx.1 hr).1]
  have h := P.rooted_weighted_stock p (J.indicator (S.rootChargeRow r))
    ((S.measurable_rootChargeRow r).indicator hJ) 3 (by norm_num)
    (indicator_norm_le _ _ _ (by norm_num) (root_row_norm_le r)) hzero
  have hIP : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      (∑ i, J.indicator (S.rootChargeRow r) (v i)) ∂P.emptySatRootPartnerLaws p n) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (P.emptySat_source_parent_facts p hpair hW hd hgap hell n),
      ae_restrict_mem (S.measurableSet_emptySatRootPartnerEvent r p n)] with v hs hv
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (hs.2.2 hv.2 i) _
  rw [hIP, add_zero, integral_indicator hJ] at h
  change _ = S.emptySatPrivateCharge p +
    S.originalAtomMass r * (∫ x in J, S.rootChargeRow r x ∂μ) - S.emptySatPrivateCharge p
  linarith only [h]

end UniversalPhysicalPrimal

namespace ReverseRecovery

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem whole_context_cancellation
    {A b K C0 CJ RJ gap DJ T JC IPJ IPq cP SigmaP ZP : ℝ}
    (hK : 0 ≤ K)
    (hroot : (K + gap) * C0 + A * JC ≤ K * (C0 - CJ + T))
    (hrest : JC = A * RJ - IPJ) (hdeletion : DJ = CJ + RJ - T)
    (hpartner : A * b * C0 + A * IPJ ≤ K * IPq)
    (hstock : IPq ≤ b * ZP - cP + SigmaP) :
    gap * C0 + K * (DJ + cP - SigmaP) ≤
      K * b * ZP - A * b * C0 - (A ^ 2 - K) * RJ := by
  have hpaid := mul_le_mul_of_nonneg_left hstock hK
  rw [hrest] at hroot
  rw [hdeletion]
  nlinarith only [hroot, hpartner, hpaid]

private theorem selector_refund_nonneg (R : S.ReverseRecovery) (r p : S.I)
    (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    0 ≤ S.emptySatPrivateSelectorRefund r p := by
  let J := S.reverseCompulsorySource {p}
  let j := μ.real J
  let A := S.originalAtomMass r
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  have hj : 0 ≤ j := measureReal_nonneg
  have hjA : j ≤ A := by
    have h := (R.saturated_empty_source_private_mass r p hpair hr hW hd hgap hell hnull).2
    have hb : 0 ≤ S.originalAtomMass p := measureReal_nonneg
    linarith only [h, hb]
  have hG : Integrable G ((μ.restrict J).prod (μ.restrict J)) := by
    apply Integrable.of_bound
      (PhysicalCliqueRepresentative.measurable_edgeIndicator
        (PhysicalRepresentative.measurable_adjacency W m)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (PhysicalCliqueRepresentative.edgeIndicator_bounds _ z).1]
      exact (PhysicalCliqueRepresentative.edgeIndicator_bounds _ z).2)
  have he := integral_mono_ae hG (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun z => (PhysicalCliqueRepresentative.edgeIndicator_bounds _ z).2))
  have hmass : ((μ.restrict J).prod (μ.restrict J)).real univ = j ^ 2 := by
    rw [← univ_prod_univ, measureReal_prod_prod]
    simp [j, pow_two]
  rw [integral_const, smul_eq_mul, mul_one, hmass] at he
  change 0 ≤ A * j - (∫ z, G z ∂(μ.restrict J).prod (μ.restrict J)) / 2
  nlinarith only [he, mul_nonneg hj (sub_nonneg.mpr hjA), sq_nonneg j]

/-- The actual original parent ledger integrates the refunded selector
and spends the same signed pair demand and partner stock exactly once. -/
theorem empty_sat_corner_context_ledger (R : S.ReverseRecovery) (r p : S.I)
    (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let K := S.emptySatPrivateSelectorRefund r p
    let C0 := S.emptySatPrivateSelectorCharge r p
    let RJ := S.emptySatPrivateRestCharge r p
    let gap := P.emptySatRootNoPartnerCost p - K
    let DJ := P.emptySatPrivateDeletionSlack p
    let ZP := ∫ x, S.rootChargeRow p x ∂μ
    0 ≤ gap ∧ 0 ≤ DJ ∧
      gap * C0 + K * (DJ + P.emptySatPartnerCost p - P.emptySatPartnerSigmaLoad p) ≤
        K * b * ZP - A * b * C0 - (A ^ 2 - K) * RJ := by
  dsimp only
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let K := S.emptySatPrivateSelectorRefund r p
  let C0 := S.emptySatPrivateSelectorCharge r p
  let CJ := S.emptySatPrivateCharge p
  let RJ := S.emptySatPrivateRestCharge r p
  let gap := P.emptySatRootNoPartnerCost p - K
  let DJ := P.emptySatPrivateDeletionSlack p
  let ZP := ∫ x, S.rootChargeRow p x ∂μ
  let T := ∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
    PhysicalPrimal.charge (privateSourceKernel S r p) v ∂P.emptySatRootNoPartnerLaws p n
  let JC := ∑ n ∈ Finset.range (P.orderCap + 1),
    ∫ v, S.emptySatPrivateContextStar r p n v ∂P.emptySatRootNoPartnerLaws p n
  let IPJ := ∑ n ∈ Finset.range (P.orderCap + 1),
    ∫ v, S.emptySatPrivateContextStar r p n v ∂P.emptySatRootPartnerLaws p n
  let IPq := ∑ n ∈ Finset.range (P.orderCap + 1),
    ∫ v, (∑ i, S.rootChargeRow p (v i)) ∂P.emptySatRootPartnerLaws p n
  have hgap0 : 0 ≤ gap := by
    exact sub_nonneg.mpr (P.emptySatRootNoPartnerCost_ge p hpair hW hd hgap hell)
  have hDJ : 0 ≤ DJ := P.emptySatPrivateDeletionSlack_nonneg p hW hd hgap
  refine ⟨hgap0, hDJ, ?_⟩
  have hK : 0 ≤ K := R.selector_refund_nonneg r p hr hpair hW hd hgap hell hnull
  have hsource := P.rooted_source_stock p hpair hW hd hgap hell
  have hbracketI : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      1 - S.emptySatPrivateContextCharge r p n v - S.emptySatPrivateRootStar r p n v
        ∂P.emptySatRootNoPartnerLaws p n) = T + (C0 - CJ) := by
    have he (n : ℕ) : (∫ v, 1 - S.emptySatPrivateContextCharge r p n v -
        S.emptySatPrivateRootStar r p n v ∂P.emptySatRootNoPartnerLaws p n) =
        (∫ v, PhysicalPrimal.charge (privateSourceKernel S r p) v
          ∂P.emptySatRootNoPartnerLaws p n) +
        ∫ v, (∑ i, (S.reverseCompulsorySource {p}).indicator (S.rootChargeRow r) (v i))
          ∂P.emptySatRootNoPartnerLaws p n := by
      rw [integral_congr_ae (P.ae_rootNoPartner_decomposition p hpair hW hd hgap hell n)]
      apply integral_add
      · exact integrable_bounded_parent_charge _ _ (measurable_privateSourceKernel r p) 3
          (privateSourceKernel_norm_le r p)
      · exact integrable_bounded_parent_sum _ _
          ((S.measurable_rootChargeRow r).indicator (S.measurableSet_reverseCompulsorySource {p})) 3
          (indicator_norm_le _ _ _ (by norm_num) (root_row_norm_le r))
    simp_rw [he]
    rw [Finset.sum_add_distrib, hsource]
  have hselectorI := UniversalPhysicalPrimal.integrated_selector R P p hr hpair hW hd hgap
    hell hnull (P.emptySatRootNoPartnerLaws p) (fun _ => Measure.restrict_le_self)
    (fun n hn => P.emptySatRootNoPartnerLaws_capped p n (Or.inr hn))
  rw [hbracketI] at hselectorI
  change C0 * P.emptySatRootNoPartnerCost p + A * JC ≤ K * (T + (C0 - CJ)) at hselectorI
  have hroot : (K + gap) * C0 + A * JC ≤ K * (C0 - CJ + T) := by
    dsimp only [gap]
    nlinarith only [hselectorI]
  have hbracketP : (∑ n ∈ Finset.range (P.orderCap + 1), ∫ v,
      1 - S.emptySatPrivateContextCharge r p n v - S.emptySatPrivateRootStar r p n v
        ∂P.emptySatRootPartnerLaws p n) = IPq := by
    apply Finset.sum_congr rfl
    intro n _
    exact integral_congr_ae (P.ae_rootPartner_decomposition p hpair hW hd hgap hell n)
  have hselectorP := UniversalPhysicalPrimal.integrated_selector R P p hr hpair hW hd hgap
    hell hnull (P.emptySatRootPartnerLaws p) (fun _ => Measure.restrict_le_self)
    (fun n hn => P.emptySatRootPartnerLaws_capped p n (Or.inr hn))
  rw [hbracketP] at hselectorP
  change C0 * P.emptySatRootPartnerCost p + A * IPJ ≤ K * IPq at hselectorP
  rw [P.emptySatRootPartnerCost_eq p hpair.1.symm hW hd hgap] at hselectorP
  have hpartner : A * b * C0 + A * IPJ ≤ K * IPq := by nlinarith only [hselectorP]
  have hrest := P.rooted_context_stock p
  change JC + IPJ = A * RJ at hrest
  have hdeletion := P.source_deletion_identity p hpair hW hd hgap hell
  change DJ = CJ + RJ - T at hdeletion
  have hstock := P.partner_weighted_stock p hW hd hgap
  change IPq + _ = b * ZP at hstock
  have hload := P.partner_load_lower p hpair hW hd hgap
    (R.empty_source_head_neutral r hr hW hd hgap hnull)
  have hstock' : IPq ≤ b * ZP - P.emptySatPartnerCost p + P.emptySatPartnerSigmaLoad p := by
    linarith only [hstock, hload]
  exact whole_context_cancellation hK hroot (by linarith only [hrest]) hdeletion hpartner hstock'

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure

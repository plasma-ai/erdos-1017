module

public import Erdos1017.Exclusions.Common.RootLeafDegreeIncidence
public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePhysicalPrimal
public import Erdos1017.Exclusions.Common.MultipartiteHeadPrice

/-!
# Root incidence of the private primal

Disjoint root sets split the leaf count at each order, strict high root charge
excludes order-two first-root leaves, and the private primal pays three
first-root incidences and one second-root incidence from every exterior event
except its order-three first-root leaves.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Disjoint root sets split the actual leaf count at each parent order. -/
theorem orderRootLeaves_union (n : ℕ) (ρ : Measure (Fin n → Ω))
    (I P : Set Ω) (hP : MeasurableSet P) (hdis : Disjoint I P) :
    orderRootLeaves n ρ (I ∪ P) =
      orderRootLeaves n ρ I + orderRootLeaves n ρ P := by
  classical
  unfold orderRootLeaves
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  have hd : Disjoint {v : Fin n → Ω | v ij.val.1 ∈ I}
      {v : Fin n → Ω | v ij.val.1 ∈ P} := by
    rw [Set.disjoint_left]
    intro v hvI hvP
    exact Set.disjoint_left.mp hdis hvI hvP
  have hm : MeasurableSet {v : Fin n → Ω | v ij.val.1 ∈ P} :=
    hP.preimage (measurable_pi_apply _)
  change (ρ.restrict
      ({v : Fin n → Ω | v ij.val.1 ∈ I} ∪
        {v : Fin n → Ω | v ij.val.1 ∈ P})).map
      (fun v => v ij.val.2) =
      (ρ.restrict {v : Fin n → Ω | v ij.val.1 ∈ I}).map
        (fun v => v ij.val.2) +
      (ρ.restrict {v : Fin n → Ω | v ij.val.1 ∈ P}).map
        (fun v => v ij.val.2)
  rw [Measure.restrict_union hd hm, Measure.map_add _ _ (measurable_pi_apply _)]

/-- The only excess over degree occupation occurs at order three from
the first root. Order-two first-root leaves are assumed absent. -/
theorem three_rootLeaves_add_second_le_degree_add_order_three
    (η : Laws Ω) (I P : Set Ω) (hI : MeasurableSet I)
    (hP : MeasurableSet P) (hdis : Disjoint I P)
    (hunique : ∀ n, ∀ᵐ v ∂η n, ∀ i j,
      v i ∈ I ∪ P → v j ∈ I ∪ P → i = j)
    (hI2 : orderRootLeaves 2 (η 2) I = 0)
    (B : Set Ω) :
    3 * rootLeaves η I B + rootLeaves η P B ≤
      (occupation η).fst B + orderRootLeaves 3 (η 3) I B := by
  have hord (n : ℕ) :
      3 * orderRootLeaves n (η n) I B +
          orderRootLeaves n (η n) P B ≤
        (orderOccupation n (η n)).fst B +
          if n = 3 then orderRootLeaves n (η n) I B else 0 := by
    have hsplit := orderRootLeaves_union n (η n) I P hP hdis
    have hroot := orderRootLeaves_le_orderFirstOccupation n (η n)
      (I ∪ P) (hI.union hP) (hunique n) B
    rw [hsplit] at hroot
    rw [Measure.add_apply] at hroot
    by_cases hn4 : 4 ≤ n
    · have hnum : (3 : ℝ≥0∞) ≤ (n - 1 : ℕ) := by
        exact_mod_cast (show 3 ≤ n - 1 by omega)
      rw [fst_orderOccupation, Measure.smul_apply, nsmul_eq_mul]
      simp only [show n ≠ 3 by omega, ↓reduceIte, add_zero]
      have hP3 : orderRootLeaves n (η n) P B ≤
          3 * orderRootLeaves n (η n) P B := by
        simpa only [one_mul] using
          mul_le_mul_left (show (1 : ℝ≥0∞) ≤ 3 by norm_num)
            (orderRootLeaves n (η n) P B)
      calc
        3 * orderRootLeaves n (η n) I B + orderRootLeaves n (η n) P B ≤
            3 * (orderRootLeaves n (η n) I B +
              orderRootLeaves n (η n) P B) := by
          simp only [mul_add]
          simpa only [add_comm] using
            add_le_add_left hP3 (3 * orderRootLeaves n (η n) I B)
        _ ≤ 3 * orderFirstOccupation n (η n) B :=
          mul_le_mul_right hroot _
        _ ≤ (n - 1 : ℕ) * orderFirstOccupation n (η n) B :=
          mul_le_mul_left hnum _
    · interval_cases n
      · simp [orderRootLeaves, orderOccupation]
      · have he : (Finset.univ : Finset (PairIndex 1)) = ∅ := by
          ext ij
          exact False.elim (ij.property (Subsingleton.elim _ _))
        simp [orderRootLeaves, orderOccupation, he]
      · rw [hI2] at hroot ⊢
        rw [fst_orderOccupation, Measure.smul_apply, nsmul_eq_mul]
        simpa using hroot
      · rw [fst_orderOccupation, Measure.smul_apply, nsmul_eq_mul]
        simp only [↓reduceIte]
        have hP2 : orderRootLeaves 3 (η 3) P B ≤
            2 * orderRootLeaves 3 (η 3) P B := by
          simpa only [one_mul] using
            mul_le_mul_left (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
              (orderRootLeaves 3 (η 3) P B)
        calc
          3 * orderRootLeaves 3 (η 3) I B +
              orderRootLeaves 3 (η 3) P B ≤
              2 * (orderRootLeaves 3 (η 3) I B +
                orderRootLeaves 3 (η 3) P B) +
                orderRootLeaves 3 (η 3) I B := by
              calc
                _ ≤ 3 * orderRootLeaves 3 (η 3) I B +
                    2 * orderRootLeaves 3 (η 3) P B :=
                  by
                    simpa only [add_comm] using
                      add_le_add_left hP2 (3 * orderRootLeaves 3 (η 3) I B)
                _ = _ := by simp only [mul_add]; ring
          _ ≤ 2 * orderFirstOccupation 3 (η 3) B +
                orderRootLeaves 3 (η 3) I B :=
            by
              simpa only [add_comm] using
                add_le_add_right (mul_le_mul_right hroot 2)
                  (orderRootLeaves 3 (η 3) I B)
  rw [rootLeaves, Measure.sum_apply_of_countable,
    rootLeaves, Measure.sum_apply_of_countable,
    occupation, Measure.fst_sum, Measure.sum_apply_of_countable]
  calc
    3 * (∑' n, orderRootLeaves n (η n) I B) +
        ∑' n, orderRootLeaves n (η n) P B =
        ∑' n, (3 * orderRootLeaves n (η n) I B +
          orderRootLeaves n (η n) P B) := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    _ ≤ ∑' n, ((orderOccupation n (η n)).fst B +
        if n = 3 then orderRootLeaves n (η n) I B else 0) :=
      ENNReal.tsum_le_tsum hord
    _ = (∑' n, (orderOccupation n (η n)).fst B) +
        orderRootLeaves 3 (η 3) I B := by
      rw [ENNReal.tsum_add]
      simp

/-- An original missing P-by-K rectangle removes its exact product mass
from the graph-degree budget on every measurable vertex event. -/
theorem graphDemand_degree_add_missing_rectangle_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set (Ω × Ω)) (hE : MeasurableSet E)
    (P K B : Set Ω) (hB : MeasurableSet B)
    (hzero : ∀ᵐ z ∂μ.prod μ, z.1 ∈ K → z.2 ∈ P → z ∉ E) :
    (graphDemand μ E).fst B + μ P * μ (B ∩ K) ≤ μ B := by
  have hle : (μ.prod μ) ((B ∩ K) ×ˢ P) ≤
      (μ.prod μ) (Eᶜ ∩ (B ×ˢ univ)) := by
    apply measure_mono_ae
    filter_upwards [hzero] with z hz hrect
    exact ⟨hz hrect.1.2 hrect.2, ⟨hrect.1.1, trivial⟩⟩
  rw [Measure.prod_prod] at hle
  have hpart := congrArg (fun ν : Measure (Ω × Ω) => ν (B ×ˢ univ))
    (Measure.restrict_add_restrict_compl hE (μ := μ.prod μ))
  rw [Measure.add_apply,
    Measure.restrict_apply (hB.prod MeasurableSet.univ),
    Measure.restrict_apply (hB.prod MeasurableSet.univ),
    Measure.prod_prod] at hpart
  rw [inter_comm (B ×ˢ univ) E, inter_comm (B ×ˢ univ) Eᶜ] at hpart
  have hdegree : (graphDemand μ E).fst B =
      (μ.prod μ) (E ∩ (B ×ˢ univ)) := by
    rw [Measure.fst_apply hB, graphDemand,
      Measure.restrict_apply (measurable_fst hB)]
    congr 1
    ext z
    simp [and_comm]
  rw [hdegree]
  calc
    (μ.prod μ) (E ∩ (B ×ˢ univ)) + μ P * μ (B ∩ K) ≤
        (μ.prod μ) (E ∩ (B ×ˢ univ)) +
          (μ.prod μ) (Eᶜ ∩ (B ×ˢ univ)) := by
      simpa only [mul_comm] using
        add_le_add_right hle ((μ.prod μ) (E ∩ (B ×ˢ univ)))
    _ = μ B := by simpa only [measure_univ, mul_one] using hpart

end Erdos1017.PhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem PrivatePhysicalPrimal.ae_original_pairs
    {S : SelectedHighLowStructure W m} {r u : S.I} {c : ℝ}
    (P : S.PrivatePhysicalPrimal r u c)
    (F : Ω × Ω → Prop) (hF : ∀ᵐ p ∂μ.prod μ, F p) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i j, i ≠ j → F (v i, v j) := by
  apply PhysicalPrimal.ae_all_pairs_of_balance P.laws _ P.feasible.2.2.2 F _ n
  exact Measure.absolutelyContinuous_restrict.ae_le hF

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem PrivatePhysicalPrimal.ae_original_vertices
    {S : SelectedHighLowStructure W m} {r u : S.I} {c : ℝ}
    (P : S.PrivatePhysicalPrimal r u c)
    (F : Ω → Prop) (hF : ∀ᵐ x ∂μ, F x) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i, F (v i) := by
  simp only [ae_all_iff]
  intro i
  have hc := PhysicalPrimal.coordinate_marginal_absolutelyContinuous_of_balance
    P.laws _ P.feasible.1 P.feasible.2.1 P.feasible.2.2.2 n i
  have hd := (PhysicalPrimal.graphDemand_fst_le μ
    {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}).absolutelyContinuous
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable ((hc.trans hd).ae_le hF)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
private theorem orderRootLeaves_eq_zero_of_no_incidence
    {n : ℕ} (ρ : Measure (Fin n → Ω)) (I B : Set Ω) (hB : MeasurableSet B)
    (hno : ∀ᵐ v ∂ρ, ∀ i j, i ≠ j → v i ∈ I → v j ∈ B → False) :
    PhysicalPrimal.orderRootLeaves n ρ I B = 0 := by
  rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ij _
  rw [Measure.map_apply (measurable_pi_apply _) hB,
    Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hno] with v hv hm
  exact hv ij.val.1 ij.val.2 ij.property hm.2 hm.1

/-- Strict original HIGH root charge excludes all actual order-two
first-root leaf incidence; no singular parent law is discarded. -/
theorem PrivatePhysicalPrimal.orderRootLeaves_two_first_eq_zero
    {S : SelectedHighLowStructure W m} {r u : S.I} {c d : ℝ}
    (P : S.PrivatePhysicalPrimal r u c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H) :
    PhysicalPrimal.orderRootLeaves 2 (P.laws 2) {x | S.ρ x = r.val} = 0 := by
  have hslack := P.ae_original_vertices _
    (S.ae_rootChargeRow_lt_one_of_high_fiber r hW hd hgap hell hhigh) 2
  have hrow := P.ae_original_pairs _ (S.ae_root_charge r hW hd hgap) 2
  apply Measure.ext
  intro B hB
  apply orderRootLeaves_eq_zero_of_no_incidence (P.laws 2) _ B hB
  filter_upwards [hslack, hrow, P.tight_physical 2]
    with v hs hr ht i j hij hi _
  have hcharge : PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v =
      PhysicalRepresentative.charge W m (v 0) (v 1) := by
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
      Fin.sum_univ_succ, PhysicalRepresentative.charge_symm W m (v 1) (v 0)]
  have hpair : ∀ a b : Fin 2, a ≠ b →
      PhysicalRepresentative.charge W m (v a) (v b) = 1 := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact False.elim (hab rfl)
    · exact hcharge.symm.trans ht
    · exact (PhysicalRepresentative.charge_symm W m (v 1) (v 0)).trans
        (hcharge.symm.trans ht)
    · exact False.elim (hab rfl)
  have hlt := hs j
  have he := hr i j hij hi
  linarith [hpair i j hij]

/-- The actual private primal pays three first-root incidences and one
second-root incidence from every exterior event, except its order-three
first-root leaves. -/
theorem PrivatePhysicalPrimal.private_root_incidence_bound
    {S : SelectedHighLowStructure W m} {r u : S.I} {c d : ℝ}
    (P : S.PrivatePhysicalPrimal r u c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (B : Set Ω) (hB : MeasurableSet B)
    (hBV : B ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val})ᶜ) :
    (3 * μ.real {x | S.ρ x = r.val} +
        μ.real {x | S.ρ x = u.val} - 1) * μ.real B ≤
      (PhysicalPrimal.orderRootLeaves 3 (P.laws 3)
        {x | S.ρ x = r.val}).real B := by
  let I := {x | S.ρ x = r.val}
  let U := {x | S.ρ x = u.val}
  let V := (I ∪ U)ᶜ
  let N := S.rootNeighborhood u
  let K := V \ N
  let E := {z : Ω × Ω | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hU : MeasurableSet U := (S.hfibers u.val u.property).1
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood u
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hdis : Disjoint I U := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact P.distinct_roots (Subtype.ext (hx.symm.trans hy))
  have hunique (n : ℕ) :
      ∀ᵐ v ∂P.laws n, ∀ a b,
        v a ∈ I ∪ U → v b ∈ I ∪ U → a = b := by
    filter_upwards [P.unique_roots n] with v hv a b ha hb
    exact hv a b ha hb
  have hI2 := P.orderRootLeaves_two_first_eq_zero hW hd hgap hell hhigh
  have hcount := PhysicalPrimal.three_rootLeaves_add_second_le_degree_add_order_three
    P.laws I U hI hU hdis hunique hI2 B
  rw [P.leaves_first, P.leaves_second, P.feasible.2.2.2,
    Measure.smul_apply, Measure.restrict_apply hB,
    Measure.smul_apply, Measure.restrict_apply hB] at hcount
  have hBV' : B ∩ V = B := Set.inter_eq_left.mpr hBV
  rw [hBV'] at hcount
  simp only [smul_eq_mul] at hcount
  have hzero : ∀ᵐ z ∂μ.prod μ, z.1 ∈ K → z.2 ∈ U → z ∉ E := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
    filter_upwards [hswap.ae (S.ae_root_adjacency u hW hd hgap)]
      with z hz hk hu he
    have hrev : PhysicalRepresentative.adjacency W m z.2 z.1 = true := by
      rw [PhysicalRepresentative.adjacency_symm W m z.2 z.1]
      exact he
    exact hk.2 ((hz hu).mp hrev)
  have hdegree := PhysicalPrimal.graphDemand_degree_add_missing_rectangle_le
    μ E hE U K B hB hzero
  have hBK : B ∩ K = B ∩ Nᶜ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff]
    exact and_congr_right (fun hx => and_iff_right (hBV hx))
  have hsplit : μ (B ∩ N) + μ (B ∩ K) = μ B := by
    rw [hBK]
    have hs := congrArg (fun ν : Measure Ω => ν B)
      (Measure.restrict_add_restrict_compl hN (μ := μ))
    simpa only [Measure.add_apply, Measure.restrict_apply hB,
      inter_comm] using hs
  have hraw : 3 * (μ I * μ B) + μ U * μ B ≤
      μ B + PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I B := by
    calc
      3 * (μ I * μ B) + μ U * μ B =
          (3 * (μ I * μ B) + μ U * μ (B ∩ N)) +
            μ U * μ (B ∩ K) := by
          calc
            _ = 3 * (μ I * μ B) +
                μ U * (μ (B ∩ N) + μ (B ∩ K)) := by rw [hsplit]
            _ = _ := by rw [mul_add]; ac_rfl
      _ ≤ ((PhysicalPrimal.graphDemand μ E).fst B +
          PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I B) +
            μ U * μ (B ∩ K) := add_le_add_left hcount _
      _ ≤ μ B + PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I B := by
        calc
          _ = ((PhysicalPrimal.graphDemand μ E).fst B +
              μ U * μ (B ∩ K)) +
                PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I B := by ac_rfl
          _ ≤ μ B + PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I B :=
            add_le_add_left hdegree _
  have : IsFiniteMeasure (P.laws 3) := P.finite 3
  have hfinRoot : PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I B ≠ ⊤ := by
    unfold PhysicalPrimal.orderRootLeaves
    exact measure_ne_top _ B
  have hfin : μ B + PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I B ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨measure_ne_top μ B, hfinRoot⟩
  have hreal := ENNReal.toReal_mono hfin hraw
  have hfinI : μ I ≠ ⊤ := measure_ne_top μ I
  have hfinU : μ U ≠ ⊤ := measure_ne_top μ U
  have hfinB : μ B ≠ ⊤ := measure_ne_top μ B
  have hfinA : 3 * (μ I * μ B) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top hfinI hfinB)
  have hfinUB : μ U * μ B ≠ ⊤ := ENNReal.mul_ne_top hfinU hfinB
  rw [ENNReal.toReal_add hfinA hfinUB,
    ENNReal.toReal_add hfinB hfinRoot] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hreal
  dsimp only [I, U] at hreal ⊢
  change 3 * (μ.real {x | S.ρ x = r.val} * μ.real B) +
      μ.real {x | S.ρ x = u.val} * μ.real B ≤
        μ.real B + (PhysicalPrimal.orderRootLeaves 3 (P.laws 3)
          {x | S.ρ x = r.val}).real B at hreal
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure

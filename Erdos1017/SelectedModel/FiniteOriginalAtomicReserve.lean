module

public import Erdos1017.Exclusions.Common.Flows.FiniteFlowClassMasses
public import Erdos1017.Exclusions.Common.Flows.FiniteDiffuseFlowBudget

/-!
# Paying finitely many low atomic squares

One avoiding full forward trace pays any finite family of original low atomic
squares while retaining the entire countable reserve of the other atoms
(`finite_low_square_reserve`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- One actual avoiding full forward trace pays any finite family of
original LOW atomic squares, retaining the entire countable nonLOW reserve.
Receiver choice, finite redirects, energy cancellation, atomization and both
scalar limits are derived inside the proof. The common-peak cap is the
hypothesis `hcap`; callers derive it from the forward peak. -/
theorem finite_low_square_reserve (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (A : ℝ) (hA : 0 < A)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i)
    (hcap : ∀ (r : Ω × Ω → ℝ), S.IsFullForwardFlow r →
      (∀ᵐ p ∂μ.prod μ, r p ≠ 0 → S.ρ p.1 ≠ i) →
      ∀ k, S.forwardClassMass r k ≤ A)
    {n : ℕ} (j : Fin n → S.I) (hj : Function.Injective j)
    (hjL : ∀ a, ∀ᵐ x ∂μ.restrict {x | S.ρ x = j a}, x ∈ S.L)
    (hjA : ∀ a, S.originalAtomMass (j a) ≤ A) :
    2 * (c - m * d) + m + (-m) *
        ((∑' k, (S.keptAtomMass k) ^ 2) + ∑ a, (S.originalAtomMass (j a)) ^ 2) ≤
      2 * A ^ 2 := by
  let P : Fin n → Set Ω := fun a => {x | S.ρ x = j a}
  let a : Fin n → ℝ := fun v => S.originalAtomMass (j v)
  have hP (v : Fin n) : MeasurableSet (P v) := (S.hfibers (j v) (j v).property).1
  have ha (v : Fin n) : 0 < a v :=
    ENNReal.toReal_pos (S.hfibers (j v) (j v).property).2.1.ne' (measure_ne_top _ _)
  have hPdis : Pairwise (Disjoint on P) := by
    intro v w hvw
    exact Set.disjoint_left.mpr (fun x hx hy => hvw (hj (Subtype.ext (hx.symm.trans hy))))
  have hPL (v : Fin n) : ∀ᵐ y ∂μ, y ∈ P v → y ∈ S.L :=
    (ae_restrict_iff' (hP v)).mp (hjL v)
  obtain ⟨κ, hreceivers⟩ := hq.exists_small_finite_low_receivers hW i j hjL havoid
  let Didx := {v : Fin n // κ v = none}
  let k := Fintype.card Didx
  let e' : Fin k ≃ Didx := (Fintype.equivFin Didx).symm
  let e : Fin k → Fin n := fun v => (e' v).val
  have he : Function.Injective e := fun _ _ h => e'.injective (Subtype.ext h)
  have heD (v : Fin k) : κ (e v) = none := (e' v).property
  have hsumD (f : Fin n → ℝ) : (∑ v : Fin k, f (e v)) =
      ∑ v : Fin n, if κ v = none then f v else 0 := by
    calc
      _ = ∑ v : Didx, f v.val := e'.sum_comp (fun v => f v.val)
      _ = ∑ v : Fin n, if κ v = none then f v else 0 := by
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (by simp) f).symm
  have hm : m < 0 := (hW.strict_gap_structure hd hgap).multiplier_neg
  have htbound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      2 * (c - m * d) + m + (-m) *
        ((∑' z, (S.keptAtomMass z) ^ 2) +
          ∑ v, if κ v = none then (t * a v) ^ 2 else (a v) ^ 2) ≤ 2 * A ^ 2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let K := 8 * A * ((k : ℝ) + 1)
    have hK : 0 < K := by dsimp only [K]; positivity
    let δ := min (ε / K) ((1 - t) * A / 2)
    have hδ : 0 < δ := lt_min (div_pos hε hK)
      (div_pos (mul_pos (sub_pos.mpr ht.2) hA) (by norm_num))
    have hδK : K * δ ≤ ε := by
      have hle : δ ≤ ε / K := min_le_left _ _
      have h := (le_div_iff₀ hK).mp hle
      nlinarith
    have hδA : δ ≤ (1 - t) * A / 2 := min_le_right _ _
    obtain ⟨C, hC, hCp, hCdis, hsmall, hCH, hCi, hCD, hCI, hrect⟩ := hreceivers δ hδ
    let θ : Fin n → ℝ := fun v => if κ v = none then t else 1
    have hθ (v : Fin n) : θ v ∈ Icc (0 : ℝ) 1 := by
      dsimp only [θ]
      split_ifs
      · exact ⟨ht.1.le, ht.2.le⟩
      · exact ⟨zero_le_one, le_rfl⟩
    let r := MissingFlow.finiteRedirect μ q C P θ
    have hr : S.IsFullForwardFlow r :=
      hq.finiteRedirect C P hC hP hCp hPdis θ hθ hPL hrect
    have hrAvoid := hq.finiteRedirect_avoids C P θ i havoid hCi
    have hclasses := hcap r hr hrAvoid
    have hκ : ∀ v z, κ v = some z → θ v = 1 ∧ C v ⊆ {x | S.ρ x = z} ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = z}, x ∈ S.H) := by
      intro v z hv
      obtain ⟨_, hsub, hzH⟩ := hCI v z hv
      refine ⟨?_, hsub, hzH⟩
      simp only [θ, hv, reduceCtorEq, ↓reduceIte]
    have hreserve := hq.finite_endpoint_square_reserve C P hC hP hCp θ hPdis hθ hr κ hκ
    let β : Fin k → ℝ := fun v => (missingFlowEndpointLaw μ r).real (C (e v))
    let η : Fin k → ℝ := fun v => μ.real (C (e v)) +
      ∫ x in C (e v), MissingFlow.receipt μ q x ∂μ
    have hη0 (v : Fin k) : 0 ≤ η v := add_nonneg measureReal_nonneg
      (integral_nonneg_of_ae (ae_restrict_of_ae (MissingFlow.nonnegative_marginals hq.nonnegative).1))
    have hηδ (v : Fin k) : η v < δ := hsmall (e v)
    have hβsplit (v : Fin k) : β v = t * a (e v) +
        ∫ x, MissingFlow.finiteEndpointRemainder μ q (C (e v)) P θ x ∂μ := by
      have hb := hq.finite_endpoint_mass_split C P hC hP θ hr (e v) (hCp (e v))
        (hCH (e v)) (fun w hw => hCdis hw.symm)
      change β v = θ (e v) * a (e v) +
        ∫ x, MissingFlow.finiteEndpointRemainder μ q (C (e v)) P θ x ∂μ at hb
      simpa only [θ, heD v, ↓reduceIte] using hb
    have hβlower (v : Fin k) : t * a (e v) ≤ β v := by
      rw [hβsplit v]
      exact le_add_of_nonneg_right (integral_nonneg_of_ae
        (MissingFlow.finiteEndpointRemainder_nonnegative q hq.nonnegative (C (e v)) P θ hPdis hθ))
    have hβpos (v : Fin k) : 0 < β v := (mul_pos ht.1 (ha (e v))).trans_le (hβlower v)
    have hβA (v : Fin k) : β v ≤ A := by
      have hrem := MissingFlow.integral_finiteEndpointRemainder_le q hq.integrable hq.nonnegative
        (C (e v)) P (hC (e v)) hP θ hPdis hθ
      have hmass := hjA (e v)
      change a (e v) ≤ A at hmass
      have hprod := mul_le_mul_of_nonneg_left hmass ht.1.le
      have hs := hβsplit v
      have hη := hηδ v
      change _ ≤ η v at hrem
      nlinarith
    have hzero (v : Fin k) : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C (e v) → p.2 ∈ P (e v) →
        shiftedKernel W m p.1 p.2 = 0 :=
      (hrect (e v)).mono (fun _ hp hx hy => (hp hx hy).1.1)
    have henergy := hq.finite_selected_endpoint_energy_bound hW hd hgap C P hC hP hCp θ
      hPdis hθ hr e he hCdis (fun v => hCH (e v)) hzero
    have hbudget := hr.finite_dust_atomization_budget hW hd hgap k (fun v => C (e v))
      (fun v => hC (e v)) (fun v => (ENNReal.toReal_pos_iff.mp (hβpos v)).1)
      (fun v w hvw => hCdis (fun heq => hvw (he heq)))
      (fun v => hCD (e v) (heD v)) A hclasses hβA
    have hβsq : (∑ v : Fin k, (t * a (e v)) ^ 2) ≤ ∑ v : Fin k, (β v) ^ 2 := by
      apply Finset.sum_le_sum
      intro v _
      nlinarith [hβlower v, mul_pos ht.1 (ha (e v)), hβpos v]
    have herror : 8 * (∑ v : Fin k, β v * η v) ≤ ε := by
      have hsum : (∑ v : Fin k, β v * η v) ≤ (k : ℝ) * (A * δ) := by
        calc
          _ ≤ ∑ _v : Fin k, A * δ := Finset.sum_le_sum (fun v _ =>
            mul_le_mul (hβA v) (hηδ v).le (hη0 v) hA.le)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsum8 := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)
      dsimp only [K] at hδK
      nlinarith [mul_nonneg hA.le hδ.le]
    have hcombined : 2 * (c - m * d) + m + (-m) *
        ((∑' z, (S.keptAtomMass z) ^ 2) +
          (∑ v, if κ v = none then 0 else (a v) ^ 2) +
          (∑ v : Fin k, (t * a (e v)) ^ 2)) ≤ 2 * A ^ 2 + ε := by
      have hmulR := mul_le_mul_of_nonpos_left hreserve hm.le
      have hmulB := mul_le_mul_of_nonpos_left hβsq hm.le
      change (∑' z, (S.keptAtomMass z) ^ 2) +
        (∑ v, if κ v = none then 0 else (a v) ^ 2) ≤ _ at hreserve
      change _ ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ r) + 8 * (∑ v, β v * η v) at henergy
      change 2 * (c - m * d) + m +
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ r) ≤
        2 * A ^ 2 + m * (∑' z, (S.forwardClassMass r z) ^ 2) + _ + m * (∑ v, (β v) ^ 2) at hbudget
      change m * (∑' z, (S.forwardClassMass r z) ^ 2) ≤
        m * ((∑' z, (S.keptAtomMass z) ^ 2) +
          (∑ v, if κ v = none then 0 else (a v) ^ 2)) at hmulR
      nlinarith
    have hsum : (∑ v, if κ v = none then 0 else (a v) ^ 2) +
        (∑ v : Fin k, (t * a (e v)) ^ 2) =
        ∑ v, if κ v = none then (t * a v) ^ 2 else (a v) ^ 2 := by
      rw [hsumD (fun v => (t * a v) ^ 2), ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> ring
    rw [add_assoc (∑' z, (S.keptAtomMass z) ^ 2), hsum] at hcombined
    exact hcombined
  have hcont : Continuous (fun t : ℝ =>
      ∑ v, if κ v = none then (t * a v) ^ 2 else (a v) ^ 2) := by
    apply continuous_finsetSum
    intro v _
    by_cases hv : κ v = none
    · simp only [hv, ↓reduceIte]
      fun_prop
    · simp only [hv, ↓reduceIte]
      exact continuous_const
  have hclosed : IsClosed {t : ℝ | 2 * (c - m * d) + m + (-m) *
      ((∑' z, (S.keptAtomMass z) ^ 2) +
        ∑ v, if κ v = none then (t * a v) ^ 2 else (a v) ^ 2) ≤ 2 * A ^ 2} :=
    isClosed_le (continuous_const.add (continuous_const.mul (continuous_const.add hcont)))
      continuous_const
  have hmem : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  have h := closure_minimal (fun t ht => htbound t ht) hclosed hmem
  change 2 * (c - m * d) + m + (-m) *
    ((∑' z, (S.keptAtomMass z) ^ 2) +
      ∑ v, if κ v = none then (1 * a v) ^ 2 else (a v) ^ 2) ≤ 2 * A ^ 2 at h
  simpa only [one_mul, ite_self] using h

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow

module

public import Erdos1017.Multipartite.MultipartiteCountableIntegral

/-!
# Edge mass of the countable carrier

The ordered edge mass of the countable anchor, head and dust carrier.
Finite-prefix integral identities and the omitted-demand bound justify the
infinite limit, including the null physical diagonal inside atomless dust.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableMeasure

open MeasureTheory
open scoped BigOperators ENNReal

local instance carrierMassMeasurableSpaceLabel : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω]

/-- This auxiliary array evaluates every actual edge at one. It is only
an integral observable; no clique-test feasibility is asserted. -/
private def unitEdgeCoefficients : MultipartiteCountableDual.Coefficients
  | .inl _ => 1
  | .inr (.inl _) => -1
  | .inr (.inr (.inl _)) => -1
  | .inr (.inr (.inr b)) => if b then -1 else 1

private theorem unitEdge_kernel {a b : Label} (hab : a ≠ b ∨ a = .inr ()) :
    kernel unitEdgeCoefficients a b = 1 := by
  rcases a with a | a <;> rcases b with b | b
  · cases a with
    | none =>
      cases b with
      | none => simp at hab
      | some j => rfl
    | some i =>
      cases b with
      | none => rfl
      | some j =>
        have hij : i ≠ j := by simpa using hab
        simp only [kernel]
        split_ifs with h₁ h₂
        · norm_num [MultipartiteCountableDual.pair, unitEdgeCoefficients]
        · norm_num [MultipartiteCountableDual.pair, unitEdgeCoefficients]
        · exact False.elim (hij (by omega))
  · cases a <;> norm_num [kernel, MultipartiteCountableDual.linear,
      MultipartiteCountableDual.incident, unitEdgeCoefficients]
  · cases b <;> norm_num [kernel, MultipartiteCountableDual.linear,
      MultipartiteCountableDual.incident, unitEdgeCoefficients]
  · norm_num [kernel, MultipartiteCountableDual.penalty, unitEdgeCoefficients]

private theorem integral_unitEdge (η : Measure (Label × Ω)) [IsFiniteMeasure η] :
    (∫ z, physicalKernel unitEdgeCoefficients z ∂PhysicalPrimal.graphDemand η edgeSet) =
      (PhysicalPrimal.graphDemand η edgeSet).real Set.univ := by
  have heq : physicalKernel (Ω := Ω) unitEdgeCoefficients =ᵐ[
      PhysicalPrimal.graphDemand η edgeSet] (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem (edgeSet_measurable (Ω := Ω))] with z hz
    apply unitEdge_kernel
    simpa only [Finset.mem_singleton] using hz.2
  rw [integral_congr_ae heq]
  simp only [integral_const, smul_eq_mul, mul_one]

private theorem finite_pair_sum {n : ℕ} (p : Fin n → ℝ) :
    2 * (∑ i, ∑ j, if i < j then p i * p j else 0) =
      (∑ i, p i) ^ 2 - ∑ i, (p i) ^ 2 := by
  have hswap : (∑ i, ∑ j, if j < i then p i * p j else 0) =
      ∑ i, ∑ j, if i < j then p i * p j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hterm (i j : Fin n) : p i * p j =
      (if i = j then (p i) ^ 2 else 0) + (if i < j then p i * p j else 0) +
        (if j < i then p i * p j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, ne_of_lt h, not_lt.mpr h.le]
    · simp [pow_two]
    · simp [h, ne_of_gt h, not_lt.mpr h.le]
  have hsq : (∑ i, p i) ^ 2 = (∑ i, (p i) ^ 2) +
      (∑ i, ∑ j, if i < j then p i * p j else 0) +
        (∑ i, ∑ j, if j < i then p i * p j else 0) := by
    rw [pow_two, Fintype.sum_mul_sum]
    have heq : (∑ i, ∑ j, p i * p j) = ∑ i, ∑ j,
        ((if i = j then (p i) ^ 2 else 0) + (if i < j then p i * p j else 0) +
          (if j < i then p i * p j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hterm i j
    rw [heq]
    simp only [Finset.sum_add_distrib]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hswap] at hsq
  linarith

private theorem unitEdge_objective {n : ℕ} (p : Fin n → ℝ) (s : ℝ) :
    MultipartiteDust.objective p s (MultipartiteCountableDual.restrict n unitEdgeCoefficients) =
      (s + ∑ i, p i) + ((s + ∑ i, p i) ^ 2 - ∑ i, (p i) ^ 2) / 2 := by
  have hp := finite_pair_sum p
  simp only [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.pair,
    MultipartiteDust.incident, MultipartiteDust.linear, MultipartiteDust.penalty,
    MultipartiteCountableDual.restrict, MultipartiteCountableDual.head,
    MultipartiteCountableDual.pair, MultipartiteCountableDual.incident,
    unitEdgeCoefficients, Bool.false_eq_true, ite_false, ite_true,
    one_mul, neg_one_mul]
  have hpair : (∑ i, ∑ j, -(if i < j then 1 else 0) * p i * p j) =
      -(∑ i, ∑ j, if i < j then p i * p j else 0) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hpair]
  simp only [sub_neg_eq_add, ← Finset.sum_mul, Finset.sum_neg_distrib]
  nlinarith

theorem prefix_graphDemand_mass (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    (PhysicalPrimal.graphDemand (prefixMeasure ν p s n) edgeSet).real Set.univ / 2 =
      (s + ∑ i ∈ Finset.range n, p i) +
        ((s + ∑ i ∈ Finset.range n, p i) ^ 2 - ∑ i ∈ Finset.range n, (p i) ^ 2) / 2 := by
  have := prefixMeasure_finite ν p hsum s n
  have h := integral_prefix_kernel ν p hp s hs unitEdgeCoefficients n
  rw [integral_unitEdge, unitEdge_objective] at h
  have hsq : (∑ i : Fin n, (p i) ^ 2) = ∑ i ∈ Finset.range n, (p i) ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun i => (p i) ^ 2) n
  simpa only [Fin.sum_univ_eq_sum_range, hsq] using h

theorem graphDemand_mass (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (hsquares : Summable (fun i => (p i) ^ 2))
    (s : ℝ) (hs : 0 ≤ s) :
    (PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet).real Set.univ / 2 =
      (s + ∑' i, p i) + ((s + ∑' i, p i) ^ 2 - ∑' i, (p i) ^ 2) / 2 := by
  have := vertexMeasure_finite ν p hsum s
  let I := (PhysicalPrimal.graphDemand (vertexMeasure ν p s) edgeSet).real Set.univ / 2
  let a (n : ℕ) := (PhysicalPrimal.graphDemand (prefixMeasure ν p s n) edgeSet).real Set.univ / 2
  have herror (n : ℕ) : I - a n =
      (PhysicalPrimal.tailDemand (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet).real
        Set.univ / 2 := by
    have := prefixMeasure_finite ν p hsum s n
    have := tailMeasure_finite ν p hsum n
    have : IsFiniteMeasure (PhysicalPrimal.graphDemand (prefixMeasure ν p s n) edgeSet) := by
      unfold PhysicalPrimal.graphDemand
      infer_instance
    have : IsFiniteMeasure (PhysicalPrimal.tailDemand
        (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet) := by
      unfold PhysicalPrimal.tailDemand
      infer_instance
    dsimp only [I, a]
    rw [vertexMeasure_eq_prefix_add_tail ν p s n, PhysicalPrimal.graphDemand_add,
      measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)]
    ring
  have hmass (n : ℕ) : (prefixMeasure ν p s n).real Set.univ +
      (tailMeasure ν p n).real Set.univ = 1 + s + ∑' i, p i := by
    rw [prefixMeasure_mass ν p hp s hs, tailMeasure_mass ν p hp hsum]
    ring
  have hzero : Filter.Tendsto (fun n => I - a n) Filter.atTop (nhds 0) := by
    apply squeeze_zero' (f := fun n => I - a n)
      (g := fun n => (1 + s + ∑' i, p i) * (tailMeasure ν p n).real Set.univ)
    · exact Filter.Eventually.of_forall fun n => by rw [herror]; positivity
    · exact Filter.Eventually.of_forall fun n => by
        have := prefixMeasure_finite ν p hsum s n
        have := tailMeasure_finite ν p hsum n
        rw [herror]
        simpa only [hmass] using PhysicalPrimal.tailDemand_mass_bound
          (prefixMeasure ν p s n) (tailMeasure ν p n) edgeSet
    · simpa using (tailMeasure_mass_tendsto_zero ν p hp hsum).const_mul
        (1 + s + ∑' i, p i)
  have hI : Filter.Tendsto a Filter.atTop (nhds I) := by
    simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := I)).sub hzero
  have htotal : Filter.Tendsto (fun n => s + ∑ i ∈ Finset.range n, p i) Filter.atTop
      (nhds (s + ∑' i, p i)) := tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  have hformula : Filter.Tendsto a Filter.atTop
      (nhds ((s + ∑' i, p i) + ((s + ∑' i, p i) ^ 2 - ∑' i, (p i) ^ 2) / 2)) := by
    have h := htotal.add (((htotal.pow 2).sub hsquares.hasSum.tendsto_sum_nat).div_const 2)
    simpa only [a, prefix_graphDemand_mass ν p hp hsum s hs] using h
  exact tendsto_nhds_unique hI hformula

theorem profile_graphDemand_mass (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) :
    (PhysicalPrimal.graphDemand
      (vertexMeasure ν x.2 (MultipartiteProfiles.dust x)) edgeSet).real Set.univ / 2 =
        x.1 + (x.1 ^ 2 - ∑' i, (x.2 i) ^ 2) / 2 := by
  have h := graphDemand_mass ν x.2 hx.1.1.2 (MultipartiteProfiles.atoms_summable hx)
    (MultipartiteProfiles.squares_summable hx) (MultipartiteProfiles.dust x)
    (MultipartiteProfiles.dust_nonneg hx)
  convert h using 1
  rw [MultipartiteProfiles.dust_eq_sub_tsum hx]
  ring

end Erdos1017.MultipartiteCountableMeasure

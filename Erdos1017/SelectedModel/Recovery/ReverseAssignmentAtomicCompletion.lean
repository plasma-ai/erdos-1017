module

public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentExchange
public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentResidual
public import Erdos1017.SelectedModel.CountableResidualRouting

/-!
# Completing a reverse assignment over atomic labels

The residual of a feasible assignment is routed over eligible atomic labels
under the displayed cap and blocked coordinates, giving a completed atomic
assignment with the same top plateau and the whole compulsory-source identity
(`exists_completed_atomic_assignment`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Erdos1017.ReverseAssignment

private theorem finite_large_coordinates {u : ℕ → ℝ} (hu : Summable u)
    {ε : ℝ} (hε : 0 < ε) : {i | ε ≤ u i}.Finite := by
  have hnear : ∀ᶠ i in cofinite, u i < ε :=
    hu.tendsto_cofinite_zero.eventually_lt_const hε
  apply (mem_cofinite.mp hnear).subset
  intro i hi
  change ε ≤ u i at hi
  change ¬u i < ε
  exact not_lt.mpr hi

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

private def atomicResidual (δ : Ω → ℝ) (q : ℕ → Lp ℝ 2 μ) : Ω → ℝ :=
  {x | δ x = 0}.indicator (residual q)

omit [IsFiniteMeasure μ] in
private theorem atomicResidual_of_eq (δ : Ω → ℝ) (q : ℕ → Lp ℝ 2 μ)
    {x : Ω} (hx : δ x = 0) : atomicResidual δ q x = residual q x :=
  indicator_of_mem (show x ∈ {y | δ y = 0} from hx) _

omit [IsFiniteMeasure μ] in
private theorem atomicResidual_of_ne (δ : Ω → ℝ) (q : ℕ → Lp ℝ 2 μ)
    {x : Ω} (hx : δ x ≠ 0) : atomicResidual δ q x = 0 :=
  indicator_of_notMem (show x ∉ {y | δ y = 0} from hx) _

omit [IsFiniteMeasure μ] in
private theorem atomicResidual_mem (δ : Ω → ℝ) (q : ℕ → Lp ℝ 2 μ) (x : Ω) :
    atomicResidual δ q x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : δ x = 0
  · rw [atomicResidual_of_eq δ q hx]
    exact residual_mem q x
  · rw [atomicResidual_of_ne δ q hx]
    exact ⟨le_rfl, by norm_num⟩

/-- The actual residual is routed over eligible atomic labels with the
displayed cap and blocked coordinates. No infinite-eligibility premise is supplied. -/
theorem Feasible.exists_capped_atomic_extension {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) (B : Finset ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℕ → Lp ℝ 2 μ, Feasible allowed δ q' ∧
      (∀ᵐ x ∂μ, ∀ i, q i x ≤ q' i x) ∧
      (∀ i, (∫ x, q' i x ∂μ) - ∫ x, q i x ∂μ ≤ ε) ∧
      (∀ i ∈ B, q' i = q i) ∧
      (∀ᵐ x ∂μ, δ x = 0 → HasSum (fun i => q' i x) 1) ∧
      (∀ᵐ x ∂μ, δ x ≠ 0 → ∀ i, q' i x = q i x) := by
  classical
  have hzero : MeasurableSet {x | δ x = 0} := measurableSet_eq_fun hδ measurable_const
  have hr : Measurable (atomicResidual δ q) := (measurable_residual q).indicator hzero
  have hrInt : Integrable (atomicResidual δ q) μ := (residual_integrable q).indicator hzero
  have hInf : ∀ᵐ x ∂μ, 0 < atomicResidual δ q x → {i | x ∈ allowed i}.Infinite := by
    filter_upwards [hq.residual_infinite_allowed hallowed hδ] with x hx hpos
    by_cases hδx : δ x = 0
    · apply hx hδx
      rwa [atomicResidual_of_eq δ q hδx] at hpos
    · rw [atomicResidual_of_ne δ q hδx] at hpos
      exact (lt_irrefl (0 : ℝ) hpos).elim
  obtain ⟨c, hc, hc0, hcs, hcap, hprefix, _, hsum, _⟩ :=
    CountableResidualRouting.exists_capped_routing allowed hallowed B (atomicResidual δ q)
      hr hrInt (ae_of_all μ (fun x => (atomicResidual_mem δ q x).1)) hε hInf
  have hcLe (i : ℕ) (x : Ω) : c i x ≤ atomicResidual δ q x := by
    calc
      c i x ≤ ∑ j ∈ Finset.range (i + 1), c j x :=
        Finset.single_le_sum (fun j _ => hc0 j x) (Finset.mem_range.mpr (Nat.lt_succ_self i))
      _ ≤ max (atomicResidual δ q x) 0 := hprefix (i + 1) x
      _ = _ := max_eq_left (atomicResidual_mem δ q x).1
  have hmem (i : ℕ) : MemLp (c i) 2 μ := by
    apply MemLp.of_bound (hc i).1.aestronglyMeasurable 1
    exact ae_of_all μ (fun x => by
      rw [Real.norm_of_nonneg (hc0 i x)]
      exact (hcLe i x).trans (atomicResidual_mem δ q x).2)
  let z : ℕ → Lp ℝ 2 μ := fun i => (hmem i).toLp (c i)
  let q' : ℕ → Lp ℝ 2 μ := fun i => q i + z i
  have hz (i : ℕ) : ∀ᵐ x ∂μ, z i x = c i x := (hmem i).coeFn_toLp
  have heq : ∀ᵐ x ∂μ, ∀ i, q' i x = q i x + c i x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_add (q i) (z i), hz i] with x ha he
    simpa only [Pi.add_apply, he] using ha
  have hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ q' i x := by
    filter_upwards [heq, ae_all_iff.mpr hq.box] with x he hb i
    rw [he i]
    exact add_nonneg (hb i).1 (hc0 i x)
  have hnewSum : ∀ᵐ x ∂μ,
      HasSum (fun i => q' i x) (total q x + atomicResidual δ q x) := by
    filter_upwards [heq, hq.ae_hasSum_total, hsum] with x he hqsum hcsum
    have heqfun : (fun i => q' i x) = (fun i => q i x + c i x) := funext he
    rw [heqfun]
    exact hqsum.add hcsum
  have hsumLe : ∀ᵐ x ∂μ, total q x + atomicResidual δ q x ≤ 1 := by
    filter_upwards [hq.ae_summable_and_total_le_one, hq.residual_eq] with x ht he
    by_cases hδx : δ x = 0
    · rw [atomicResidual_of_eq δ q hδx, he]
      linarith
    · rw [atomicResidual_of_ne δ q hδx, add_zero]
      exact ht.2.2
  have hpartial (J : Finset ℕ) : ∀ᵐ x ∂μ, ∑ i ∈ J, q' i x ≤ 1 := by
    filter_upwards [hnewSum, hnonneg, hsumLe] with x hs hn hle
    have h := hs.summable.sum_le_tsum J (fun i _ => hn i)
    rw [hs.tsum_eq] at h
    exact h.trans hle
  have hsupport : ∀ᵐ x ∂μ, ∀ i, x ∉ allowed i → q' i x = 0 := by
    filter_upwards [heq, ae_all_iff.mpr hq.support] with x he hs i hi
    rw [he i, hs i hi, hcs i x (Or.inr hi), add_zero]
  have hfull : ∀ᵐ x ∂μ, δ x = 0 → HasSum (fun i => q' i x) 1 := by
    filter_upwards [hnewSum, hq.residual_eq] with x hs he hδx
    have hid : total q x + atomicResidual δ q x = 1 := by
      rw [atomicResidual_of_eq δ q hδx, he]
      ring
    rwa [hid] at hs
  have hq' : Feasible allowed δ q' := by
    refine ⟨?_, ?_, hpartial, ?_⟩
    · intro i
      filter_upwards [hnonneg, hpartial {i}] with x hn hp
      exact ⟨hn i, by simpa only [Finset.sum_singleton] using hp⟩
    · intro i
      exact hsupport.mono (fun _ hx => hx i)
    · intro J
      filter_upwards [ae_restrict_of_ae hfull, ae_restrict_of_ae hsupport,
        ae_restrict_mem (measurableSet_finitePattern hallowed hδ J)] with x hf hs hx
      have hsum' := hf hx.1
      have htsum : (∑' i, q' i x) = ∑ i ∈ J, q' i x := by
        apply tsum_eq_sum
        intro i hi
        exact hs i (fun hia => hi ((hx.2 i).mpr hia))
      exact htsum.symm.trans hsum'.tsum_eq
  refine ⟨q', hq', ?_, ?_, ?_, hfull, ?_⟩
  · filter_upwards [heq] with x he i
    rw [he i]
    linarith [hc0 i x]
  · intro i
    have hint : (∫ x, q' i x ∂μ) = (∫ x, q i x ∂μ) + ∫ x, c i x ∂μ := by
      rw [integral_congr_ae (heq.mono (fun _ hx => hx i))]
      exact integral_add (coordinate_integrable q i) (hc i).2
    linarith [hcap i]
  · intro i hiB
    have hzi : z i = 0 := by
      apply Lp.ext
      filter_upwards [hz i, Lp.coeFn_zero ℝ 2 μ] with x he hzero'
      rw [he, hcs i x (Or.inl hiB), hzero']
      simp only [Pi.zero_apply]
    simp only [q', hzi, add_zero]
  · filter_upwards [heq] with x he hδx i
    have hzero' : atomicResidual δ q x = 0 := atomicResidual_of_ne δ q hδx
    have hci : c i x = 0 := le_antisymm (by simpa only [hzero'] using hcLe i x) (hc0 i x)
    rw [he i, hci, add_zero]

/-- One feasible assignment constructs a completed atomic assignment with
the same actual top plateau and the entire original compulsory-source identity. -/
theorem exists_completed_atomic_assignment {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a)
    (hpositive : ∃ i, 0 < a i) (q0 : ℕ → Lp ℝ 2 μ) (hq0 : Feasible allowed δ q0) :
    ∃ q : ℕ → Lp ℝ 2 μ, Feasible allowed δ q ∧
      ∃ t : ℝ, 0 < t ∧ ∃ P : Finset ℕ, P.Nonempty ∧
        (∀ i, mass a q i ≤ t) ∧ (∀ i, mass a q i = t ↔ i ∈ P) ∧
        (∀ᵐ x ∂μ, δ x = 0 → HasSum (fun i => q i x) 1) ∧
        (∀ᵐ x ∂μ, δ x ≠ 0 → ∀ i, q i x = 0) ∧
        (∀ᵐ x ∂μ,
          (∑ i ∈ P, q i x) = (compulsorySource allowed δ P).indicator (fun _ => 1) x) ∧
        (P.card : ℝ) * t = (∑ i ∈ P, a i) + μ.real (compulsorySource allowed δ P) := by
  classical
  obtain ⟨q, hq, hmin, t, ht, P, hP, hmax, hmaxiff, hreceipt, hcard⟩ :=
    exists_minimizer_top_plateau hallowed hδ ha haSum hpositive q0 hq0
  have hfinite : {i | t / 4 ≤ mass a q i}.Finite :=
    finite_large_coordinates (hq.mass_summable ha haSum) (by linarith)
  let B := hfinite.toFinset
  have hBiff (i : ℕ) : i ∈ B ↔ t / 4 ≤ mass a q i := hfinite.mem_toFinset
  have hPB : P ⊆ B := by
    intro i hi
    apply (hBiff i).mpr
    rw [(hmaxiff i).mpr hi]
    linarith
  obtain ⟨q', hq', _, hcap, hunchanged, hfull, hdiffuse⟩ :=
    hq.exists_capped_atomic_extension hallowed hδ B (show 0 < t / 4 by linarith)
  have hmass_same (i : ℕ) (hi : i ∈ B) : mass a q' i = mass a q i := by
    simp only [mass, hunchanged i hi]
  have hmass_cap (i : ℕ) : mass a q' i ≤ mass a q i + t / 4 := by
    dsimp only [mass]
    linarith [hcap i]
  have hsmall (i : ℕ) (hi : i ∉ B) : mass a q' i < t / 2 := by
    have hlt : mass a q i < t / 4 := lt_of_not_ge (fun h => hi ((hBiff i).mpr h))
    linarith [hmass_cap i]
  have hmax' (i : ℕ) : mass a q' i ≤ t := by
    by_cases hi : i ∈ B
    · rw [hmass_same i hi]
      exact hmax i
    · have hlt := hsmall i hi
      linarith
  have hmaxiff' (i : ℕ) : mass a q' i = t ↔ i ∈ P := by
    constructor
    · intro heq
      by_cases hi : i ∈ B
      · apply (hmaxiff i).mp
        rwa [hmass_same i hi] at heq
      · have hlt := hsmall i hi
        linarith
    · intro hi
      rw [hmass_same i (hPB hi)]
      exact (hmaxiff i).mpr hi
  have hzero : ∀ᵐ x ∂μ, δ x ≠ 0 → ∀ i, q' i x = 0 := by
    have hold : ∀ᵐ x ∂μ, ∀ i, δ x ≠ 0 → q i x = 0 :=
      ae_all_iff.mpr (fun i => hq.no_diffuse_receipt_of_minimum hallowed hδ ha haSum hmin i)
    filter_upwards [hdiffuse, hold] with x hn hz hδx i
    rw [hn hδx i, hz i hδx]
  have hreceipt' : ∀ᵐ x ∂μ,
      (∑ i ∈ P, q' i x) = (compulsorySource allowed δ P).indicator (fun _ => 1) x := by
    filter_upwards [hreceipt] with x hx
    calc
      (∑ i ∈ P, q' i x) = ∑ i ∈ P, q i x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hunchanged i (hPB hi)]
      _ = _ := hx
  exact ⟨q', hq', t, ht, P, hP, hmax', hmaxiff', hfull, hzero, hreceipt', hcard⟩

end Erdos1017.ReverseAssignment

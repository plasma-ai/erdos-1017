module

public import Erdos1017.Multipartite.Dust.DustSingleSplit
public import Erdos1017.Multipartite.Dust.DustZeroHead
public import Erdos1017.Multipartite.MultipartiteProfiles
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Limiting coefficient value of a profile

`finiteValue` keeps the first `n` independent heads and completes residual mass
to dust, and `limitValue` is its limit; finite values converge uniformly on the
compact profile space with an explicit error from the omitted square mass, so
the limiting value is continuous.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteProfiles

/-- Keep the first n independent heads and complete all residual mass to dust. -/
def finiteValue (n : ℕ) (x : Profile) : ℝ :=
  MultipartiteDust.value (fun i : Fin n => x.2 i.val) (residual n x)

/-- Every finite truncation is continuous in the product profile coordinates. -/
theorem finiteValue_continuous (n : ℕ) : Continuous (finiteValue n) := by
  unfold finiteValue
  have harg : Continuous (fun x : Profile => ((fun i : Fin n => x.2 i.val), residual n x)) :=
    (continuous_pi (fun i => (continuous_apply i.val).comp continuous_snd)).prodMk
      (residual_continuous n)
  simpa only [Function.comp_def] using (MultipartiteDust.value_continuous n).comp harg

/-- Successive truncations differ by at most half the newly separated square
mass. This is a consequence of the actual merge theorem, not continuity. -/
theorem finiteValue_step {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    0 ≤ finiteValue (n + 1) x - finiteValue n x ∧
      finiteValue (n + 1) x - finiteValue n x ≤ (x.2 n) ^ 2 / 2 := by
  let p : Fin (n + 1) → ℝ := fun i => x.2 i.val
  have h := MultipartiteDust.single_merge_value_error p (residual (n + 1) x) (Fin.last n)
    (hx.1.1.2 n) (residual_nonneg hx (n + 1))
  have hp : Function.update p (Fin.last n) 0 =
      (Fin.last n).insertNth 0 (fun i : Fin n => x.2 i.val) := by
    rw [Fin.insertNth_last']
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · simp [p]
  have hs : residual (n + 1) x + p (Fin.last n) = residual n x := by
    simp only [residual, Finset.sum_range_succ, p, Fin.val_last]
    ring
  rw [hp, hs, MultipartiteDust.value_insert_zero] at h
  exact h

/-- Finite-head values increase as more independent parts are retained. -/
theorem finiteValue_monotone {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    Monotone (fun n => finiteValue n x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact sub_nonneg.mp (finiteValue_step hx n).1

/-- Telescoping the actual merge estimates controls every finite tail. -/
theorem finiteValue_tail_error {L : ℝ} {x : Profile} (hx : x ∈ space L)
    (n N : ℕ) (hnN : n ≤ N) :
    finiteValue N x - finiteValue n x ≤
      (∑ i ∈ (Finset.range N).filter (fun i => n ≤ i), (x.2 i) ^ 2) / 2 := by
  induction N, hnN using Nat.le_induction with
  | base =>
    have he : (Finset.range n).filter (fun i => n ≤ i) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      omega
    simp [he]
  | @succ N hnN ih =>
    have he : (Finset.range (N + 1)).filter (fun i => n ≤ i) =
        insert N ((Finset.range N).filter (fun i => n ≤ i)) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      simp [hnN]
    have hnot : N ∉ (Finset.range N).filter (fun i => n ≤ i) := by simp
    rw [he, Finset.sum_insert hnot]
    linarith [(finiteValue_step hx N).2]

/-- Sorted square tails give an error bound uniform over the whole compact
profile space, independently of the number of retained additional heads. -/
theorem finiteValue_uniform_error {L : ℝ} {x : Profile} (hx : x ∈ space L)
    (n N : ℕ) : finiteValue N x - finiteValue n x ≤ L ^ 2 / (2 * (n + 1)) := by
  by_cases h : n ≤ N
  · have htail := finiteValue_tail_error hx n N h
    have hsquare := square_tail_bound hx n N
    have hdiv : L ^ 2 / ((n : ℝ) + 1) / 2 = L ^ 2 / (2 * (n + 1)) := by
      rw [div_div, mul_comm ((n : ℝ) + 1) 2]
    rw [← hdiv]
    linarith
  · have hmono := finiteValue_monotone hx (Nat.le_of_lt (Nat.lt_of_not_ge h))
    have hnonneg : 0 ≤ L ^ 2 / (2 * ((n : ℝ) + 1)) := by positivity
    linarith

/-- The limiting coefficient value. Its physical interpretation is given by a
countable-profile theorem, not by this definition. -/
def limitValue (x : Profile) : ℝ := sSup (Set.range (fun n => finiteValue n x))

theorem finiteValue_bddAbove {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    BddAbove (Set.range (fun n => finiteValue n x)) := by
  refine ⟨finiteValue 0 x + L ^ 2 / 2, ?_⟩
  rintro _ ⟨N, rfl⟩
  have h := finiteValue_uniform_error hx 0 N
  norm_num at h
  linarith

/-- Uniform one-sided approximation of the limiting coefficient value. -/
theorem limitValue_error {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    0 ≤ limitValue x - finiteValue n x ∧
      limitValue x - finiteValue n x ≤ L ^ 2 / (2 * (n + 1)) := by
  have hlower : finiteValue n x ≤ limitValue x :=
    le_csSup (finiteValue_bddAbove hx) ⟨n, rfl⟩
  have hupper : limitValue x ≤ finiteValue n x + L ^ 2 / (2 * (n + 1)) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨N, rfl⟩
    linarith [finiteValue_uniform_error hx n N]
  constructor <;> linarith

/-- Actual finite-head values converge uniformly on the compact profile space. -/
theorem finiteValue_tendstoUniformlyOn (L : ℝ) :
    TendstoUniformlyOn finiteValue limitValue Filter.atTop (space L) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (L ^ 2 / ε)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro x hx
  have herr := limitValue_error hx n
  rw [Real.dist_eq, abs_of_nonneg herr.1]
  apply lt_of_le_of_lt herr.2
  apply (div_lt_iff₀ (show (0 : ℝ) < 2 * ((n : ℝ) + 1) by positivity)).mpr
  have hsmall := (div_lt_iff₀ hε).mp hN
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hcast hε.le
  nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

/-- The limiting coefficient value is continuous because the quantitative
merge estimate gives uniform convergence of the actual finite values. -/
theorem limitValue_continuousOn (L : ℝ) : ContinuousOn limitValue (space L) := by
  apply (finiteValue_tendstoUniformlyOn L).continuousOn
  exact (Filter.Eventually.of_forall (fun n => (finiteValue_continuous n).continuousOn)).frequently

/-- The actual omitted square mass, independent of a chosen uniform bound L. -/
def squareTail (n : ℕ) (x : Profile) : ℝ := ∑' i, if n ≤ i then (x.2 i) ^ 2 else 0

theorem squareTail_summable {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    Summable (fun i => if n ≤ i then (x.2 i) ^ 2 else 0) := by
  have h := (squares_summable hx).indicator {i | n ≤ i}
  convert h using 1
  funext i
  by_cases hi : n ≤ i
  · rw [ite_eq_left hi, Set.indicator_of_mem (show i ∈ {i | n ≤ i} from hi)]
  · rw [ite_eq_right hi, Set.indicator_of_notMem (show i ∉ {i | n ≤ i} from hi)]

/-- The exact omitted-square version of the coefficient approximation bound. -/
theorem limitValue_squareTail_error {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    limitValue x - finiteValue n x ≤ squareTail n x / 2 := by
  have hnonneg (i : ℕ) : 0 ≤ (if n ≤ i then (x.2 i) ^ 2 else 0) := by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have htail₀ : 0 ≤ squareTail n x := tsum_nonneg hnonneg
  have hupper : limitValue x ≤ finiteValue n x + squareTail n x / 2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨N, rfl⟩
    by_cases hnN : n ≤ N
    · have hfinite := finiteValue_tail_error hx n N hnN
      have hsum := Summable.sum_le_tsum (Finset.range N) (fun i _ => hnonneg i)
        (squareTail_summable hx n)
      rw [← Finset.sum_filter] at hsum
      change (∑ i ∈ (Finset.range N).filter (fun i => n ≤ i), (x.2 i) ^ 2) ≤ squareTail n x at hsum
      linarith
    · have hmono := finiteValue_monotone hx (Nat.le_of_lt (Nat.lt_of_not_ge hnN))
      linarith
  linarith

end Erdos1017.MultipartiteProfiles

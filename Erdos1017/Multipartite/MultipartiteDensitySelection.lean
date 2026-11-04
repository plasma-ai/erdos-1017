module

public import Erdos1017.Multipartite.MultipartiteStrictPairs
public import Erdos1017.Multipartite.Dust.DustPaddedCells

/-!
# Selecting a fixed-density maximum

The countable coefficient value is at most one, the fixed-density set is compact
in the sorted profile space, and the normalized value attains a fixed-density
maximum that bounds every summable profile at that density, with a strict
optimum having greatest dust and strict pair bounds.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Finite-cell restriction bounds the actual finite-head dust value by one. -/
theorem value_le_one {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) : value p s ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max s 0)
  have hn0 : 0 < n := by exact_mod_cast (lt_of_le_of_lt (le_max_right s 0) hn)
  have hsn : s ≤ n := (le_max_left _ _).trans hn.le
  have herror := (DustPaddedCells.finite_cell_value_error p hp s hs n hn0 hsn).1
  have hbound := Selector.value_le_one _ (DustPaddedCells.target_cube p hp s hs n hn0 hsn)
  linarith

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

/-- The actual countable coefficient value is at most one for every
summable normalized profile, without a square-moment or sorting premise. -/
theorem value_le_one (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) : value p s ≤ 1 := by
  obtain ⟨D, hD, heq⟩ := exists_value_eq p hp hsum s
  rw [heq]
  apply le_of_tendsto (objective_restrict_tendsto p hp hsum s hD.1)
  apply Filter.Eventually.of_forall
  intro n
  exact (MultipartiteDust.objective_le_value (fun i : Fin n => p i.val) s
    (restrict n D) (restrict_mem_feasible hD n)).trans
      (MultipartiteDust.value_le_one _ (fun i => ⟨hp i.val, hp1 i.val⟩) s hs)

end Erdos1017.MultipartiteCountableDual

namespace Erdos1017.MultipartiteProfiles

/-- The physical compact-profile value has the anchor-square upper bound
before returning to physical mass normalization. -/
theorem limitValue_le_one {L : ℝ} {x : Profile} (hx : x ∈ space L) : limitValue x ≤ 1 := by
  apply le_of_tendsto ((finiteValue_tendstoUniformlyOn L).tendsto_at hx)
  exact Filter.Eventually.of_forall fun n => MultipartiteDust.value_le_one
    (fun i : Fin n => x.2 i.val) (fun i => ⟨hx.1.1.2 i.val, hx.1.2.2 i.val⟩)
    (residual n x) (residual_nonneg hx n)

/-- Return the anchored coefficient value to total physical mass one. -/
def normalizedValue (x : Profile) : ℝ := limitValue x / (1 + x.1) ^ 2

/-- The normalized missing edge density is fixed by the two moments. -/
def densityFiber (L ε : ℝ) : Set Profile :=
  space L ∩ {x | 1 + (∑' i, (x.2 i) ^ 2) = 2 * ε * (1 + x.1) ^ 2}

theorem normalizedValue_continuousOn (L : ℝ) : ContinuousOn normalizedValue (space L) := by
  apply (limitValue_continuousOn L).div (by fun_prop)
  intro x hx
  have hx0 : 0 ≤ x.1 := hx.1.1.1
  positivity

/-- The actual fixed-density set is compact in the sorted profile space. -/
theorem densityFiber_isCompact (L ε : ℝ) : IsCompact (densityFiber L ε) := by
  have hc : ContinuousOn (fun x : Profile =>
      1 + (∑' i, (x.2 i) ^ 2) - 2 * ε * (1 + x.1) ^ 2) (space L) :=
    (continuousOn_const.add (squareMoment_continuousOn L)).sub (by fun_prop)
  have hclosed := hc.preimage_isClosed_of_isClosed (space_isCompact L).isClosed
    (isClosed_singleton (x := (0 : ℝ)))
  apply (space_isCompact L).of_isClosed_subset
  · simpa only [densityFiber, Set.preimage, Set.mem_singleton_iff, sub_eq_zero] using hclosed
  · exact Set.inter_subset_left

/-- The actual normalized multipartite value attains a fixed-density maximum
inside every nonempty compact cutoff. -/
theorem exists_density_maximum (L ε : ℝ) (hne : (densityFiber L ε).Nonempty) :
    ∃ x ∈ densityFiber L ε, ∀ y ∈ densityFiber L ε, normalizedValue y ≤ normalizedValue x := by
  exact (densityFiber_isCompact L ε).exists_isMaxOn hne
    ((normalizedValue_continuousOn L).mono Set.inter_subset_left)

/-- Every summable normalized profile above the missing-density baseline
has an exact sorted representative inside the compact cutoff. -/
theorem exists_density_representative_of_above_missing
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p)
    (s : ℝ) (hs : 0 ≤ s) (ε : ℝ) (hε : 0 < ε)
    (hmoment : 1 + (∑' i, (p i) ^ 2) = 2 * ε * (1 + (s + ∑' i, p i)) ^ 2)
    (hvalue : ε < MultipartiteCountableDual.value p s / (1 + (s + ∑' i, p i)) ^ 2) :
    ∃ x ∈ densityFiber (1 / Real.sqrt ε - 1) ε,
      x.1 = s + (∑' i, p i) ∧ dust x = s ∧
      (∑' i, (x.2 i) ^ 2) = (∑' i, (p i) ^ 2) ∧
      MultipartiteCountableDual.value p s / (1 + (s + ∑' i, p i)) ^ 2 = normalizedValue x := by
  have hT : 0 ≤ s + ∑' i, p i := add_nonneg hs (tsum_nonneg hp)
  have hden : 0 < 1 + (s + ∑' i, p i) := by linarith
  have hden2 : 0 < (1 + (s + ∑' i, p i)) ^ 2 := sq_pos_of_pos hden
  have hv := (lt_div_iff₀ hden2).mp hvalue
  have hbound := MultipartiteCountableDual.value_le_one p hp hp1 hsum s hs
  have hQ : (∑' i, (p i) ^ 2) ≤ 1 := by nlinarith
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hprod : Real.sqrt ε * (1 + (s + ∑' i, p i)) < 1 := by
    have heq : (Real.sqrt ε * (1 + (s + ∑' i, p i))) ^ 2 =
        ε * (1 + (s + ∑' i, p i)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hε.le]
    nlinarith [mul_pos hsqrt hden]
  have hL : s + (∑' i, p i) ≤ 1 / Real.sqrt ε - 1 := by
    have h := (lt_div_iff₀ hsqrt).mpr (show (1 + (s + ∑' i, p i)) * Real.sqrt ε < 1 by
      nlinarith [hprod])
    linarith
  obtain ⟨x, hx, hxT, hxs, hxQ, hxvalue⟩ := exists_sorted_representative
    p hp hp1 hsum s hs (1 / Real.sqrt ε - 1) hL hQ
  refine ⟨x, ⟨hx, ?_⟩, hxT, hxs, hxQ, ?_⟩
  · change 1 + (∑' i, (x.2 i) ^ 2) = 2 * ε * (1 + x.1) ^ 2
    rw [hxT, hxQ]
    exact hmoment
  · simp only [normalizedValue, hxT, hxvalue]

/-- A selected maximum above the baseline bounds every arbitrary summable
profile at that density, including profiles outside the initial compact cutoff. -/
theorem normalized_value_le_density_maximum {ε : ℝ} (hε : 0 < ε) {x : Profile}
    (hmax : ∀ y ∈ densityFiber (1 / Real.sqrt ε - 1) ε, normalizedValue y ≤ normalizedValue x)
    (hxvalue : ε ≤ normalizedValue x)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p)
    (s : ℝ) (hs : 0 ≤ s)
    (hmoment : 1 + (∑' i, (p i) ^ 2) = 2 * ε * (1 + (s + ∑' i, p i)) ^ 2) :
    MultipartiteCountableDual.value p s / (1 + (s + ∑' i, p i)) ^ 2 ≤ normalizedValue x := by
  by_cases hsmall : MultipartiteCountableDual.value p s / (1 + (s + ∑' i, p i)) ^ 2 ≤ ε
  · exact hsmall.trans hxvalue
  · obtain ⟨y, hy, _, _, _, hyvalue⟩ := exists_density_representative_of_above_missing
      p hp hp1 hsum s hs ε hε hmoment (lt_of_not_ge hsmall)
    rw [hyvalue]
    exact hmax y hy

/-- Every actual feasible dual objective at the selected density obeys the
same global profile maximum. This supplies the later feasible-variation bound. -/
theorem normalized_objective_le_density_maximum {ε : ℝ} (hε : 0 < ε) {x : Profile}
    (hmax : ∀ y ∈ densityFiber (1 / Real.sqrt ε - 1) ε, normalizedValue y ≤ normalizedValue x)
    (hxvalue : ε ≤ normalizedValue x)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p)
    (s : ℝ) (hs : 0 ≤ s)
    (hmoment : 1 + (∑' i, (p i) ^ 2) = 2 * ε * (1 + (s + ∑' i, p i)) ^ 2)
    {D : MultipartiteCountableDual.Coefficients} (hD : D ∈ MultipartiteCountableDual.feasible) :
    MultipartiteCountableDual.objective p s D / (1 + (s + ∑' i, p i)) ^ 2 ≤ normalizedValue x := by
  have hden : 0 < (1 + (s + ∑' i, p i)) ^ 2 := by
    have hT : 0 ≤ s + ∑' i, p i := add_nonneg hs (tsum_nonneg hp)
    positivity
  exact ((div_le_div_iff_of_pos_right hden).mpr
    (MultipartiteCountableDual.objective_le_value p hp hsum s hD)).trans
      (normalized_value_le_density_maximum hε hmax hxvalue p hp hp1 hsum s hs hmoment)

/-- A density maximum can be selected with greatest dust on its own moment
fiber and an actual optimal dual satisfying every positive-head strict pair bound. -/
theorem exists_density_strict_optimum (L ε : ℝ) (hne : (densityFiber L ε).Nonempty) :
    ∃ x ∈ densityFiber L ε,
      (∀ y ∈ densityFiber L ε, normalizedValue y ≤ normalizedValue x) ∧
      (∀ y ∈ momentFiber L x.1 (∑' k, (x.2 k) ^ 2),
        limitValue y = limitValue x → dust y ≤ dust x) ∧
      ∃ D ∈ MultipartiteCountableDual.feasible,
        MultipartiteCountableDual.objective x.2 (dust x) D = limitValue x ∧
        ∀ i j, i ≠ j → 0 < x.2 i → 0 < x.2 j →
          -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) <
            min (MultipartiteCountableDual.repeatPenalty D i)
              (MultipartiteCountableDual.repeatPenalty D j) ∧ MultipartiteCountableDual.head D i < 1 := by
  obtain ⟨z, hz, hzmax⟩ := exists_density_maximum L ε hne
  obtain ⟨x, hx, hxmax, hxdust, D, hD, hopt, hstrict⟩ :=
    MultipartiteCountableDual.exists_greatest_dust_strict_optimum L z.1
      (∑' k, (z.2 k) ^ 2) ⟨z, hz.1, rfl, rfl⟩
  have hxdensity : x ∈ densityFiber L ε := by
    refine ⟨hx.1, ?_⟩
    change 1 + (∑' k, (x.2 k) ^ 2) = 2 * ε * (1 + x.1) ^ 2
    rw [hx.2.1, hx.2.2]
    exact hz.2
  have hden : 0 < (1 + z.1) ^ 2 := by
    have hz0 : 0 ≤ z.1 := hz.1.1.1.1
    positivity
  have hzle : normalizedValue z ≤ normalizedValue x := by
    unfold normalizedValue
    rw [hx.2.1]
    exact (div_le_div_iff_of_pos_right hden).mpr (hxmax z ⟨hz.1, rfl, rfl⟩)
  refine ⟨x, hxdensity, fun y hy => (hzmax y hy).trans hzle, ?_, D, hD, hopt, hstrict⟩
  simpa only [hx.2.1, hx.2.2] using hxdust

/-- A fixed-density optimizer above the missing density has atomic square
moment below one and anchor mass greater than the square root of that density. -/
theorem above_missing_density_bounds {L ε : ℝ} {x : Profile}
    (hx : x ∈ densityFiber L ε) (hε : 0 < ε) (hvalue : ε < normalizedValue x) :
    (∑' i, (x.2 i) ^ 2) < 1 ∧ Real.sqrt ε < 1 / (1 + x.1) := by
  have hden : 0 < 1 + x.1 := by linarith [hx.1.1.1.1]
  have hden2 : 0 < (1 + x.1) ^ 2 := sq_pos_of_pos hden
  have hv : ε * (1 + x.1) ^ 2 < limitValue x := (lt_div_iff₀ hden2).mp hvalue
  have hbound := limitValue_le_one hx.1
  have hmoment : 1 + (∑' i, (x.2 i) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
  constructor
  · nlinarith [hmoment]
  · apply (Real.sqrt_lt hε.le (by positivity : (0 : ℝ) ≤ 1 / (1 + x.1))).mpr
    have hanchor : ε < 1 / (1 + x.1) ^ 2 :=
      (lt_div_iff₀ hden2).mpr (hv.trans_le hbound)
    simpa only [div_pow, one_pow] using hanchor

end Erdos1017.MultipartiteProfiles

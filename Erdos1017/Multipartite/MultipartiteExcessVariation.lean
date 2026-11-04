module

public import Erdos1017.Multipartite.MultipartiteExcessSelection

/-!
# Mass transfers at an excess maximum

Moving one head against the anchor gives the exact density-increasing variation
polynomial, every sufficiently small such transfer is an admissible competitor
in an interior density window, and at an interior excess maximum the optimal
dual's head multiplier dominates the benchmark's right slope.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- A bounded admissible raw-mass competitor is compared with the actual
compact excess maximum after normalization and sorting. -/
theorem physical_excess_le_maximum {L lo hi : ℝ} {x : MultipartiteProfiles.Profile}
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow L lo hi,
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ a) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s)
    (hL : (s + ∑' i, p i) / a ≤ L)
    (hQ : (∑' i, (p i) ^ 2) / a ^ 2 ≤ 1)
    (hd : 1 / 2 - (a ^ 2 + ∑' i, (p i) ^ 2) /
      (2 * (a + s + ∑' i, p i) ^ 2) ∈ Set.Icc lo hi)
    {D : Coefficients} (hD : D ∈ feasible) :
    physicalObjective a p s D / (a + s + ∑' i, p i) ^ 2 -
      benchmark (1 / 2 - (a ^ 2 + ∑' i, (p i) ^ 2) /
        (2 * (a + s + ∑' i, p i) ^ 2)) ≤ MultipartiteProfiles.benchmarkExcess x := by
  have hM : 0 < a + s + ∑' i, p i := by
    have hpSum : 0 ≤ ∑' i, p i := tsum_nonneg hp
    linarith
  have hp' : ∀ i, 0 ≤ p i / a := fun i => div_nonneg (hp i) ha.le
  have hsum' := hsum.div_const a
  have hQ' : (∑' i, (p i / a) ^ 2) ≤ 1 := by
    simpa only [div_pow, tsum_div_const] using hQ
  have hp1' (i : ℕ) : p i / a ≤ 1 := (div_le_one ha).mpr (hp1 i)
  obtain ⟨y, hy, hyT, _, hyQ, hyvalue⟩ := MultipartiteProfiles.exists_sorted_representative
    (fun i => p i / a) hp' hp1' hsum' (s / a) (div_nonneg hs ha.le) L
    (by simpa only [tsum_div_const, ← add_div] using hL) hQ'
  have hden : 1 + y.1 = (a + s + ∑' i, p i) / a := by
    rw [hyT, tsum_div_const]
    field_simp
    ring
  have hyd : MultipartiteProfiles.density y =
      1 / 2 - (a ^ 2 + ∑' i, (p i) ^ 2) / (2 * (a + s + ∑' i, p i) ^ 2) := by
    unfold MultipartiteProfiles.density MultipartiteProfiles.missingDensity
    rw [hyQ, hden]
    simp_rw [div_pow, tsum_div_const]
    field_simp
  have hcompare := hmax y ⟨hy, by change MultipartiteProfiles.density y ∈ Set.Icc lo hi; rwa [hyd]⟩
  have hobj := objective_le_value (fun i => p i / a) hp' hsum' (s / a) hD
  have hvalue : physicalObjective a p s D / (a + s + ∑' i, p i) ^ 2 ≤
      MultipartiteProfiles.normalizedValue y := by
    rw [← normalized_physicalObjective a ha p s hM D]
    unfold MultipartiteProfiles.normalizedValue
    rw [← hyvalue, hyT]
    exact div_le_div_of_nonneg_right hobj (sq_nonneg _)
  unfold MultipartiteProfiles.benchmarkExcess at hcompare
  rw [hyd] at hcompare
  change _ ≤ MultipartiteProfiles.normalizedValue x - benchmark (MultipartiteProfiles.density x)
  linarith

/-- Moving one head against the anchor gives the exact density-increasing
variation polynomial of the old optimal charges. -/
theorem physicalObjective_one_transfer {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) (s : ℝ)
    (i : ℕ) (t : ℝ) (ht : 0 ≤ p i + t) :
    physicalObjective (1 - t) (Function.update p i (p i + t)) s D =
      objective p s D + t * (headRow p s D i - anchorRow p s D) - head D i * t ^ 2 := by
  rw [physicalObjective_eq_objective, objective_update hD p hp hsum s i _ ht,
    anchorRow_update hD p hp hsum s i]
  ring

/-- Every sufficiently small transfer from the anchor to one positive head
is an actual admissible competitor in an interior density window. -/
theorem one_transfer_excess_local_max {L lo hi : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) (hT : x.1 < L)
    (hQ : (∑' k, (x.2 k) ^ 2) < 1)
    (hd : MultipartiteProfiles.density x ∈ Set.Ioo lo hi)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow L lo hi,
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) :
    ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0),
      (MultipartiteProfiles.limitValue x +
        t * (headRow x.2 (MultipartiteProfiles.dust x) D i -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) - head D i * t ^ 2) / (1 + x.1) ^ 2 -
        benchmark (MultipartiteProfiles.density x + ((1 - x.2 i) * t - t ^ 2) / (1 + x.1) ^ 2) ≤
          MultipartiteProfiles.benchmarkExcess x := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx
  have hsqsum := MultipartiteProfiles.squares_summable hx
  have hs := MultipartiteProfiles.dust_nonneg hx
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1]
  let b := Real.sqrt (∑' k, (x.2 k) ^ 2)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = ∑' k, (x.2 k) ^ 2 := Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg _)
  have hb1 : b < 1 := by nlinarith
  have hpb (k : ℕ) : x.2 k ≤ b := by
    have hk := hsqsum.le_tsum k (fun _ _ => sq_nonneg _)
    nlinarith [hp k]
  have ha : ∀ᶠ t : ℝ in nhds 0, t < (1 - b) / 2 :=
    eventually_lt_nhds (by linarith : (0 : ℝ) < (1 - b) / 2)
  have hct : ContinuousAt (fun t : ℝ => (x.1 + t) / (1 - t)) 0 := by fun_prop (disch := norm_num)
  have hlt : ∀ᶠ t : ℝ in nhds 0, (x.1 + t) / (1 - t) < L :=
    hct.eventually (eventually_lt_nhds (by simpa using hT))
  have hcq : ContinuousAt (fun t : ℝ =>
      ((∑' k, (x.2 k) ^ 2) + 2 * x.2 i * t + t ^ 2) / (1 - t) ^ 2) 0 := by fun_prop (disch := norm_num)
  have hlq : ∀ᶠ t : ℝ in nhds 0,
      ((∑' k, (x.2 k) ^ 2) + 2 * x.2 i * t + t ^ 2) / (1 - t) ^ 2 < 1 :=
    hcq.eventually (eventually_lt_nhds (by simpa using hQ))
  have hcd : ContinuousAt (fun t : ℝ => MultipartiteProfiles.density x +
      ((1 - x.2 i) * t - t ^ 2) / (1 + x.1) ^ 2) 0 := by fun_prop
  have hld : ∀ᶠ t : ℝ in nhds 0, MultipartiteProfiles.density x +
      ((1 - x.2 i) * t - t ^ 2) / (1 + x.1) ^ 2 ∈ Set.Ioo lo hi :=
    hcd.eventually (isOpen_Ioo.mem_nhds (by simpa using hd))
  filter_upwards [ha.filter_mono nhdsWithin_le_nhds, hlt.filter_mono nhdsWithin_le_nhds,
    hlq.filter_mono nhdsWithin_le_nhds, hld.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t hta htl htq htd ht0
  have ht0 : 0 ≤ t := ht0
  have ha0 : 0 < 1 - t := by linarith
  let p := Function.update x.2 i (x.2 i + t)
  have hp' (k : ℕ) : 0 ≤ p k := by
    by_cases hk : k = i
    · subst k; simp only [p, Function.update_self]; linarith [hp i]
    · simpa only [p, Function.update_of_ne hk] using hp k
  have hp1' (k : ℕ) : p k ≤ 1 - t := by
    by_cases hk : k = i
    · subst k; simp only [p, Function.update_self]; linarith [hpb i]
    · simpa only [p, Function.update_of_ne hk] using (by linarith [hpb k] : x.2 k ≤ 1 - t)
  have hpsum : (∑' k, p k) = (∑' k, x.2 k) + t := by
    have h := (hsum.hasSum.update i (x.2 i + t)).tsum_eq
    dsimp [p]
    linarith
  have hpQ : (∑' k, (p k) ^ 2) = (∑' k, (x.2 k) ^ 2) + 2 * x.2 i * t + t ^ 2 := by
    have heq : (fun k => (p k) ^ 2) = Function.update (fun k => (x.2 k) ^ 2) i ((x.2 i + t) ^ 2) := by
      funext k
      by_cases hk : k = i <;> simp [p, hk, Function.update_of_ne]
    rw [heq, (hsqsum.hasSum.update i _).tsum_eq]
    ring
  have htotal : 1 - t + MultipartiteProfiles.dust x + (∑' k, p k) = 1 + x.1 := by
    rw [hpsum, MultipartiteProfiles.dust_eq_sub_tsum hx]
    ring
  have htotal' : (MultipartiteProfiles.dust x + ∑' k, p k) / (1 - t) ≤ L := by
    rw [hpsum, MultipartiteProfiles.dust_eq_sub_tsum hx]
    convert htl.le using 1
    ring
  have hdensity : 1 / 2 - ((1 - t) ^ 2 + ∑' k, (p k) ^ 2) /
      (2 * (1 - t + MultipartiteProfiles.dust x + ∑' k, p k) ^ 2) =
      MultipartiteProfiles.density x + ((1 - x.2 i) * t - t ^ 2) / (1 + x.1) ^ 2 := by
    rw [htotal, hpQ]
    unfold MultipartiteProfiles.density MultipartiteProfiles.missingDensity
    field_simp
    ring
  have hraw := physical_excess_le_maximum hmax (1 - t) ha0 p hp' hp1' (hsum.update i _)
    (MultipartiteProfiles.dust x) hs htotal' (by rw [hpQ]; exact htq.le)
    (by rw [hdensity]; exact ⟨htd.1.le, htd.2.le⟩) hD
  rw [hdensity, htotal, show p = Function.update x.2 i (x.2 i + t) from rfl,
    physicalObjective_one_transfer hD x.2 hp hsum _ i t (by linarith [hp i]), hopt] at hraw
  exact hraw

/-- A right local maximum has a nonpositive right derivative. -/
theorem right_derivative_nonpos_of_local_max {f : ℝ → ℝ} {v : ℝ}
    (hf : HasDerivWithinAt f v (Set.Ici 0) 0)
    (hmax : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0), f t ≤ f 0) : v ≤ 0 := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp
    hf.Ioi_of_Ici
  apply le_of_tendsto ht
  filter_upwards [hmax.filter_mono (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self),
    self_mem_nhdsWithin] with t hft ht0
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hft) (by simpa using le_of_lt ht0)

/-- At an interior actual excess maximum, the old optimal dual's head
multiplier dominates the benchmark's actual right slope. -/
theorem benchmark_slope_le_multiplier {L lo hi : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) (hT : x.1 < L)
    (hQ : (∑' k, (x.2 k) ^ 2) < 1)
    (hd : MultipartiteProfiles.density x ∈ Set.Ioo lo hi)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityWindow L lo hi,
      MultipartiteProfiles.benchmarkExcess y ≤ MultipartiteProfiles.benchmarkExcess x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (ℓ B : ℝ)
    (hrow : headRow x.2 (MultipartiteProfiles.dust x) D i -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 i - 1))
    (hB : HasDerivWithinAt benchmark (-B) (Set.Ici (MultipartiteProfiles.density x))
      (MultipartiteProfiles.density x)) : B ≤ ℓ := by
  let M := 1 + x.1
  have hM : 0 < M := by dsimp [M]; linarith [hx.1.1.1]
  have hpi : x.2 i < 1 := by
    have hk := (MultipartiteProfiles.squares_summable hx).le_tsum i (fun _ _ => sq_nonneg _)
    nlinarith [hx.1.1.2 i]
  let f := fun t : ℝ => (MultipartiteProfiles.limitValue x +
    t * (headRow x.2 (MultipartiteProfiles.dust x) D i -
      anchorRow x.2 (MultipartiteProfiles.dust x) D) - head D i * t ^ 2) / M ^ 2
  let g := fun t : ℝ => MultipartiteProfiles.density x + ((1 - x.2 i) * t - t ^ 2) / M ^ 2
  have hf : HasDerivAt f ((headRow x.2 (MultipartiteProfiles.dust x) D i -
      anchorRow x.2 (MultipartiteProfiles.dust x) D) / M ^ 2) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) (MultipartiteProfiles.limitValue x)).add
      ((hasDerivAt_id 0).const_mul (headRow x.2 (MultipartiteProfiles.dust x) D i -
        anchorRow x.2 (MultipartiteProfiles.dust x) D))).sub
      (((hasDerivAt_id 0).pow 2).const_mul (head D i))).div_const (M ^ 2) using 1 <;>
      simp [f, mul_comm]
  have hg : HasDerivAt g ((1 - x.2 i) / M ^ 2) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (MultipartiteProfiles.density x)).add
      ((((hasDerivAt_id 0).const_mul (1 - x.2 i)).sub
        ((hasDerivAt_id 0).pow 2)).div_const (M ^ 2)) using 1 <;> simp [g]
    rfl
  have hmaps : Set.MapsTo g (Set.Icc 0 (1 - x.2 i))
      (Set.Ici (MultipartiteProfiles.density x)) := by
    intro t ht
    change MultipartiteProfiles.density x ≤ g t
    dsimp [g]
    have hnum : 0 ≤ (1 - x.2 i) * t - t ^ 2 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
    exact le_add_of_nonneg_right (div_nonneg hnum (sq_nonneg _))
  have hcomp := hB.comp_of_eq 0 (hg.hasDerivWithinAt (s := Set.Icc 0 (1 - x.2 i))) hmaps
    (by simp [g])
  have hcomp' : HasDerivWithinAt (benchmark ∘ g) (-B * ((1 - x.2 i) / M ^ 2)) (Set.Ici 0) 0 :=
    hcomp.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith))
  have hlocal := one_transfer_excess_local_max hx hT hQ hd hmax hD hopt i
  have hlocal' : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0),
      (f t - benchmark (g t)) ≤ f 0 - benchmark (g 0) := by
    simpa only [f, g, M, zero_mul, mul_zero, zero_pow (by omega : 2 ≠ 0), add_zero,
      sub_zero, zero_div, MultipartiteProfiles.benchmarkExcess, MultipartiteProfiles.normalizedValue] using hlocal
  have hnonpos := right_derivative_nonpos_of_local_max (hf.hasDerivWithinAt.sub hcomp') hlocal'
  rw [hrow] at hnonpos
  have hscaled := mul_nonpos_of_nonpos_of_nonneg hnonpos (sq_nonneg M)
  field_simp [hM.ne'] at hscaled
  nlinarith

end Erdos1017.MultipartiteCountableDual

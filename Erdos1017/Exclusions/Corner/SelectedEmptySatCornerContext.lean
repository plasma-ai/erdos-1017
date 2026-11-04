module

public import Erdos1017.Exclusions.Common.SelectedEmptySource
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPrimal
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalSATGeometry
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTriangle
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalCliqueRepresentative
public import Erdos1017.Exclusions.Common.Physical.PhysicalTriangleExposure

/-!
# Private source context of the empty-source saturated corner

The private high source is measurable, pays its unit receipt to its head, has
the mass cap from the saturated partner, is a union of positive whole parts, and
its two-point selector refund tests every rest subtuple under the same parent
law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

private theorem singleton_labels (p : S.I) (hp : p ∈ S.eligibleReverseAtom) :
    R.data.plateauLabels {R.data.code p} = {p} := by
  ext q
  rw [R.data.mem_plateauLabels, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, hlabel⟩
    have hi' : i = R.data.code p := Finset.mem_singleton.mp hi
    subst i
    exact Option.some.inj (hlabel.symm.trans (R.data.label_at_code p hp))
  · intro hq
    subst q
    exact ⟨R.data.code p, by simp, R.data.label_at_code p hp⟩

omit [MeasurableSpace Ω] in
private theorem compulsory_singleton_eq_pattern
    (allowed : ℕ → Set Ω) (delta : Ω → ℝ) (i : ℕ) :
    ReverseAssignment.compulsorySource allowed delta {i} =
      ReverseAssignment.finitePattern allowed delta {i} := by
  ext x
  constructor
  · rintro ⟨hd, ⟨j, hj⟩, hall⟩
    have hji : j = i := Finset.mem_singleton.mp (hall j hj)
    refine ⟨hd, fun k => ?_⟩
    constructor
    · intro hk
      have hki : k = i := Finset.mem_singleton.mp hk
      simpa only [hki, hji] using hj
    · exact hall k
  · rintro ⟨hd, hall⟩
    exact ⟨hd, ⟨i, (hall i).mp (by simp)⟩, fun k hk => (hall k).mpr hk⟩

include R in
/-- The entire private HIGH source is measurable even when its head is
not a member of this actual recovered plateau. -/
theorem measurableSet_private_compulsorySource (p : S.I)
    (hp : p ∈ S.eligibleReverseAtom) :
    MeasurableSet (S.reverseCompulsorySource {p}) := by
  have h := R.data.measurableSet_compulsorySource {R.data.code p}
  rwa [R.singleton_labels p hp] at h

/-- Every point in the entire private source pays its full unit receipt
to the same original head in the actual completed assignment. -/
theorem private_compulsorySource_mass_le_receipt (p : S.I)
    (hp : p ∈ S.eligibleReverseAtom) :
    μ.real (S.reverseCompulsorySource {p}) ≤
      ∫ x, R.fractions (R.data.code p) x ∂μ.restrict S.H := by
  let J := S.reverseCompulsorySource {p}
  have hJ : MeasurableSet J := R.measurableSet_private_compulsorySource p hp
  have hsubset : J ⊆ S.H := fun _ hx => hx.1
  have hsource : S.H ∩ ReverseAssignment.compulsorySource R.data.allowed
      R.data.δ {R.data.code p} = J := by
    rw [R.data.compulsorySource_eq_original, R.singleton_labels p hp]
  have hpattern := (ae_restrict_iff' (ReverseAssignment.measurableSet_finitePattern
    R.data.hmeasurableAllowed R.data.hmeasurableδ {R.data.code p})).mp
      (R.feasible.full_pattern {R.data.code p})
  have hle : ∀ᵐ x ∂μ.restrict S.H,
      J.indicator (fun _ => (1 : ℝ)) x ≤ R.fractions (R.data.code p) x := by
    filter_upwards [hpattern, R.feasible.box (R.data.code p)] with x hx hbox
    by_cases hxJ : x ∈ J
    · have hxsource : x ∈ S.H ∩ ReverseAssignment.compulsorySource
          R.data.allowed R.data.δ {R.data.code p} := by rwa [hsource]
      have hxpattern : x ∈ ReverseAssignment.finitePattern R.data.allowed
          R.data.δ {R.data.code p} := by
        rw [← compulsory_singleton_eq_pattern]
        exact hxsource.2
      simpa only [indicator_of_mem hxJ, Finset.sum_singleton] using (hx hxpattern).ge
    · simpa only [indicator_of_notMem hxJ] using hbox.1
  have hint := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hJ)
    (ReverseAssignment.coordinate_integrable R.fractions (R.data.code p)) hle
  rw [integral_indicator hJ, setIntegral_const, smul_eq_mul, mul_one] at hint
  have hmass : (μ.restrict S.H).real J = μ.real J := by
    simp only [measureReal_def, Measure.restrict_apply hJ,
      inter_eq_left.mpr hsubset]
  rwa [hmass] at hint

private theorem two_point_selector_bound (J : Set Ω) (A T : ℝ)
    (G Y : Ω × Ω → ℝ) (f : Ω → ℝ)
    (hf : Integrable f (μ.restrict J))
    (hG : Integrable G ((μ.restrict J).prod (μ.restrict J)))
    (hGY : Integrable (fun z => G z * Y z) ((μ.restrict J).prod (μ.restrict J)))
    (hGbox : ∀ᵐ z ∂(μ.restrict J).prod (μ.restrict J), G z ∈ Icc (0 : ℝ) 1)
    (hsingle : ∀ᵐ x ∂μ.restrict J, f x ≤ T)
    (hpair : ∀ᵐ z ∂(μ.restrict J).prod (μ.restrict J),
      0 < G z → Y z + f z.1 + f z.2 ≤ T)
    (hA : μ.real J ≤ A) :
    (∫ z, G z * Y z ∂(μ.restrict J).prod (μ.restrict J)) / 2 +
        A * (∫ x in J, f x ∂μ) ≤
      (A * μ.real J - (∫ z, G z ∂(μ.restrict J).prod (μ.restrict J)) / 2) * T := by
  let nu := μ.restrict J
  have hf1 : Integrable (fun z : Ω × Ω => f z.1) (nu.prod nu) := by
    simpa only [mul_one] using hf.mul_prod (integrable_const (1 : ℝ))
  have hf2 : Integrable (fun z : Ω × Ω => f z.2) (nu.prod nu) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hf
  have hpoint : ∀ᵐ z ∂nu.prod nu,
      G z * Y z + f z.1 + f z.2 ≤ (2 - G z) * T := by
    filter_upwards [hGbox, hpair, Measure.quasiMeasurePreserving_fst.ae hsingle,
      Measure.quasiMeasurePreserving_snd.ae hsingle] with z hz hp hx hy
    by_cases hg : 0 < G z
    · have hfirst := mul_le_mul_of_nonneg_left (hp hg) hz.1
      have hsecond := mul_le_mul_of_nonneg_left (add_le_add hx hy)
        (sub_nonneg.mpr hz.2)
      nlinarith only [hfirst, hsecond]
    · have he : G z = 0 := le_antisymm (le_of_not_gt hg) hz.1
      rw [he]
      nlinarith only [hx, hy]
  have hmain := integral_mono_ae ((hGY.add hf1).add hf2)
    (((integrable_const (2 : ℝ)).sub hG).mul_const T) hpoint
  have hmass : nu.real univ = μ.real J := by simp [nu, measureReal_def]
  have hprod : (nu.prod nu).real univ = (μ.real J) ^ 2 := by
    rw [← univ_prod_univ, measureReal_prod_prod, hmass, pow_two]
  have hfirst : (∫ z : Ω × Ω, f z.1 ∂nu.prod nu) =
      μ.real J * (∫ x in J, f x ∂μ) := by
    simpa only [mul_one, integral_const, smul_eq_mul, hmass, mul_comm, one_mul]
      using (integral_prod_mul (μ := nu) (ν := nu) f (fun _ => (1 : ℝ)))
  have hsecond : (∫ z : Ω × Ω, f z.2 ∂nu.prod nu) =
      μ.real J * (∫ x in J, f x ∂μ) := by
    simpa only [one_mul, integral_const, smul_eq_mul, mul_one, hmass]
      using (integral_prod_mul (μ := nu) (ν := nu) (fun _ => (1 : ℝ)) f)
  have hleft1 := integral_add (hGY.add hf1) hf2
  have hleft2 := integral_add hGY hf1
  have hright := integral_sub (integrable_const (2 : ℝ)) hG
  dsimp only [Pi.add_apply, Pi.sub_apply] at hmain hleft1 hleft2 hright
  rw [hleft1, hleft2, hfirst, hsecond, integral_mul_const, hright,
    integral_const, smul_eq_mul, hprod] at hmain
  have hsingleint := integral_mono_ae hf (integrable_const T) hsingle
  rw [setIntegral_const, smul_eq_mul] at hsingleint
  have hremaining := mul_le_mul_of_nonneg_left hsingleint (sub_nonneg.mpr hA)
  nlinarith only [hmain, hremaining]

omit [MeasurableSpace Ω] in
private theorem context_clique_cons (G : Ω × Ω → Bool)
    (hsym : ∀ x y, G (x, y) = G (y, x)) {n : ℕ} (v : Fin n → Ω)
    (hv : PhysicalCliqueRepresentative.Clique G v) (z : Ω)
    (hz : ∀ i, G (z, v i) = true) :
    PhysicalCliqueRepresentative.Clique G (Fin.cons z v) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => exact hz j
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa only [Fin.cons_succ, Fin.cons_zero, hsym] using hz i
    | succ j => exact hv i j (fun h => hij (congrArg Fin.succ h))

private theorem context_source_tests (I J : Set Ω) (hI : μ I ≠ 0)
    (hJ : MeasurableSet J) (G : Ω × Ω → Bool) (Y : Ω × Ω → ℝ) (beta : Ω → ℝ)
    (hGsym : ∀ x y, G (x, y) = G (y, x))
    (hYsym : ∀ x y, Y (x, y) = Y (y, x))
    (htest : ∀ n (v : Fin n → Ω), PhysicalCliqueRepresentative.Clique G v →
      PhysicalPrimal.charge Y v ≤ 1)
    (hroot : ∀ᵐ x ∂μ, x ∈ J → ∀ᵐ z ∂μ,
      z ∈ I → G (z, x) = true ∧ Y (z, x) = beta x)
    {n : ℕ} (v : Fin n → Ω) (hv : PhysicalCliqueRepresentative.Clique G v)
    (hrootold : ∀ᵐ z ∂μ, z ∈ I → ∀ i,
      G (z, v i) = true ∧ Y (z, v i) = beta (v i))
    (hjoinold : ∀ᵐ x ∂μ, x ∈ J → ∀ i, G (x, v i) = true) :
    let f := fun x => beta x + ∑ i, Y (x, v i)
    let T := 1 - PhysicalPrimal.charge Y v - ∑ i, beta (v i)
    (∀ᵐ x ∂μ.restrict J, f x ≤ T) ∧
      ∀ᵐ q ∂(μ.restrict J).prod (μ.restrict J),
        0 < PhysicalCliqueRepresentative.edgeIndicator G q →
          Y q + f q.1 + f q.2 ≤ T := by
  dsimp only
  have hsingle : ∀ᵐ x ∂μ.restrict J,
      beta x + ∑ i, Y (x, v i) ≤
        1 - PhysicalPrimal.charge Y v - ∑ i, beta (v i) := by
    filter_upwards [ae_restrict_of_ae hroot, ae_restrict_of_ae hjoinold,
      ae_restrict_mem hJ] with x hx hj hxJ
    have hjoin := hj hxJ
    obtain ⟨z, hzI, hzold, hzx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hI
      ((ae_restrict_of_ae hrootold).and (ae_restrict_of_ae (hx hxJ)))
    have hfirst := context_clique_cons G hGsym v hv x hjoin
    have hsecond := context_clique_cons G hGsym (Fin.cons x v) hfirst z (by
      intro i
      cases i using Fin.cases with
      | zero => exact (hzx hzI).1
      | succ i => exact (hzold hzI i).1)
    have hb := htest _ _ hsecond
    rw [PhysicalTriangleExposure.charge_cons Y hYsym,
      PhysicalTriangleExposure.charge_cons Y hYsym, Fin.sum_univ_succ] at hb
    have hsum : (∑ i, Y (z, v i)) = ∑ i, beta (v i) :=
      Finset.sum_congr rfl (fun i _ => (hzold hzI i).2)
    simp only [Fin.cons_zero, Fin.cons_succ] at hb
    rw [hsum, (hzx hzI).2] at hb
    linarith only [hb]
  refine ⟨hsingle, ?_⟩
  have hnew : ∀ᵐ x ∂μ.restrict J,
      (∀ᵐ z ∂μ, z ∈ I → G (z, x) = true ∧ Y (z, x) = beta x) ∧
        ∀ i, G (x, v i) = true := by
    filter_upwards [ae_restrict_of_ae hroot, ae_restrict_of_ae hjoinold,
      ae_restrict_mem hJ] with x hx hj hxJ
    exact ⟨hx hxJ, hj hxJ⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnew,
    Measure.quasiMeasurePreserving_snd.ae hnew] with q hx hy hpos
  have hedge : G q = true := by
    by_contra hh
    have hf : G q = false := Bool.eq_false_iff.mpr hh
    simp only [PhysicalCliqueRepresentative.edgeIndicator, hf,
      Bool.false_eq_true, ite_false, lt_self_iff_false] at hpos
  obtain ⟨z, hzI, hzold, hzx, hzy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hI
    ((ae_restrict_of_ae hrootold).and ((ae_restrict_of_ae hx.1).and
      (ae_restrict_of_ae hy.1)))
  have hyclique := context_clique_cons G hGsym v hv q.2 hy.2
  have hxclique := context_clique_cons G hGsym (Fin.cons q.2 v) hyclique q.1 (by
    intro i
    cases i using Fin.cases with
    | zero => exact hedge
    | succ i => exact hx.2 i)
  have hzclique := context_clique_cons G hGsym (Fin.cons q.1 (Fin.cons q.2 v))
    hxclique z (by
      intro i
      cases i using Fin.cases with
      | zero => exact (hzx hzI).1
      | succ i =>
        cases i using Fin.cases with
        | zero => exact (hzy hzI).1
        | succ i => exact (hzold hzI i).1)
  have hb := htest _ _ hzclique
  rw [PhysicalTriangleExposure.charge_cons Y hYsym,
    PhysicalTriangleExposure.charge_cons Y hYsym,
    PhysicalTriangleExposure.charge_cons Y hYsym] at hb
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hb
  have hsum : (∑ i, Y (z, v i)) = ∑ i, beta (v i) :=
    Finset.sum_congr rfl (fun i _ => (hzold hzI i).2)
  rw [hsum, (hzx hzI).2, (hzy hzI).2] at hb
  change Y q + (beta q.1 + ∑ i, Y (q.1, v i)) +
    (beta q.2 + ∑ i, Y (q.2, v i)) ≤ _
  linarith only [hb]

private theorem context_selector_integral (I J : Set Ω) (hI : μ I ≠ 0)
    (hJ : MeasurableSet J) (A : ℝ) (hA : μ.real J ≤ A)
    (G : Ω × Ω → Bool) (Y : Ω × Ω → ℝ) (beta : Ω → ℝ)
    (hG : Measurable G) (hY : Measurable Y) (B : ℝ) (hB : ∀ z, |Y z| ≤ B)
    (hbeta : Integrable beta (μ.restrict J))
    (hGsym : ∀ x y, G (x, y) = G (y, x))
    (hYsym : ∀ x y, Y (x, y) = Y (y, x))
    (hzero : ∀ z, G z = false → Y z = 0)
    (htest : ∀ n (v : Fin n → Ω), PhysicalCliqueRepresentative.Clique G v →
      PhysicalPrimal.charge Y v ≤ 1)
    (hroot : ∀ᵐ x ∂μ, x ∈ J → ∀ᵐ z ∂μ,
      z ∈ I → G (z, x) = true ∧ Y (z, x) = beta x)
    {n : ℕ} (v : Fin n → Ω) (hv : PhysicalCliqueRepresentative.Clique G v)
    (hrootold : ∀ᵐ z ∂μ, z ∈ I → ∀ i,
      G (z, v i) = true ∧ Y (z, v i) = beta (v i))
    (hjoinold : ∀ᵐ x ∂μ, x ∈ J → ∀ i, G (x, v i) = true) :
    (∫ z, Y z ∂(μ.restrict J).prod (μ.restrict J)) / 2 +
        A * (∫ x in J, beta x ∂μ) + A * (∑ i, ∫ x in J, Y (x, v i) ∂μ) ≤
      (A * μ.real J - (∫ z, PhysicalCliqueRepresentative.edgeIndicator G z
        ∂(μ.restrict J).prod (μ.restrict J)) / 2) *
        (1 - PhysicalPrimal.charge Y v - ∑ i, beta (v i)) := by
  let G0 := PhysicalCliqueRepresentative.edgeIndicator G
  let f := fun x => beta x + ∑ i, Y (x, v i)
  let T := 1 - PhysicalPrimal.charge Y v - ∑ i, beta (v i)
  have hYi (nu : Measure (Ω × Ω)) [IsFiniteMeasure nu] : Integrable Y nu :=
    Integrable.of_bound hY.aestronglyMeasurable B
      (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB z))
  have hYsection (i : Fin n) : Integrable (fun x => Y (x, v i)) (μ.restrict J) := by
    apply Integrable.of_bound
      (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
    exact Eventually.of_forall (fun x => by
      change ‖Y (x, v i)‖ ≤ B
      simpa only [Real.norm_eq_abs] using hB (x, v i))
  have hsum : Integrable (fun x => ∑ i, Y (x, v i)) (μ.restrict J) :=
    integrable_finsetSum _ (fun i _ => hYsection i)
  have hf : Integrable f (μ.restrict J) := hbeta.add hsum
  have hG0 : Integrable G0 ((μ.restrict J).prod (μ.restrict J)) := by
    apply Integrable.of_bound
      (PhysicalCliqueRepresentative.measurable_edgeIndicator hG).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (PhysicalCliqueRepresentative.edgeIndicator_bounds G z).1]
      exact (PhysicalCliqueRepresentative.edgeIndicator_bounds G z).2)
  have hGY : (fun z => G0 z * Y z) = Y := by
    funext z
    by_cases he : G z = true
    · simp only [G0, PhysicalCliqueRepresentative.edgeIndicator, he, ite_true, one_mul]
    · have he' : G z = false := Bool.eq_false_iff.mpr he
      have hz : G0 z = 0 := ite_eq_right he
      rw [hz, zero_mul]
      exact (hzero z he').symm
  obtain ⟨hsingle, hpair⟩ := context_source_tests I J hI hJ G Y beta hGsym hYsym
    htest hroot v hv hrootold hjoinold
  have hb := two_point_selector_bound J A T G0 Y f hf hG0
    (by rw [hGY]; exact hYi _)
    (Eventually.of_forall (PhysicalCliqueRepresentative.edgeIndicator_bounds G))
    hsingle hpair hA
  rw [hGY] at hb
  have hfint : (∫ x in J, f x ∂μ) = (∫ x in J, beta x ∂μ) +
      ∑ i, ∫ x in J, Y (x, v i) ∂μ := by
    rw [show f = fun x => beta x + ∑ i, Y (x, v i) from rfl,
      integral_add hbeta hsum, integral_finsetSum _ (fun i _ => hYsection i)]
  rw [hfint] at hb
  dsimp only [T, G0] at hb
  linarith only [hb]

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The same null-source recovered endpoint strictly bounds its other
head together with that head's entire private source. No source subset or
new assignment is selected. -/
theorem empty_source_private_head_mass_lt (r p : S.I) (hpr : p ≠ r)
    (hp : p ∈ S.eligibleReverseAtom) (hr : R.plateau = {r})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    S.originalAtomMass p + μ.real (S.reverseCompulsorySource {p}) <
      S.originalAtomMass r := by
  have hreceipt := R.private_compulsorySource_mass_le_receipt p hp
  have hbase : R.data.a (R.data.code p) = S.originalAtomMass p := by
    rw [R.data.ha, reverseAtomMass, R.data.label_at_code p hp]
    rfl
  have hmass : S.reverseClassMass R.flow p = ReverseAssignment.mass R.data.a
      R.fractions (R.data.code p) := R.data.completedFlow_classMass hW R.fractions
    R.feasible R.full_atomic R.zero_diffuse p
  have hnot : p ∉ R.plateau := by simpa only [hr, Finset.mem_singleton] using hpr
  have hstrict : S.reverseClassMass R.flow p < R.height :=
    lt_of_le_of_ne (R.classMass_le hW p) (fun he => hnot ((R.classMass_eq_iff hW p).mp he))
  rw [R.empty_source_height_eq_original_mass r hr hnull] at hstrict
  rw [hmass, ReverseAssignment.mass, hbase] at hstrict
  change S.originalAtomMass p +
    (∫ x, R.fractions (R.data.code p) x ∂μ.restrict S.H) < S.originalAtomMass r at hstrict
  linarith only [hreceipt, hstrict]

private theorem cost_of_joint_context_quota
    {c A b K C0 gap DJ cP cH cU WP sigmaP t eta Uload Rctx : ℝ}
    (hK : 0 < K) (hC0 : 0 < C0) (heta : 0 < eta)
    (hC0K : C0 ≤ K) (ht : 0 ≤ t) (hDJ : 0 ≤ DJ)
    (hcP : 0 ≤ cP) (hcU : 0 ≤ cU) (hWP : 0 ≤ WP)
    (hprice : 2 * K * t ≤ 3 * C0)
    (hcount : c ≤ A * b + K + gap + cP + cH + cU)
    (hcontext : gap * C0 + K * (DJ + cP - sigmaP) ≤ Rctx)
    (hsigma : eta * sigmaP ≤ t * (WP - cP))
    (hquota : 3 * WP + 2 * eta * cH + 12 * eta * cU ≤ Uload) :
    c ≤ A * b + K + Rctx / C0 + Uload / (2 * eta) := by
  have hscale : 0 < 2 * eta * C0 := by positivity
  have hcount' := mul_le_mul_of_nonneg_left hcount hscale.le
  have hcontext' := mul_le_mul_of_nonneg_left hcontext (show 0 ≤ 2 * eta by positivity)
  have hsigma' := mul_le_mul_of_nonneg_left hsigma (show 0 ≤ 2 * K by positivity)
  have hquota' := mul_le_mul_of_nonneg_left hquota hC0.le
  have hcoeff : 0 ≤ K * (eta + t) - eta * C0 := by
    nlinarith only [mul_nonneg hK.le ht, mul_nonneg heta.le (sub_nonneg.mpr hC0K)]
  have hp := mul_nonneg hcoeff hcP
  have hq := mul_nonneg (sub_nonneg.mpr hprice) hWP
  have hr := mul_nonneg (show 0 ≤ eta * C0 by positivity) hcU
  have hs := mul_nonneg (show 0 ≤ eta * K by positivity) hDJ
  have hbound : 2 * eta * C0 * (c - A * b - K) ≤ 2 * eta * Rctx + C0 * Uload := by
    nlinarith only [hcount', hcontext', hsigma', hquota', hp, hq, hr, hs]
  have hid : (Rctx / C0 + Uload / (2 * eta)) * (2 * eta * C0) =
      2 * eta * Rctx + C0 * Uload := by
    field_simp
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith only [hbound, hid]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The actual saturated partner pays eligibility and the strict entire
private-source mass cap in the same original empty-source recovery. -/
theorem saturated_empty_source_private_mass (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (hr : R.plateau = {r})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    MeasurableSet (S.reverseCompulsorySource {p}) ∧
      S.originalAtomMass p + μ.real (S.reverseCompulsorySource {p}) <
        S.originalAtomMass r := by
  have hp : p ∈ S.eligibleReverseAtom := by
    have hzero := hpair.symm.high_head_null hW hd hgap hell
    change ∀ᵐ x ∂μ.restrict {x | S.ρ x = p.val}, x ∉ S.H
    rw [ae_iff]
    simp only [not_not, ofPred_mem_eq]
    rw [Measure.restrict_apply S.hpartition.1, inter_comm]
    exact hzero
  exact ⟨R.measurableSet_private_compulsorySource p hp,
    R.empty_source_private_head_mass_lt r p hpair.1.symm hp hr hW hnull⟩

/-- The nonempty zero/one/two-point source selector has its exact refund.
All source clique tests come from the original universal triangle, and
the same recovered endpoint supplies the full private-source mass cap. -/
theorem empty_source_private_selector_bound (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (hr : R.plateau = {r})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    let A := S.originalAtomMass r
    let J := S.reverseCompulsorySource {p}
    let G := PhysicalCliqueRepresentative.edgeIndicator
      (Function.uncurry (PhysicalRepresentative.adjacency W m))
    (∫ z, PhysicalRepresentative.charge W m z.1 z.2
        ∂(μ.restrict J).prod (μ.restrict J)) / 2 +
        A * (∫ x in J, S.rootChargeRow r x ∂μ) ≤
      A * μ.real J - (∫ z, G z ∂(μ.restrict J).prod (μ.restrict J)) / 2 := by
  let A := S.originalAtomMass r
  let J := S.reverseCompulsorySource {p}
  let g := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let G := PhysicalCliqueRepresentative.edgeIndicator g
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let beta := S.rootChargeRow r
  let nu := μ.restrict J
  obtain ⟨hJ, hmass⟩ := R.saturated_empty_source_private_mass r p hpair hr hW hd hgap hell hnull
  have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
  have hA : μ.real J ≤ A := by
    have hb : 0 ≤ S.originalAtomMass p := measureReal_nonneg
    dsimp only [J, A]
    linarith only [hmass, hb]
  have hf : Integrable beta nu := by
    apply Integrable.of_bound (S.measurable_rootChargeRow r).aestronglyMeasurable 3
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(S.rootChargeRow_mem_Icc r x).1,
        (S.rootChargeRow_mem_Icc r x).2.trans (by norm_num)⟩)
  have hG : Integrable G (nu.prod nu) := by
    apply Integrable.of_bound
      (PhysicalCliqueRepresentative.measurable_edgeIndicator
        (PhysicalRepresentative.measurable_adjacency W m)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (PhysicalCliqueRepresentative.edgeIndicator_bounds g z).1]
      exact (PhysicalCliqueRepresentative.edgeIndicator_bounds g z).2)
  have hY : Integrable Y (nu.prod nu) := by
    apply Integrable.of_bound (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    exact Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs, Function.uncurry] using
        PhysicalRepresentative.charge_bound W m z.1 z.2)
  have hGY : (fun z => G z * Y z) = Y := by
    funext z
    cases he : g z with
    | false =>
      have hy := PhysicalRepresentative.charge_zero_of_nonedge W m z.1 z.2 he
      simp only [G, PhysicalCliqueRepresentative.edgeIndicator, he, Bool.false_eq_true,
        ite_false, zero_mul]
      exact hy.symm
    | true => simp only [G, PhysicalCliqueRepresentative.edgeIndicator, he, ite_true, one_mul]
  have hGYint : Integrable (fun z => G z * Y z) (nu.prod nu) := by rwa [hGY]
  have houtside : ∀ᵐ x ∂nu, S.ρ x ≠ r.val := by
    filter_upwards [ae_restrict_of_ae
      (S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell),
      ae_restrict_mem hJ] with x hx hxJ hxr
    exact hx hxJ (Or.inl (Or.inl hxr))
  have hpairtest : ∀ᵐ z ∂nu.prod nu,
      0 < G z → Y z + beta z.1 + beta z.2 ≤ 1 := by
    filter_upwards [ae_mono
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (S.ae_universal_root_triangle r hW hd hgap hN),
      Measure.quasiMeasurePreserving_fst.ae houtside,
      Measure.quasiMeasurePreserving_snd.ae houtside] with z hz hx hy hpos
    have hedge : g z = true := by
      cases he : g z
      · simp only [G, PhysicalCliqueRepresentative.edgeIndicator, he,
          Bool.false_eq_true, ite_false, lt_self_iff_false] at hpos
      · rfl
    have ht := hz hx hy hedge
    change beta z.1 + beta z.2 + Y z ≤ 1 at ht
    linarith only [ht]
  have hbound := two_point_selector_bound J A 1 G Y beta hf hG hGYint
    (Eventually.of_forall (fun z => PhysicalCliqueRepresentative.edgeIndicator_bounds g z))
    (Eventually.of_forall (fun x => (S.rootChargeRow_mem_Icc r x).2)) hpairtest hA
  rw [hGY, mul_one] at hbound
  exact hbound

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The entire private source is a union of original positive whole parts
modulo one product-null event; diffuse points remain genuine dust. -/
theorem ae_private_source_sameAtom (p : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ z ∂μ.prod μ, z ∈ S.sameAtomRelation →
      (z.1 ∈ S.reverseCompulsorySource {p} ↔
        z.2 ∈ S.reverseCompulsorySource {p}) := by
  let : Countable S.I := S.hI.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ k : S.I, S.ρ x = k.val →
      (x ∈ S.reverseCompulsorySource {p} ↔ S.fiberCompulsoryPredicate k {p}) := by
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (S.hfibers k.val k.property).1).mp
      (S.ae_compulsorySource_iff_fiberPredicate k {p} hW)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hall,
    Measure.quasiMeasurePreserving_snd.ae hall] with z hx hy hz
  let k : S.I := ⟨S.ρ z.1, hz.2⟩
  exact (hx k rfl).trans (hy k hz.1.symm).symm

/-- The actual private-source graph marginal removes exactly the original
own independent part, with mass zero on the diffuse remainder. -/
theorem ae_private_source_graph_marginal (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
      (∫ y in S.reverseCompulsorySource {p},
        PhysicalCliqueRepresentative.edgeIndicator
          (Function.uncurry (PhysicalRepresentative.adjacency W m)) (x, y) ∂μ) =
        μ.real (S.reverseCompulsorySource {p}) - S.ownIndependentMass x := by
  let J := S.reverseCompulsorySource {p}
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
  have hsource := S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
  have hraw := PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have hpoint : ∀ᵐ z ∂μ.prod μ, z.1 ∈ J →
      J.indicator (fun y => 1 - G (z.1, y)) z.2 =
        {y | (y, z.1) ∈ S.sameAtomRelation}.indicator (fun _ => (1 : ℝ)) z.2 := by
    filter_upwards [ae_private_source_sameAtom p hW,
      S.ae_universalPartnerHole_missing_iff_sameAtom r p hpair hW hd hgap hell,
      Measure.quasiMeasurePreserving_fst.ae hsource,
      Measure.quasiMeasurePreserving_snd.ae hsource, hraw]
      with z hwhole hmissing hx hy hphys hxJ
    have hphys' : adjacencyKernel W z.1 z.2 = G z := hphys
    have hswap : (z.2, z.1) ∈ S.sameAtomRelation ↔ z ∈ S.sameAtomRelation := by
      constructor
      · rintro ⟨he, hi⟩
        exact ⟨he.symm, he ▸ hi⟩
      · rintro ⟨he, hi⟩
        exact ⟨he.symm, he ▸ hi⟩
    by_cases hyJ : z.2 ∈ J
    · rw [indicator_of_mem hyJ]
      have hm := hmissing (hx hxJ) (hy hyJ)
      by_cases hs : z ∈ S.sameAtomRelation
      · rw [indicator_of_mem (show z.2 ∈ {y | (y, z.1) ∈ S.sameAtomRelation} from
          hswap.mpr hs)]
        have hz : adjacencyKernel W z.1 z.2 = 0 := hm.mpr hs
        have hg : G z = 0 := hphys'.symm.trans hz
        rw [hg]
        norm_num
      · rw [indicator_of_notMem (show z.2 ∉ {y | (y, z.1) ∈ S.sameAtomRelation} from
          fun hh => hs (hswap.mp hh))]
        have hn : adjacencyKernel W z.1 z.2 ≠ 0 := fun hh => hs (hm.mp hh)
        have hg : G z = 1 := by
          have hcases : G z = 0 ∨ G z = 1 := by
            by_cases he : Function.uncurry (PhysicalRepresentative.adjacency W m) z = true
            · exact Or.inr (ite_eq_left he)
            · exact Or.inl (ite_eq_right he)
          exact hcases.resolve_left (fun hh => hn (hphys'.trans hh))
        rw [hg]
        norm_num
    · rw [indicator_of_notMem hyJ,
        indicator_of_notMem (show z.2 ∉ {y | (y, z.1) ∈ S.sameAtomRelation} from by
          intro hs
          exact hyJ ((hwhole (hswap.mp hs)).mp hxJ))]
  apply (ae_restrict_iff' hJ).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod hpoint] with x hx hxJ
  have hrow := hx.mono (fun _ hy => hy hxJ)
  have hsame : MeasurableSet {y | (y, x) ∈ S.sameAtomRelation} :=
    measurable_prodMk_right S.measurableSet_sameAtomRelation
  have hmass : (∫ y in J, 1 - G (x, y) ∂μ) = S.ownIndependentMass x := by
    have hi := integral_congr_ae hrow
    rw [integral_indicator hJ, integral_indicator hsame, setIntegral_const,
      smul_eq_mul, mul_one] at hi
    exact hi
  have hG : Integrable (fun y => G (x, y)) (μ.restrict J) := by
    apply Integrable.of_bound
      ((PhysicalCliqueRepresentative.measurable_edgeIndicator
        (PhysicalRepresentative.measurable_adjacency W m)).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun y => by
      change ‖G (x, y)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg
        (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).1]
      exact (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).2)
  rw [integral_sub (integrable_const (1 : ℝ)) hG, setIntegral_const,
    smul_eq_mul, mul_one] at hmass
  linarith only [hmass]


private theorem ae_source_join_context (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.reverseCompulsorySource {p} →
      q.2 ∉ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
        S.reverseCompulsorySource {p} →
      PhysicalRepresentative.adjacency W m q.1 q.2 = true := by
  filter_upwards [S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell
      |> Measure.quasiMeasurePreserving_fst.ae,
    ae_private_source_sameAtom p hW,
    S.ae_universalPartnerHole_missing_iff_sameAtom r p hpair hW hd hgap hell,
    S.ae_partner_compulsorySource_joined_common r p hpair hW hd hgap hell,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support]
    with q hsource hwhole hmissing hcommon hphys hx hq
  by_contra hn
  have hf : PhysicalRepresentative.adjacency W m q.1 q.2 = false :=
    Bool.eq_false_iff.mpr hn
  have hzero : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 = _ at hphys
    rw [hphys, hf]
    norm_num
  by_cases hyH : q.2 ∈ S.universalPartnerHoleRegion r p
  · have hs := (hmissing (hsource hx) hyH).mp hzero
    exact hq (Or.inr ((hwhole hs).mp hx))
  · have hyU : q.2 ∈ S.universalPartnerCommonRegion r p := by
      intro hy
      rcases hy with (hr | hp) | hH
      · exact hq (Or.inl (Or.inl hr))
      · exact hq (Or.inl (Or.inr hp))
      · exact hyH hH
    have hone := hcommon hx hyU
    linarith only [hone, hzero]

/-- The exact two-point source refund tests every old rest subtuple under
the same actual parent law. All original signed charges and product
moments are retained, including singular parent laws and genuine dust. -/
theorem empty_source_context_selector (R : S.ReverseRecovery) (r p : S.I)
    (hr : R.plateau = {r}) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) (n : ℕ) :
    let A := S.originalAtomMass r
    let J := S.reverseCompulsorySource {p}
    let G := PhysicalCliqueRepresentative.edgeIndicator
      (Function.uncurry (PhysicalRepresentative.adjacency W m))
    let Y := Function.uncurry (PhysicalRepresentative.charge W m)
    ∀ᵐ v ∂P.laws n, ∀ k (e : Fin k ↪ Fin n),
      (∀ i, v (e i) ∉ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪ J) →
      (∫ z, Y z ∂(μ.restrict J).prod (μ.restrict J)) / 2 +
          A * (∫ x in J, S.rootChargeRow r x ∂μ) +
          A * (∑ i, ∫ x in J, Y (x, v (e i)) ∂μ) ≤
        (A * μ.real J - (∫ z, G z ∂(μ.restrict J).prod (μ.restrict J)) / 2) *
          (1 - PhysicalPrimal.charge Y (fun i => v (e i)) -
            ∑ i, S.rootChargeRow r (v (e i))) := by
  dsimp only
  by_cases hn : 2 ≤ n
  · let I := {x | S.ρ x = r.val}
    let J := S.reverseCompulsorySource {p}
    let Q := ((I ∪ {x | S.ρ x = p.val}) ∪ J)ᶜ
    let G0 := Function.uncurry (PhysicalRepresentative.adjacency W m)
    let Y0 := Function.uncurry (PhysicalRepresentative.charge W m)
    let beta := S.rootChargeRow r
    have hJ : MeasurableSet J := S.measurableSet_reverseCompulsorySource {p}
    have hI : μ I ≠ 0 := (S.hfibers r.val r.property).2.1.ne'
    have hN := R.empty_source_head_neutral r hr hW hd hgap hnull
    have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
        PhysicalCliqueRepresentative.Clique G0 v → PhysicalPrimal.charge Y0 v ≤ 1 := by
      intro k _
      filter_upwards [PhysicalRepresentative.full_feasible W hW.full m
        (hW.strict_gap_structure hd hgap).strict_support hW.deterministic k]
        with v hv hclique
      rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
      exact hv hclique
    obtain ⟨G, Y, hG, hY, hGae, hYae, hGsym, hYsym, _, hzero, hB, htest⟩ :=
      PhysicalCliqueRepresentative.exists_everywhere_representative μ
        (PhysicalRepresentative.measurable_adjacency W m)
        (PhysicalRepresentative.measurable_charge W m)
        (fun z => PhysicalRepresentative.adjacency_symm W m z.2 z.1)
        (fun z => PhysicalRepresentative.charge_symm W m z.2 z.1)
        (fun z => PhysicalRepresentative.charge_zero_of_nonedge W m z.1 z.2)
        3 (by norm_num) (fun z => PhysicalRepresentative.charge_bound W m z.1 z.2) htest
    have hroot : ∀ᵐ q ∂μ.prod μ, q.1 ∈ I → q.2 ∉ I →
        G q = true ∧ Y q = beta q.2 := by
      filter_upwards [S.neutral_atom_physical_adjacency r hW hd hgap hN,
        S.ae_root_charge r hW hd hgap, hGae, hYae]
        with q ha hy hg he hx hn
      exact ⟨hg.trans ((ha hx).mpr hn), he.trans (hy hx)⟩
    have hjoin : ∀ᵐ q ∂μ.prod μ, q.1 ∈ J → q.2 ∈ Q → G q = true := by
      filter_upwards [ae_source_join_context r p hpair hW hd hgap hell, hGae]
        with q hj hg hx hy
      exact hg.trans (hj hx hy)
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
    have hrootsec := Measure.ae_ae_of_ae_prod (hswap.ae hroot)
    have hjoinsec := Measure.ae_ae_of_ae_prod (hswap.ae hjoin)
    have hYsec := Measure.ae_ae_of_ae_prod (hswap.ae hYae)
    let Good := fun x =>
      (∀ᵐ z ∂μ, z ∈ I → x ∉ I → G (z, x) = true ∧ Y (z, x) = beta x) ∧
      (∀ᵐ z ∂μ, z ∈ J → x ∈ Q → G (z, x) = true) ∧
      ∀ᵐ z ∂μ, Y (z, x) = Y0 (z, x)
    have hgood : ∀ᵐ x ∂μ, Good x := by
      filter_upwards [hrootsec, hjoinsec, hYsec] with x hx hy hz
      exact ⟨hx, hy, hz⟩
    have hpairs : ∀ i j : Fin n, i ≠ j →
        (P.laws n).map (fun v => (v i, v j)) ≪ μ.prod μ := by
      intro i j hij
      exact (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
        P.feasible.2.2.2 n ⟨(i, j), hij⟩).trans Measure.absolutelyContinuous_restrict
    have hcoordinates : ∀ᵐ v ∂P.laws n, ∀ i, Good (v i) := by
      apply ae_all_iff.mpr
      intro i
      exact ae_of_ae_map (measurable_pi_apply i).aemeasurable
        ((PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs
          μ hn (P.laws n) hpairs i).ae_le hgood)
    have hpairdata : ∀ᵐ v ∂P.laws n, ∀ i j, i ≠ j →
        G (v i, v j) = G0 (v i, v j) ∧ Y (v i, v j) = Y0 (v i, v j) :=
      PhysicalPrimal.ae_all_pairs_of_balance P.laws _ P.feasible.2.2.2 _
        (ae_restrict_of_ae (hGae.and hYae)) n
    have hrootJ : ∀ᵐ x ∂μ, x ∈ J → ∀ᵐ z ∂μ,
        z ∈ I → G (z, x) = true ∧ Y (z, x) = beta x := by
      filter_upwards [hrootsec,
        S.ae_partner_compulsorySource_subset_hole r p hpair hW hd hgap hell]
        with x hx hsrc hxJ
      have hxI : x ∉ I := fun h => hsrc hxJ (Or.inl (Or.inl h))
      exact hx.mono (fun _ hz hzI => hz hzI hxI)
    have hbeta : Integrable beta (μ.restrict J) := by
      apply Integrable.of_bound (S.measurable_rootChargeRow r).aestronglyMeasurable 3
      exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨(S.rootChargeRow_mem_Icc r x).1,
          (S.rootChargeRow_mem_Icc r x).2.trans (by norm_num)⟩)
    have hAj : μ.real J ≤ S.originalAtomMass r := by
      have hm := (R.saturated_empty_source_private_mass r p hpair hr hW hd hgap hell hnull).2
      have hb : 0 ≤ S.originalAtomMass p := measureReal_nonneg
      linarith only [hm, hb]
    filter_upwards [hcoordinates, hpairdata, P.feasible.2.2.1 n] with v hv hp hc k e hQ
    let w := fun i : Fin k => v (e i)
    have hw : PhysicalCliqueRepresentative.Clique G w := by
      intro i j hij
      exact (hp (e i) (e j) (fun h => hij (e.injective h))).1.trans
        (hc (e i) (e j) (fun h => hij (e.injective h)))
    have hrootold : ∀ᵐ z ∂μ, z ∈ I → ∀ i,
        G (z, w i) = true ∧ Y (z, w i) = beta (w i) := by
      have hh := ae_all_iff.mpr (fun i : Fin k => (hv (e i)).1)
      filter_upwards [hh] with z hz hzI i
      exact hz i hzI (fun hi => hQ i (Or.inl (Or.inl hi)))
    have hjoinold : ∀ᵐ x ∂μ, x ∈ J → ∀ i, G (x, w i) = true := by
      have hh := ae_all_iff.mpr (fun i : Fin k => (hv (e i)).2.1)
      filter_upwards [hh] with x hx hxJ i
      exact hx i hxJ (hQ i)
    have hb := context_selector_integral I J hI hJ (S.originalAtomMass r) hAj
      G Y beta hG hY 3 hB hbeta (fun x y => hGsym (y, x))
      (fun x y => hYsym (y, x)) hzero htest hrootJ w hw hrootold hjoinold
    have hYJJ : (∫ z, Y z ∂(μ.restrict J).prod (μ.restrict J)) =
        ∫ z, Y0 z ∂(μ.restrict J).prod (μ.restrict J) :=
      integral_congr_ae (ae_mono
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hYae)
    have hGJJ : (∫ z, PhysicalCliqueRepresentative.edgeIndicator G z
        ∂(μ.restrict J).prod (μ.restrict J)) =
        ∫ z, PhysicalCliqueRepresentative.edgeIndicator G0 z
          ∂(μ.restrict J).prod (μ.restrict J) :=
      integral_congr_ae (ae_mono
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (hGae.mono (fun _ h => congrArg (fun b : Bool => if b then (1 : ℝ) else 0) h)))
    have hstars : (∑ i, ∫ x in J, Y (x, w i) ∂μ) =
        ∑ i, ∫ x in J, Y0 (x, w i) ∂μ := by
      exact Finset.sum_congr rfl (fun i _ => integral_congr_ae
        (ae_restrict_of_ae (hv (e i)).2.2))
    have hcharge : PhysicalPrimal.charge Y w = PhysicalPrimal.charge Y0 w := by
      unfold PhysicalPrimal.charge
      congr 1
      exact Finset.sum_congr rfl (fun ij _ =>
        (hp (e ij.val.1) (e ij.val.2) (fun h => ij.property (e.injective h))).2)
    rw [hYJJ, hGJJ, hstars, hcharge] at hb
    exact hb
  · have hz := P.capped n (Or.inl (by omega))
    simp only [hz, ae_zero, eventually_bot]


end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

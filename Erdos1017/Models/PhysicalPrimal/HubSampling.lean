module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Sampling a good hub tuple

Independent centered Hilbert-valued samples have a dimension-free centered sum
bound, so bounded features admit a good empirical approximation with a
quantitative sample size, and a single finite hub tuple controls almost every
row while retaining any additional almost-sure tuple conditions.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.FiniteArity

variable {Ω E ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

omit [IsProbabilityMeasure μ] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
private theorem integrable_inner_memLp {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫) μ := by
  apply (hf.norm.integrable_mul hg.norm).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => norm_inner_le_norm (f x) (g x))

/-- Orthogonality of independent centered Hilbert-valued samples gives the exact
second moment of their sum. -/
theorem independent_centered_second_moment (X : ι → Ω → E)
    (hind : iIndepFun X μ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hzero : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, ‖∑ i, X i ω‖ ^ 2 ∂μ) = ∑ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  classical
  have hint (i j : ι) : Integrable (fun ω => ⟪X i ω, X j ω⟫) μ :=
    integrable_inner_memLp (hX i) (hX j)
  have hoff (i j : ι) (hij : i ≠ j) : (∫ ω, ⟪X i ω, X j ω⟫ ∂μ) = 0 := by
    have h := (hind.indepFun hij).integral_bilin
      ((hX i).integrable (by norm_num)) ((hX j).integrable (by norm_num)) (innerSL ℝ)
    rw [hzero, hzero] at h
    convert h using 1 <;> first | rfl | simp
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  exact Finset.sum_eq_single i (fun j _ hij => hoff i j hij.symm) (by simp)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Centering removes precisely the squared norm of the mean. -/
theorem integral_centered_norm_sq (f : Ω → E) (hf : MemLp f 2 μ) (v : E)
    (hmean : ∫ ω, f ω ∂μ = v) :
    (∫ ω, ‖f ω - v‖ ^ 2 ∂μ) = (∫ ω, ‖f ω‖ ^ 2 ∂μ) - ‖v‖ ^ 2 := by
  have hfi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hi := hfi.inner_const (𝕜 := ℝ) v
  have hi2 : Integrable (fun ω => 2 * ⟪f ω, v⟫) μ := hi.const_mul 2
  have hsub : Integrable (fun ω => ‖f ω‖ ^ 2 - 2 * ⟪f ω, v⟫) μ := hsq.sub hi2
  simp_rw [norm_sub_sq_real]
  rw [integral_add hsub (integrable_const _),
    integral_sub hsq hi2, integral_const_mul, integral_const]
  have heq : (∫ ω, ⟪f ω, v⟫ ∂μ) = ‖v‖ ^ 2 := by
    simp_rw [real_inner_comm v (f _)]
    rw [integral_inner hfi, hmean, real_inner_self_eq_norm_sq]
  rw [heq]
  simp
  ring

/-- Independent samples with a common mean have a dimension-free centered sum bound. -/
theorem independent_centered_sum_bound (X : ι → Ω → E)
    (hind : iIndepFun X μ) (hX : ∀ i, MemLp (X i) 2 μ) (v : E)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = v) (R : ℝ)
    (hsecond : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ R ^ 2) :
    (∫ ω, ‖∑ i, (X i ω - v)‖ ^ 2 ∂μ) ≤ Fintype.card ι * R ^ 2 := by
  have hind' : iIndepFun (fun i ω => X i ω - v) μ :=
    hind.comp (fun _ x => x - v) (fun _ => (continuous_id.sub continuous_const).measurable)
  have hX' : ∀ i, MemLp (fun ω => X i ω - v) 2 μ := fun i => (hX i).sub (memLp_const v)
  have hzero : ∀ i, (∫ ω, X i ω - v ∂μ) = 0 := by
    intro i
    rw [integral_sub ((hX i).integrable (by norm_num)) (integrable_const v),
      hmean, integral_const]
    simp
  rw [independent_centered_second_moment _ hind' hX' hzero]
  calc
    (∑ i, ∫ ω, ‖X i ω - v‖ ^ 2 ∂μ) ≤ ∑ _ : ι, R ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [integral_centered_norm_sq _ (hX i) v (hmean i)]
      exact (sub_le_self _ (sq_nonneg _)).trans (hsecond i)
    _ = Fintype.card ι * R ^ 2 := by simp

/-- The preceding bound for the actual independent product sampling law. -/
theorem iid_centered_sum_bound (f : Ω → E) (hf : MemLp f 2 μ) (R : ℝ)
    (hsecond : (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ R ^ 2) :
    (∫ ω : ι → Ω, ‖∑ i, (f (ω i) - ∫ x, f x ∂μ)‖ ^ 2
      ∂Measure.pi (fun _ : ι => μ)) ≤ Fintype.card ι * R ^ 2 := by
  refine independent_centered_sum_bound (μ := Measure.pi (fun _ : ι => μ))
    (fun (i : ι) (ω : ι → Ω) => f (ω i))
    (iIndepFun_pi (fun _ => hf.aestronglyMeasurable.aemeasurable))
    (fun i => hf.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i))
    (∫ x, f x ∂μ) ?_ R ?_
  · intro i
    exact integral_comp_eval (μ := fun _ : ι => μ) (i := i) hf.aestronglyMeasurable
  · intro i
    rw [integral_comp_eval (μ := fun _ : ι => μ) (i := i)
      (f := fun ω => ‖f ω‖ ^ 2) (hf.aestronglyMeasurable.norm.pow 2)]
    exact hsecond

/-- A good hub sample exists inside any prescribed probability-one set of tuples.
This retains the Fubini section and distinctness conditions needed by the source. -/
theorem exists_good_sample (f : Ω → E) (hf : MemLp f 2 μ) (R q : ℝ)
    (hsecond : (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ R ^ 2)
    (hq : Fintype.card ι * R ^ 2 < q) (Good : (ι → Ω) → Prop)
    (hGood : ∀ᵐ ω ∂Measure.pi (fun _ : ι => μ), Good ω) :
    ∃ ω : ι → Ω, Good ω ∧ ‖∑ i, (f (ω i) - ∫ x, f x ∂μ)‖ ^ 2 < q := by
  by_contra hno
  push Not at hno
  have hbound : ∀ᵐ ω ∂Measure.pi (fun _ : ι => μ),
      q ≤ ‖∑ i, (f (ω i) - ∫ x, f x ∂μ)‖ ^ 2 := by
    filter_upwards [hGood] with ω hω
    exact hno ω hω
  have hsum : MemLp (fun ω : ι → Ω => ∑ i, (f (ω i) - ∫ x, f x ∂μ)) 2
      (Measure.pi (fun _ : ι => μ)) := by
    apply memLp_finsetSum
    intro i _
    exact (hf.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)).sub
      (memLp_const _)
  have hint := (memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).mp hsum
  have hlow := integral_mono_ae (integrable_const q) hint hbound
  simp only [integral_const, probReal_univ, one_smul] at hlow
  have hupp := iid_centered_sum_bound (ι := ι) f hf R hsecond
  exact hq.not_ge (hlow.trans hupp)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem centered_average_eq (k : ℕ) (hk : 0 < k) (h : Fin k → E) (v : E) :
    (k : ℝ)⁻¹ • ∑ i, (h i - v) = (k : ℝ)⁻¹ • ∑ i, h i - v := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hk', one_smul]

/-- Bounded features admit a good empirical approximation with the quantitative
sample size required for the finite hub cover. -/
theorem exists_good_empirical_sample (k : ℕ) (hk : 0 < k) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) (R ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R) (hsize : R ^ 2 < k * ε ^ 2)
    (Good : (Fin k → Ω) → Prop)
    (hGood : ∀ᵐ ω ∂Measure.pi (fun _ : Fin k => μ), Good ω) :
    ∃ ω : Fin k → Ω, Good ω ∧
      ‖(k : ℝ)⁻¹ • ∑ i, f (ω i) - ∫ x, f x ∂μ‖ < ε := by
  have hLp : MemLp f 2 μ := MemLp.of_bound hf R hbound
  have hsecond : (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ R ^ 2 := by
    have hsq := (memLp_two_iff_integrable_sq_norm hf).mp hLp
    have h := integral_mono_ae hsq (integrable_const (R ^ 2))
      (hbound.mono (fun x hx => pow_le_pow_left₀ (norm_nonneg _) hx 2))
    simpa using h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨ω, hω, herr⟩ := exists_good_sample (ι := Fin k) f hLp R
    ((k : ℝ) ^ 2 * ε ^ 2) hsecond (by
      simp only [Fintype.card_fin]
      nlinarith [mul_lt_mul_of_pos_left hsize hk']) Good hGood
  refine ⟨ω, hω, ?_⟩
  rw [← centered_average_eq k hk, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk'), ← div_eq_inv_mul,
    div_lt_iff₀ hk']
  have hpos : 0 < ε * (k : ℝ) := mul_pos hε hk'
  nlinarith [norm_nonneg (∑ i, (f (ω i) - ∫ x, f x ∂μ))]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Cauchy–Schwarz turns empirical feature error into a uniform row error. -/
theorem inner_lower_of_feature_error (J : E →ₗᵢ[ℝ] E) (u v z : E) (ε R : ℝ)
    (hu : ‖u - v‖ ≤ ε) (hz : ‖z‖ ≤ R) :
    ⟪J v, z⟫ - ε * R ≤ ⟪J u, z⟫ := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hu
  have hnorm : ‖J u - J v‖ = ‖u - v‖ := by rw [← J.map_sub, J.norm_map]
  have h : |⟪J u - J v, z⟫| ≤ ε * R := by
    calc
      _ ≤ ‖J u - J v‖ * ‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ ε * R := by rw [hnorm]; exact mul_le_mul hu hz (norm_nonneg _) hε
  rw [inner_sub_left] at h
  have hlo := (abs_le.mp h).1
  linarith

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The actual hub charges inherit the uniform mean-row lower bound. -/
theorem hub_charge_lower (k : ℕ) (hk : 0 < k) (J : E →ₗᵢ[ℝ] E)
    (h : Fin k → E) (v z : E) (Y : Fin k → ℝ) (ν ℓ ε R : ℝ)
    (herr : ‖(k : ℝ)⁻¹ • ∑ i, h i - v‖ ≤ ε) (hz : ‖z‖ ≤ R)
    (hrow : ⟪J v, z⟫ = ν) (hY : ∀ i, ⟪J (h i), z⟫ - ℓ ≤ Y i) :
    ν - ℓ - ε * R ≤ (k : ℝ)⁻¹ * ∑ i, Y i := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hfeature := inner_lower_of_feature_error J ((k : ℝ)⁻¹ • ∑ i, h i) v z ε R herr hz
  rw [hrow] at hfeature
  have hinner : ⟪J ((k : ℝ)⁻¹ • ∑ i, h i), z⟫ =
      (k : ℝ)⁻¹ * ∑ i, ⟪J (h i), z⟫ := by
    rw [J.map_smul, map_sum J, real_inner_smul_left, sum_inner]
  rw [hinner] at hfeature
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hY i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have havg := mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hk').le
  have hcancel : (k : ℝ)⁻¹ * ((k : ℝ) * ℓ) = ℓ := by
    rw [← mul_assoc, inv_mul_cancel₀ hk'.ne', one_mul]
  rw [mul_sub, hcancel] at havg
  linarith

/-- A single finite hub tuple controls almost every row, while retaining any
additional almost-sure tuple conditions supplied by the clique-section argument. -/
theorem exists_hub_cover (k : ℕ) (hk : 0 < k) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) (J : E →ₗᵢ[ℝ] E) (Y : Ω → Ω → ℝ)
    (ν ℓ R ε : ℝ) (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R)
    (hsize : R ^ 2 < k * ε ^ 2)
    (hrow : ∀ᵐ x ∂μ, ⟪J (∫ y, f y ∂μ), f x⟫ = ν)
    (hpair : ∀ᵐ h ∂μ, ∀ᵐ x ∂μ, ⟪J (f h), f x⟫ - ℓ ≤ Y h x)
    (Good : (Fin k → Ω) → Prop)
    (hGood : ∀ᵐ ω ∂Measure.pi (fun _ : Fin k => μ), Good ω) :
    ∃ ω : Fin k → Ω, Good ω ∧
      ∀ᵐ x ∂μ, ν - ℓ - ε * R ≤ (k : ℝ)⁻¹ * ∑ i, Y (ω i) x := by
  have hsections : ∀ᵐ ω ∂Measure.pi (fun _ : Fin k => μ),
      ∀ i, ∀ᵐ x ∂μ, ⟪J (f (ω i)), f x⟫ - ℓ ≤ Y (ω i) x := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin k => μ) i).quasiMeasurePreserving.ae hpair
  obtain ⟨ω, hω, herr⟩ := exists_good_empirical_sample k hk f hf R ε hε hbound hsize
    (fun ω => Good ω ∧ ∀ i, ∀ᵐ x ∂μ, ⟪J (f (ω i)), f x⟫ - ℓ ≤ Y (ω i) x)
    (hGood.and hsections)
  refine ⟨ω, hω.1, ?_⟩
  filter_upwards [hbound, hrow, ae_all_iff.mpr hω.2] with x hx hrowx hpairx
  exact hub_charge_lower k hk J (fun i => f (ω i)) (∫ y, f y ∂μ) (f x)
    (fun i => Y (ω i) x) ν ℓ ε R herr.le hx hrowx hpairx

end Erdos1017.FiniteArity

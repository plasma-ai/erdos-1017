module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassInternalTuran
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Realizing an internal density by multipartite part masses

Interpolating from one unit part to `k` equal parts, every Turán-admissible
internal edge density is attained by nonnegative complete multipartite part
masses (`exists_part_masses`), and a zero restricted clique test produces such a
realization on fresh labels.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos1017.MultipartiteDensityRealization

/-- Interpolate from one unit independent part to equally weighted parts. -/
def partMassPath {k : ℕ} (i₀ : Fin k) (t : ℝ) (i : Fin k) : ℝ :=
  (if i = i₀ then 1 - t else 0) + t / k

theorem partMassPath_sum {k : ℕ} (hk : 0 < k) (i₀ : Fin k) (t : ℝ) :
    ∑ i, partMassPath i₀ t i = 1 := by
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [partMassPath, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem partMassPath_nonneg {k : ℕ} (hk : 0 < k) (i₀ : Fin k)
    {t : ℝ} (ht : t ∈ Icc 0 1) (i : Fin k) : 0 ≤ partMassPath i₀ t i := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hi : i = i₀
  · simp only [partMassPath, hi, ↓reduceIte]
    exact add_nonneg (sub_nonneg.mpr ht.2) (div_nonneg ht.1 hkreal.le)
  · simp only [partMassPath, hi, ↓reduceIte, zero_add]
    exact div_nonneg ht.1 hkreal.le

theorem partMassPath_pos {k : ℕ} (hk : 0 < k) (i₀ : Fin k)
    {t : ℝ} (ht : t ∈ Icc 0 1) (ht0 : 0 < t) (i : Fin k) :
    0 < partMassPath i₀ t i := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hi : i = i₀
  · simp only [partMassPath, hi, ↓reduceIte]
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (div_pos ht0 hkreal)
  · simp only [partMassPath, hi, ↓reduceIte, zero_add]
    exact div_pos ht0 hkreal

theorem partMassPath_square_zero {k : ℕ} (i₀ : Fin k) :
    (∑ i, partMassPath i₀ 0 i ^ 2) = 1 := by
  simp [partMassPath]

theorem partMassPath_square_one {k : ℕ} (hk : 0 < k) (i₀ : Fin k) :
    (∑ i, partMassPath i₀ 1 i ^ 2) = 1 / (k : ℝ) := by
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [partMassPath, sub_self, ite_self, zero_add, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem partMassPath_square_continuous {k : ℕ} (i₀ : Fin k) :
    Continuous (fun t : ℝ => ∑ i, partMassPath i₀ t i ^ 2) := by
  have hi (i : Fin k) : Continuous (fun t : ℝ => partMassPath i₀ t i) := by
    by_cases h : i = i₀
    · simp [partMassPath, h]
      fun_prop
    · simp [partMassPath, h]
      fun_prop
  exact continuous_finsetSum _ (fun i _ => (hi i).pow 2)

/-- Every Turán-admissible internal edge density is attained by actual
nonnegative complete multipartite part masses. Positive density makes each
of the chosen `k` parts positive. -/
theorem exists_part_masses (k : ℕ) (hk : 0 < k) (q : ℝ)
    (hq0 : 0 ≤ q) (hqk : q ≤ 1 - 1 / (k : ℝ)) :
    ∃ a : Fin k → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧
      (∑ i, (a i) ^ 2) = 1 - q ∧ (0 < q → ∀ i, 0 < a i) := by
  let i₀ : Fin k := ⟨0, hk⟩
  let f : ℝ → ℝ := fun t => ∑ i, partMassPath i₀ t i ^ 2
  have hf : Continuous f := partMassPath_square_continuous i₀
  have htarget : 1 - q ∈ Icc (f 1) (f 0) := by
    rw [show f 1 = 1 / (k : ℝ) from partMassPath_square_one hk i₀,
      show f 0 = 1 from partMassPath_square_zero i₀]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn htarget
  refine ⟨partMassPath i₀ t, partMassPath_nonneg hk i₀ ht,
    partMassPath_sum hk i₀ t, hft, ?_⟩
  intro hq i
  have ht0 : 0 < t := by
    by_contra hn
    have htz : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
    dsimp [f] at hft
    rw [htz, partMassPath_square_zero] at hft
    linarith
  exact partMassPath_pos hk i₀ ht ht0 i

/-- The actual finite probability law with the realized part masses. -/
def labelLaw {k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = 1) : Measure (Fin k) :=
  (PMF.ofFintype (fun i => ENNReal.ofReal (a i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i), hsum]
    norm_num)).toMeasure

instance labelLaw_probability {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    IsProbabilityMeasure (labelLaw a ha hsum) := by
  unfold labelLaw
  infer_instance

theorem labelLaw_singleton {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) (i : Fin k) :
    labelLaw a ha hsum {i} = ENNReal.ofReal (a i) := by
  simp [labelLaw]

/-- Every exact finite label tuple has its independent product mass. -/
theorem labelTuple_singleton {k j : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) (b : Fin j → Fin k) :
    Measure.pi (fun _ : Fin j => labelLaw a ha hsum) {b} =
      ∏ i, ENNReal.ofReal (a (b i)) := by
  rw [Measure.pi_singleton]
  simp only [labelLaw_singleton]

theorem labelTuple_singleton_pos {k j : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) (b : Fin j → Fin k)
    (hb : ∀ i, 0 < a (b i)) :
    0 < Measure.pi (fun _ : Fin j => labelLaw a ha hsum) {b} := by
  rw [labelTuple_singleton]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (ENNReal.ofReal_pos.mpr (hb i)).ne'

end Erdos1017.MultipartiteDensityRealization

namespace Erdos1017.CappedModel

/-- The actual zero restricted clique test and Turán bound produce a
finite complete multipartite internal density realization on fresh labels. -/
theorem exists_part_masses_of_restricted_clique_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Model Ω μ) (s : Set Ω) (hpos : 0 < μ s)
    (k : ℕ) (hk : 0 < k)
    (hzero : restrictedCliquePresence W s (k + 1) = 0) :
    ∃ a : Fin k → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧
      (∑ i, (a i) ^ 2) = 1 - 2 * density (conditionOn W s hpos) ∧
      (0 < density (conditionOn W s hpos) → ∀ i, 0 < a i) := by
  let q := 2 * density (conditionOn W s hpos)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    rw [density_conditionOn]
    apply mul_nonneg (by norm_num)
    apply div_nonneg
    · apply integral_nonneg
      intro p
      exact (W.moment_mem_Icc CappedColor.continuous_adjacency.stronglyMeasurable
        CappedColor.adjacency_mem p).1
    · positivity
  have hqk : q ≤ 1 - 1 / (k : ℝ) := by
    have h := internal_density_le_turan_of_zero_restricted_clique W s hpos k hk hzero
    have heq : q = (∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ) /
        (μ.real s) ^ 2 := by
      dsimp [q]
      rw [density_conditionOn]
      ring
    rw [heq]
    exact h
  obtain ⟨a, ha, hsum, hsquare, hposparts⟩ :=
    MultipartiteDensityRealization.exists_part_masses k hk q hq0 hqk
  exact ⟨a, ha, hsum, hsquare, fun hd => hposparts (by dsimp [q]; linarith)⟩

end Erdos1017.CappedModel

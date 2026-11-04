module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Small density return with positive quadratic gain

A small signed vertex edit and a small positive completion parameter return an
exact quadratic density change to zero while keeping a strictly positive
quadratic gain (`exists_small_exact_density_return`).
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Erdos1017.CompletionDensityReturn

/-- A small signed vertex edit and a small positive completion parameter
return an exact quadratic density change to zero while keeping a strictly
positive quadratic gain. The completion coefficient need only be positive
and continuous at the origin. -/
theorem exists_small_exact_density_return
    (L qGraph qShift : ℝ) (Z : ℝ → ℝ)
    (hL : L ≠ 0) (hZ : ContinuousAt Z 0) (hZ0 : 0 < Z 0)
    (hQ : 0 < qShift) (ε : ℝ) (hε : 0 < ε) :
    ∃ s t : ℝ, |s| < ε ∧ t ∈ Ioo (0 : ℝ) 1 ∧ t < ε ∧ L * s < 0 ∧
      t = -(L * s + qGraph * s ^ 2) / Z s ∧
        L * s + qGraph * s ^ 2 + t * Z s = 0 ∧
          0 < qShift * s ^ 2 := by
  let s : ℝ → ℝ := fun a => -a * L
  let t : ℝ → ℝ := fun a => -(L * s a + qGraph * (s a) ^ 2) / Z (s a)
  have hscont : ContinuousAt s 0 := by fun_prop
  have hZcont : ContinuousAt (fun a => Z (s a)) 0 := by
    simpa only [Function.comp_def] using hZ.comp_of_eq hscont (by simp [s])
  have htcont : ContinuousAt t 0 := by
    dsimp [t]
    have hnumcont : ContinuousAt (fun a => -(L * s a + qGraph * (s a) ^ 2)) 0 := by
      fun_prop
    exact hnumcont.div hZcont (by simpa [s] using hZ0.ne')
  have ht0 : t 0 = 0 := by simp [t, s]
  have hsmall : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), |s a| < ε := by
    have hc : ContinuousAt (fun a => |s a|) 0 := hscont.abs
    exact hc.eventually (eventually_lt_nhds (by simpa [s] using hε))
  have htε : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), t a < ε :=
    htcont.eventually (eventually_lt_nhds (by simpa [ht0] using hε))
  have ht1 : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), t a < 1 :=
    htcont.eventually (eventually_lt_nhds (by simp [ht0]))
  have hZpos : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), 0 < Z (s a) :=
    hZcont.eventually (eventually_gt_nhds (by simpa [s] using hZ0))
  have hqcont : ContinuousAt (fun a : ℝ => qGraph * a) 0 := by fun_prop
  have hqsmall : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), qGraph * a < 1 :=
    hqcont.eventually (eventually_lt_nhds (by norm_num))
  have hnear : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      0 < a ∧ |s a| < ε ∧ t a < ε ∧ t a < 1 ∧ 0 < Z (s a) ∧ qGraph * a < 1 := by
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      htε.filter_mono nhdsWithin_le_nhds, ht1.filter_mono nhdsWithin_le_nhds,
      hZpos.filter_mono nhdsWithin_le_nhds,
      hqsmall.filter_mono nhdsWithin_le_nhds] with a ha hs htε ht1 hZ hq
    exact ⟨ha, hs, htε, ht1, hZ, hq⟩
  obtain ⟨a, ha, hsε, htaε, hta1, hZa, hqa⟩ := hnear.exists
  have hLsq : 0 < L ^ 2 := sq_pos_of_ne_zero hL
  have hLs : L * s a < 0 := by
    change L * (-a * L) < 0
    nlinarith [mul_pos ha hLsq]
  have hnum : L * s a + qGraph * (s a) ^ 2 < 0 := by
    calc
      L * s a + qGraph * (s a) ^ 2 = a * L ^ 2 * (qGraph * a - 1) := by
        dsimp [s]
        ring
      _ < 0 := mul_neg_of_pos_of_neg (mul_pos ha hLsq) (sub_neg.mpr hqa)
  have hta0 : 0 < t a := div_pos (neg_pos.mpr hnum) hZa
  have hZa0 : Z (s a) ≠ 0 := ne_of_gt hZa
  have hdensity : L * s a + qGraph * (s a) ^ 2 + t a * Z (s a) = 0 := by
    dsimp [t]
    field_simp
    ring
  have hsa : s a ≠ 0 := by
    change -a * L ≠ 0
    exact mul_ne_zero (neg_ne_zero.mpr ha.ne') hL
  have hgain : 0 < qShift * (s a) ^ 2 :=
    mul_pos hQ (sq_pos_of_ne_zero hsa)
  exact ⟨s a, t a, hsε, ⟨hta0, hta1⟩, htaε, hLs, rfl, hdensity, hgain⟩

end Erdos1017.CompletionDensityReturn

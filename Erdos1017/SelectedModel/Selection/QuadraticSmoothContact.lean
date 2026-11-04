module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FunProp

/-!
# Contact and curvature for quadratic curves

A twice continuously differentiable function has nonpositive second derivative
at a local maximum, which gives first-order contact of exact quadratic density
and objective curves and controls the unhalved second variation by the second
derivative of a smooth comparison curve.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Erdos1017.SmoothContact

/-- A twice continuously differentiable real function has nonpositive
second derivative at a local maximum. -/
theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hmax : IsLocalMax f 0) : deriv (deriv f) 0 ≤ 0 := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  let I : Set ℝ := Ioo (-ε) ε
  have hI : I ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) hε
  have hsub : I ⊆ s := by
    intro x hx
    apply hball
    simpa only [I, mem_Ioo, Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using hx
  have hcont : ContDiffOn ℝ 2 f I := hfs.mono hsub
  have hzero : deriv f 0 = 0 := hmax.deriv_eq_zero
  have hiter (k : ℕ) (hk : k ≤ 2) :
      iteratedDerivWithin k f I 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo _ _) (hf.of_le (by exact_mod_cast hk))
      (mem_of_mem_nhds hI)
  have hpoly (x : ℝ) : taylorWithinEval f 2 I 0 x = f 0 + deriv (deriv f) 0 * x ^ 2 / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hiter 0 (by omega), hiter 1 (by omega), hiter 2 (by omega)]
    simp [iteratedDeriv_succ, hzero]
    ring
  dsimp only [I] at hpoly
  have ht := Real.taylor_tendsto (f := f) (n := 2) (convex_Ioo _ _) (mem_of_mem_nhds hI) hcont
  rw [nhdsWithin_eq_nhds.mpr hI] at ht
  simp only [hpoly, sub_zero] at ht
  have ht' := ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hle : 0 ≤ -deriv (deriv f) 0 / 2 := by
    apply le_of_tendsto ht'
    filter_upwards [hmax.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hx0
    have hx : f x ≤ f 0 := hx
    have hx0 : 0 < x := hx0
    apply (div_le_iff₀ (sq_pos_of_pos hx0)).mpr
    nlinarith
  linarith

private theorem quadratic_hasDerivAt (c a q t : ℝ) :
    HasDerivAt (fun t : ℝ => c + t * a + t ^ 2 * q / 2) (a + t * q) t := by
  convert ((hasDerivAt_const t c).add ((hasDerivAt_id t).mul_const a)).add
    ((((hasDerivAt_id t).pow 2).mul_const q).div_const 2) using 1
  · funext x
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq]
    ring

/-- First-order contact of exact quadratic density and objective curves. -/
theorem quadratic_first_variation {B : ℝ → ℝ} {d c a y qA qY β : ℝ}
    (hB : HasDerivAt B β d)
    (hmax : IsLocalMax
      (fun t : ℝ => c + t * y + t ^ 2 * qY / 2 - B (d + t * a + t ^ 2 * qA / 2)) 0) :
    y = β * a := by
  have hcomp := hB.comp_of_eq 0 (quadratic_hasDerivAt d a qA 0) (by simp)
  have h := hmax.hasDerivAt_eq_zero ((quadratic_hasDerivAt c y qY 0).sub hcomp)
  simp only [zero_mul, add_zero] at h
  linarith

/-- The unhalved second variation is controlled in every direction by the
second derivative of the supplied smooth comparison curve. -/
theorem quadratic_curvature {B : ℝ → ℝ} {d c a y qA qY : ℝ}
    (hB : ContDiffAt ℝ 2 B d)
    (hmax : IsLocalMax
      (fun t : ℝ => c + t * y + t ^ 2 * qY / 2 - B (d + t * a + t ^ 2 * qA / 2)) 0) :
    qY - deriv B d * qA ≤ deriv (deriv B) d * a ^ 2 := by
  let D := fun t : ℝ => d + t * a + t ^ 2 * qA / 2
  let H := fun t : ℝ => c + t * y + t ^ 2 * qY / 2 - B (D t)
  have hD0 : D 0 = d := by simp [D]
  have hD : ContDiffAt ℝ 2 D 0 := by fun_prop
  have hBc : ContDiffAt ℝ 2 B (D 0) := hD0.symm ▸ hB
  have hH : ContDiffAt ℝ 2 H 0 := (by fun_prop :
    ContDiffAt ℝ 2 (fun t : ℝ => c + t * y + t ^ 2 * qY / 2) 0).sub (hBc.comp 0 hD)
  have hderiv : deriv H =ᶠ[nhds 0]
      (fun t : ℝ => y + t * qY - deriv B (D t) * (a + t * qA)) := by
    have hDt : Tendsto D (nhds 0) (nhds d) := by simpa only [hD0] using hD.continuousAt.tendsto
    have hnear : ∀ᶠ t : ℝ in nhds 0, ContDiffAt ℝ 2 B (D t) :=
      hDt.eventually (hB.eventually (by norm_num))
    filter_upwards [hnear] with t ht
    have hcomp := (ht.differentiableAt (by norm_num)).hasDerivAt.comp t
      (quadratic_hasDerivAt d a qA t)
    exact ((quadratic_hasDerivAt c y qY t).sub hcomp).deriv
  have hB' : HasDerivAt (deriv B) (deriv (deriv B) d) d :=
    (hB.derivWithin (m := 1) (by norm_num)).differentiableAt_one.hasDerivAt
  have hcomp := hB'.comp_of_eq 0 (quadratic_hasDerivAt d a qA 0) (by simp)
  have hformula := ((hasDerivAt_const (0 : ℝ) y).add
    ((hasDerivAt_id 0).mul_const qY)).sub
    (hcomp.mul ((hasDerivAt_const (0 : ℝ) a).add ((hasDerivAt_id 0).mul_const qA)))
  have hsecond := hformula.congr_of_eventuallyEq hderiv
  have heq := hsecond.deriv
  simp only [Pi.add_apply, Function.comp_apply, id_eq, zero_mul, add_zero, one_mul,
    zero_add, zero_pow (by omega : 2 ≠ 0), zero_div] at heq
  have hnonpos := second_deriv_nonpos_of_local_max hH hmax
  rw [heq] at hnonpos
  nlinarith

end Erdos1017.SmoothContact

module

public import Erdos1017.SelectedModel.Selection.QuadraticSmoothContact

/-!
# One-sided curvature bound of the quadratic contact curve

A one-sided maximum of the exact quadratic contact curve whose first variation
vanishes gives the unhalved curvature bound (`quadratic_right_curvature`).
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Erdos1017.SmoothContact

private theorem second_deriv_nonpos_of_right_local_max {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hzero : deriv f 0 = 0)
    (hmax : IsLocalMaxOn f (Ici 0) 0) : deriv (deriv f) 0 ≤ 0 := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  let I : Set ℝ := Ioo (-ε) ε
  have hI : I ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) hε
  have hsub : I ⊆ s := by
    intro x hx
    apply hball
    simpa only [I, mem_Ioo, Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using hx
  have hcont : ContDiffOn ℝ 2 f I := hfs.mono hsub
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
  have hmax' : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi 0), f x ≤ f 0 :=
    hmax.filter_mono (nhdsWithin_mono 0 (fun _ hx => le_of_lt hx))
  have hle : 0 ≤ -deriv (deriv f) 0 / 2 := by
    apply le_of_tendsto ht'
    filter_upwards [hmax', self_mem_nhdsWithin] with x hx hx0
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

/-- A one-sided maximum of the exact quadratic contact curve gives the
unhalved curvature bound when its actual first variation vanishes. -/
theorem quadratic_right_curvature {B : ℝ → ℝ} {d c a y qA qY : ℝ}
    (hB : ContDiffAt ℝ 2 B d) (hfirst : y = deriv B d * a)
    (hmax : IsLocalMaxOn
      (fun t : ℝ => c + t * y + t ^ 2 * qY / 2 - B (d + t * a + t ^ 2 * qA / 2))
      (Ici 0) 0) :
    qY - deriv B d * qA ≤ deriv (deriv B) d * a ^ 2 := by
  let D := fun t : ℝ => d + t * a + t ^ 2 * qA / 2
  let H := fun t : ℝ => c + t * y + t ^ 2 * qY / 2 - B (D t)
  have hD0 : D 0 = d := by simp [D]
  have hD : ContDiffAt ℝ 2 D 0 := by fun_prop
  have hBc : ContDiffAt ℝ 2 B (D 0) := hD0.symm ▸ hB
  have hH : ContDiffAt ℝ 2 H 0 := (by fun_prop :
    ContDiffAt ℝ 2 (fun t : ℝ => c + t * y + t ^ 2 * qY / 2) 0).sub (hBc.comp 0 hD)
  have hDfirst : HasDerivAt D a 0 := by
    simpa only [zero_mul, add_zero] using quadratic_hasDerivAt d a qA 0
  have hYfirst : HasDerivAt (fun t : ℝ => c + t * y + t ^ 2 * qY / 2) y 0 := by
    simpa only [zero_mul, add_zero] using quadratic_hasDerivAt c y qY 0
  have hHfirst : HasDerivAt H (y - deriv B d * a) 0 :=
    hYfirst.sub ((hB.differentiableAt (by norm_num)).hasDerivAt.comp_of_eq 0 hDfirst hD0.symm)
  have hzero : deriv H 0 = 0 := by
    rw [hHfirst.deriv, hfirst, sub_self]
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
  have hnonpos := second_deriv_nonpos_of_right_local_max hH hzero hmax
  rw [heq] at hnonpos
  nlinarith

end Erdos1017.SmoothContact

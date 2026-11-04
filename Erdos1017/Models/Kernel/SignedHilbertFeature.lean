module

public import Erdos1017.Models.Kernel.CountableHilbertFeature

/-!
# Signs for the indefinite feature representation

`signChange` reverses the negative spectral coordinates and `spectralSign` is
the self-adjoint linear isometry that supplies the signs in the indefinite
spectral feature representation; signed feature inner products equal the
spectral series whenever the coordinate identities hold.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {ι : Type*}

/-- Coordinatewise sign reversal on the negative spectral coordinates. -/
def signChange (t : ι → ℝ) (f : lp (fun _ : ι => ℝ) 2) : lp (fun _ : ι => ℝ) 2 :=
  ⟨fun i => if t i < 0 then -f i else f i,
    (lp.memℓp f).mono' (fun i => by split_ifs <;> simp)⟩

theorem signChange_norm (t : ι → ℝ) (f : lp (fun _ : ι => ℝ) 2) :
    ‖signChange t f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num)
    intro i
    change ‖if t i < 0 then -f i else f i‖ ≤ ‖f i‖
    split_ifs <;> simp
  · apply lp.norm_mono (by norm_num)
    intro i
    change ‖f i‖ ≤ ‖if t i < 0 then -f i else f i‖
    split_ifs <;> simp

/-- The self-adjoint linear isometry supplying the signs in the indefinite
spectral feature representation. -/
def spectralSign (t : ι → ℝ) :
    lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] lp (fun _ : ι => ℝ) 2 where
  toFun := signChange t
  map_add' f g := by
    apply lp.ext
    funext i
    change (if t i < 0 then -(f i + g i) else f i + g i) =
      (if t i < 0 then -f i else f i) + (if t i < 0 then -g i else g i)
    by_cases hi : t i < 0 <;> simp [hi, add_comm]
  map_smul' c f := by
    apply lp.ext
    funext i
    change (if t i < 0 then -(c * f i) else c * f i) =
      c * (if t i < 0 then -f i else f i)
    by_cases hi : t i < 0 <;> simp [hi]
  norm_map' := signChange_norm t

theorem spectralSign_self_adjoint (t : ι → ℝ) (f g : lp (fun _ : ι => ℝ) 2) :
    ⟪spectralSign t f, g⟫ = ⟪f, spectralSign t g⟫ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  by_cases hi : t i < 0 <;> simp [spectralSign, signChange, hi, RCLike.inner_apply]

theorem signed_sqrt_mul (t a b : ℝ) :
    (if t < 0 then -(Real.sqrt |t| * a) else Real.sqrt |t| * a) *
      (Real.sqrt |t| * b) = t * a * b := by
  have hs := Real.sq_sqrt (abs_nonneg t)
  by_cases ht : t < 0
  · rw [ite_eq_left ht]
    calc
      -(Real.sqrt |t| * a) * (Real.sqrt |t| * b) = -(Real.sqrt |t|) ^ 2 * a * b := by ring
      _ = t * a * b := by rw [hs, abs_of_neg ht]; ring
  · rw [ite_eq_right ht]
    calc
      (Real.sqrt |t| * a) * (Real.sqrt |t| * b) = (Real.sqrt |t|) ^ 2 * a * b := by ring
      _ = t * a * b := by rw [hs, abs_of_nonneg (le_of_not_gt ht)]

/-- Signed feature inner products equal the spectral series whenever the
coordinate identities hold. -/
theorem spectralSign_inner_eq_tsum (t a b : ι → ℝ)
    (F G : lp (fun _ : ι => ℝ) 2)
    (hF : ∀ i, F i = Real.sqrt |t i| * a i)
    (hG : ∀ i, G i = Real.sqrt |t i| * b i) :
    ⟪spectralSign t F, G⟫ = ∑' i, t i * a i * b i := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  change inner ℝ (if t i < 0 then -F i else F i) (G i) = _
  rw [RCLike.inner_apply]
  simp only [conj_trivial, hF, hG]
  rw [mul_comm]
  exact signed_sqrt_mul _ _ _

end Erdos1017.KernelOperator
